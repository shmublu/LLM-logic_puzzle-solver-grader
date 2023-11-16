import re
import subprocess
import tempfile
import os
from openai import OpenAI

class PuzzleSolver:
    def __init__(self, LLMapi, example=None):
        self.example = example
        self.LLMapi = LLMapi
        self.conversation = [] if not self.example else [self.example, ""]

    def solve_puzzle(self, prompt):
        self.conversation.append(prompt)
        response = self.LLMapi.get_response(self.conversation)
        self.conversation.append(response)
        query = self.extract_substring(response, "(set-logic", "(get-model)").replace('`', '')
        return response, query

    def clear(self):
        self.conversation = [] if not self.example else [self.example, ""]
    @staticmethod
    def extract_substring(s, b, e):
        # Find the starting position of the substring 'b'
        start = s.find(b)
        if start == -1:
            return ""  # 'b' not found in 's'

        # Find the starting position of the substring 'e' after 'b'
        end = s.find(e, start)
        if end == -1:
            return ""  # 'e' not found after 'b' in 's'

        # Return the substring from 'b' to 'e' inclusive
        # Add len(e) to include 'e' in the result
        return s[start:end + len(e)]
    def solve_with_z3(self,smt_lib_code):
        try:
            # Step 1: Create a temporary file
            with tempfile.NamedTemporaryFile(mode='w+', delete=False) as temp_file:
                temp_file_name = temp_file.name
                temp_file.write(smt_lib_code)

            # Step 2: Execute Z3 with the temporary file
            z3_command = ["z3", temp_file_name]
            result = subprocess.run(z3_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            print(result)

            # Step 3: Capture the output
            output = result.stdout if result.stdout else result.stderr

        except Exception as e:
            output = f"An error occurred: {e}"

        finally:
            # Clean up the temporary file
            if os.path.exists(temp_file_name):
                os.remove(temp_file_name)
            pass

        # Step 4: Return the output
        return output


class SolverGrader:
  def __init__(self, LLMapi, example=None):
        self.example = example
        self.LLMapi = LLMapi
        self.conversation = [] if not self.example else [self.example, ""]

  def get_grade(self, answer_key, llm_answer, smt_output):
        to_be_graded = [("Answer to be graded: " + llm_answer + "\nSMT-LIB Solver Output: " + smt_output + "\nAnswer Key: " +answer_key)]
        response = self.LLMapi.get_response(to_be_graded)
        return response, self.extract_answer(response)

  def extract_answer(self, s):
        pattern = r'\b(\d{1,3})/(\d{1,3})\b'
        matches = re.findall(pattern, s)
        valid_fractions = [(x, y) for x, y in matches if int(x) <= int(y)]
        if valid_fractions:
            return '/'.join(valid_fractions[-1])
        else:
            return None

class LLMApi:
    def __init__(self, role, model="gpt-4"):
        self.client = OpenAI()
        self.model = model
        self.role = role

    def get_response(self, conversation_history):
        # If there is existing conversation history, include it
        messages = self.process_conversation_history(conversation_history) if conversation_history else []

        # Adding the system instruction for the task
        messages = [{"role": "system", "content": self.role}] + messages

        # Generate the response
        response = self.client.chat.completions.create(
            model=self.model,
            messages=messages
        )

        # Extract and return the SMT-LIB code
        return response.choices[0].message.content

    @staticmethod
    def process_conversation_history(plaintext_history):
        """
        Processes a plaintext conversation history into a structured format.
        
        Args:
        plaintext_history (list): A list of strings representing the conversation history, 
                                  alternating between user and assistant messages.
        
        Returns:
        list: A list of dictionaries representing the structured conversation.
        """
        structured_history = []
        role = "user"  # Start with the assumption that the first message is from the user

        for message in plaintext_history:
            structured_history.append({"role": role, "content": message})
            # Alternate between 'user' and 'assistant' for each message
            role = "assistant" if role == "user" else "user"

        return structured_history


solver_llm = LLMApi(role="Generate SMT-LIB code that encodes each fact, whether implict or explicit, in the following logic puzzle. Make sure to set the logic and check-sat and get-model.")
grader_llm = LLMApi(role="Based on the answer to be graded, the SMT-LIB solver output use the answer key to grade it numerically in the form X/Y, where X is the number of correct assignments(from the answer to be graded) and Y is the total number of assignments(counted from the answer key).")
solver = PuzzleSolver(solver_llm)
grader = SolverGrader(grader_llm)


puzzle_description = '''Friends, Activities, Years

Dustin, James, Yvonne, Zachary
camping, cycling, hang gliding, kayaking
2001, 2002, 2003, 2004
The vacation with Dustin is either the 2004 holiday or the hang gliding holiday.
The kayaking trip was 2 years after the camping vacation.
The trip with Zachary was after the kayaking vacation.
The camping trip was 2 years before the vacation with James.'''

# Use LLMApi to generate SMT-LIB code from the puzzle description
full_response, smt_lib_code = solver.solve_puzzle(puzzle_description)

print(full_response, smt_lib_code)
# Solve the puzzle using Z3
attempted_solution = solver.solve_with_z3(smt_lib_code)
solution = '''Dustin went hang gliding in 2002
James went kayaking in 2003
Yvonne went camping in 2001
Zachary went cycling in 2004'''
full_response, grade = grader.get_grade(solution, attempted_solution, full_response)

print("SMT-LIB Code:\n", smt_lib_code)
print("Solution:\n", attempted_solution)
print("Grading Process: ", full_response)
print("Grade: ", grade)