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
        # Find the last occurrence of the substring 'b'
        start = s.rfind(b)
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
        self.conv_length = 0 if not example else len(example)

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


solver_llm = LLMApi(role="Generate SMT-LIB code that encodes each fact, whether implicit or explicit, in the following logic puzzle, one by one. After you respond, you will receive the output of your SMT-LIB code in z3; use it to correct your mistakes in coding. syntax and encoding the puzzle constraints. Make sure to set the logic and check-sat and get-model. Write 'I am done.' in your response, along with the SMT code, when you are sure of your response and it is free of errors.")
grader_llm = LLMApi(role="Based on the answer to be graded, the SMT-LIB solver output use the answer key to grade it numerically in the form X/Y, where X is the number of correct assignments(from the answer to be graded) and Y is the total number of assignments(counted from the answer key). Please give your thought process as well in calculating both X and Y.")
solver = PuzzleSolver(solver_llm)
grader = SolverGrader(grader_llm)


puzzle_description = '''customers, cake shapes, delivery dates

Becker, Ingram, Keller, Massey
bowling pin, rocket ship, sailboat, turtle
October 5, October 6, October 7, October 8
The October 8 delivery will be in the shape of a sailboat.
The order shaped like a bowling pin will be delivered sometime before Mrs. Keller's cake.
Mrs. Massey's cake will be delivered on October 8.
The order shaped like a turtle is either Mrs. Becker's order or Mrs. Massey's cake.
Mrs. Becker's cake will be delivered 1 day after the order shaped like a rocket ship.'''

# Use LLMApi to generate SMT-LIB code from the puzzle description
next_input = puzzle_description
max_conversation_length = 6
for i in range(max_conversation_length):
    full_response, smt_lib_code = solver.solve_puzzle(next_input)
    if 'I am done.' in full_response:
        break
    next_input = solver.solve_with_z3(smt_lib_code)
    print(full_response, next_input)

print(full_response, smt_lib_code)
# Solve the puzzle using Z3
attempted_solution = solver.solve_with_z3(smt_lib_code)
solution = '''Becker, turtle, October 7
Ingram, bowling pin, October 5
Keller, rocket ship, October 6
Massey, sailboat, October 8 '''
full_response, grade = grader.get_grade(solution, attempted_solution, full_response)

print("SMT-LIB Code:\n", smt_lib_code)
print("Solution:\n", attempted_solution)
print("Grading Process: ", full_response)
print("Grade: ", grade)