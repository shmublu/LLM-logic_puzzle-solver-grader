import re
import subprocess
import tempfile
import os
from openai import OpenAI
import datetime
import csv

class NaiveSolver:
    def __init__(self, LLMapi, example=None):
        self.example = example
        self.LLMapi = LLMapi
        self.conversation = [] if not self.example else [self.example, ""]
    def solve_puzzle(self, prompt):
        self.conversation.append(prompt)
        response = self.LLMapi.get_response(self.conversation)
        self.conversation.append(response)
        return response
    def clear(self):
        self.conversation = [] if not self.example else [self.example, ""]

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
    def getConversation(self):
        """
        Formats the conversation history into a string, labeling user and LLM entries.
        
        Returns:
            str: A formatted string of the conversation.
        """
        conversation_str = ""
        for i, entry in enumerate(self.conversation):
            label = "User: " if i % 2 == 0 else "LLM: "
            conversation_str += label + entry + "\n"
        return conversation_str
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


class PuzzleData:
    def __init__(self, answers, entities, clues):
        self.answers = answers
        self.entities = entities
        self.clues = clues

def read_file_contents(file_path):
    with open(file_path, 'r') as file:
        return file.read()

def process_puzzles(directory_path):
    import os

    puzzles = []

    for folder in os.listdir(directory_path):
        folder_path = os.path.join(directory_path, folder)

        if not os.path.isdir(folder_path):
            continue

        # Check for required files
        answers_path = os.path.join(folder_path, 'answers.txt')
        entities_path = os.path.join(folder_path, 'entities.txt')
        clues_path = os.path.join(folder_path, 'clues.txt')

        if os.path.exists(answers_path) and os.path.exists(entities_path) and os.path.exists(clues_path):
            answers = read_file_contents(answers_path)
            entities = read_file_contents(entities_path)
            clues = read_file_contents(clues_path)

            puzzles.append(PuzzleData(answers, entities, clues))

    return puzzles



timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
csv_file_name = f'LLM-SMT_log_{timestamp}.csv'
csv_file = open(csv_file_name, 'w', newline='')
csv_writer = csv.writer(csv_file)
csv_writer.writerow(['Puzzle', 'SMT-LIB Code', 'Attempted Solution', 'Full LLM Convo' , 'Grading Process', 'Grade', 'Solution'])

puzzles = process_puzzles("./data/puzzles")
for puzzle in puzzles:
    puzzle_description = puzzle.entities + "\n" + puzzle.clues
    solution = puzzle.answers
    print(puzzle_description)
    solver_role_text = (
    "Role: Encode the logic puzzle given to you into SMT-LIB code, taking into account all explicit and implicit facts. Make sure to set-logic in your code."
    "After encoding, I will submit the code to the z3 solver for analysis and return to you the output. If there is an error, "
    "carefully correct any syntactical mistakes or misinterpretations of the puzzle constraints in your code. "
    "Continuously refine your code and resubmit to me until I send you back a solution that precisely aligns with the puzzle's parameters. "
    "The phrase 'I am done.' should only be used to conclude your response when you have submitted the SMT-LIB code to me, "
    " you have received a model output, and are confident that this model accurately and completely solves the puzzle. "
    "In your final response, include the phrase 'I am done.' followed by the correct, error-free SMT-LIB code."
)

    grader_role_text = (
    "Role: Grade SMT-LIB solver outputs numerically. Use the answer key and the latest solver output "
    "to determine the score in the format X/Y. 'X' represents the number of correct assignments in the "
    "given answer; attempt to interpret the solution and find X even if the SMT model contains errors. 'Y' is the total number of assignments as per "
    "the answer key. Provide a detailed explanation of your thought process in calculating both X and Y."
    )

    solver_llm = LLMApi(role=solver_role_text)
    grader_llm = LLMApi(role=grader_role_text)
    solver = PuzzleSolver(solver_llm)
    grader = SolverGrader(grader_llm)

    # Use LLMApi to generate SMT-LIB code from the puzzle description
    next_input = puzzle_description
    max_conversation_length = 6
    latest_smt_code = ""
    for i in range(max_conversation_length):
        full_response, smt_lib_code = solver.solve_puzzle(next_input)
        if smt_lib_code and "(set-logic" in smt_lib_code:
            latest_smt_code = smt_lib_code
        if 'I am done.' in full_response:
            break
        next_input = solver.solve_with_z3(latest_smt_code)

    # Solve the puzzle using Z3
    attempted_solution = solver.solve_with_z3(latest_smt_code)
    #print(full_response, latest_smt_code, attempted_solution)
    full_convo = solver.getConversation()
    grading_full_response, grade = grader.get_grade(solution, full_convo, attempted_solution)
    csv_writer.writerow([puzzle_description, latest_smt_code, attempted_solution, full_convo,grading_full_response, grade, solution])
    print("SMT-LIB Code:\n", latest_smt_code)
    print("Solution:\n", attempted_solution)
    print("Grading Process: ", grading_full_response)
    print("Grade: ", grade)

"""
baseline LLM
vs us

benchmark the grader
"""