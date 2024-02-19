import re
import subprocess
import tempfile
import os
from openai import OpenAI
import datetime
import csv

class NaiveSolver:
    def __init__(self, LLMapi, examples=None):
        self.examples = examples
        self.LLMapi = LLMapi
        self.conversation = [] if not self.examples else [self.examples[0], self.examples[1]]
    def solve_puzzle(self, prompt):
        self.conversation.append(prompt)
        response = self.LLMapi.get_response(self.conversation)
        self.conversation.append(response)
        return response
    def clear(self):
        self.conversation = [] if not self.example else [self.examples[0], self.examples[1]]
    def getConversation(self):
        """
        Formats the conversation history into a string, labeling user and LLM entries.
        
        Returns:
            str: A formatted string of the conversation.
        """
        conversation_str = ""
        for i, entry in enumerate(self.conversation):
            if self.examples and i <2:
                continue
            label = "User: " if i % 2 == 0 else "LLM: "
            conversation_str += label + entry + "\n"
        return conversation_str

class PuzzleSolver:
    def __init__(self, LLMapi, examples=None):
        self.examples = examples
        self.LLMapi = LLMapi
        self.conversation = [example for example in self.examples] if self.examples else []

    def solve_puzzle(self, prompt):
        self.conversation.append(prompt)
        response = self.LLMapi.get_response(self.conversation)
        self.conversation.append(response)
        query = self.extract_substring(response, "(set-logic", "(get-model)").replace('`', '')
        return response, query

    def clear(self):
        self.conversation = self.conversation = [example for example in self.examples] if self.examples else []
    def getConversation(self):
        """
        Formats the conversation history into a string, labeling user and LLM entries.

        Returns:
            str: A formatted string of the conversation.
        """
        conversation_str = ""
        examples_length = len(self.examples) if self.examples else 0

        for i, entry in enumerate(self.conversation):
            if i < examples_length:
                continue 
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

  def get_grade(self, answer_key, llm_answer, smt_output= None):
        smt_solver_output = ("\nSMT-LIB Solver Output: " + smt_output) if smt_output else ""
        to_be_graded = [("Answer to be graded: " + llm_answer + smt_solver_output + "\nAnswer Key: " +answer_key)]
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
        self.client = OpenAI(organization='org-bY4lHDd6A0w5itFiXf15EdJ0',)
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
            temperature=0.01,
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
