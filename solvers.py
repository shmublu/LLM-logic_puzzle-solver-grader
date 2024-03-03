import re
import subprocess
import tempfile
import os
from openai import OpenAI
import tiktoken
import csv
from abc import ABC, abstractmethod
import requests


class BaseClient(ABC):
    @abstractmethod
    def get_response(self, role, conversation_history):
        pass


class OpenAIClient(BaseClient):
    def __init__(self, organization = os.environ["OPENAI_ORG_TOK"], model="gpt-3.5-turbo"):
        self.client = OpenAI(organization=organization)
        self.model = model

    def get_response(self, role, conversation_history):
        messages = [{"role": "system", "content": role}] + self.process_conversation_history(conversation_history)
        response = self.client.chat.completions.create(model=self.model, messages=messages)
        return response.choices[0].message.content

    @staticmethod
    def process_conversation_history(plaintext_history):
        structured_history = []
        role = "user"
        for message in plaintext_history:
            structured_history.append({"role": role, "content": message})
            role = "assistant" if role == "user" else "user"
        return structured_history
    
class HuggingFaceClient(BaseClient):
    def __init__(self, api_token= os.environ["HUGGING_FACE_TOK"], model="bigcode/starcoder2-15b"):
        self.api_url = f"https://api-inference.huggingface.co/models/{model}"
        self.headers = {"Authorization": f"Bearer {api_token}"}
        self.model = model  # Store model name for tracking

    def get_response(self, role, conversation_history):
        # Concatenate all messages for APIs that expect a single text input
        input_text = " ".join(conversation_history)  # Adjust as needed for your API's expected format
        try:
            response = requests.post(self.api_url, headers=self.headers, json={"inputs": input_text})
            response.raise_for_status()  # Raises HTTPError for bad responses
            data = response.json()
            # Assuming the response contains a key 'generated_text' or similar; adjust as needed
            return data[0].get("generated_text", "")
        except requests.exceptions.RequestException as e:
            return f"Error: {e}"
class LLMApi:
    def __init__(self, role="", client_type="OpenAI", **kwargs):
        if client_type == "OpenAI":
            self.client = OpenAIClient(**kwargs)
        elif client_type == "HuggingFace":
            self.client = HuggingFaceClient(**kwargs)
        else:
            raise ValueError("Unsupported client type")
        self.role = role
        self.model = self.client.model  # Use the model from the client
        self.tokens_sent = 0
        self.tokens_received = 0
        self.api_call_count = 0

    def get_response(self, conversation_history):
        # Token counting should be adapted if the encoding method changes
        response = self.client.get_response(self.role, conversation_history)
        self.api_call_count += 1
        if self.api_call_count >= 2:
            self.update_csv()
            self.api_call_count = 0
        return response

    def update_csv(self):
        filename = "tokens_count.csv"
        data = []
        model_found = False
        try:
            if os.path.exists(filename):
                with open(filename, 'r', newline='') as csvfile:
                    reader = csv.DictReader(csvfile)
                    for row in reader:
                        if row['Model'] == self.model:
                            row['Tokens Sent'] = int(row['Tokens Sent']) + self.tokens_sent
                            row['Tokens Received'] = int(row['Tokens Received']) + self.tokens_received
                            model_found = True
                        data.append(row)
        except FileNotFoundError:
            print("File not found. Creating a new file.")
        
        if not model_found:
            data.append({'Model': self.model, 'Tokens Sent': self.tokens_sent, 'Tokens Received': self.tokens_received})
        
        fieldnames = ['Model', 'Tokens Sent', 'Tokens Received']
        with open(filename, 'w', newline='') as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            if not os.path.exists(filename) or os.path.getsize(filename) == 0:
                writer.writeheader()
            writer.writerows(data)
        
        self.tokens_sent = 0
        self.tokens_received = 0

    def __del__(self):
        self.update_csv()



"""
class LLMApi:
    def __init__(self, role, model="gpt-3.5-turbo"):
        self.client = OpenAI(organization='org-bY4lHDd6A0w5itFiXf15EdJ0')  # Assuming OpenAI is imported
        self.model = model
        self.role = role
        self.encoding = tiktoken.encoding_for_model(model)
        self.tokens_sent = 0
        self.tokens_received = 0
        self.api_call_count = 0  # Counter for API calls

    def get_response(self, conversation_history):
        messages = self.process_conversation_history(conversation_history) if conversation_history else []
        messages = [{"role": "system", "content": self.role}] + messages

        for message in messages:
            self.tokens_sent += len(self.encoding.encode(message["content"]))

        response = self.client.chat.completions.create(
            model=self.model,
            temperature=0.01,
            messages=messages
        )

        response_content = response.choices[0].message.content
        self.tokens_received += len(self.encoding.encode(response_content))

        self.api_call_count += 1
        if self.api_call_count >= 2:
            self.update_csv()
            self.api_call_count = 0  # Reset the counter

        return response_content

    @staticmethod
    def process_conversation_history(plaintext_history):
        structured_history = []
        role = "user"

        for message in plaintext_history:
            structured_history.append({"role": role, "content": message})
            role = "assistant" if role == "user" else "user"

        return structured_history

    def update_csv(self):
            filename = "tokens_count.csv"
            data = []
            model_found = False

            try:
                with open(filename, 'r', newline='') as csvfile:
                    reader = csv.DictReader(csvfile)
                    for row in reader:
                        if row['Model'] == self.model:
                            row['Tokens Sent'] = int(row['Tokens Sent']) + self.tokens_sent
                            row['Tokens Received'] = int(row['Tokens Received']) + self.tokens_received
                            model_found = True
                        data.append(row)  # Move inside the loop to ensure all rows are added
            except FileNotFoundError:
                print("File not found. A new file will be created.")

            if not model_found:
                data.append({'Model': self.model, 'Tokens Sent': self.tokens_sent, 'Tokens Received': self.tokens_received})
            
            fieldnames = ['Model', 'Tokens Sent', 'Tokens Received']
            with open(filename, 'w', newline='') as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                writer.writeheader()
                writer.writerows(data)
            
            # Reset tokens count after updating CSV
            self.tokens_sent = 0
            self.tokens_received = 0
    def __del__(self):
        self.update_csv()
"""
class PuzzleData:
    def __init__(self, answers, entities, clues):
        self.answers = answers
        self.entities = entities
        self.clues = clues


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

  def get_grade(self, answer_key, llm_answer):
        to_be_graded = [("Answer to be graded: " + llm_answer + "\nAnswer Key: " +answer_key)]
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
        

class AnswerFormatter:
  def __init__(self):
        obscurer_role = "Role: You will be given an answer key. Obscure the answer key so that the formatting and categories are clear (and exactly the same as the original) but the actual answer is COMPLETELY gone and unreadable. DO NOT CHANGE THE FORMATTING OF THE ANSWER KEY. Only output the obscured answer key as a string and nothing else."
        consistency_checker = "Role: You will be given a list of logic puzzles clues and an attempted solution. Your job is to determine if the attempted solution is consistent with the logic puzzle clues. If it is consistent you can explain why and end with the exact words \"Therefore, it is consistent.\" If it is inconsistent, give a full explanation of which clues and assignments are inconsistent and WHY (be specific) and then end with the exact words \"Therefore, it is inconsistent.\" "
        smt_interpreter_role = "Role: You will be given a blank answer key, an LLM conversation and an SMT output. Use the LLM conversation to interpret the SMT output as faithfully as possible. Fill in the blank answer key using this information, interpretting it as close as you can to the SMT output. DO NOT CHANGE THE FORMATTING OF THE ANSWER KEY. Only output the answer key and nothing else."
        llm_only_interpreter_role = "Role: You will be given a blank answer key and an LLM conversation. Use the LLM conversation to interpret the SMT output as faithfully as possible. Fill in the blank answer key using this information, interpretting it as close as you can to the SMT output. Only output the answer key and nothing else."
        self.obscurer = LLMApi(obscurer_role)
        self.smt_interpreter = LLMApi(smt_interpreter_role)
        self.llm_only_interpreter = LLMApi(llm_only_interpreter_role)
        
        self.conversation = [] 
        self.conv_length = 0

  def obscure(self, answer_key):
        response = self.obscurer.get_response([answer_key])
        return response
  def check_consistency(self, clues, attempted_solution):
      response = self.smt_interpreter.get_response([("Puzzle clues: " + clues + "\nAttempted Solution: " + attempted_solution)])
      return response
  def interpret_smt(self, convo, smt, obsc_answer_key):
      response = self.smt_interpreter.get_response([("LLM Conversation: " + convo + "\nSMT Output: " + smt + "\nBlank Answer Key: " +obsc_answer_key)])
      return response
  def interpret_llm_only(self, convo, obsc_answer_key):
      response = self.llm_only_interpreter.get_response([("LLM Conversation: " + convo +  "\nBlank Answer Key: " +obsc_answer_key)])
      return response
      

  def extract_answer(self, s):
        pattern = r'\b(\d{1,3})/(\d{1,3})\b'
        matches = re.findall(pattern, s)
        valid_fractions = [(x, y) for x, y in matches if int(x) <= int(y)]
        if valid_fractions:
            return '/'.join(valid_fractions[-1])
        else:
            return None



class Decomposer:
    def __init__(self, LLMapi):
        self.LLMapi = LLMapi

    def decompose_puzzle(self, puzzle):
        messages = [puzzle]
        response = self.LLMapi.get_response(messages)
        questions = response.split('\n')
        return questions

    def gradual_decomp(self, puzzle):
        """
        Gradually decomposes a logic puzzle into steps, asking for each step one at a time.

        Args:
            puzzle (str): The logic puzzle to be decomposed.

        Returns:
            list: An ordered list of steps to solve the puzzle, from easiest to more complex.
        """
        steps = []
        current_step = 1
        conversation_history = []

        # Define a role message to guide the LLM through the gradual decomposition
        gradual_decomposition_role = "Role: Given a logic puzzle, break it down into sequential steps necessary for solving it. Start with the easiest or first logical step, and proceed to the next steps in order. When there are no more steps, give the exact phrase \"no more steps\"."

        conversation_history.append(puzzle)

        while True:
            # Ask for the next step in the decomposition
            ask_for_step = f"What is step {current_step} in solving this puzzle?"
            conversation_history.append(ask_for_step)

            # Generate the response
            step_response = self.LLMapi.get_response(conversation_history)

            # Check if the response indicates completion or provides a valid next step
            if "no more steps" in step_response.lower() or step_response.strip() == "":
                break  # Exit the loop if no more steps are identified

            steps.append(step_response)
            current_step += 1

            # Update the conversation history with the response
            conversation_history.append(step_response)

        return steps
