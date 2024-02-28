import re
import subprocess
import tempfile
import os
from openai import OpenAI
import datetime
import csv

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
        obscurer_role = "Role: You will be given an answer key. Obscure the answer key so that the formatting and categories are clear (and exactly the same as the original) but the actual answer is gone. If the answer key is not numbered(meaning if it does not have columns numbered 1, 2, 3, etc; this does not mean it has numbers in it.), do NOT obscure the first column. DO NOT CHANGE THE FORMATTING OF THE ANSWER KEY. Only output the obscured answer key as a string and nothing else."
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
        decomposition_role = "Role: You will be given a complex logic puzzle. Your task is to break it down into smaller, more manageable questions or pieces that, when solved, will help in solving the overall puzzle. Provide a list of these questions."
        messages = [{"role": "system", "content": decomposition_role}, {"role": "user", "content": puzzle}]
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
        gradual_decomposition_role = "Role: Given a logic puzzle, break it down into sequential steps necessary for solving it. Start with the easiest or first logical step, and proceed to the next steps in order."

        # Add the initial puzzle and role to the conversation
        conversation_history.append({"role": "system", "content": gradual_decomposition_role})
        conversation_history.append({"role": "user", "content": puzzle})

        while True:
            # Ask for the next step in the decomposition
            ask_for_step = f"What is step {current_step} in solving this puzzle?"
            conversation_history.append({"role": "user", "content": ask_for_step})

            # Generate the response
            step_response = self.LLMapi.get_response(conversation_history)

            # Check if the response indicates completion or provides a valid next step
            if "there are no more steps" in step_response.lower() or step_response.strip() == "":
                break  # Exit the loop if no more steps are identified

            steps.append(step_response)
            current_step += 1

            # Update the conversation history with the response
            conversation_history.append({"role": "assistant", "content": step_response})

        return steps
