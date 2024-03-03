import re
import subprocess
import tempfile
import os
from openai import OpenAI
import datetime
import csv
from solvers import NaiveSolver, PuzzleSolver, SolverGrader, PuzzleData, LLMApi, AnswerFormatter


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
csv_file_name = f'LLM_log_{timestamp}.csv'
csv_file = open(csv_file_name, 'w', newline='')
csv_writer = csv.writer(csv_file)
csv_writer.writerow(['Grade', 'Puzzle', 'Obscured Answer Key', 'Solution', 'Attempted Solution', 'Full LLM Convo' , 'Grading Process'])
example = [("""Movie-Genre: epic, superhero, zombie
Transport: airplane, helicopter, roller
1. Transport:airplane and Movie-Genre:superhero have different parity positions
2. Transport:helicopter is not to the left of Movie-Genre:superhero
3. Movie-Genre:epic is somewhere to the right of Movie-Genre:zombie
4. Movie-Genre:superhero is somewhere to the right of Movie-Genre:epic
"""
), (""""User: Movie-Genre: epic, superhero, zombie
Transport: airplane, helicopter, roller
1. Transport:airplane and Movie-Genre:superhero have different parity positions
2. Transport:helicopter is not to the left of Movie-Genre:superhero
3. Movie-Genre:epic is somewhere to the right of Movie-Genre:zombie
4. Movie-Genre:superhero is somewhere to the right of Movie-Genre:epic
LLM: Let's start by understanding the clues:

1. Transport:airplane and Movie-Genre:superhero have different parity positions: This means that if one is in an odd-numbered position, the other is in an even-numbered position, or vice versa.

2. Transport:helicopter is not to the left of Movie-Genre:superhero: This means that the helicopter is either in the same position as the superhero movie or to the right of it.

3. Movie-Genre:epic is somewhere to the right of Movie-Genre:zombie: This means that the zombie movie is to the left of the epic movie.

4. Movie-Genre:superhero is somewhere to the right of Movie-Genre:epic: This means that the epic movie is to the left of the superhero movie.

From clues 3 and 4, we can deduce that the order of the movie genres is: zombie, epic, superhero.

Now, let's consider the transport. From clue 2, we know that the helicopter is not to the left of the superhero movie. Since the superhero movie is in the third position, the helicopter must also be in the third position.

From clue 1, we know that the airplane and the superhero movie have different parity positions. Since the superhero movie is in the third position (an odd number), the airplane must be in the second position (an even number).

This leaves the roller in the first position.

So, the final associations are:

1. Zombie - Roller
2. Epic - Airplane
3. Superhero - Helicopter

 """)]
puzzles = process_puzzles("./data/puzzles")
for puzzle in puzzles:
    puzzle_description = puzzle.entities + "\n" + puzzle.clues
    solution = puzzle.answers
    print(puzzle_description)
    solver_role_text = (
    "Role: Solve the logic puzzles you are given, assigning each item properly in accordance with the clues. Please explain your logic fully and spell out your train of thought, and format your answer meaningfully and clearly."
)
    grader_role_text = ("Role: You are a fair and logical grader of logical puzzles. Grade the attepted solution to the logic puzzle that is given using the answer key. Use the answer key and the given final answer"
    "to determine the score in the format X/Y.  'X' represents the number of correct assignments in the "
    "given answer, please make sure to give partial credit (like if only one part of an assignment is correct) and attempt to interpret the solution charitably: for example, if the answer key says 10 and the attempted solution says 10th, tenth, or ten, any of those are correct. Same thing with spelling errors or formatting differences "
    "and find X even if the answer contains errors. 'Y' is the total number of assignments as per "
    "the answer key. Provide a detailed explanation of your thought process in calculating both X and Y before you give X and Y."
    )

    solver_llm = LLMApi(role=solver_role_text, client_type="HuggingFace")
    grader_llm = LLMApi(role=grader_role_text)
    solver = NaiveSolver(solver_llm, example)
    grader = SolverGrader(grader_llm)
    full_response = solver.solve_puzzle(puzzle_description)
            

    #print(full_response, latest_smt_code, attempted_solution)
    full_convo = solver.getConversation()
    answer_fixer = AnswerFormatter()
    obscured_answer_key = answer_fixer.obscure(solution)
    attempted_solution = answer_fixer.interpret_llm_only(full_convo, obscured_answer_key)
    grading_full_response, grade = grader.get_grade(solution, attempted_solution)
    csv_writer.writerow([grade, puzzle_description,obscured_answer_key,solution, attempted_solution, full_response,  grading_full_response])
    print("Solution:\n", attempted_solution)
    print("Grading Process: ", grading_full_response)
    print("Grade: ", grade)

"""
baseline LLM
vs us

benchmark the grader
"""