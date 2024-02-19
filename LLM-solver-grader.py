import re
import subprocess
import tempfile
import os
from openai import OpenAI
import datetime
import csv
from solvers import NaiveSolver, PuzzleSolver, SolverGrader, PuzzleData, LLMApi 


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
csv_file_name = f'LLM_log_{timestamp}.csv'
csv_file = open(csv_file_name, 'w', newline='')
csv_writer = csv.writer(csv_file)
csv_writer.writerow(['Puzzle', 'SMT-LIB Code', 'Attempted Solution', 'Full LLM Convo' , 'Grading Process', 'Grade', 'Solution'])

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
grading_example = """
The answer key provides four assignments, each with three parts: month, rocket name, and company. This gives us a total of 8 degrees of freedom (because the numbering of the months in this case does not matter), so Y = 8. If the ordering mattered, we would have a correct assignment for the months also, so Y would theoretically be 12.

Let's look at the answer key:
January, Athios, SpaceZen
February, Foltron, Omnipax
March, Exatris, Vexatech
April, Worul, Techtrin

Let's compare the given answer to the answer key and score accordingly:

1. January - Athios - SpaceZen: This matches the answer key exactly, so we have 2 correct assignments (2 degrees of freedom in what to match with January even though there are 3 categories).
2. February - Exatris - Techtrin: The answer key has February associated with Foltron and Omnipax. February does not match with either, so we have 0 correct assignments.
3. March - Foltron - Vexatech: The answer key has March associated with Exatris and Vexatech. The company is correct, but the rocket name is not, so we have 1 correct assignments.
4. April - Worul - Omnipax: The answer key has April associated with Worul and Techtrin. The rocket name is correct, but the company is not, so we have 1 correct assignments.

Adding these up, we have X = 2 + 0 + 1 + 1 , so X = 4.

So, the score for this logic puzzle solution is X divided by Y, so it is 4/8.



"""
puzzles = process_puzzles("./data/puzzles")
for puzzle in puzzles:
    puzzle_description = puzzle.entities + "\n" + puzzle.clues
    solution = puzzle.answers
    print(puzzle_description)
    solver_role_text = (
    "Role: Solve the logic puzzles you are given, assigning each item properly in accordance with the clues. Please explain your logic fully and spell out your train of thought, and format your answer meaningfully and clearly."
)
    grader_role_text = (
    """Role: You are a logical and fair grader of logic puzzles. Your task involves grading two types of assignments: 'Category Matching' and 'Item Ordering'. 
    In 'Category Matching' assignments, where items from various categories are matched together, each successful match between different categories earns points. 
    The total points for each line are one less than the number of items to be matched, as matching an item to itself is not counted. For 'Item Ordering' assignments, points are awarded based on the correct order of items. You can tell it is an 'Item Ordering' assignment if the answer key is numbered.
    Each correct placement in the sequence earns a point, making the total points for each line equal to the number of items to be ordered. Use the final answer as compared with the answer key to determine the score in the format X/Y. 
    'X' is the number of points earned, and 'Y' is the total possible points for the assignment, calculated based on the specific grading criteria for each type of assignment. 
    Provide a detailed explanation of your thought process in calculating both X and Y for each assignment. Remember, X must be less than or equal to Y."""
    )
    solver_llm = LLMApi(role=solver_role_text)
    grader_llm = LLMApi(role=grader_role_text)
    solver = NaiveSolver(solver_llm, example)
    grader = SolverGrader(grader_llm, grading_example)
    full_response = solver.solve_puzzle(puzzle_description)
            

    #print(full_response, latest_smt_code, attempted_solution)
    full_convo = solver.getConversation()
    grading_full_response, grade = grader.get_grade(solution, full_convo)
    csv_writer.writerow([puzzle_description, "", full_response, full_convo,grading_full_response, grade, solution])
    print("Solution:\n", full_response)
    print("Grading Process: ", grading_full_response)
    print("Grade: ", grade)

"""
baseline LLM
vs us

benchmark the grader
"""