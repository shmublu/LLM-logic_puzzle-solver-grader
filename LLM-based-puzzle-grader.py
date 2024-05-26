import os
import csv
import datetime
from solvers import PuzzleSolver, SolverGrader, PuzzleData, LLMApi, Decomposer, NaiveSolver

# Define role descriptions
solver_role_text = (
    "Role: Encode the logic puzzle given to you into SMT-LIB code, taking into account all explicit and implicit facts; explain your logic and what implicit facts you are encoding. The questions in the \"Guiding Questions:\" section are not part of the problem and do not need to be answered explicitly but are meant to guide you to a solution. Make sure to set-logic in your code."
    "After encoding, I will submit the last SMT-LIB code you have sent me to an SMT solver for analysis and return to you the output. If there is an error, "
    "carefully correct any syntactical mistakes or misinterpretations of the puzzle constraints in your code. "
    "Continuously refine your code and resubmit to me until I send you back a correct solution that precisely aligns with the puzzle's parameters. "
    "Once you have sent the correct, error-free, final SMT-LIB code, only respond 'I am done.' from then on."
)

grader_role_text = (
    "Role: Grade SMT-LIB solver outputs numerically. Use the answer key, the LLM conversation, the latest solver output "
    "to determine the score in the format X/Y. 'X' represents the number of correct assignments in the "
    "given answer, including partial credit; attempt to interpret the solution and find X even if the SMT model contains errors. Please only grade the final puzzle solved. 'Y' is the total number of assignments as per "
    "the answer key. If the answer is blank, provide 0 credit. Provide a detailed explanation of your thought process in calculating both X and Y."
    )

decomposer_role_text = (
    "Role: You are an extremely intelligent teacher whose job it is to identify small pieces of a logic puzzle that are "
    "more manageable than the whole thing at once. You will be given a complex logic puzzle. Your task is to break it down "
    "into smaller, more manageable questions or pieces that, when solved, will help in planning how to provide a complete "
    "solution to the puzzle. Provide a list of these questions, and structure them such that they can be used to plan a "
    "solution to the overall problem."
)

solver_role_text_no_smt = (
    "Role: Solve the logic puzzles you are given, assigning each item properly in accordance with the clues. Please explain your logic fully and spell out your train of thought, and format your answer meaningfully and clearly."
)
grader_role_text_no_smt = (
    "Role: Grade logic puzzle solutions presented in natural language numerically. Use the answer key, the LLM conversation, "
    "and the latest natural language output to determine the score in the format X/Y. 'X' represents the number of correct assignments in the "
    "given answer, including partial credit; attempt to interpret the solution and assess correctness even if the natural language response contains inaccuracies. Please only grade the final puzzle solved. 'Y' is the total number of assignments as per "
    "the answer key. Provide a detailed explanation of your thought process in calculating both X and Y."
)


example = [(""" Here is an example puzzle, along with feedback from the theorem prover. Use this type of workflow to answer the puzzle you are presented with. 
User: 
Ages, names, lengths
5, 10, 15, 20
Barnabas, Bubba, Draco, Merlin
9.4 feet, 10.2 feet, 12.0 feet, 14.0 feet

Merlin is somewhat older than Bubba.
Merlin is 10.2 feet long.
Bubba is 10 years older than the gator that is 14.0 feet long.
Barnabas is 12.0 feet long."""

), ("""Let's start by declaring all the constants required:
- integer constants for every person's age.
- integer constants for every person's length.

(set-logic QF_LIA)

; Age of each person
(declare-const Merlin_Age Int)
(declare-const Bubba_Age Int)
(declare-const Draco_Age Int)
(declare-const Barnabas_Age Int)

; Length of each person
(declare-const Merlin_Length Real)
(declare-const Bubba_Length Real)
(declare-const Draco_Length Real)
(declare-const Barnabas_Length Real)

We'll explicit the conditions in the logic puzzle. The ages are in the set {5, 10, 15, 20} and lengths are in the set {9.4, 10.2, 12.0, 14.0}. Let's add these constraints first:

(assert (and
(or (= Merlin_Age 5) (= Merlin_Age 10) (= Merlin_Age 15) (= Merlin_Age 20))
(or (= Bubba_Age 5) (= Bubba_Age 10) (= Bubba_Age 15) (= Bubba_Age 20))
(or (= Draco_Age 5) (= Draco_Age 10) (= Draco_Age 15) (= Draco_Age 20))
(or (= Barnabas_Age 5) (= Barnabas_Age 10) (= Barnabas_Age 15) (= Barnabas_Age 20))
))

(assert (and
(or (= Merlin_Length 9.4) (= Merlin_Length 10.2) (= Merlin_Length 12.0) (= Merlin_Length 14.0))
(or (= Bubba_Length 9.4) (= Bubba_Length 10.2) (= Bubba_Length 12.0) (= Bubba_Length 14.0))
(or (= Draco_Length 9.4) (= Draco_Length 10.2) (= Draco_Length 12.0) (= Draco_Length 14.0))
(or (= Barnabas_Length 9.4) (= Barnabas_Length 10.2) (= Barnabas_Length 12.0) (= Barnabas_Length 14.0))
))

Now let's add the constraints given in the puzzle:

; Merlin is somewhat older than Bubba.
(assert (> Merlin_Age Bubba_Age))

; Merlin is 10.2 feet long.
(assert (= Merlin_Length 10.2))

; Bubba is 10 years older than the gator that is 14.0 feet long.
(assert (or (and (= Draco_Length 14.0) (= Bubba_Age (+ Draco_Age 10)))
            (and (= Barnabas_Length 14.0) (= Bubba_Age (+ Barnabas_Age 10)))))

; Barnabas is 12.0 feet long.
(assert (= Barnabas_Length 12.0))

Now let's ensure that they all have distinct ages and lengths:

; Distinct ages
(assert (distinct Merlin_Age Bubba_Age Draco_Age Barnabas_Age))

; Distinct lengths
(assert (distinct Merlin_Length Bubba_Length Draco_Length Barnabas_Length))

We close with the check-sat and get-model commands:

(check-sat)
(get-model)
 """), ("""(error ""line 10 column 34: logic does not support reals"")
(error ""line 11 column 32: logic does not support reals"")
(error ""line 12 column 32: logic does not support reals"")
(error ""line 13 column 35: logic does not support reals"")
(error ""line 15 column 2: unexpected character"")
(error ""line 15 column 75: unexpected character"")
(error ""line 15 column 89: unexpected character"")
(error ""line 15 column 118: unexpected character"")
(error ""line 15 column 140: unexpected character"")
(error ""line 15 column 146: unexpected character"")
(error ""line 25 column 7: unknown constant Merlin_Length"")
(error ""line 31 column 7: unexpected character"")
(error ""line 37 column 12: unknown constant Merlin_Length"")
(error ""line 40 column 21: unknown constant Draco_Length"")
(error ""line 44 column 12: unknown constant Barnabas_Length"")
(error ""line 46 column 7: unexpected character"")
(error ""line 52 column 19: unknown constant Merlin_Length"")
sat
(
  (define-fun Merlin_Age () Int
    15)
  (define-fun Draco_Age () Int
    10)
  (define-fun Barnabas_Age () Int
    20)
  (define-fun Bubba_Age () Int
    5)
)"""), ("""Apologies for the incorrect logic - we're trying to model real numbers which are not supported in QF_LIA. We can resolve this issue by using the logic QF_LIRA (Quantifier-Free Linear Integer and Real Arithmetic) instead, which supports both integers and real numbers.

Here's the corrected SMT-LIB code:

```
(set-logic QF_LIRA)

; Age of each person
(declare-const Merlin_Age Int)
(declare-const Bubba_Age Int)
(declare-const Draco_Age Int)
(declare-const Barnabas_Age Int)

; Length of each person
(declare-const Merlin_Length Real)
(declare-const Bubba_Length Real)
(declare-const Draco_Length Real)
(declare-const Barnabas_Length Real)

; The ages are in the set {5, 10, 15, 20}
(assert (and
(or (= Merlin_Age 5) (= Merlin_Age 10) (= Merlin_Age 15) (= Merlin_Age 20))
(or (= Bubba_Age 5) (= Bubba_Age 10) (= Bubba_Age 15) (= Bubba_Age 20))
(or (= Draco_Age 5) (= Draco_Age 10) (= Draco_Age 15) (= Draco_Age 20))
(or (= Barnabas_Age 5) (= Barnabas_Age 10) (= Barnabas_Age 15) (= Barnabas_Age 20))))

; Lengths are in the set {9.4, 10.2, 12.0, 14.0}
(assert (and
(or (= Merlin_Length 9.4) (= Merlin_Length 10.2) (= Merlin_Length 12.0) (= Merlin_Length 14.0))
(or (= Bubba_Length 9.4) (= Bubba_Length 10.2) (= Bubba_Length 12.0) (= Bubba_Length 14.0))
(or (= Draco_Length 9.4) (= Draco_Length 10.2) (= Draco_Length 12.0) (= Draco_Length 14.0))
(or (= Barnabas_Length 9.4) (= Barnabas_Length 10.2) (= Barnabas_Length 12.0) (= Barnabas_Length 14.0))))

; Merlin is somewhat older than Bubba.
(assert (> Merlin_Age Bubba_Age))

; Merlin is 10.2 feet long.
(assert (= Merlin_Length 10.2))

; Bubba is 10 years older than the gator that is 14.0 feet long.
(assert (or (and (= Draco_Length 14.0) (= Bubba_Age (+ Draco_Age 10)))
            (and (= Barnabas_Length 14.0) (= Bubba_Age (+ Barnabas_Age 10)))))

; Barnabas is 12.0 feet long.
(assert (= Barnabas_Length 12.0))

; Distinct ages
(assert (distinct Merlin_Age Bubba_Age Draco_Age Barnabas_Age))

; Distinct lengths
(assert (distinct Merlin_Length Bubba_Length Draco_Length Barnabas_Length))

(check-sat)
(get-model)
"""), ("""sat
(
  (define-fun Merlin_Age () Int
    20)
  (define-fun Bubba_Length () Real
    (/ 47.0 5.0))
  (define-fun Barnabas_Age () Int
    10)
  (define-fun Bubba_Age () Int
    15)
  (define-fun Merlin_Length () Real
    (/ 51.0 5.0))
  (define-fun Draco_Age () Int
    5)
  (define-fun Barnabas_Length () Real
    12.0)
  (define-fun Draco_Length () Real
    14.0)
)"""), "I am done."]
example_no_smt = [("""Movie-Genre: epic, superhero, zombie
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


class Config:
    def __init__(self, solving_model, grading_model, decomp_model=None, use_decomposer=False, max_tries=3, max_conversation_length=4, temperatures=[0, 0.001, 0.01], csv_name=None, use_smt=True):
        
        self.solving_model = solving_model
        self.grading_model = grading_model
        self.decomp_model = decomp_model
        self.use_decomposer = use_decomposer
        self.max_tries = max_tries
        self.max_conversation_length = max_conversation_length
        self.temperatures = temperatures
        self.csv_name = csv_name if csv_name else f'AAtest-exp-log_{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}.csv'
        self.use_smt = use_smt

def read_file_contents(file_path):
    with open(file_path, 'r') as file:
        return file.read()

def process_puzzles(directory_path):
    puzzles = []
    for folder in os.listdir(directory_path):
        folder_path = os.path.join(directory_path, folder)
        if os.path.isdir(folder_path):
            answers_path = os.path.join(folder_path, 'answers.txt')
            entities_path = os.path.join(folder_path, 'entities.txt')
            clues_path = os.path.join(folder_path, 'clues.txt')
            if all(os.path.exists(path) for path in [answers_path, entities_path, clues_path]):
                answers = read_file_contents(answers_path)
                entities = read_file_contents(entities_path)
                clues = read_file_contents(clues_path)
                puzzles.append(PuzzleData(answers, entities, clues))
    return puzzles

def run_puzzles(config):
    puzzles = process_puzzles("./data/puzzles")
    csv_file = open(config.csv_name, 'w', newline='')
    csv_writer = csv.writer(csv_file)
    csv_writer.writerow(['Grade', 'Puzzle', 'SMT-LIB Code', 'Attempted Solution', 'Full LLM Convo', 'Grading Process', 'Solution'])

    for puzzle in puzzles:
        if config.use_smt:
            solve_puzzle_smt(puzzle, config, csv_writer)
        else:
            solve_puzzle(puzzle, config, csv_writer)
    csv_file.close()

def solve_puzzle_smt(puzzle, config, csv_writer):
    solver_llm = LLMApi(role=solver_role_text, client_type="OpenAI", model=config.solving_model, temperature=config.temperatures[0])
    grader_llm = LLMApi(role=grader_role_text, client_type="OpenAI", model=config.grading_model, temperature=0)
    solver = PuzzleSolver(solver_llm,example)
    grader = SolverGrader(grader_llm)

    full_description = f"{puzzle.entities}\n{puzzle.clues}"

    decomposed_questions_str = ""
    if config.use_decomposer:
        decomposer_llm = LLMApi(role=decomposer_role_text, client_type="OpenAI", model=config.decomp_model, temperature=config.temperatures[0])
        decomposer = Decomposer(decomposer_llm)
        decomposed_questions = decomposer.decompose_puzzle(full_description)
        decomposed_questions_str = "\n".join(decomposed_questions)

    retries_left = config.max_tries
    latest_smt_code = ""
    successful = False

    while retries_left > 0 and not successful:
        solver.clear()
        next_input = full_description + ("\n\"Guiding Questions:\"" + decomposed_questions_str if config.use_decomposer else "")
        try:
            for i in range(config.max_conversation_length):
                full_response, smt_lib_code = solver.solve_puzzle(next_input)
                if smt_lib_code and "(set-logic" in smt_lib_code:
                    latest_smt_code = smt_lib_code
                next_input = solver.solve_with_z3(latest_smt_code)
        except Exception as e:
            print(f"Error during solving: {str(e)}") 
        if not ("error" in next_input):
            successful = True
            break
        retries_left -= 1
        if not successful and retries_left > 0:
            solver_llm.temperature = config.temperatures[min(len(config.temperatures)-1, config.max_tries - retries_left)]

    attempted_solution = solver.solve_with_z3(latest_smt_code)
    full_convo = solver.getConversation()
    grading_full_response, grade = grader.get_grade(puzzle.answers, full_convo, attempted_solution)
    csv_writer.writerow([grade, full_description, latest_smt_code, attempted_solution, full_convo, grading_full_response, puzzle.answers])

    print("SMT-LIB Code:\n", latest_smt_code)
    print("Solution:\n", attempted_solution)
    print("Grading Process: ", grading_full_response)
    print("Grade: ", grade)

def solve_puzzle(puzzle, config, csv_writer):
    puzzle_description = puzzle.entities + "\n" + puzzle.clues
    solution = puzzle.answers
    solver_llm = LLMApi(role=solver_role_text_no_smt, client_type="OpenAI", model=config.solving_model,temperature = 0)
    grader_llm = LLMApi(role=grader_role_text_no_smt, client_type="OpenAI", model=config.grading_model,temperature = 0)
    solver = NaiveSolver(solver_llm, example_no_smt)
    grader = SolverGrader(grader_llm)
    full_response = solver.solve_puzzle(puzzle_description)
            

    #print(full_response, latest_smt_code, attempted_solution)
    full_convo = solver.getConversation()
    grading_full_response, grade = grader.get_grade(solution, full_convo)
    csv_writer.writerow([grade, puzzle_description,"N/A",solution, full_response,  grading_full_response, puzzle.answers])
    print("Solution:\n", full_response)
    print("Full Convo: ", full_convo)
    print("Grade: ", grade)


if __name__ == "__main__":
    config = Config(solving_model="gpt-3.5-turbo-0125", grading_model="gpt-4o-2024-05-13", use_decomposer=False, decomp_model="gpt-3.5-turbo-0125", max_tries=1, max_conversation_length=4, temperatures=[0, 0.001, 0.01], use_smt=False)
    run_puzzles(config)
