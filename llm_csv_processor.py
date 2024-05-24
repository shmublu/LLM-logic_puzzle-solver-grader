import csv
from fractions import Fraction

def calculate_average(csv_file_path):
    total = Fraction(0)
    count = 0
    how_many_perfect = 0

    with open(csv_file_path, newline='') as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            if len(row) >= 5:  # Check if the 5th column exists
                try:
                    fraction = Fraction(row[-2])  # Convert 5th column to Fraction
                    if abs(fraction - 1) < 0.001:
                        how_many_perfect += 1
                    total += fraction
                    count += 1
                except Exception:
                    # Skip rows where the 5th column cannot be converted to a fraction
                    continue

    if count > 0:
        average = total / count
        print(str(how_many_perfect) + " solved perfectly")
        print(count)
        return float(average)  # Convert Fraction to float for decimal representation
    else:
        return "No valid data"

# Replace 'yourfile.csv' with your actual file path
nodecomp_file = 'LLM-SMT-non-decomp_log_20240331_184935.csv'
decomp_file = 'test-exp5-3.5-LLM_log_20240524_094700.csv'
csv_file_path = decomp_file
average = calculate_average(csv_file_path)
print("Average:", average)