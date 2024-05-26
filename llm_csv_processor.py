import csv
from fractions import Fraction

def calculate_average(csv_file_path):
    total = Fraction(0)
    count = 0
    how_many_perfect = 0

    with open(csv_file_path, newline='') as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            if len(row) > 0:  
                try:
                    fraction = Fraction(row[0])  
                    if abs(fraction - 1) < 0.001:
                        how_many_perfect += 1
                    total += fraction
                    count += 1
                except Exception:
                    
                    continue

    if count > 0:
        average = total / count
        print(str(how_many_perfect) + " solved perfectly")
        print(count)
        return float(average)  # Convert Fraction to float for decimal representation
    else:
        return "No valid data"

graded_file = 'AAtest-exp-log_20240525_231212.csv'
csv_file_path = graded_file
average = calculate_average(csv_file_path)
print("Average:", average)