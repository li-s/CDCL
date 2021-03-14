import re
from main.helper import debug_print


def read_file_and_parse(file_name):
    f = open(file_name, "r")
    p_line = f.readline().strip()
    while p_line[0] == 'c':
        p_line = f.readline().strip()
    p_line_split = [i for i in re.compile("\\s+").split(p_line)]
    num_variables = int(p_line_split[2])
    num_clauses = int(p_line_split[3])
    debug_print(f"[Parser] Num variables: {num_variables}")
    debug_print(f"[Parser] Num clauses: {num_clauses}")

    clauses = {}
    for i in range(num_clauses):
        next_line = f.readline().strip()
        DNF = [int(i) for i in re.compile("\\s+").split(next_line)]
        DNF = DNF[:len(DNF) - 1]
        DNF = list(set(DNF))
        clauses[i] = DNF

    return num_variables, clauses


if __name__ == "__main__":
    a, b = read_file_and_parse("../data/lecture")
    print(a)
    print(b)