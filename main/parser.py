

def read_file_and_parse(file_name):
    f = open(file_name, "r")
    comments = f.readline()
    p_line = f.readline()
    p_line = [i for i in p_line.split(" ")]
    num_variables = int(p_line[2])
    num_clauses = int(p_line[3][:1])

    clauses = {}
    for i in range(num_clauses):
        next_line = f.readline()
        DNF = [int(i) for i in next_line.split(" ")]
        DNF = DNF[1:len(DNF) - 1]
        clauses[i + 1] = DNF

    return num_variables, clauses

if __name__ == "__main__":
    a, b = read_file_and_parse("../data/base_case.txt")
    print(a)
    print(b)
