import os
import time
from CDCL import CDCLSolver


def test_all(root):
    for directory in os.listdir(root):
        full_dir = os.path.join(root, directory)
        if directory.startswith("uuf"):
            print(f"Testing {full_dir}, target: UNSAT")
            test(full_dir, "UNSAT")
        elif directory.startswith("uf"):
            print(f"Testing {full_dir}, target: SAT")
            test(full_dir, "SAT")


def test(directory, sat="SAT"):
    start_time = time.time()
    total_branching = 0
    index = 1
    num_total_test = len(os.listdir(directory))
    alert_interval = set([i * int(num_total_test / 10) for i in range(1, 11)])
    for test_input in os.listdir(directory):
        # print(test_input)
        if test_input.endswith(".cnf"):
            solver = CDCLSolver(os.path.join(directory, test_input))
            answer = solver.solve()
            total_branching += solver.num_PBV_invocations
            if not check_answer(answer, sat):
                print(f"Error at: {test_input}")
                return
            # print(answer)
        if index in alert_interval:
            print(f"Done {index} out of {num_total_test} testcases.")
        index += 1
    end_time = time.time()
    print(f"Total time: {end_time - start_time}")
    print(f"Average time: {(end_time - start_time) / num_total_test}")
    print(f"Total branching: {total_branching}")
    print(f"Average branching: {total_branching / num_total_test}")


def check_answer(answer, sat):
    if sat == "SAT":
        return answer != "UNSAT"
    if sat == "UNSAT":
        return answer == "UNSAT"


if __name__ == "__main__":
    test("../data/test/uuf50-218", "UNSAT")
