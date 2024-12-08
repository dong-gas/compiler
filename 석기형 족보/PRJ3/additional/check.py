#!/usr/bin/python3
import sys, os, subprocess
from os import path
from subprocess import PIPE


ROOT_DIR = path.dirname(path.abspath(__file__))
CONFIG_FILE = "config"
TIMEOUT = 5
DELAY_PENALTY = 0.8
TESTCASE_DIRNAME = "testcase"
EXECUTABLE_NAME = "main.bin"


# Exception must be handled by the caller.
def run_cmd(cmd_str, check=True):
    args = cmd_str.split()
    p = subprocess.run(args, check=check, stdout=PIPE, stderr=PIPE,
                       timeout=TIMEOUT)
    return "".join(map(chr, p.stdout))


def run_make():
    try:
        orig_cwd = os.getcwd()
        os.chdir(ROOT_DIR)
        run_cmd("make clean")
        run_cmd("make")
        os.chdir(orig_cwd)
        return True
    except Exception as e:
        return False


def parse_output(output):
    result_lines = []
    cost_sum = 0
    for line in output.strip().split("\n"):
        tokens = line.split(",")
        result_lines.append(tokens[0].split(":")[1].strip())
        cost_sum += int(tokens[1].split(":")[1].strip())
    result_str = "\n".join(result_lines).strip()
    return (result_str, cost_sum)


def compute_perf_score(cost, base_cost, opt_cost):
    if cost >= base_cost:
        return 0
    elif cost <= opt_cost:
        return 100
    else:
        return (int (100.0 * (base_cost - cost) / (base_cost - opt_cost)))


def check(submit_files, tc_num, point, is_delay):
    # If any of the file is missing, it means no submission.
    for submit_file in submit_files:
        submit_path = path.join(ROOT_DIR, submit_file)
        if not path.isfile(submit_path):
            return (" ", 0.0)

    # Build the problem directory.
    build_success = run_make()
    executable = path.join(ROOT_DIR, EXECUTABLE_NAME)
    if not build_success or not path.isfile(executable):
        return ("C" * tc_num, 0.0)

    grading_str = ""
    point_per_tc = float(point) / tc_num
    obtained_point = 0
    # Now start the grading with each testcase file.
    for i in range(tc_num):
        prog_path = path.join(ROOT_DIR, TESTCASE_DIRNAME, "prog-%d" % (i + 1))
        inp_path = path.join(ROOT_DIR, TESTCASE_DIRNAME, "inp-%d" % (i + 1))
        ans_path = path.join(ROOT_DIR, TESTCASE_DIRNAME, "ans-%d" % (i + 1))
        cost_path = path.join(ROOT_DIR, TESTCASE_DIRNAME, "cost-%d" % (i + 1))
        f = open(ans_path)
        ans = f.read()
        f.close()
        f = open(cost_path)
        tokens = f.read().strip().split()
        base_cost, opt_cost = int(tokens[0]), int(tokens[1])
        f.close()
        try:
            cmd = "%s run-opt %s %s" % (executable, prog_path, inp_path)
            output = run_cmd(cmd)
            result, cost = parse_output(output)
            perf_score = compute_perf_score(cost, base_cost, opt_cost)
            if ans.strip() == result:
                grading_str += "O (%d/100) " % perf_score
                obtained_point += point_per_tc * perf_score / 100
            else:
                grading_str += "X "
        except subprocess.TimeoutExpired:
            grading_str += "T "
        except subprocess.CalledProcessError as e:
            grading_str += "E "

    if is_delay:
        grading_str += " (Delay)"
        obtained_point *= DELAY_PENALTY
    return grading_str, obtained_point


def parse_config():
    f = open(path.join(ROOT_DIR, CONFIG_FILE))
    line = f.readline()
    f.close()
    tokens = line.strip().split()
    submit_files = tokens[0].split(",")
    point = int(tokens[1])
    tc_num = int(tokens[2])
    return (submit_files, point, tc_num)


def main():
    if len(sys.argv) not in [1, 2]:
        # --delay or --normal option is hidden.
        print("Usage: %s" % sys.argv[0])
        exit(1)

    delay_flag = False
    csv_flag = False
    if len(sys.argv) == 2:
        csv_flag = True
        if sys.argv[1] == "--delay":
            delay_flag = True
        elif sys.argv[1] != "--normal": # Nothing to do if it's --normal.
            print("Invalid option: %s" % sys.argv[2])
            exit(1)

    submit_files, point, tc_num = parse_config()
    grading_str, obtained_point = check(submit_files, tc_num, point, delay_flag)
    if csv_flag:
        print("%s, %.1f, " % (grading_str, obtained_point), end="")
    else:
        print("[*] Result: %s" % grading_str)


if __name__ == "__main__":
    main()
