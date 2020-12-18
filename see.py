# Notes
#	Track values symbolically during symbolic execution
#	Pass path constraints to SMT solver to get the concrete values that violate the assertions
#	Can probably reuse parsing and calling SMT solver from Project 1

#	Assertions can also appear in loop. Whenever you see assertion, just call solver to see
#		if it's true

#	To find violations, negate the postcondition

# Language
#	While loops should not have invariants
#	Program no longer has postconditions (can have preconditions though)

# Design
	# parse iteratively. handle if/while statements recursively.

import sys
import os

from program_parser import *
from solver import exp_to_z3
from z3 import *

prints = []

def parse_head(program):
	# useful for solver
	program_idx_start, program_idx_end = 0, len(program) - 1

	# get program name, variables
	name_and_var_idx_start = program.find("(")
	name_and_var_idx_end = program.find(")")

	name = program[program.find("program ") + 8:name_and_var_idx_start]
	var_list = ['ARR_' + s[:-2] if s.endswith("[]") else s for s in program[name_and_var_idx_start+1:name_and_var_idx_end].split()]

	program = program[name_and_var_idx_end+2:]
	program_idx_start = program_idx_start + name_and_var_idx_end + 2

	# get preconditions
	pre_idx_end = program.find("is")
	precondition_strs = program[:pre_idx_end].split("pre")
	if not precondition_strs[0]:
		precondition_strs = precondition_strs[1:]

	preconditions = []
	for s in precondition_strs:
		preconditions.append(parse_assn(s))

	program_idx_start = program_idx_start + pre_idx_end + 3
	program_idx_end -= 3

	return program_idx_start, program_idx_end, name, var_list, preconditions


def check_assertion(solver, assignments, var_list, name):
	for k, v in assignments.items():
		if isinstance(v, list):
			solver.add(Int(k) == exp_to_z3(v))
		# z3 array
		else:
			solver.add(Array(k, IntSort(), IntSort()) == v)

	if solver.check() == sat:
		vars_to_print = {}
		m = solver.model()
		for d in m.decls():
			if d.name() in var_list:
				vars_to_print[var_list.index(d.name())] = m[d]

		violation = f"{name}"
		for i in range(len(var_list)):
			if i in vars_to_print:
				violation += " "
				violation += str(vars_to_print[i])

		prints.append(violation)

def parse_body(program, num_unrolls, program_idx_start, program_idx_end, name, solver, assignments, var_list):
	# check for semicolon statement
	if program_idx_start < program_idx_end:
		if not program[program_idx_start:].startswith("if") and not program[program_idx_start:].startswith("while"):
			stmt_idx_end = program[program_idx_start:].find(";")
			stmt = program[program_idx_start:program_idx_start + stmt_idx_end]


			# 4 types of semicolon statements: assert, array assignment (with "[" before ":="), double assignment (with "," before ":="), and single assignment
			if stmt.find("assert") != -1:
				assertion = Not(exp_to_z3(parse_assn(stmt[7:])))
				solver.push()
				solver.add(assertion)
				check_assertion(solver, assignments, var_list, name)
				solver.pop()

			elif stmt.find("[") != -1 and stmt.find("[") < stmt.find(":="):
				arr_name = "ARR_" + stmt[:stmt.find("[")]
				if arr_name not in assignments:
					assignments[arr_name] = exp_to_z3(['STORE', arr_name, parse_aexp(stmt[stmt.find("[")+1:stmt.find("]")], assignments, True),\
					 parse_aexp(stmt[stmt.find(":=")+3:], assignments, True)])

				else:
					assignments[arr_name] = exp_to_z3(['STORE', assignments[arr_name], parse_aexp(stmt[stmt.find("[")+1:stmt.find("]")], assignments, True),\
					 parse_aexp(stmt[stmt.find(":=")+3:], assignments, True)])

			elif stmt.find(",") != -1 and stmt.find(",") < stmt.find(":="):
				var1, var2 = stmt[:stmt.find(",")], stmt[stmt.find(",")+2:stmt.find(":=")-1]
				if var1 not in assignments:
					assignments[var1] = parse_aexp(stmt[stmt.find(":=")+3:stmt.rfind(",")])
				else:
					assignments[var1] = parse_aexp(stmt[stmt.find(":=")+3:stmt.rfind(",")], assignments, True)

				if var2 not in assignments:
					assignments[var2] = parse_aexp(stmt[stmt.rfind(",")+2:])
				else:
					assignments[var2] = parse_aexp(stmt[stmt.rfind(",")+2:], assignments, True)

			else:
				var = stmt[:stmt.find(":=")-1]
				if var not in assignments:
					assignments[var] = parse_aexp(stmt[stmt.find(":=")+3:])
				else:
					assignments[var] = parse_aexp(stmt[stmt.find(":=")+3:], assignments, True)

			program_idx_start = program_idx_start + stmt_idx_end + 2
			parse_body(program, num_unrolls, program_idx_start, program_idx_end, name, solver, assignments, var_list)

		# handle if/while
		else:
			# determine when the stmt ends (when the number of "end" is the same as number of "while" + "if")
			stmt_idx_end = None
			num_end, num_while_or_if = 0, 0
			tmp_idx = program_idx_start
			while tmp_idx < len(program):
				if program[tmp_idx:].startswith("while") or program[tmp_idx:].startswith("if"):
					num_while_or_if += 1
				elif program[tmp_idx:].startswith("end"):
					num_end += 1

				if num_while_or_if == num_end:
					stmt_idx_end = tmp_idx
					break

				tmp_idx += 1

			stmt = program[program_idx_start:stmt_idx_end+3]

			bexp = stmt[3:stmt.find("then")-1] if stmt.startswith("if") else stmt[6:stmt.find("do")-1]

			end_idx = program_idx_start + stmt.rfind("end") - 2

			# 3 types: while, if with "else" (number of "else" matches number of "if"), and if
			if stmt.startswith("while"):
				bexp_before = exp_to_z3(parse_bexp(bexp))
				bexp_after = Not(exp_to_z3(parse_bexp(bexp)))

				if num_unrolls == 0:
					# skip body
					new_idx_start = end_idx + 6
					solver.push()
					solver.add(bexp_after)
					parse_body(program, num_unrolls, new_idx_start, program_idx_end, name, solver, assignments, var_list)
					solver.pop()
					return

				if num_unrolls != 0:
					# skip body
					new_idx_start = end_idx + 6
					solver.push()
					solver.add(bexp_after)
					parse_body(program, num_unrolls, new_idx_start, program_idx_end, name, solver, assignments, var_list)
					solver.pop()

					last_bexp = exp_to_z3(parse_bexp(bexp, assignments, True))

					solver.add(last_bexp)

					# to persist the negation of the condition?
					solver.push()

					# eval body num_unrolls times
					new_idx_start = program_idx_start + stmt.find("do") + 3
					for i in range(num_unrolls):
						solver.push()
						solver.add(bexp_before)
						parse_body(program, num_unrolls, new_idx_start, end_idx, name, solver, assignments, var_list)
						solver.pop()

						if i != num_unrolls - 1:
							last_bexp = exp_to_z3(parse_bexp(bexp, assignments, True))
							solver.add(last_bexp)

					solver.add(bexp_after)
					program_idx_start = end_idx + 6	


			elif stmt.count("if") == stmt.count("else"):
				# eval else
				bexp = exp_to_z3(parse_bexp(bexp))
				new_idx_start = program_idx_start + stmt.find("else") + 5
				solver.push()
				solver.add(Not(bexp))
				parse_body(program, num_unrolls, new_idx_start, end_idx, name, solver, assignments, var_list)

				if num_unrolls != 0:
					# eval then

					# match pop with push in eval else part
					solver.pop()

					# find index of matching else (for end_idx)
					else_idx = None
					num_if, num_else = 1, 0
					tmp_idx = program_idx_start + stmt.find("then") + 5
					while tmp_idx < program_idx_end:
						if program[tmp_idx:].startswith("if"):
							num_if += 1
						elif program[tmp_idx:].startswith("else"):
							num_else += 1

						if num_else == num_if:
							else_idx = tmp_idx
							break

						tmp_idx += 1
					new_idx_start = program_idx_start + stmt.find("then") + 5
					solver.add(bexp)
					parse_body(program, num_unrolls, new_idx_start, else_idx - 1, name, solver, assignments, var_list)

				program_idx_start = end_idx + 6


			else:
				# skip body
				bexp = exp_to_z3(parse_bexp(bexp))
				new_idx_start = end_idx + 6
				solver.push()
				solver.add(Not(bexp))
				parse_body(program, num_unrolls, new_idx_start, program_idx_end, name, solver, assignments, var_list)
				solver.pop()	

				if num_unrolls != 0:
					# eval body
					solver.push()
					solver.add(bexp)
					new_idx_start = program_idx_start + stmt.find("then") + 5
					parse_body(program, num_unrolls, new_idx_start, end_idx, name, solver, assignments, var_list)
					solver.pop()
						
				program_idx_start = end_idx + 6

			if program_idx_start < program_idx_end:
				parse_body(program, num_unrolls, program_idx_start, program_idx_end, name, solver, assignments, var_list)

	return program_idx_start


def main():
	if len(sys.argv) != 3 or sys.argv[0] != "see.py":
		sys.exit("Usage: python see.py <input_file> #num_unrolls")

	if not sys.argv[2].isdigit() or int(sys.argv[2]) < 0:
		sys.exit("num_unrolls must be a non-negative integer")

	script_dir = os.path.dirname(__file__)
	abs_file_path = os.path.join(script_dir, sys.argv[1])
	with open(abs_file_path) as myFile:
		program = myFile.read()
		program = prune_whitespace(program, 1)

		program_idx_start, program_idx_end, name, var_list, preconditions = parse_head(program)

		solver = Solver()
		for precondition in preconditions:
			solver.add(exp_to_z3(precondition))

		assignments = {}
		parse_body(program, int(sys.argv[2]), program_idx_start, program_idx_end, name, solver, assignments, var_list)

		if prints:
			for violation in prints:
				print(violation)
		else:
			print("No violations found")

if __name__ == "__main__":
	main()
