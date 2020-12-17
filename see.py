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
#	Cannot just have a list of all assertions at the end (not treating assertions as postconditions). Evaluate assertions in the right context, or level of nestedness.
#	The asserts get CONCAT'd onto the rest of the program

#	Treating input variables as normal program variables for now
#	Arrays as input don't have an index whereas other array references in the program do

#	Preconditions serve to limit the input. They should not be the reason for a violation (unless they don't allow input?)

import sys
import os

from program_parser import *
from solver import exp_to_z3
from z3 import *


def process(program, num_unrolls, solver, assignments):

	if program[0] == 'CONCAT':
		process(program[1], num_unrolls, solver, assignments)
		process(program[2], num_unrolls, solver, assignments)

	elif program[0] == 'ASSIGN':
		assignments[program[1]] = program[2]

	elif program[0] == 'WHILE':
		for i in range(num_unrolls+1):
			if i == 0:
				solver.append(['!', program[1]])
				return


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


# Call SMT solver
def check_assertion(solver, assignments, var_list, name):
	print("solver:", solver)
	print("assignments:", assignments)
	print("var_list:", var_list)
	for k, v in assignments.items():
		if isinstance(v, list):
			# print(k, v)
			solver.add(Int(k) == exp_to_z3(v))
		# z3 array
		else:
			solver.add(Array(k, IntSort(), IntSort()) == v)

	if solver.check() == sat:
		vars_to_print = {}
		m = solver.model()
		for d in m.decls():
			if d.name().startswith("ARR") and d.name() in var_list:
				print("PRINT ARRAY\n")
				raise NotImplementedError
			elif d.name() in var_list:
				vars_to_print[var_list.index(d.name())] = m[d]

		print(name, end="")
		for i in range(len(var_list)):
			if i in vars_to_print:
				print(" " + str(vars_to_print[i]), end="")
		print()

def parse_body(program, num_unrolls, program_idx_start, program_idx_end, name, solver, assignments, var_list):
	# while program_idx_start < program_idx_end:
	print(f"\nprogram at top of func: {program[program_idx_start:program_idx_end]}\n")
	print(program_idx_start, program_idx_end)
	# check for semicolon statement
	if program_idx_start < program_idx_end:
		if not program[program_idx_start:].startswith("if") and not program[program_idx_start:].startswith("while"):
			stmt_idx_end = program[program_idx_start:].find(";")
			stmt = program[program_idx_start:program_idx_start + stmt_idx_end]

			print(f"stmt: {stmt}\n")

			# 4 types of semicolon statements: assert, array assignment (with "[" before ":="), double assignment (with "," before ":="), and single assignment
			if stmt.find("assert") != -1:
				# print(f"assertion: {exp_to_z3(parse_assn(stmt[7:]))}\n")
				assertion = Not(exp_to_z3(parse_assn(stmt[7:])))
				solver.push()
				solver.add(assertion)
				check_assertion(solver, assignments, var_list, name)
				solver.pop()

			elif stmt.find("[") != -1 and stmt.find("[") < stmt.find(":="):
				arr_name = "ARR_" + stmt[:stmt.find("[")]
				if arr_name not in assignments:
					assignments[arr_name] = exp_to_z3(['STORE', arr_name, parse_aexp(stmt[stmt.find("[")+1:stmt.find("]")]), parse_aexp(stmt[stmt.find(":=")+3:])])
				else:
					assignments[arr_name] = exp_to_z3(['STORE', assignments[arr_name], parse_aexp(stmt[stmt.find("[")+1:stmt.find("]")]), parse_aexp(stmt[stmt.find(":=")+3:])])

			elif stmt.find(",") != -1 and stmt.find(",") < stmt.find(":="):
				var1, var2 = stmt[:stmt.find(",")], stmt[stmt.find(",")+2:stmt.find(":=")-1]
				if var1 not in assignments:
					assignments[var1] = parse_aexp(stmt[stmt.find(":=")+3:stmt.rfind(",")])
				else:
					# TODO: handle array sub in parse_aexp
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

			print(f"stmt: {stmt}\n")

			bexp = stmt[3:stmt.find("then")-1] if stmt.startswith("if") else stmt[6:stmt.find("do")-1]
			bexp = exp_to_z3(parse_bexp(bexp))
			print(f"bexp: {bexp}\n")

			end_idx = program_idx_start + stmt.rfind("end") - 2

			# 3 types: while, if with "else" (number of "else" matches number of "if"), and if
			if stmt.startswith("while"):
				# skip body
				new_idx_start = end_idx + 6
				solver.push()
				solver.add(Not(bexp))
				print("ABOUT TO RECURSE\n")
				program_idx_start = parse_body(program, num_unrolls, new_idx_start, program_idx_end, name, solver, assignments, var_list)
				solver.pop()
				print("DONE WITH SKIPPING\n")

				if num_unrolls != 0:
					# eval body num_unrolls times
					new_idx_start = program_idx_start + stmt.find("do") + 3
					for i in range(num_unrolls):
						solver.push()
						solver.add(bexp)
						parse_body(program, num_unrolls, new_idx_start, end_idx, name, solver, assignments, var_list)
						solver.pop()

				# program_idx_start = end_idx + 6	

			elif stmt.count("if") == stmt.count("else"):
				# eval else
				new_idx_start = program_idx_start + stmt.find("else") + 5
				solver.push()
				solver.add(Not(bexp))
				parse_body(program, num_unrolls, new_idx_start, end_idx, name, solver, assignments, var_list)
				solver.pop()

				if num_unrolls != 0:
					# eval then
					# find index of matching else (for END_IDX)
					else_idx = None
					num_if, num_else = 1, 0
					tmp_idx = program_idx_start + stmt.find("then") + 5
					while tmp_idx < program_idx_end:
						if program[tmp_idx:].startswith("if"):
							num_if += 1
						elif program[tmp_idx:].startswith("else"):
							num_else += 1

						if num_else == num_end:
							else_idx = tmp_idx
							break

						tmp_idx += 1

					new_idx_start = program_idx_start + stmt.find("then") + 5
					solver.push()
					solver.add(bexp)
					parse_body(program, num_unrolls, new_idx_start, else_idx - 1, name, solver, assignments, var_list)
					solver.pop()

				program_idx_start = end_idx + 6


			else:
				# skip body
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
				
					print(f"solver: {solver}\n")
						
				program_idx_start = end_idx + 6

			if program_idx_start < program_idx_end:
				parse_body(program, num_unrolls, program_idx_start, program_idx_end, name, solver, assignments, var_list)

	return program_idx_start

# 3bc9b1419944ef8cb29cfef730e22cf3158b677c
# TODO: think about how to represent something as simple as "n = 0; n = n + 1;"
	#	don't have to check conditions at all. just assume they're true or false
	#	have a formula with a bunch of chained Implies that you create from whatever
		# is in solver.assertions() at the time. or should it be And's? How the fuck
			# do I represent "n = 0; n = 1;"
			# maybe I actually need a dict from var to val.
				# when I check for violation, I add var == val to solver before checking
				# to deal with "n = n + 1;" I need to send in assignments and apply dict[n]


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
		print(f"program: {program}\n")

		program_idx_start, program_idx_end, name, var_list, preconditions = parse_head(program)

		# print(f"program_idx_start: {program_idx_start}\n")
		# print(f"program_idx_end: {program_idx_end}\n")
		# print(f"name: {name}\n")
		# print(f"var_list: {var_list}\n")
		# print(f"preconditions: {preconditions}\n")
		# print(f"program: {program[program_idx_start:program_idx_end]}\n")

		solver = Solver()
		for precondition in preconditions:
			solver.add(exp_to_z3(precondition))

		assignments = {}
		parse_body(program, int(sys.argv[2]), program_idx_start, program_idx_end, name, solver, assignments, var_list)

		


if __name__ == "__main__":
	main()


# for i in range(2):
# 	if i == 0:
# 		new_idx_start = end_idx + 4
# 		parse_body(program, num_unrolls, new_idx_start, end_idx, name, solver, assignments)
# 	else:
# 		solver.push()
# 		solver.add(exp_to_z3(parse_bexp(bexp)))
# 		new_idx_start = program_idx_start + stmt.find("then") + 5
# 		parse_body(program, num_unrolls, new_idx_start, end_idx, name, solver, assignments)
# 		solver.pop()

# 	program_idx_start = end_idx + 6	








