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


# Call SMT solver
def check_assertion(path_conditions, assignments):
	print("Checking assertion\n")



['CONCAT', 
	['CONCAT', 
		['CONCAT', 
			['ASSIGN', 'VAR_n', ['INT', 0]], 
			['WHILE', 
				['&&', 
					['<', 
						['VAR', 'VAR_n'], 
						['VAR', 'VAR_N']],
  					['!=', 
  						['ARR', 'ARR_a', ['VAR', 'VAR_n']], 
  						['VAR', 'VAR_x']]],
  				['CONCAT', 
  					['ASSIGN', 'VAR_n', ['+', ['VAR', 'VAR_n'], ['INT', 1]]],\
   					['ASSERT', ['=', ['VAR', 'VAR_x'], ['INT', 1]]]]]],
   		['ASSERT', ['!', ['||', 
   							['=', ['ARR', 'ARR_a', ['VAR', 'VAR_n']], ['VAR', 'VAR_x']],\
    						['forall', ['VAR_i'], 
    							['==>', 
    								['&&', 
    									['<=', ['INT', 0], ['VAR', 'VAR_i']], 
    										['<', ['VAR', 'VAR_i'], ['VAR', 'VAR_N']]],\
     								['!=', ['ARR', 'ARR_a', ['VAR', 'VAR_i']], ['VAR', 'VAR_x']]]]]]]], 
    ['ASSERT', ['=', ['ARR', 'ARR_a', ['INT', 0]], ['VAR', 'VAR_i']]]]

def process(program, num_unrolls, path_conditions, assignments):

	if program[0] == 'CONCAT':
		process(program[1], num_unrolls, path_conditions, assignments)
		process(program[2], num_unrolls, path_conditions, assignments)

	elif program[0] == 'ASSIGN':
		assignments[program[1]] = program[2]

	elif program[0] == 'WHILE':
		for i in range(num_unrolls+1):
			if i == 0:
				path_conditions.append(['!', program[1]])
				return

			# if eval_condition():
			# 	process(program[])


# Recursively process program and update path_conditions and assignments
	# would it be easier to parse iteratively and process as we go along?
		# This could have it's own challenges. For example, how do I know "n := 0;" is the next thing to process? Can look for keywords as a priority, like "while"

		# TODO: parse iteratively. I can get rid of most statements from the in_str. When encountering a loop, handle that recursively.
			# have a bool to signify loop for processing iteratively

# Call solver whenever assertion is encountered (precondition must not be assertion then?)
def see(parsed, num_unrolls):
	name, variables, preconditions, program = parsed
	print(f"name: {name}\n")
	print(f"variables: {variables}\n")
	print(f"preconditions: {preconditions}\n")
	print(f"program: {program}\n")


	# I can probably represent active assertions by adding/removing in path_conditions
	# path_conditions is dict from index of "end" in program string to list of conditions. this allows for easy removal when the loop or if stmt is done
		# might need data, like the idx of the last active if or while. or might be able to search shaved substr in unshaved program
	# assignments is dict from name to value. for arrays, it is from name to list of tuple(index, value). for ex, "a[5] := 1;" becomes {"a": [(5, 1)]}
		# this way it is easy to determine the length of the array later and assign the array explicity (multiple writes to same idx is not issue bc can overwrite)
		# store arrays as plain name (not "ARR_") and determine it's array because value is list
	path_conditions, assignments = {}, {}

	process(program, num_unrolls, path_conditions, assignments)



# program find(N a[]) 
#	pre 0 <= N pre N <= 10
#	is 
#		n := 0; 
#		while n < N && a[n] != x do n := n + 1; assert x = 1; end
#		assert !(a[n] = x || forall i, (0 <= i && i < N) ==> a[i] != x); 
#		assert a[0] = i; 
#	end

def eval_condition(bexp, assignments):
	return True


def parse_head(program):
	# useful for path_conditions
	program_idx_start, program_idx_end = 0, len(program) - 1

	# get program name, variables
	name_and_var_idx_start = program.find("(")
	name_and_var_idx_end = program.find(")")

	name = program[program.find("program ") + 8:name_and_var_idx_start]
	var_list = [['ARR', 'ARR_' + s[:-2]] if s.endswith("[]") else ['VAR', 'VAR_' + s] for s in program[name_and_var_idx_start+1:name_and_var_idx_end].split()]

	program = program[name_and_var_idx_end+2:]
	program_idx_start = program_idx_start + name_and_var_idx_end + 2

	# print(f"name: {name}\n")
	# print(f"var_list: {var_list}\n")
	# print(f"program: {program}\n")

	# get preconditions
	pre_idx_end = program.find("is")
	precondition_strs = program[:pre_idx_end].split("pre")
	if not precondition_strs[0]:
		precondition_strs = precondition_strs[1:]

	preconditions = []
	for s in precondition_strs:
		preconditions.append(parse_assn(s))

	# program = program[pre_idx_end+3:-4]
	program_idx_start = program_idx_start + pre_idx_end + 3
	program_idx_end -= 3

	# print(f"preconditions: {preconditions}\n")
	# print(f"program: {program}\n")

	return program_idx_start, program_idx_end, name, var_list, preconditions


def parse_body(program, program_idx_start, program_idx_end, name, path_conditions, assignments):
	while program_idx_start < program_idx_end:
		# check for semicolon statement
		if not program[program_idx_start:].startswith("if") and not program[program_idx_start:].startswith("while"):
			stmt_idx_end = program[program_idx_start:].find(";")
			stmt = program[program_idx_start:program_idx_start + stmt_idx_end]

			print(f"stmt: {stmt}\n")

			# 4 types of semicolon statements: assert, array assignment (with "[" before ":="), double assignment (with "," before ":="), and single assignment
			if stmt.find("assert") != -1:
				check_assertion(path_conditions, assignments)

			elif stmt.find("[") != -1 and stmt.find("[") < stmt.find(":="):
				arr_name = stmt[:stmt.find("[")]
				idx_and_val = (parse_aexp(stmt[stmt.find("[")+1:stmt.find("]")]), parse_aexp(stmt[stmt.find(":=")+3:]))
				if arr_name not in assignments:
					assignments[arr_name] = [idx_and_val]
				else:
					assignments[arr_name].append(idx_and_val)

			elif stmt.find(",") != -1 and stmt.find(",") < stmt.find(":="):
				var1, var2 = stmt[:stmt.find(",")], stmt[stmt.find(",")+2:stmt.find(":=")-1]
				if var1 not in assignments:
					assignments[var1] = [parse_aexp(stmt[stmt.find(":=")+3:stmt.rfind(",")])]
				else:
					assignments[var1].append(parse_aexp(stmt[stmt.find(":=")+3:stmt.rfind(",")]))
				if var2 not in assignments:
					assignments[var2] = [parse_aexp(stmt[stmt.rfind(",")+2:])]
				else:
					assignments[var2].append(parse_aexp(stmt[stmt.rfind(",")+2:]))

			else:
				var = stmt[:stmt.find(":=")-1]
				if var not in assignments:
					assignments[var] = [parse_aexp(stmt[stmt.find(":=")+3:])]
				else:
					assignments[var].append(parse_aexp(stmt[stmt.find(":=")+3:]))

			program_idx_start = program_idx_start + stmt_idx_end + 2
			# print(f"stmt: {stmt}, assignments: {assignments}\n")

		else:
			print(f"program: {program[program_idx_start:program_idx_end]}\n")

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

			bexp = stmt[3: stmt.find("then")-1] if stmt.startswith("if") else stmt[6: stmt.find("do")-1]

			print(f"bexp: {bexp}\n")

			# 3 types: while, if with "else" (number of "else" matches number of "if"), and if
			if stmt.startswith("while"):
				# definitely need a for loop here. for each call, evaluate loop body i times and allow execution to continue. and backtrack after?
					# num_unrolls does not change between calls
				# try the if case first 
				# could help to just track the index into the original program I'm at and never actually shave the program
					# make this function recursive
				pass

			elif stmt.count("if") == stmt.count("else"):
				pass

			else:
				if eval_condition(bexp, assignments):
					if_end_idx = program_idx_start + stmt.rfind("end")
					if if_end_idx in path_conditions:
						path_conditions[if_end_idx].append(parse_bexp(bexp))
					else:
						path_conditions[if_end_idx] = [parse_bexp(bexp)]

					block = stmt[stmt.find("then")+5:stmt.rfind("end")-1]

					print(f"path_conditions: {path_conditions}\n")
					print(f"block: {block}\n")

					# do recursive call with block
					new_idx_start, new_idx_end = program_idx_start + stmt.find("then") + 5, program_idx_start + stmt.rfind("end")-1
					parse_body(program, new_idx_start, new_idx_end, name, path_conditions, assignments)

					# remove path_condition now that the block is done
					del path_conditions[if_end_idx]
					print(f"assignments: {assignments}\n")
					print(f"path_conditions: {path_conditions}\n")
					return 


					# TODO: adding assignments onto a list for each var will not work because i don't know the order they should be applied relative
						# to other vars. So I need to apply it on the spot.
							# should eval each parsed aexp on the spot rather than combining two aexp and trying to eval later

			return


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

		path_conditions, assignments = {}, {}
		parse_body(program, program_idx_start, program_idx_end, name, path_conditions, assignments)

		


if __name__ == "__main__":
	main()









