import program_parser
import os
from z3 import *

def exp_to_z3(exp):
	"""
	Convert exp to a pySMT formula
	"""

	if not exp:
		return

	# AEXP 
	# negation is subtraction from 0 right?
	if exp[0] == 'INT':
		return exp[1]

	elif exp[0] == 'VAR':
		return Int(exp[1])

	elif exp[0] == 'ARR':
		if len(exp) == 2:
			return Array(exp[1], IntSort(), IntSort())
		else:
			# select
			return Array(exp[1], IntSort(), IntSort())[exp_to_z3(exp[2])]

	elif exp[0] == 'STORE':
		for i in (2, 3):
			if isinstance(exp[i], int):
				exp[i] = Int(exp[i])
		return Store(Array(exp[1], IntSort(), IntSort()), exp_to_z3(exp[2]), exp_to_z3(exp[3]))

	elif exp[0] == '+':
		return exp_to_z3(exp[1]) + exp_to_z3(exp[2])

	elif exp[0] == '-':
		return exp_to_z3(exp[1]) - exp_to_z3(exp[2])

	elif exp[0] == '*':
		return exp_to_z3(exp[1]) * exp_to_z3(exp[2])

	elif exp[0] == '/':
		if isinstance(exp_to_z3(exp[1]), int) and isinstance(exp_to_z3(exp[2]), int):  # Deal with true integers separately, as / will float-divide for these
			return exp_to_z3(exp[1]) // exp_to_z3(exp[2])
		else:
			assert is_idiv(exp_to_z3(exp[1]) / exp_to_z3(exp[2]))
			return exp_to_z3(exp[1]) / exp_to_z3(exp[2])
		

	elif exp[0] == '%':
		return exp_to_z3(exp[1]) % exp_to_z3(exp[2])


	# BEXP
	if exp[0] == '!':
		return Not(exp_to_z3(exp[1]))

	elif exp[0] == '&&':
		return And(exp_to_z3(exp[1]), exp_to_z3(exp[2]))

	elif exp[0] == '||':
		return Or(exp_to_z3(exp[1]), exp_to_z3(exp[2]))


	# COMP
	if exp[0] == '>':
		return exp_to_z3(exp[1]) > exp_to_z3(exp[2])

	elif exp[0] == '<':
		return exp_to_z3(exp[1]) < exp_to_z3(exp[2])

	elif exp[0] == '>=':
		return exp_to_z3(exp[1]) >= exp_to_z3(exp[2])

	elif exp[0] == '<=':
		return exp_to_z3(exp[1]) <= exp_to_z3(exp[2])

	elif exp[0] == '=':
		return exp_to_z3(exp[1]) == exp_to_z3(exp[2])

	elif exp[0] == '!=':
		return exp_to_z3(exp[1]) != exp_to_z3(exp[2])

	# ASSN
	if exp[0] == '==>':
		return Implies(exp_to_z3(exp[1]), exp_to_z3(exp[2]))

	elif exp[0] == 'forall':
		return ForAll([Int(i) for i in exp[1]], exp_to_z3(exp[2]))

	elif exp[0] == 'exists':
		return Exists([Int(i) for i in exp[1]], exp_to_z3(exp[2]))

	raise NotImplementedError

# assert parse_aexp("x+2*3%4") == ['+', ['VAR', 'VAR_x'], ['%', ['*', ['INT', 2], ['INT', 3]], ['INT', 4]]]


# def z3valid(program, verbose=0, ret_expr=False):
# 	fvg = converter.FreshVarGenerator()
# 	if verbose > 0:
# 		print("Checking ", program)
# 	exp = program_parser.parse_stmt(program)
# 	if verbose > 1:
# 		print("exp:", exp)
# 	gc = converter.exp_stmt_to_GC(exp, fvg)
# 	if verbose > 1:
# 		print("GC:", gc)
# 	exp = exp_generation.backprop_gc(gc, converter.TRUE, fvg)
# 	if verbose > 1:
# 		print("exp:", exp)
# 	unsat_formula = Not(exp_to_z3(exp))
# 	s = Solver()
# 	s.add(unsat_formula)
# 	if verbose > 1:
# 		print(unsat_formula)
# 	if ret_expr:
# 		return(s.sexpr())
# 	else:
# 		verified = s.check() == unsat
# 		if verbose > 0:
# 			print("Verified:", verified)
# 		return(verified)


# fvg = converter.FreshVarGenerator()


# smtform = exp_to_z3(exp_generation.backprop_gc(converter.exp_stmt_to_GC(\
# 	program_parser.parse_stmt("program brief pre x > 8 post x = 4 is x:=x+3; end"), fvg),\
# 	 converter.TRUE, fvg))
# print()
# print(smtform)

# print()
# print(exp_generation.backprop_gc(converter.exp_stmt_to_GC(\
# 	program_parser.parse_stmt("program brief pre x > 8 post x = 4 is x:=x+3; end"), fvg),\
# 	 converter.TRUE, fvg))










