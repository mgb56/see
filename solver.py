import program_parser
from z3 import *

def exp_to_z3(exp, quant_vars=None):
	"""
	Convert exp to a pySMT formula
	"""

	if not exp:
		return

	# AEXP 
	if exp[0] == 'INT':
		return exp[1]

	elif exp[0] == 'VAR':
		if quant_vars and exp[1] in quant_vars:
			return Int("quant_" + exp[1])
		return Int(exp[1])

	elif exp[0] == 'ARR':
		if len(exp) == 2:
			return Array(exp[1], IntSort(), IntSort())
		else:
			# select
			return Array(exp[1], IntSort(), IntSort())[exp_to_z3(exp[2], quant_vars)]

	elif exp[0] == 'STORE':
		for i in (2, 3):
			if isinstance(exp[i], int):
				exp[i] = Int(exp[i])
		if not isinstance(exp[1], str):
			return Store(exp[1], exp_to_z3(exp[2], quant_vars), exp_to_z3(exp[3], quant_vars))
		return Store(Array(exp[1], IntSort(), IntSort()), exp_to_z3(exp[2], quant_vars), exp_to_z3(exp[3], quant_vars))

	elif exp[0] == '+':
		return exp_to_z3(exp[1], quant_vars) + exp_to_z3(exp[2], quant_vars)

	elif exp[0] == '-':
		return exp_to_z3(exp[1], quant_vars) - exp_to_z3(exp[2], quant_vars)

	elif exp[0] == '*':
		return exp_to_z3(exp[1], quant_vars) * exp_to_z3(exp[2], quant_vars)

	elif exp[0] == '/':
		if isinstance(exp_to_z3(exp[1], quant_vars), int) and isinstance(exp_to_z3(exp[2], quant_vars), int):  
			return exp_to_z3(exp[1], quant_vars) // exp_to_z3(exp[2], quant_vars)
		else:
			assert is_idiv(exp_to_z3(exp[1], quant_vars) / exp_to_z3(exp[2], quant_vars))
			return exp_to_z3(exp[1], quant_vars) / exp_to_z3(exp[2], quant_vars)
		

	elif exp[0] == '%':
		return exp_to_z3(exp[1], quant_vars) % exp_to_z3(exp[2], quant_vars)


	# BEXP
	if exp[0] == '!':
		return Not(exp_to_z3(exp[1]), quant_vars)

	elif exp[0] == '&&':
		return And(exp_to_z3(exp[1], quant_vars), exp_to_z3(exp[2], quant_vars))

	elif exp[0] == '||':
		return Or(exp_to_z3(exp[1], quant_vars), exp_to_z3(exp[2], quant_vars))


	# COMP
	if exp[0] == '>':
		return exp_to_z3(exp[1], quant_vars) > exp_to_z3(exp[2], quant_vars)

	elif exp[0] == '<':
		return exp_to_z3(exp[1], quant_vars) < exp_to_z3(exp[2], quant_vars)

	elif exp[0] == '>=':
		return exp_to_z3(exp[1], quant_vars) >= exp_to_z3(exp[2], quant_vars)

	elif exp[0] == '<=':
		return exp_to_z3(exp[1], quant_vars) <= exp_to_z3(exp[2], quant_vars)

	elif exp[0] == '=':
		return exp_to_z3(exp[1], quant_vars) == exp_to_z3(exp[2], quant_vars)

	elif exp[0] == '!=':
		return exp_to_z3(exp[1], quant_vars) != exp_to_z3(exp[2], quant_vars)

	# ASSN
	if exp[0] == '==>':
		return Implies(exp_to_z3(exp[1], quant_vars), exp_to_z3(exp[2], quant_vars))

	elif exp[0] == 'forall':
		quant_vars = [i for i in exp[1]]
		return ForAll([Int("quant_" + i) for i in exp[1]], exp_to_z3(exp[2], quant_vars))

	elif exp[0] == 'exists':
		quant_vars = [i for i in exp[1]]
		return Exists([Int("quant_" + i) for i in exp[1]], exp_to_z3(exp[2], quant_vars))

	raise NotImplementedError
