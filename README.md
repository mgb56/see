# Symbolic Execution Engine

An implementation of a symbolic execution engine, used to find assertion violations. Makes use of z3py as the SMT solver.

Setup: "pip install z3"

Usage: python see.py <path_to_file> #num_unrolls

Example usage: python see.py find.imp 3
