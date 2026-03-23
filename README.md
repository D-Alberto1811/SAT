SAT Solver (Python)

This project is a Boolean satisfiability (SAT) solver implemented in Python. It parses logical formulas, converts them to CNF (Conjunctive Normal Form), and solves them using multiple algorithms.

Features
Supports common logical operators:
¬ (NOT), ∧ (AND), ∨ (OR), → (IMPLIES), ↔ (EQUIVALENT)
Converts formulas to CNF using sympy
Implements multiple SAT solving algorithms:
DPLL (Davis–Putnam–Logemann–Loveland)
DP (Davis–Putnam)
Resolution-based solver
Automatically selects the best solver based on heuristics
Provides satisfying assignments when possible
How It Works
Input a logical formula (e.g. A ∧ (B → C))
The program:
Validates the formula
Converts it to CNF
Translates clauses into integer form
Chooses a solving strategy
Outputs whether the formula is:
Satisfiable (SAT) with assignment
Unsatisfiable (UNSAT)
