import re
from copy import deepcopy
from sympy import to_cnf, symbols, sympify, false, true
from sympy.logic.boolalg import And, Or, Not, Equivalent
from collections import Counter

RED = "\033[91m"
GREEN = "\033[92m"
RESET = "\033[0m"

symbol_map = {chr(c): symbols(chr(c)) for c in range(ord('A'), ord('Z') + 1)}

def convert_to_sympy_expr(expr):
    expr = expr.replace("¬", "~")
    expr = expr.replace("∧", "&")
    expr = expr.replace("∨", "|")
    expr = expr.replace("→", ">>")
    expr = expr.replace("↔", "==")
    return expr

def reverse_translate_expr(expr):
    expr = expr.replace("~", "¬")
    expr = expr.replace("&", "∧")
    expr = expr.replace("|", "∨")
    expr = expr.replace(">>", "→")
    expr = expr.replace("==", "↔")
    return expr

def translate_input_logic_symbols(logic_expr):
    converted = convert_to_sympy_expr(logic_expr)
    return converted

def is_wff(formula):
    try:
        expr = convert_to_sympy_expr(formula)
        sympify(expr, locals=symbol_map)
        return True
    except:
        return False

def convert_to_cnf(expr):
    try:
        if expr.count("↔") > 1 or expr.count("→") > 1 or "↔(" in expr or "→(" in expr:
            return "UNSUPPORTED_STRUCTURE"
        if expr.count("→") >= 1 and "∨" in expr and "→" in expr:
            return "UNSUPPORTED_STRUCTURE"
        if expr.count("(") - expr.count(")") != 0:
            return None

        sympy_expr = sympify(convert_to_sympy_expr(expr), locals=symbol_map)
        cnf_expr = to_cnf(sympy_expr, simplify=False)
        if cnf_expr == false:
            return "CONTRADICTION"
        elif cnf_expr == true:
            return "TAUTOLOGY"
        return str(cnf_expr)
    except:
        return None

def parse_cnf(cnf_str):
    cnf_str = cnf_str.replace("(", "").replace(")", "")
    return [[lit.strip() for lit in clause.split("|")] for clause in cnf_str.split(" & ")]

def to_int_clauses(clauses):
    var_map, counter, result = {}, 1, []
    for clause in clauses:
        int_clause = []
        for lit in clause:
            is_neg = lit.startswith("~")
            var = lit[1:] if is_neg else lit
            if var not in var_map:
                var_map[var] = counter
                counter += 1
            int_clause.append(-var_map[var] if is_neg else var_map[var])
        result.append(int_clause)
    return result, var_map

def display_clauses_as_letters(int_clauses, var_map):
    reverse_map = {v: k for k, v in var_map.items()}
    return [[f"¬{reverse_map[abs(l)]}" if l < 0 else reverse_map[abs(l)] for l in clause] for clause in int_clauses]

def dpll_with_assignment(clauses, assignment=[]):
    if not clauses:
        return True, assignment
    if [] in clauses:
        return False, []

    unit_clauses = [c[0] for c in clauses if len(c) == 1]
    if unit_clauses:
        return dpll_with_assignment(simplify_dpll(clauses, unit_clauses[0]), assignment + [unit_clauses[0]])

    literal_counts = Counter(lit for clause in clauses for lit in clause)
    best_lit = literal_counts.most_common(1)[0][0]

    sat, assign = dpll_with_assignment(simplify_dpll(clauses, best_lit), assignment + [best_lit])
    if sat:
        return True, assign
    return dpll_with_assignment(simplify_dpll(clauses, -best_lit), assignment + [-best_lit])

def simplify_dpll(clauses, literal):
    return [[l for l in clause if l != -literal] for clause in clauses if literal not in clause]

def dp_solver(clauses):
    assignment = []
    variables = set(abs(lit) for clause in clauses for lit in clause)
    def eliminate(var):
        pos, neg, rest = [], [], []
        for clause in clauses:
            if var in clause:
                pos.append(clause)
            elif -var in clause:
                neg.append(clause)
            else:
                rest.append(clause)
        new_clauses = rest[:]
        for p in pos:
            for n in neg:
                resolvent = list(set(p + n) - {var, -var})
                if not resolvent:
                    return None
                new_clauses.append(resolvent)
        return new_clauses
    for var in variables:
        result = eliminate(var)
        if result is None:
            return False, []
        clauses = result
        assignment.append(var)
    return True, assignment

def resolution_solver(clauses):
    new = set()
    clauses = [frozenset(c) for c in clauses]
    clause_set = set(clauses)
    while True:
        pairs = [(ci, cj) for i, ci in enumerate(clauses) for j, cj in enumerate(clauses) if i < j]
        for (ci, cj) in pairs:
            resolvents = resolve(ci, cj)
            if frozenset() in resolvents:
                return False
            new.update(resolvents)
        if new.issubset(clause_set):
            return True
        clause_set.update(new)
        clauses = list(clause_set)

def resolve(ci, cj):
    resolvents = set()
    for lit in ci:
        if -lit in cj:
            new_clause = (ci - {lit}) | (cj - {-lit})
            resolvents.add(frozenset(new_clause))
    return resolvents

def predict_best_solver(int_clauses):
    num_clauses = len(int_clauses)
    unit_clauses = [c for c in int_clauses if len(c) == 1]
    unit_ratio = len(unit_clauses) / num_clauses
    pure_literals = Counter(lit for clause in int_clauses for lit in clause)
    pure = [v for v in pure_literals if -v not in pure_literals]

    if num_clauses > 5 and len(pure) == 0 and unit_ratio < 0.1:
        return "Resolution", ["Resolution selected due to large and balanced clause set."]
    if unit_ratio > 0.35:
        return "DPLL", ["DPLL selected due to high unit clause ratio."]
    if len(pure) > 0:
        return "DP", ["DP selected due to pure literals."]
    return "DPLL", ["Fallback to DPLL."]

def test_formula(formula):
    print(f"\n--- Testing Formula ---")
    transformed = reverse_translate_expr(convert_to_sympy_expr(formula))
    print(f"Transformed formula: {transformed}")
    
    if not is_wff(formula):
        print(f"{RED}Invalid WFF.{RESET}")
        return

    raw_cnf = convert_to_cnf(formula)
    if raw_cnf == "UNSUPPORTED_STRUCTURE":
        print(f"{RED}Could not convert to CNF .{RESET}")
        return
    elif raw_cnf == "CONTRADICTION":
        print("CNF: Contradiction")
        print(f"{RED}UNSAT Result.{RESET}")
        return
    elif raw_cnf == "TAUTOLOGY":
        print("CNF: Tautology")
        print(f"{GREEN}SAT Result. (Tautology){RESET}")
        return
    elif raw_cnf is None:
        print(f"{RED}Could not convert to CNF.{RESET}")
        return

    readable_cnf = raw_cnf.replace("&", "∧").replace("|", "∨").replace("~", "¬")
    print(f"CNF: {readable_cnf}")

    parsed = parse_cnf(raw_cnf)
    int_clauses, var_map = to_int_clauses(parsed)
    print("CNF Clauses:")
    for clause in display_clauses_as_letters(int_clauses, var_map):
        print(" ", clause)

    solver, reasons = predict_best_solver(int_clauses)
    print(f"\nPredicted Solver: {solver}")
    for r in reasons:
        print("  •", r)

    reverse_var_map = {v: k for k, v in var_map.items()}
    def print_assignment(assign, tag):
        named = [f"{reverse_var_map[abs(l)]} = {'True' if l > 0 else 'False'}"
                 for l in assign if abs(l) in reverse_var_map]
        print(f"{GREEN}SAT Result. Assignment ({tag}):{RESET}")
        for a in named:
            print("  ", a)

    if solver == "Resolution":
        result = resolution_solver(int_clauses)
        print(f"{GREEN}SAT Result.{RESET}" if result else f"{RED}UNSAT Result.{RESET}")
    elif solver == "DP":
        result, assignment = dp_solver(deepcopy(int_clauses))
        print_assignment(assignment, "DP") if result else print(f"{RED}UNSAT Result.{RESET}")
    else:
        result, assignment = dpll_with_assignment(deepcopy(int_clauses))
        print_assignment(assignment, "DPLL") if result else print(f"{RED}UNSAT Result.{RESET}")

test_cases = [
    "((A>>B)&A)",                                    
    "(A|~B)",                                      
    "((A|B)&(~A|~B)&(C|D)&(~C|~D)&(E|F)&(~E|~F))",  
    "(~(A&(¬A)))",                                  
    "(A&~A)",                                       
    "(A&B)&(~A|~B)",                                
    "(~)",                                          
    "(A|(B&))",                                     
    "(A==(B==C))"
]
if __name__ == "__main__":
    for i, formula in enumerate(test_cases, 1):
        print(f"\n=== Test Case {i} ===")
        test_formula(formula)
