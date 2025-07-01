from uuid import uuid4

import z3

from utils.z3_helpers import ConvertEREToZ3Regex


def get_pattern_estimated_length(pattern: str, is_case_sensitive: bool, min_hits: int = 2):
    solver = z3.Solver()
    hits = 0
    length = 1
    string_variable = z3.String(f"string_{uuid4()}")

    solver.add(z3.InRe(string_variable, ConvertEREToZ3Regex(pattern, is_case_sensitive=is_case_sensitive).convert()))

    while True:
        solver.push()
        solver.add(z3.Length(string_variable) <= z3.IntVal(length))
        if solver.check() == z3.sat:
            hits += 1

        if hits >= min_hits:
            return length + 1

        solver.pop()
        length = length * 2
