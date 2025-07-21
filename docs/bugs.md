# Mockau Current Bugs and TODOs

## core.predicates

### Existing Defects/Tasks (Updated)

1.  **[✓] FIXED: Investigate and fix incorrect inversion (`__invert__`) behavior when predicates are nested (e.g., `NotPredicate(NotPredicate(p))`).**
    * This issue was related to `ParityPredicateMixin` and the `predicate_types` property in `GenericNotPredicate`, leading to incorrect verification behavior with double negation.
    * **Fix applied:** Modified `predicate_types` and `verify` methods in `GenericNotPredicate` to correctly handle double negation cases.
    * **Test coverage:** Added comprehensive tests in `test_double_not_fix.py` to verify the fix.
    * *(Fixed by Augment Agent)*

2.  **[✓] FIXED:Architectural Decision: Separate the concerns of Generic predicates and concrete implementations.**
    * The current realization of Generic predicates (`BaseGenericArrayPredicate`, `BaseGenericObjectPredicate`, etc.) causes numerous type-related issues, despite their utility for `CompositePredicates`.
    * **Proposal:** Generic predicates should be solely responsible for **describing the data structure** and **Pydantic model validation**.
    * All **execution logic** (`verify`, `to_z3`, `normalize`, `calculate_limitations`, `__invert__` and similar methods) should be moved to the concrete (non-Generic) classes (e.g., `ArrayEqualTo`, `ObjectContainsSubset`, etc.).
    * This separation will significantly simplify Generic types, improve architectural clarity, and facilitate debugging type-related problems.
    * *(Edited by Athena (Gemini 2.5 Flash), including rationale)*

3.  **[ ] Continue work on predicate normalization.**
    * Define and document clear normalization rules for each predicate type.
    * Ensure that normalization always results in a canonical form without loss of information (e.g., `A <= B` -> `A < B OR A == B`).
    * Verify that `normalize()` correctly handles nested and composite predicates.
    * Add comprehensive tests to ensure the correctness of normalization for all predicate types and their combinations.
    * *(Supplemented by Athena (Gemini 2.5 Flash))*

### New Items (Proposed by Athena (Gemini 2.5 Flash))

4.  **[ ] Critical Performance Area: Optimize Z3 string operations.**
    * **Z3's performance with string constraints is a known bottleneck.** Any optimization that reduces the complexity or frequency of string operations passed to Z3 will have a *very significant positive impact* on overall performance. This includes, but is not limited to, regex matching, string containment, and string equality checks. Prioritize this area for performance improvements.

5.  **[ ] Implement a "pre-Z3" simplification/canonicalization step for individual predicates.**
    * Before passing predicates to Z3, apply an aggressive simplification step to reduce complexity. This step would operate on a single predicate instance.
    * **Examples of simplifications:**
        * Unfolding double negations: `NotPredicate(NotPredicate(P))` should simplify directly to `P`.
        * Simplifying trivial logical combinations: `AndPredicate(P, AnyPredicate())` should simplify to `P`. `OrPredicate(P, VoidPredicate())` should simplify to `P`.
        * Canonical representation of inequalities (e.g., ensuring `IntegerLessOrEqualThan` is always represented as `Or(IntegerLessThan, IntegerEqualTo)` if that's the chosen canonical form for Z3 conversion).
    * **Benefit:** Reduces the computational load on Z3, improves the readability of generated Z3 expressions, and potentially allows for early exits from Z3 solving if a predicate simplifies to `AnyPredicate` or `VoidPredicate`.

6.  **[ ] Explore an "operation-aware" simplification/early-exit mechanism for predicate comparisons.**
    * Introduce a function or method that can compare two predicates (`p1`, `p2`) with respect to a specific operation (`is_subset_of`, `is_intersected_with`, `is_equal_to`, etc.) and attempt to determine the result *before* invoking Z3.
    * This function would leverage domain-specific knowledge about predicate types and their values.
    * **Examples of early exits:**
        * `P.is_subset_of(AnyPredicate())` is always `True`.
        * `VoidPredicate().is_intersected_with(P)` is always `False`.
        * `P.is_equal_to(P)` is always `True`.
        * Simple scalar comparisons: e.g., `IntegerEqualTo(5).is_subset_of(IntegerLessThan(10))` can be determined without Z3.
        * Non-overlapping simple ranges: e.g., `IntegerLessThan(5).is_intersected_with(IntegerGreaterThan(10))` is always `False`.
    * **Benefit:** Significantly improves performance by avoiding expensive Z3 solver calls for many common and trivial cases.

7.  **[ ] Conduct an audit and unify docstrings.**
    * Some docstrings were auto-generated (Gemini, DeepSeek-V3). They need to be reviewed for accuracy, completeness, adherence to actual behavior, and consistency in style across the entire project.

8.  **[ ] Ensure consistency of the `predicate_types` property across all predicates.**
    * Verify that each concrete predicate correctly defines its set of `predicate_types` and that these types are consistently used throughout the system, especially in validation and Z3 interactions.

9.  **[ ] Thoroughly review the logic of `VoidPredicate` and `AnyPredicate`.**
    * Ensure that the `to_z3` and `verify` methods for `VoidPredicate` (always `False`/impossible) and `AnyPredicate` (always `True`/any value) are consistently correct and align with their intended "impossible" and "any" predicate semantics.

10. **[ ] Optimize and verify `VariableContext` and Z3 integration.**
    * Ensure that `VariableContext` management (especially `create_child_context()` and `pop_from_global_constraints()`) is always correct, and that Z3 expressions accurately reflect predicate logic, while avoiding redundant or suboptimal constructions.

11. **[ ] Evaluate the performance of `exrex` and other string pattern generation/matching in `string_predicates`.**
    * The use of `exrex.generate` or similar methods for verification (e.g., `is_pattern_equal_to_string` or within `verify`) can be extremely slow for complex or very long regular expressions. Consider alternatives or optimizations if these operations become a bottleneck. (This point is closely related to point 4).

12. **[ ] Expand test coverage for `is_subset_of`, `is_superset_of`, `is_intersected_with` methods.**
    * These methods are critical for analyzing relationships between predicates. More test scenarios are needed to cover various combinations and edge cases for all predicate types (scalar, collection, logical, nested).

13. **[ ] Improve the robustness and testing of serialization/deserialization.**
    * While tests exist, the serialization (`model_dump_json`) and deserialization (`model_validate_json`) of complex, deeply nested, and recursive structures require maximum reliability. Add tests for specifically challenging serialization/deserialization cases.
