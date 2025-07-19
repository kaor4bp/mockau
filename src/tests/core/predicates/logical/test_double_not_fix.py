"""
Test for the double NOT predicate bug fix.

This test verifies that NOT(NOT(P)) behaves correctly with respect to:
1. predicate_types property
2. verify method
3. normalization
"""

from core.predicates import IntegerEqualTo, NotPredicate, StringEqualTo
from core.predicates.consts import PredicateType


class TestDoubleNotPredicateFix:
    """Test the fix for double NOT predicate bug."""

    def test_double_not_predicate_types(self):
        """Test that double NOT has correct predicate_types."""
        base = IntegerEqualTo(value=5)
        single_not = NotPredicate(predicate=base)
        double_not = NotPredicate(predicate=single_not)

        # Base predicate should support only Integer
        assert base.predicate_types == {PredicateType.Integer}

        # Single NOT should support only Integer (same as base)
        assert single_not.predicate_types == {PredicateType.Integer}

        # Double NOT should support only Integer (same as base, since NOT(NOT(P)) = P)
        assert double_not.predicate_types == {PredicateType.Integer}

    def test_double_not_verify_behavior(self):
        """Test that double NOT verify behaves like the original predicate."""
        base = IntegerEqualTo(value=5)
        single_not = NotPredicate(predicate=base)
        double_not = NotPredicate(predicate=single_not)

        # Test with integer value 5
        assert base.verify(5) is True
        assert single_not.verify(5) is False
        assert double_not.verify(5) is True  # Should behave like base

        # Test with integer value 6
        assert base.verify(6) is False
        assert single_not.verify(6) is True  # True because NOT(IntegerEqualTo(5)).verify(6) = NOT(False) = True
        assert double_not.verify(6) is False  # Should behave like base

        # Test with string value
        assert base.verify('hello') is False
        assert single_not.verify('hello') is True  # True because 'hello' is not an integer
        assert double_not.verify('hello') is False  # Should behave like base

    def test_double_not_normalization(self):
        """Test that double NOT normalizes correctly."""
        base = IntegerEqualTo(value=5)
        double_not = NotPredicate(predicate=NotPredicate(predicate=base))

        normalized = double_not.normalize()

        # Double NOT should normalize to the base predicate
        assert isinstance(normalized, IntegerEqualTo)
        assert normalized.value == 5

    def test_triple_not_behavior(self):
        """Test that triple NOT behaves like single NOT."""
        base = IntegerEqualTo(value=5)
        single_not = NotPredicate(predicate=base)
        triple_not = NotPredicate(predicate=NotPredicate(predicate=single_not))

        # Triple NOT should behave like single NOT
        assert triple_not.verify(5) is False
        assert triple_not.verify(6) is True  # True because NOT(IntegerEqualTo(5)).verify(6) = NOT(False) = True
        assert triple_not.verify('hello') is True  # 'hello' is not an integer

    def test_different_base_predicate_types(self):
        """Test double NOT with different base predicate types."""
        # Test with StringEqualTo
        string_base = StringEqualTo(value='test')
        string_double_not = NotPredicate(predicate=NotPredicate(predicate=string_base))

        assert string_double_not.predicate_types == {PredicateType.String}
        assert string_double_not.verify('test') is True  # Should behave like base
        assert string_double_not.verify('other') is False  # Should behave like base
        assert string_double_not.verify(123) is False  # Should behave like base

    def test_parity_handling(self):
        """Test that _parity is handled correctly in double NOT."""
        base = IntegerEqualTo(value=5)
        single_not = NotPredicate(predicate=base)
        double_not = NotPredicate(predicate=single_not)

        # Check parity values - only ParityPredicateMixin classes have _parity
        # IntegerEqualTo doesn't inherit from ParityPredicateMixin
        assert single_not._parity is True  # Outer NOT has _parity=True
        assert double_not._parity is True  # Outer NOT has _parity=True

        # Check compiled_value parity
        assert isinstance(single_not.compiled_value, IntegerEqualTo)  # compiled_value is the base predicate
        assert double_not.compiled_value._parity is False  # Inner NOT gets inverted parity
        assert isinstance(double_not.compiled_value.compiled_value, IntegerEqualTo)  # Base predicate
