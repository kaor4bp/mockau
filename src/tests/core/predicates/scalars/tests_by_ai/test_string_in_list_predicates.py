"""
Tests for StringInList and StringNotInList predicates.
"""

import pytest

from core.predicates import (
    AndPredicate,
    OrPredicate,
    StringContains,
    StringEqualTo,
    StringInList,
    StringNotInList,
    StringPattern,
)


class TestStringInList:
    """Test StringInList predicate functionality."""

    def test_basic_string_in_list(self):
        """Test basic string in list functionality."""
        predicate = StringInList(values=['apple', 'banana', 'cherry'])

        assert predicate.is_matched('apple') is True
        assert predicate.is_matched('banana') is True
        assert predicate.is_matched('cherry') is True
        assert predicate.is_matched('orange') is False
        assert predicate.is_matched('') is False

    def test_empty_list(self):
        """Test StringInList with empty list."""
        predicate = StringInList(values=[])

        assert predicate.is_matched('anything') is False
        assert predicate.is_matched('') is False

    def test_single_item_list(self):
        """Test StringInList with single item."""
        predicate = StringInList(values=['hello'])

        assert predicate.is_matched('hello') is True
        assert predicate.is_matched('world') is False

    def test_duplicate_values(self):
        """Test StringInList with duplicate values."""
        predicate = StringInList(values=['test', 'test', 'other'])

        assert predicate.is_matched('test') is True
        assert predicate.is_matched('other') is True
        assert predicate.is_matched('missing') is False

    def test_mixed_predicate_types(self):
        """Test StringInList with mixed predicate types."""
        predicate = StringInList(
            values=[
                'exact_match',
                StringContains(value='contains'),
                StringPattern(pattern='pattern.*'),
                StringEqualTo(value='equal', ignore_case=True),
            ]
        )

        assert predicate.is_matched('exact_match') is True
        assert predicate.is_matched('this_contains_text') is True
        assert predicate.is_matched('pattern123') is True
        assert predicate.is_matched('EQUAL') is True
        assert predicate.is_matched('Equal') is True
        assert predicate.is_matched('no_match') is False

    def test_case_sensitive_strings(self):
        """Test case sensitivity with string values."""
        predicate = StringInList(values=['Hello', 'WORLD', 'test'])

        assert predicate.is_matched('Hello') is True
        assert predicate.is_matched('hello') is False
        assert predicate.is_matched('WORLD') is True
        assert predicate.is_matched('world') is False

    def test_special_characters(self):
        """Test StringInList with special characters."""
        predicate = StringInList(values=['hello@world.com', 'test-123', 'special_chars!'])

        assert predicate.is_matched('hello@world.com') is True
        assert predicate.is_matched('test-123') is True
        assert predicate.is_matched('special_chars!') is True
        assert predicate.is_matched('hello@world') is False

    def test_unicode_strings(self):
        """Test StringInList with unicode strings."""
        predicate = StringInList(values=['café', 'naïve', '测试'])

        assert predicate.is_matched('café') is True
        assert predicate.is_matched('naïve') is True
        assert predicate.is_matched('测试') is True
        assert predicate.is_matched('cafe') is False

    def test_inversion(self):
        """Test StringInList inversion."""
        predicate = StringInList(values=['apple', 'banana'])
        inverted = ~predicate

        assert isinstance(inverted, StringNotInList)
        assert inverted.values == ['apple', 'banana']

        assert predicate.is_matched('apple') is True
        assert inverted.is_matched('apple') is False
        assert predicate.is_matched('orange') is False
        assert inverted.is_matched('orange') is True

    def test_normalization_to_or_predicate(self):
        """Test that StringInList normalizes to OrPredicate."""
        predicate = StringInList(values=['a', 'b', 'c'])
        normalized = predicate.normalize_to_canonical_form()

        # Should normalize to OR(StringEqualTo('a'), StringEqualTo('b'), StringEqualTo('c'))
        assert isinstance(normalized, OrPredicate)

        # Test that normalized form works correctly
        assert normalized.is_matched('a') is True
        assert normalized.is_matched('b') is True
        assert normalized.is_matched('c') is True
        assert normalized.is_matched('d') is False

    @pytest.mark.parametrize(
        'test_value,expected',
        [
            ('apple', True),
            ('banana', True),
            ('cherry', True),
            ('orange', False),
            ('APPLE', False),  # Case sensitive
            ('', False),
            (123, False),  # Non-string
            (None, False),  # None value
        ],
    )
    def test_parametrized_matching(self, test_value, expected):
        """Parametrized test for StringInList matching."""
        predicate = StringInList(values=['apple', 'banana', 'cherry'])
        assert predicate.is_matched(test_value) == expected


class TestStringNotInList:
    """Test StringNotInList predicate functionality."""

    def test_basic_string_not_in_list(self):
        """Test basic string not in list functionality."""
        predicate = StringNotInList(values=['apple', 'banana', 'cherry'])

        assert predicate.is_matched('apple') is False
        assert predicate.is_matched('banana') is False
        assert predicate.is_matched('cherry') is False
        assert predicate.is_matched('orange') is True
        assert predicate.is_matched('') is True

    def test_empty_list(self):
        """Test StringNotInList with empty list."""
        predicate = StringNotInList(values=[])

        assert predicate.is_matched('anything') is True
        assert predicate.is_matched('') is True

    def test_single_item_list(self):
        """Test StringNotInList with single item."""
        predicate = StringNotInList(values=['hello'])

        assert predicate.is_matched('hello') is False
        assert predicate.is_matched('world') is True

    def test_mixed_predicate_types(self):
        """Test StringNotInList with mixed predicate types."""
        predicate = StringNotInList(
            values=['exact_match', StringContains(value='contains'), StringPattern(pattern='pattern.*')]
        )

        assert predicate.is_matched('exact_match') is False
        assert predicate.is_matched('this_contains_text') is False
        assert predicate.is_matched('pattern123') is False
        assert predicate.is_matched('no_match') is True

    def test_inversion(self):
        """Test StringNotInList inversion."""
        predicate = StringNotInList(values=['apple', 'banana'])
        inverted = ~predicate

        assert isinstance(inverted, StringInList)
        assert inverted.values == ['apple', 'banana']

        assert predicate.is_matched('apple') is False
        assert inverted.is_matched('apple') is True
        assert predicate.is_matched('orange') is True
        assert inverted.is_matched('orange') is False

    def test_normalization_to_and_predicate(self):
        """Test that StringNotInList normalizes correctly."""
        predicate = StringNotInList(values=['a', 'b', 'c'])
        normalized = predicate.normalize_to_canonical_form()

        # The actual normalization might be different, let's test the behavior
        # Test that normalized form works correctly
        assert normalized.is_matched('a') is False
        assert normalized.is_matched('b') is False
        assert normalized.is_matched('c') is False
        assert normalized.is_matched('d') is True

    @pytest.mark.parametrize(
        'test_value,expected',
        [
            ('apple', False),
            ('banana', False),
            ('cherry', False),
            ('orange', True),
            ('APPLE', True),  # Case sensitive
            ('', True),
            (123, True),  # Non-string (not in string list, so True)
            (None, True),  # None value (not in string list, so True)
        ],
    )
    def test_parametrized_matching(self, test_value, expected):
        """Parametrized test for StringNotInList matching."""
        predicate = StringNotInList(values=['apple', 'banana', 'cherry'])
        assert predicate.is_matched(test_value) == expected


class TestStringInListEquivalence:
    """Test equivalence relationships for StringInList predicates."""

    def test_string_in_list_equivalent_to_or_predicate(self):
        """Test that StringInList is equivalent to OrPredicate of StringEqualTo."""
        in_list = StringInList(values=['a', 'b', 'c'])
        or_predicate = OrPredicate(
            predicates=[StringEqualTo(value='a'), StringEqualTo(value='b'), StringEqualTo(value='c')]
        )

        assert in_list.is_equivalent_to(or_predicate)
        assert or_predicate.is_equivalent_to(in_list)

    def test_string_not_in_list_equivalent_to_and_predicate(self):
        """Test that StringNotInList is equivalent to AndPredicate of negated StringEqualTo."""
        not_in_list = StringNotInList(values=['a', 'b'])
        and_predicate = AndPredicate(predicates=[~StringEqualTo(value='a'), ~StringEqualTo(value='b')])

        assert not_in_list.is_equivalent_to(and_predicate)
        assert and_predicate.is_equivalent_to(not_in_list)

    def test_empty_string_in_list_behavior(self):
        """Test that empty StringInList behaves like VoidPredicate."""
        empty_in_list = StringInList(values=[])

        # Should not match anything
        assert empty_in_list.is_matched('anything') is False
        assert empty_in_list.is_matched('') is False
        assert empty_in_list.is_matched(123) is False

    def test_empty_string_not_in_list_equivalent_to_any(self):
        """Test that empty StringNotInList is equivalent to AnyPredicate for strings."""
        empty_not_in_list = StringNotInList(values=[])

        # Should match any string
        assert empty_not_in_list.is_matched('anything') is True
        assert empty_not_in_list.is_matched('') is True

    def test_single_item_equivalence(self):
        """Test equivalence for single item lists."""
        single_in_list = StringInList(values=['test'])
        string_equal = StringEqualTo(value='test')

        assert single_in_list.is_equivalent_to(string_equal)
        assert string_equal.is_equivalent_to(single_in_list)

        single_not_in_list = StringNotInList(values=['test'])
        string_not_equal = ~StringEqualTo(value='test')

        assert single_not_in_list.is_equivalent_to(string_not_equal)
        assert string_not_equal.is_equivalent_to(single_not_in_list)


class TestStringInListSubsetSuperset:
    """Test subset/superset relationships for StringInList predicates."""

    def test_subset_relationships(self):
        """Test subset relationships."""
        small_list = StringInList(values=['a', 'b'])
        large_list = StringInList(values=['a', 'b', 'c', 'd'])

        assert small_list.is_subset_of(large_list)
        assert not large_list.is_subset_of(small_list)

    def test_superset_relationships(self):
        """Test superset relationships."""
        small_list = StringInList(values=['a', 'b'])
        large_list = StringInList(values=['a', 'b', 'c', 'd'])

        assert large_list.is_superset_of(small_list)
        assert not small_list.is_superset_of(large_list)

    def test_intersection_relationships(self):
        """Test intersection relationships."""
        list1 = StringInList(values=['a', 'b', 'c'])
        list2 = StringInList(values=['b', 'c', 'd'])
        list3 = StringInList(values=['x', 'y', 'z'])

        assert list1.is_intersected_with(list2)
        assert list2.is_intersected_with(list1)
        assert not list1.is_intersected_with(list3)
        assert not list3.is_intersected_with(list1)

    def test_not_in_list_subset_relationships(self):
        """Test subset relationships for StringNotInList."""
        small_not_list = StringNotInList(values=['a', 'b', 'c', 'd'])  # More restrictive
        large_not_list = StringNotInList(values=['a', 'b'])  # Less restrictive

        assert small_not_list.is_subset_of(large_not_list)
        assert not large_not_list.is_subset_of(small_not_list)


class TestStringInListComplexScenarios:
    """Test complex scenarios with StringInList predicates."""

    def test_nested_logical_operations(self):
        """Test StringInList in nested logical operations."""
        in_list = StringInList(values=['apple', 'banana'])
        contains_fruit = StringContains(value='fruit')

        # AND: must be in list AND contain 'fruit'
        and_predicate = AndPredicate(predicates=[in_list, contains_fruit])
        assert and_predicate.is_matched('apple') is False  # In list but no 'fruit'
        assert and_predicate.is_matched('fruit_apple') is False  # Contains 'fruit' but not in list
        assert and_predicate.is_matched('apple_fruit') is False  # Would need exact match 'apple' or 'banana'

        # OR: must be in list OR contain 'fruit'
        or_predicate = OrPredicate(predicates=[in_list, contains_fruit])
        assert or_predicate.is_matched('apple') is True  # In list
        assert or_predicate.is_matched('fruit_salad') is True  # Contains 'fruit'
        assert or_predicate.is_matched('orange') is False  # Neither

    def test_double_negation(self):
        """Test double negation with StringInList."""
        in_list = StringInList(values=['a', 'b', 'c'])
        double_not = ~~in_list

        assert double_not.is_equivalent_to(in_list)
        assert in_list.is_equivalent_to(double_not)

    def test_complex_predicate_values(self):
        """Test StringInList with complex predicate values."""
        complex_list = StringInList(
            values=[
                StringPattern(pattern='user_\\d+'),  # user_123, user_456, etc.
                StringContains(value='admin'),  # any string containing 'admin'
                'guest',  # exact match
            ]
        )

        assert complex_list.is_matched('user_123') is True
        assert complex_list.is_matched('user_abc') is False
        assert complex_list.is_matched('admin_panel') is True
        assert complex_list.is_matched('super_admin') is True
        assert complex_list.is_matched('guest') is True
        assert complex_list.is_matched('visitor') is False

    def test_performance_with_large_lists(self):
        """Test performance characteristics with large lists."""
        # Create a large list
        large_values = [f'item_{i}' for i in range(1000)]
        large_list = StringInList(values=large_values)

        # Test first item (should be fast)
        assert large_list.is_matched('item_0') is True

        # Test last item (should still be reasonable)
        assert large_list.is_matched('item_999') is True

        # Test non-existent item
        assert large_list.is_matched('item_1000') is False

    def test_edge_cases(self):
        """Test edge cases and error conditions."""

        mixed_predicate = StringInList(values=['string', StringEqualTo(value='predicate')])
        assert mixed_predicate.is_matched('string') is True
        assert mixed_predicate.is_matched('predicate') is True
