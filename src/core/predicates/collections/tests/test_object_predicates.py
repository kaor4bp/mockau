"""
Manually written tests for object predicates, modified by Gemini 2.5 Flash (added extra cases and fixed cases naming)
"""

import json
import pathlib

import pytest

from core.predicates.collections.array_predicates import ArrayContains
from core.predicates.collections.nested_predicates import NestedObjectContainsSubset, NestedObjectEqualTo
from core.predicates.collections.object_predicates import ObjectContainsSubset, ObjectEqualTo, ObjectHasValue
from core.predicates.logical.logical_predicates import AndPredicate, NotPredicate, OrPredicate
from core.predicates.scalars import (
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    StringContains,
    StringEqualTo,
    StringPattern,
)
from utils.formatters import get_params_argv

CURRENT_DIR = pathlib.Path(__file__).parent.resolve()
BIG_JSON_REQUEST_1_FILE_PATH = CURRENT_DIR.joinpath('./big_json_request_1.json')

INCONSISTENTS = {
    'two_overlapping_string_key_predicates_in_object_equal_to': [
        ObjectEqualTo(
            value={
                StringEqualTo(value='rabbit'): IntegerGreaterThan(value=4),
                StringEqualTo(value='rabbit'): IntegerGreaterThan(value=1),
            }
        )
    ],
    'integer_less_than_and_greater_than_conflict': [
        ObjectEqualTo(value={'age': AndPredicate(predicates=[IntegerLessThan(value=10), IntegerGreaterThan(value=20)])})
    ],
    'string_contains_and_exact_not_matching_values': [
        ObjectEqualTo(
            value={'name': AndPredicate(predicates=[StringContains(value='curious'), StringEqualTo(value='mad')])}
        )
    ],
}

NOT_INTERSECTIONS = {
    'object_equal_to_and_superset': [
        ObjectEqualTo(value={'alice': 'rabbit'}),
        ObjectEqualTo(value={'alice': 'rabbit', 'hatter': 'wonderland'}),
    ],
    'object_equal_to_different_scalar_value_types': [
        ObjectEqualTo(value={'alice': 'rabbit'}),
        ObjectEqualTo(value={'alice': 2}),
    ],
    'object_contains_subset_different_scalar_value_types': [
        ObjectContainsSubset(value={'alice': 'rabbit'}),
        ObjectContainsSubset(value={'alice': 2}),
    ],
    'nested_object_key_predicate_conflict': [
        ObjectEqualTo(
            value={
                StringContains(value='abbit'): {'alice': 'rabbit'},
            }
        ),
        ObjectEqualTo(
            value={
                StringContains(value='rabbit'): ObjectEqualTo(value={'alice': StringContains(value='tarts')}),
            }
        ),
    ],
    'nested_strict_unstrict_predicate_value_conflict': [
        ObjectEqualTo(
            value={
                StringContains(value='abbit'): {'alice': 'rabbit'},
            }
        ),
        ObjectContainsSubset(
            value={
                StringContains(value='rabbit'): ObjectContainsSubset(
                    value={'alice': StringContains(value='rabbit'), 'queen': 2}
                ),
            }
        ),
    ],
    'deeply_nested_objects_conflicting_values': [
        ObjectContainsSubset(value={'tea_party': {'door': {'key': IntegerEqualTo(value=1)}}}),
        ObjectContainsSubset(value={'tea_party': {'door': {'key': IntegerEqualTo(value=2)}}}),
    ],
    'not_contains_subset_and_exact_object_equal_to': [
        NotPredicate(predicate=ObjectContainsSubset(value={'alice': 1})),
        ObjectEqualTo(value={'alice': 1}),
    ],
    'nested_object_equal_to_and_flat_object_equal_to_type_mismatch': [
        NestedObjectEqualTo(value={'card': 'queen'}),
        ObjectEqualTo(value={'card': 1}),
    ],
    'nested_object_equal_to_and_deep_object_equal_to_array_type_mismatch': [
        NestedObjectEqualTo(value={'card': 'queen'}),
        ObjectEqualTo(value={'card': [{'tea': {'hatter': 'mad'}}]}),
    ],
    'not_nested_object_equal_to_and_deep_object_equal_to_array_no_match_1': [
        NotPredicate(predicate=NestedObjectEqualTo(value={'card': 'queen'})),
        ObjectEqualTo(value={'card': [{'tea': {'hatter': 'mad', 'dormouse': {'card': 'queen'}}}]}),
    ],
    'not_nested_object_equal_to_and_deep_object_equal_to_array_no_match_2': [
        NotPredicate(predicate=NestedObjectEqualTo(value={'card': 'queen'})),
        ObjectEqualTo(value={'card': [{'tea': {'hatter': 'mad', 'dormouse': [{'card': 'queen'}]}}]}),
    ],
    'object_with_nested_subset_and_flat_nested_value_mismatch': [
        ObjectEqualTo(
            value={
                'alice': 'rabbit',
                'hatter': NestedObjectContainsSubset(value={'alice': 'rabbit'}),
            }
        ),
        ObjectEqualTo(value={'alice': 'rabbit', 'hatter': {'alice': 123}}),
    ],
    'nested_subset_and_unrelated_object': [
        NestedObjectContainsSubset(value={'alice': 'rabbit'}),
        ObjectEqualTo(value={'queen': 'cards'}),
    ],
    'non_overlapping_integer_ranges': [
        ObjectEqualTo(value={'value': IntegerLessThan(value=5)}),
        ObjectEqualTo(value={'value': IntegerGreaterThan(value=10)}),
    ],
    'different_string_exact_matches': [
        ObjectEqualTo(value={'item': StringEqualTo(value='rose')}),
        ObjectEqualTo(value={'item': StringEqualTo(value='card')}),
    ],
    'object_equal_to_with_different_keys': [
        ObjectEqualTo(value={'key_rabbit': 'tea_time'}),
        ObjectEqualTo(value={'key_hatter': 'mad_tea'}),
    ],
}

INTERSECTIONS = {
    # 'complex_object_contains_subset_with_big_json_exact': [
    #     ObjectContainsSubset(
    #         value={
    #             'options': ObjectContainsSubset(value={'label_format': StringEqualTo(value='PDF')}),
    #             'from_address': ObjectContainsSubset(
    #                 value={
    #                     'name': OrPredicate(
    #                         predicates=[StringContains(value='Bernadette'), StringContains(value='Maria')]
    #                     ),
    #                     'city': 'Pasadena',
    #                 }
    #             ),
    #             'rates': ArrayContains(
    #                 value=[
    #                     ObjectContainsSubset(value={'carrier': 'USPS', 'service': 'Priority'}),
    #                 ]
    #             ),
    #             'object': 'Shipment',
    #         }
    #     ),
    #     ObjectEqualTo(value=json.loads(BIG_JSON_REQUEST_1_FILE_PATH.read_text())),
    # ],
    'two_exact_object_equal_to': [ObjectEqualTo(value={'alice': 'rabbit'}), ObjectEqualTo(value={'alice': 'rabbit'})],
    'object_contains_subset_and_exact_object_equal_to': [
        ObjectContainsSubset(value={'alice': 'rabbit'}),
        ObjectEqualTo(value={'alice': 'rabbit'}),
    ],
    'object_contains_subset_and_superset_exact_object_equal_to': [
        ObjectContainsSubset(value={'alice': 'rabbit'}),
        ObjectEqualTo(value={'alice': 'rabbit', 'hatter': 'wonderland'}),
    ],
    'two_object_contains_subset_with_common_part': [
        ObjectContainsSubset(value={'alice': 'rabbit'}),
        ObjectContainsSubset(value={'alice': 'rabbit'}),
    ],
    'superset_object_contains_subset_and_subset_object_contains_subset': [
        ObjectContainsSubset(value={'alice': 'rabbit', 'hatter': 'wonderland'}),
        ObjectContainsSubset(value={'alice': 'rabbit'}),
    ],
    'nested_object_key_predicate_overlap': [
        ObjectEqualTo(
            value={
                StringContains(value='abbit'): {'alice': 'rabbit'},
            }
        ),
        ObjectEqualTo(
            value={
                StringContains(value='rabbit'): ObjectEqualTo(value={'alice': StringContains(value='rabbit')}),
            }
        ),
    ],
    'integer_greater_than_overlapping_ranges': [
        ObjectEqualTo(
            value={
                'rabbit': IntegerGreaterThan(value=4),
            }
        ),
        ObjectEqualTo(
            value={
                'rabbit': IntegerGreaterThan(value=24),
            }
        ),
    ],
    'concurrent_string_key_predicate_overlap_1': [
        ObjectEqualTo(
            value={
                StringContains(value='atter'): IntegerGreaterThan(value=4),
                StringContains(value='hat'): IntegerGreaterThan(value=1),
            }
        ),
        ObjectEqualTo(
            value={
                'hatter': IntegerGreaterThan(value=24),
                'hatter_tea': IntegerLessThan(value=3),
            }
        ),
    ],
    'concurrent_string_key_predicate_overlap_2': [
        ObjectEqualTo(
            value={
                StringContains(value='hat'): IntegerGreaterThan(value=1),
                StringContains(value='atter'): IntegerGreaterThan(value=4),
            }
        ),
        ObjectEqualTo(
            value={
                'hatter': IntegerGreaterThan(value=24),
                'hatter_tea': IntegerLessThan(value=3),
            }
        ),
    ],
    'same_string_key_predicate_content_overlap': [
        ObjectEqualTo(
            value={
                StringContains(value='atter'): IntegerGreaterThan(value=4),
                StringContains(value='atter'): IntegerGreaterThan(value=1),
            }
        ),
        ObjectEqualTo(
            value={
                'hatter': IntegerGreaterThan(value=24),
                'hatter_tea': IntegerLessThan(value=3),
            }
        ),
    ],
    'and_predicate_and_exact_object_equal_to_value': [
        AndPredicate(
            predicates=[
                ObjectEqualTo(value={'alice': StringContains(value='wonder')}),
                ObjectEqualTo(value={'alice': StringContains(value='land')}),
            ]
        ),
        ObjectEqualTo(value={'alice': 'wonderland'}),
    ],
    'not_predicate_and_unrelated_object': [
        NotPredicate(predicate=ObjectContainsSubset(value={'hatter': StringContains(value='tea')})),
        ObjectEqualTo(value={'queen': StringContains(value='red_paint')}),
    ],
    'object_and_not_predicate': [
        ObjectContainsSubset(value={'hatter': StringContains(value='tea')}),
        NotPredicate(predicate=ObjectEqualTo(value={'queen': StringContains(value='red_paint')})),
    ],
    'deeply_nested_object_equal_to': [
        NestedObjectEqualTo(value={'tea_cup': NestedObjectEqualTo(value={'tarts': 'stolen'})}),
        ObjectEqualTo(
            value={
                'wonderland': {
                    'garden': [
                        {'rose': 'white'},
                        {'tea_cup': {'madness': [{'tarts': 'stolen'}]}},
                    ]
                }
            }
        ),
    ],
    'nested_object_equal_to_with_nested_object_equal_to': [
        ObjectEqualTo(value={'tea_cup': NestedObjectEqualTo(value={'tarts': 'stolen'})}),
        NestedObjectEqualTo(
            value={
                'wonderland': {
                    'garden': [
                        {'rose': 'white'},
                        {'tea_cup': {'madness': [{'tarts': 'stolen'}]}},
                    ]
                }
            }
        ),
    ],
    'nested_object_equal_to_and_nested_object_contains_subset_overlap': [
        NestedObjectEqualTo(value={'alice': 'rabbit', 'queen': 'cards'}),
        NestedObjectContainsSubset(value={'alice': 'rabbit'}),
    ],
    'nested_object_equal_to_and_or_predicate_overlap': [
        NestedObjectEqualTo(value={'alice': 'rabbit', 'queen': 'cards'}),
        OrPredicate(
            predicates=[NestedObjectEqualTo(value={'hatter': 'mad'}), ObjectEqualTo(value={'gryphon': 'mock_turtle'})]
        ),
    ],
    'not_nested_object_equal_to_and_deep_object_with_extra_field': [
        NotPredicate(predicate=NestedObjectEqualTo(value={'alice': 'rabbit'})),
        ObjectEqualTo(value={'alice': {'alice': 'rabbit', 'extra_tea': True}}),
    ],
    'not_nested_object_equal_to_and_deep_object_with_array_and_extra_field': [
        NotPredicate(predicate=NestedObjectEqualTo(value={'alice': 'rabbit'})),
        ObjectEqualTo(
            value={'alice': [{'hatter': {'queen': 'cards', 'tea_time': [{'alice': 'rabbit', 'extra_tea': True}]}}]}
        ),
    ],
    'not_object_equal_to_and_different_structure': [
        NotPredicate(predicate=ObjectEqualTo(value={'alice': 'rabbit'})),
        ObjectEqualTo(value={'alice': {'queen': 'cards'}}),
    ],
    'object_with_nested_not_subset_and_flat_nested_value': [
        ObjectEqualTo(
            value={
                'alice': 'rabbit',
                'hatter': NotPredicate(predicate=NestedObjectContainsSubset(value={'alice': 'rabbit'})),
            }
        ),
        ObjectEqualTo(value={'alice': 'rabbit', 'hatter': {'alice': 'flamingo'}}),
    ],
    'overlapping_integer_ranges': [
        ObjectEqualTo(value={'value': IntegerGreaterThan(value=5)}),
        ObjectEqualTo(value={'value': IntegerLessThan(value=15)}),
    ],
    'string_contains_and_string_pattern_overlap': [
        ObjectEqualTo(value={'text': StringContains(value='wonder')}),
        ObjectEqualTo(value={'text': StringPattern(pattern='^w.*d$')}),
    ],
    'nested_object_contains_subset_partial_overlap': [
        ObjectContainsSubset(value={'data': ObjectContainsSubset(value={'id': 10})}),
        ObjectContainsSubset(value={'data': ObjectContainsSubset(value={'name': 'cheshire'})}),
    ],
}

EQUIVALENTS = {
    'two_exact_object_equal_to': [ObjectEqualTo(value={'alice': 'rabbit'}), ObjectEqualTo(value={'alice': 'rabbit'})],
    'string_contains_and_pattern': [
        ObjectEqualTo(value={'alice': StringContains(value='hatter')}),
        ObjectEqualTo(value={'alice': StringPattern(pattern='.*hatter.*')}),
    ],
    'integer_equal_to_and_not_greater_or_less': [
        ObjectEqualTo(value={'alice': IntegerEqualTo(value=1)}),
        AndPredicate(
            predicates=[
                ObjectEqualTo(value={'alice': NotPredicate(predicate=IntegerGreaterThan(value=1))}),
                ObjectEqualTo(value={'alice': NotPredicate(predicate=IntegerLessThan(value=1))}),
            ]
        ),
    ],
    'integer_greater_or_equal_and_or_greater_or_equal': [
        ObjectEqualTo(value={'alice': IntegerGreaterOrEqualThan(value=1)}),
        OrPredicate(
            predicates=[
                ObjectEqualTo(value={'alice': IntegerGreaterThan(value=1)}),
                ObjectEqualTo(value={'alice': IntegerEqualTo(value=1)}),
            ]
        ),
    ],
    'nested_integer_greater_or_equal_and_or_greater_or_equal': [
        ObjectEqualTo(value={'alice': {'hatter': IntegerGreaterOrEqualThan(value=1)}}),
        OrPredicate(
            predicates=[
                ObjectEqualTo(value={'alice': {'hatter': IntegerGreaterThan(value=1)}}),
                ObjectEqualTo(value={'alice': {'hatter': IntegerEqualTo(value=1)}}),
            ]
        ),
    ],
    'object_equal_to_keys_order': [
        ObjectEqualTo(value={'alice': 'rabbit', 'hatter': 'wonderland'}),
        ObjectEqualTo(value={'hatter': 'wonderland', 'alice': 'rabbit'}),
    ],
    'range_inequalities_and_not_equal_boundaries': [
        AndPredicate(
            predicates=[
                ObjectEqualTo(value={'hatter': IntegerGreaterThan(value=1)}),
                ObjectEqualTo(value={'hatter': IntegerLessThan(value=5)}),
            ]
        ),
        AndPredicate(
            predicates=[
                ObjectEqualTo(value={'hatter': IntegerGreaterOrEqualThan(value=1)}),
                ObjectEqualTo(value={'hatter': IntegerLessOrEqualThan(value=5)}),
                ObjectEqualTo(value={'hatter': NotPredicate(predicate=IntegerEqualTo(value=1))}),
                ObjectEqualTo(value={'hatter': NotPredicate(predicate=IntegerEqualTo(value=5))}),
            ]
        ),
    ],
    'not_not_predicate_equivalent_to_original': [
        NotPredicate(predicate=NotPredicate(predicate=ObjectEqualTo(value={'alice_door': 1}))),
        ObjectEqualTo(value={'alice_door': 1}),
    ],
    'or_with_same_predicate_equivalent_to_predicate': [
        OrPredicate(predicates=[ObjectEqualTo(value={'rabbit_hole': 2}), ObjectEqualTo(value={'rabbit_hole': 2})]),
        ObjectEqualTo(value={'rabbit_hole': 2}),
    ],
    'and_with_same_predicate_equivalent_to_predicate': [
        AndPredicate(predicates=[ObjectEqualTo(value={'queen_cards': 3}), ObjectEqualTo(value={'queen_cards': 3})]),
        ObjectEqualTo(value={'queen_cards': 3}),
    ],
}

SUPERSETS = {
    'object_contains_subset_and_superset_with_extra_key': [
        ObjectContainsSubset(value={'alice': 'rabbit'}),
        ObjectContainsSubset(value={'alice': 'rabbit', 'hatter': 'wonderland'}),
    ],
    'object_contains_subset_and_exact_object_equal_to': [
        ObjectContainsSubset(value={'alice': 'rabbit'}),
        ObjectEqualTo(value={'alice': 'rabbit'}),
    ],
    'string_contains_and_exact_string': [
        ObjectEqualTo(value={'alice': StringContains(value='rabbit')}),
        ObjectEqualTo(value={'alice': 'rabbit'}),
    ],
    'integer_greater_than_and_stricter_greater_than': [
        ObjectContainsSubset(value={'alice': IntegerGreaterThan(value=1)}),
        ObjectContainsSubset(value={'alice': IntegerGreaterThan(value=2)}),
    ],
    'integer_equal_to_and_stricter_integer_equal_to': [
        ObjectEqualTo(value={'alice': IntegerGreaterThan(value=1)}),
        ObjectEqualTo(value={'alice': IntegerGreaterThan(value=2)}),
    ],
    'nested_integer_and_stricter_equal_to': [
        ObjectEqualTo(value={'alice': {'rabbit': IntegerGreaterThan(value=1)}}),
        ObjectEqualTo(value={'alice': {'rabbit': IntegerGreaterThan(value=2)}}),
    ],
    'nested_contains_subset_and_stricter_equal_to': [
        ObjectContainsSubset(value={'alice': {'rabbit': IntegerGreaterThan(value=1)}}),
        ObjectEqualTo(value={'alice': {'rabbit': IntegerGreaterThan(value=2)}}),
    ],
    'object_contains_subset_and_stricter_equal_to': [
        ObjectContainsSubset(value={'alice': IntegerGreaterThan(value=1)}),
        ObjectEqualTo(value={'alice': IntegerGreaterThan(value=2)}),
    ],
    'object_equal_to_and_exact_match_with_string_contains': [
        ObjectEqualTo(value={'alice': 'rabbit', 'hatter': StringContains(value='wonderland')}),
        ObjectEqualTo(value={'hatter': 'wonderland', 'alice': 'rabbit'}),
    ],
    'object_contains_subset_and_exact_integer_match': [
        ObjectContainsSubset(value={'tea_cup': IntegerGreaterThan(value=0)}),
        ObjectContainsSubset(value={'tea_cup': IntegerEqualTo(value=1), 'dormouse': IntegerEqualTo(value=2)}),
    ],
    'object_has_value_and_object_contains_subset': [
        ObjectHasValue(predicate=IntegerGreaterThan(value=0)),
        ObjectContainsSubset(value={'tea_cup': IntegerGreaterThan(value=0), 'hatter': 'wonderland'}),
    ],
    'nested_object_equal_to_and_deeply_nested_object': [
        NestedObjectEqualTo(value={'hatter': 'wonderland'}),
        ObjectEqualTo(value={'alice': {'hatter': 'wonderland'}}),
    ],
    'nested_object_equal_to_and_exact_object_equal_to': [
        NestedObjectEqualTo(value={'hatter': 'wonderland'}),
        ObjectEqualTo(value={'hatter': 'wonderland'}),
    ],
    'nested_object_contains_subset_and_exact_object_equal_to': [
        NestedObjectContainsSubset(value={'hatter': 'wonderland'}),
        ObjectEqualTo(value={'hatter': 'wonderland'}),
    ],
    'nested_object_contains_subset_and_or_predicate': [
        NestedObjectContainsSubset(value={'hatter': 'wonderland'}),
        OrPredicate(
            predicates=[
                ObjectEqualTo(value={'alice': {'hatter': 'wonderland'}}),
                ObjectEqualTo(value={'hatter': 'wonderland'}),
            ]
        ),
    ],
    'nested_object_contains_subset_and_another_nested_object': [
        NestedObjectContainsSubset(value={'madness': 'curiosity'}),
        ObjectEqualTo(value={'tea_party': {'madness': 'curiosity'}}),
    ],
    'object_equal_to_with_nested_subset_and_concrete_nested_value': [
        ObjectEqualTo(
            value={'alice_door': NestedObjectContainsSubset(value={'madness': 'curiosity'}), 'rabbit_watch': 'late'}
        ),
        ObjectEqualTo(value={'alice_door': {'wonder_garden': {'madness': 'curiosity'}}, 'rabbit_watch': 'late'}),
    ],
    'object_equal_to_with_nested_equal_to_and_concrete_nested_value': [
        ObjectEqualTo(
            value={'alice_door': NestedObjectEqualTo(value={'madness': 'curiosity'}), 'rabbit_watch': 'late'}
        ),
        ObjectEqualTo(value={'alice_door': {'wonder_garden': {'madness': 'curiosity'}}, 'rabbit_watch': 'late'}),
    ],
    'object_equal_to_with_nested_string_contains_and_concrete_string': [
        ObjectEqualTo(
            value={
                'alice_door': NestedObjectEqualTo(value={'madness': StringContains(value='DrinkMe')}),
                'rabbit_watch': 'late',
            }
        ),
        ObjectEqualTo(value={'alice_door': {'wonder_garden': {'madness': 'DrinkMe potion!'}}, 'rabbit_watch': 'late'}),
    ],
    'object_equal_to_with_nested_none_and_concrete_none_value': [
        ObjectEqualTo(value={'alice_door': NestedObjectEqualTo(value={'madness': None}), 'rabbit_watch': 'late'}),
        ObjectEqualTo(value={'alice_door': {'wonder_garden': {'madness': None}}, 'rabbit_watch': 'late'}),
    ],
    'integer_range_superset': [
        ObjectEqualTo(value={'time': IntegerGreaterOrEqualThan(value=0)}),
        ObjectEqualTo(value={'time': IntegerGreaterOrEqualThan(value=10)}),
    ],
    'string_pattern_superset': [
        ObjectEqualTo(value={'creature': StringPattern(pattern='.*')}),  # Matches any string
        ObjectEqualTo(value={'creature': StringContains(value='Gryphon')}),
    ],
    'object_contains_subset_over_object_equal_to': [
        ObjectContainsSubset(value={'key': 'value'}),
        ObjectEqualTo(value={'key': 'value', 'extra_key': 'extra_value'}),
    ],
}

MATCHED = {
    'simple_object_exact': [ObjectEqualTo(value={'alice': 'rabbit'}), {'alice': 'rabbit'}],
    'nested_object_exact': [
        ObjectEqualTo(
            value={
                'hatter': {'alice': 'rabbit'},
            }
        ),
        {'hatter': {'alice': 'rabbit'}},
    ],
    'scalar_predicates_matching': [
        ObjectEqualTo(value={'key_tea': StringContains(value='party'), 'key_time': IntegerGreaterThan(value=10)}),
        {'key_tea': 'tea party', 'key_time': 15},
    ],
    'nested_predicates_matching': [
        ObjectEqualTo(
            value={'key_card': ObjectEqualTo(value={'rank': 'queen'}), 'key_num': IntegerGreaterThan(value=10)}
        ),
        {'key_card': {'rank': 'queen'}, 'key_num': 15},
    ],
    'subset_predicate_with_extra_keys_in_value': [
        ObjectContainsSubset(value={'creature': 'cheshire'}),
        {'creature': 'cheshire', 'disposition': 'grinning'},
    ],
    'nested_subset_predicate_with_extra_keys_in_value': [
        ObjectContainsSubset(value={'wonderland': ObjectContainsSubset(value={'location': 'garden'})}),
        {'wonderland': {'location': 'garden', 'flora': 'roses'}, 'inhabitants': 'cards'},
    ],
    'and_predicate_all_conditions': [
        AndPredicate(
            predicates=[ObjectContainsSubset(value={'tea': 'hot'}), ObjectContainsSubset(value={'time': 'late'})]
        ),
        {'tea': 'hot', 'time': 'late', 'guest': 'dormouse'},
    ],
    'or_predicate_one_condition': [
        OrPredicate(predicates=[ObjectEqualTo(value={'item': 'foul'}), ObjectEqualTo(value={'item': 'fair'})]),
        {'item': 'fair'},
    ],
    'big_json_request_1_with_object_contains_subset': [
        ObjectContainsSubset(
            value={
                'options': ObjectContainsSubset(value={'label_format': StringEqualTo(value='PDF')}),
                'from_address': ObjectContainsSubset(
                    value={
                        'name': OrPredicate(
                            predicates=[StringContains(value='Bernadette'), StringContains(value='Maria')]
                        ),
                        'city': 'Pasadena',
                    }
                ),
                'rates': ArrayContains(
                    value=[
                        ObjectContainsSubset(value={'carrier': 'USPS', 'service': 'Priority'}),
                    ]
                ),
                'object': 'Shipment',
            }
        ),
        json.loads(BIG_JSON_REQUEST_1_FILE_PATH.read_text()),
    ],
    'big_json_request_1_with_nested_object_equal_to': [
        NestedObjectEqualTo(
            value={
                'label_format': StringEqualTo(value='pdf', ignore_case=True),
                'label_size': '4X6',
                'postage_label_inline': False,
                'currency': 'USD',
                'payment': ObjectEqualTo(value={'type': 'SENDER'}),
                'date_advance': IntegerGreaterOrEqualThan(value=0),
            }
        ),
        json.loads(BIG_JSON_REQUEST_1_FILE_PATH.read_text()),
    ],
    'big_json_request_1_with_nested_object_contains_subset': [
        NestedObjectContainsSubset(
            value={
                'payment': ObjectEqualTo(value={'type': 'SENDER'}),
                'date_advance': IntegerGreaterOrEqualThan(value=0),
            }
        ),
        json.loads(BIG_JSON_REQUEST_1_FILE_PATH.read_text()),
    ],
    'object_has_value_match': [
        ObjectHasValue(predicate=StringEqualTo(value='DrinkMe')),
        {'bottle': 'EatMe', 'label': 'DrinkMe'},
    ],
    'integer_range_match': [
        ObjectEqualTo(value={'height': IntegerLessOrEqualThan(value=30)}),
        {'height': 25},
    ],
    'array_contains_match': [
        ObjectEqualTo(value={'garden_items': ArrayContains(value=[StringEqualTo(value='croquet')])}),
        {'garden_items': ['rose', 'flamingo', 'croquet']},
    ],
}

NOT_MATCHED = {
    'simple_object_value_mismatch': [ObjectEqualTo(value={'alice': 'rabbit'}), {'alice': 'queen'}],
    'nested_object_value_mismatch': [
        ObjectEqualTo(
            value={
                'hatter': {'alice': 'rabbit'},
            }
        ),
        {'hatter': {'alice': 'mad_hatter'}},
    ],
    'scalar_predicate_value_out_of_range': [
        ObjectEqualTo(value={'key_dream': StringContains(value='land'), 'key_hours': IntegerGreaterThan(value=10)}),
        {'key_dream': 'wonderland', 'key_hours': 5},
    ],
    'nested_predicate_value_mismatch': [
        ObjectEqualTo(
            value={'key_queen': ObjectEqualTo(value={'ruling': 'cards'}), 'key_army': IntegerGreaterThan(value=10)}
        ),
        {'key_queen': {'ruling': 'roses'}, 'key_army': 15},
    ],
    'subset_predicate_missing_required_key': [
        ObjectContainsSubset(value={'tea_set': 'complete'}),
        {'cookies': 'crumbs', 'tarts': 'missing'},
    ],
    'nested_subset_predicate_missing_required_key': [
        ObjectContainsSubset(value={'tea_party': ObjectContainsSubset(value={'guests': 'hatter'})}),
        {'tea_party': {'drinks': 'tea'}, 'food': 'bread'},
    ],
    'and_predicate_not_all_conditions': [
        AndPredicate(
            predicates=[ObjectContainsSubset(value={'book': 'open'}), ObjectContainsSubset(value={'page': 'read'})]
        ),
        {'book': 'open', 'page': 'unopened'},
    ],
    'or_predicate_no_conditions': [
        OrPredicate(
            predicates=[ObjectEqualTo(value={'story': 'foul_ending'}), ObjectEqualTo(value={'story': 'foul_beginning'})]
        ),
        {'story': 'strange_plot'},
    ],
    'nested_object_equal_to_key_not_found': [
        NestedObjectEqualTo(value={'door': 'closed'}),
        {'garden': {'path': 'winding'}},
    ],
    'object_has_value_no_match': [
        ObjectHasValue(predicate=IntegerEqualTo(value=100)),
        {'key_time': 10, 'key_riddle': 20},
    ],
    'array_contains_no_match': [
        ArrayContains(value=[StringEqualTo(value='griffin')]),
        ['flamingo', 'hedgehog', 'cards'],
    ],
    'string_exact_match_case_mismatch': [
        StringEqualTo(value='Cheshire'),
        'cheshire',
    ],
    'integer_range_no_match': [
        ObjectEqualTo(value={'temp': IntegerGreaterThan(value=30)}),
        {'temp': 25},
    ],
}


class TestObjectIsNotIntersectedWith:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_not_intersected(self, p1, p2):
        assert not p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_symmetrical_not_intersected(self, p1, p2):
        assert not p2.is_intersected_with(p1)


class TestObjectIsSubsetOf:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_one_equivalent_is_subset_of_another(self, p1, p2):
        assert p1.is_subset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_subset_is_subset_of_superset(self, p1, p2):
        assert p2.is_subset_of(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_superset_is_not_subset_of_subset(self, p1, p2):
        assert not p1.is_subset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_subset_of_equivalents_is_symmetric(self, p1, p2):
        assert p2.is_subset_of(p1)


class TestObjectIsSupersetOf:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_superset_is_superset_of_subset(self, p1, p2):
        assert p1.is_superset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_subset_is_not_superset_of_superset(self, p1, p2):
        assert not p2.is_superset_of(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_one_equivalent_is_superset_of_another(self, p1, p2):
        assert p1.is_superset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_superset_of_equivalents_is_symmetric(self, p1, p2):
        assert p2.is_superset_of(p1)


class TestObjectIsIntersectedWith:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_is_consistent(self, p1, p2):
        assert p1.is_consistent()
        assert p2.is_consistent()

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_intersections_are_intersected(self, p1, p2):
        assert p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_intersections_are_symmetrical_intersected(self, p1, p2):
        assert p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_intersected(self, p1, p2):
        assert p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_symmetrically_intersected(self, p1, p2):
        assert p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_superset_and_subset_are_intersected(self, p1, p2):
        assert p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_subset_and_superset_are_symmetrically_intersectable(self, p1, p2):
        assert p1.is_intersected_with(p2)


class TestObjectIsMatched:
    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(MATCHED))
    def test_is_consistent(self, predicate, value):
        assert predicate.is_consistent()

    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(MATCHED))
    def test_matched_values_are_matched(self, predicate, value):
        assert predicate.is_matched(value)

    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(NOT_MATCHED))
    def test_not_matched_values_are_not_matched(self, predicate, value):
        assert not predicate.is_matched(value)


class TestObjectInconsistency:
    @pytest.mark.parametrize(['predicate'], **get_params_argv(INCONSISTENTS))
    def test_is_consistent_is_false(self, predicate):
        assert not predicate.is_consistent()
