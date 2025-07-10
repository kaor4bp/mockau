import pytest

from core.deprecated_matchers.variable_matcher import SetVariableMatcher
from schemas.variables import VariablesContext, VariablesGroup


class TestVariableMatcher:
    # HTML source: https://en.wikipedia.org/wiki/Apollo_11
    HTML_EXAMPLE = '''
        <p>The <a href="/wiki/Capsule_communicator" class="mw-redirect" title="Capsule communicator">capsule communicator</a>
        (CAPCOM) was an astronaut at the <a href="/wiki/Christopher_C._Kraft_Jr._Mission_Control_Center"
                                            title="Christopher C. Kraft Jr. Mission Control Center">Mission Control
            Center</a> in <a href="/wiki/Houston" title="Houston">Houston</a>, Texas, who was the only person who
        communicated directly with the flight crew.<sup id="cite_ref-FOOTNOTEKranz200027_63-0" class="reference"><a
                href="#cite_note-FOOTNOTEKranz200027-63"><span class="cite-bracket">[</span>62<span
                class="cite-bracket">]</span></a></sup> For Apollo 11, the CAPCOMs were: <a href="/wiki/Charles_Duke"
                                                                                            title="Charles Duke">Charles
            Duke</a>, Ronald Evans, <a href="/wiki/Bruce_McCandless_II" title="Bruce McCandless II">Bruce McCandless II</a>,
        James Lovell, William Anders, Ken Mattingly, Fred Haise, <a href="/wiki/Don_L._Lind" class="mw-redirect"
                                                                    title="Don L. Lind">Don L. Lind</a>, <a
                href="/wiki/Owen_K._Garriott" class="mw-redirect" title="Owen K. Garriott">Owen K. Garriott</a> and <a
                href="/wiki/Harrison_Schmitt" title="Harrison Schmitt">Harrison Schmitt</a>.<sup
                id="cite_ref-FOOTNOTEBrooksGrimwoodSwenson1979375_62-1" class="reference"><a
                href="#cite_note-FOOTNOTEBrooksGrimwoodSwenson1979375-62"><span class="cite-bracket">[</span>61<span
                class="cite-bracket">]</span></a></sup>
        </p>
        <div class="mw-heading mw-heading3"><h3 id="Flight_directors">Flight directors</h3></div>
        <p>The <a href="/wiki/Flight_controller#FLIGHT" title="Flight controller">flight directors</a> for this mission
            were:<sup id="cite_ref-FOOTNOTEOrloff2000272_64-0" class="reference"><a
                    href="#cite_note-FOOTNOTEOrloff2000272-64"><span class="cite-bracket">[</span>63<span
                    class="cite-bracket">]</span></a></sup><sup id="cite_ref-FOOTNOTEKranz2000230,_236,_273,_320_65-0"
                                                                class="reference"><a
                    href="#cite_note-FOOTNOTEKranz2000230,_236,_273,_320-65"><span class="cite-bracket">[</span>64<span
                    class="cite-bracket">]</span></a></sup><sup id="cite_ref-NASA-SP4223_66-0" class="reference"><a
                    href="#cite_note-NASA-SP4223-66"><span class="cite-bracket">[</span>65<span
                    class="cite-bracket">]</span></a></sup><sup id="cite_ref-Murray-Cox_67-0" class="reference"><a
                    href="#cite_note-Murray-Cox-67"><span class="cite-bracket">[</span>66<span class="cite-bracket">]</span></a></sup><sup
                    id="cite_ref-A11FJ-4-4_68-0" class="reference"><a href="#cite_note-A11FJ-4-4-68"><span class="cite-bracket">[</span>67<span
                    class="cite-bracket">]</span></a></sup><sup id="cite_ref-A11FJ-3-1_69-0" class="reference"><a
                    href="#cite_note-A11FJ-3-1-69"><span class="cite-bracket">[</span>68<span class="cite-bracket">]</span></a></sup>
        </p>
    '''

    @pytest.mark.parametrize(
        argnames=['pattern', 'value', 'expected_result'],
        argvalues=[
            ['/some/path/${variable_1}', '/some/path/hello', {'${variable_1}': 'hello'}],
            ['/some/path/${variable_1}/.+', '/some/path/hello/world', {'${variable_1}': 'hello'}],
            ['/some/path/${variable_1}/and/${variable_1}/', '/some/path/hello/and/hello/', {'${variable_1}': 'hello'}],
            ['/some/path/${variable_1}/.+', '/some/path/hello/world?hello=[..]+', {'${variable_1}': 'hello'}],
            ['/some/path/.+', '/some/path/hello', {}],
        ],
        ids=[
            'one_variable',
            'one_variable_with_extra_regex',
            'one_repeated_variable',
            'unsafe_regex_chars_in_value',
            'no_variables',
        ],
    )
    def test_is_matched(self, pattern, value, expected_result):
        pattern_matcher = SetVariableMatcher(set_variable=pattern)
        context = VariablesContext(variables_group=VariablesGroup(variables=[]))
        assert pattern_matcher.is_matched(value, context=context)
        assert context.variables == expected_result

    @pytest.mark.parametrize(
        argnames=['pattern', 'value'],
        argvalues=[
            [
                '/some/path/${variable_1}',
                '/some/another/path/hello',
            ]
        ],
        ids=[
            'value_is_not_matched',
        ],
    )
    def test_is_not_matched_if_value_does_not_match_to_template(self, pattern, value):
        pattern_matcher = SetVariableMatcher(set_variable=pattern)
        context = VariablesContext(variables_group=VariablesGroup(variables=[]))
        assert not pattern_matcher.is_matched(value, context=context)
        assert context.variables == {}

    def test_is_matched_with_unoptimized_pattern(self):
        pattern_matcher = SetVariableMatcher(
            set_variable='[\r\n\s\S]*<h3 id="Flight_directors">${variable_1}</h3>[\r\n\s\S]*'
        )
        context = VariablesContext(variables_group=VariablesGroup(variables=[]))
        assert pattern_matcher.is_matched(self.HTML_EXAMPLE, context=context)
        assert context.variables == {'${variable_1}': 'Flight directors'}
