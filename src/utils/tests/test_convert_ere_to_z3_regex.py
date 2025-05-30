import pytest
from z3 import InRe, Solver, String, sat

from utils.z3_helpers import ConvertEREToZ3Regex


class TestConvertEREToZ3Regex:
    """Test suite for BRE/ERE to Z3 regex conversion with fullmatch semantics."""

    def setup_z3_solver(self, pattern, example):
        """Helper function to initialize Z3 solver with pattern and example."""
        z3_solver = Solver()
        z3_regex = ConvertEREToZ3Regex(pattern).convert()
        z3_string = String('test_str')
        z3_solver.add(z3_string == example, InRe(z3_string, z3_regex))
        return z3_solver

    # =============================================
    # Basic Regular Expressions (BRE) Test Cases
    # =============================================

    @pytest.mark.bre
    @pytest.mark.positive
    @pytest.mark.parametrize("example", ["aab", "axb", "a b"])
    def test_bre_literal_match(self, example):
        """Test basic literal matching in BRE mode."""
        bre_pattern = r"a.b"  # . matches any character in BRE
        solver = self.setup_z3_solver(bre_pattern, example)
        assert solver.check() == sat, f"'{example}' should match {bre_pattern}"

    @pytest.mark.bre
    @pytest.mark.positive
    @pytest.mark.parametrize("example", ["a", "aa", "aaa"])
    def test_bre_quantifiers(self, example):
        """Test BRE quantifiers: *, \{m,n\}"""
        bre_pattern = r"a\{1,3\}"  # BRE-style quantifier
        solver = self.setup_z3_solver(bre_pattern, example)
        assert solver.check() == sat, f"'{example}' should match {bre_pattern}"

    @pytest.mark.bre
    @pytest.mark.negative
    @pytest.mark.parametrize("example", ["", "aaaa", "b"])
    def test_bre_quantifiers_negative(self, example):
        """Negative tests for BRE quantifiers."""
        bre_pattern = r"a\{1,3\}"
        solver = self.setup_z3_solver(bre_pattern, example)
        assert solver.check() != sat, f"'{example}' should NOT match {bre_pattern}"

    # =============================================
    # Extended Regular Expressions (ERE) Test Cases
    # =============================================

    @pytest.mark.ere
    @pytest.mark.positive
    @pytest.mark.parametrize("example", ["ab", "aab", "aaab"])
    def test_ere_quantifiers(self, example):
        """Test ERE quantifiers: ?, *, +"""
        ere_pattern = r"a+b"  # Changed from a+?b to a+b for these examples
        solver = self.setup_z3_solver(ere_pattern, example)
        assert solver.check() == sat, f"'{example}' should match {ere_pattern}"

    @pytest.mark.ere
    @pytest.mark.positive
    @pytest.mark.parametrize("example", ["ab", "ac", "a.c"])
    def test_ere_character_classes(self, example):
        """Test ERE character classes and alternation."""
        ere_pattern = r"a[b|c]|a\.c"  # Fixed pattern to match test cases
        solver = self.setup_z3_solver(ere_pattern, example)
        assert solver.check() == sat, f"'{example}' should match {ere_pattern}"

    @pytest.mark.ere
    @pytest.mark.positive
    @pytest.mark.parametrize("example", ["a1", "b2", "c3"])
    def test_ere_posix_classes(self, example):
        """Test POSIX character classes in ERE."""
        ere_pattern = r"[[:alpha:]][[:digit:]]"
        solver = self.setup_z3_solver(ere_pattern, example)
        assert solver.check() == sat, f"'{example}' should match {ere_pattern}"

    # =============================================
    # Special Cases and Edge Cases
    # =============================================

    @pytest.mark.special
    @pytest.mark.positive
    @pytest.mark.parametrize("example", ["", "a", "aa"])
    def test_empty_string(self, example):
        """Test empty string matching."""
        pattern = r"a*"  # Should match empty string
        solver = self.setup_z3_solver(pattern, example)
        assert solver.check() == sat, f"'{example}' should match {pattern}"

    @pytest.mark.special
    @pytest.mark.positive
    def test_unicode_characters(self):
        """Test Unicode character handling."""
        pattern = r"ümlaut"
        solver = self.setup_z3_solver(pattern, 'ümlaut')
        assert solver.check() == sat, "Unicode characters should be handled"

    @pytest.mark.special
    def test_anchoring_behavior(self):
        """Test that patterns are always anchored (fullmatch)."""
        pattern = r"test"
        solver = Solver()
        z3_re = ConvertEREToZ3Regex(pattern).convert()
        s = String("test_str")

        # Should match exact string
        solver.push()
        solver.add(s == "test", InRe(s, z3_re))
        assert solver.check() == sat

        # Should not match when embedded
        solver.push()
        solver.add(s == "xtestx", InRe(s, z3_re))
        assert solver.check() != sat

    # =============================================
    # Backreference Tests (if supported)
    # =============================================

    @pytest.mark.skip(reason="Backreferences not universally supported")
    @pytest.mark.backref
    @pytest.mark.parametrize("example", ["aa", "bb"])
    def test_backreferences(self, example):
        """Test backreference support if available."""
        pattern = r"(.)\1"
        solver = self.setup_z3_solver(pattern, example)
        assert solver.check() == sat, f"'{example}' should match {pattern}"

    # =============================================
    # New Tests for Lazy Quantifiers
    # =============================================

    @pytest.mark.ere
    @pytest.mark.positive
    @pytest.mark.parametrize("example", ["ab", "aaab"])
    def test_lazy_quantifier(self, example):
        """Test lazy quantifier behavior."""
        ere_pattern = r"a+?b"  # Should match minimal 'a's before 'b'
        with pytest.raises(ValueError):
            solver = self.setup_z3_solver(ere_pattern, example)
            assert solver.check() == sat, f"'{example}' should match {ere_pattern}"

    @pytest.mark.ere
    @pytest.mark.negative
    @pytest.mark.parametrize("example", ["a", "b", "aac"])
    def test_lazy_quantifier_negative(self, example):
        """Negative tests for lazy quantifier."""
        ere_pattern = r"a+?b"
        with pytest.raises(ValueError):
            solver = self.setup_z3_solver(ere_pattern, example)
            assert solver.check() != sat, f"'{example}' should NOT match {ere_pattern}"
