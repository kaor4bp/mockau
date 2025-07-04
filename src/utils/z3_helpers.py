import z3


def string_to_case_insensitive_z3_regex(z3_context: z3.Context, text: str):
    expressions = []
    for c in text:
        expressions.append(
            z3.Union(z3.Re(z3.StringVal(c.lower(), ctx=z3_context)), z3.Re(z3.StringVal(c.upper(), ctx=z3_context)))
        )
    return z3.simplify(z3.Concat(*expressions))


class ConvertEREToZ3Regex:
    def __init__(self, z3_context: z3.Context, ere_pattern: str, is_case_sensitive=True):
        self.ere_pattern = ere_pattern.removeprefix('^').removesuffix('$')
        self.is_case_sensitive = is_case_sensitive
        self.any_char = z3.AllChar(z3.ReSort(z3.StringSort(ctx=z3_context)))
        self._z3_context = z3_context

    def handle_posix_character_groups(self, pattern: str):
        posix_mapping = {
            '[:alnum:]': '[A-Za-z0-9]',
            '[:alpha:]': '[A-Za-z]',
            '[:blank:]': '[ \t]',
            '[:cntrl:]': '[\x00-\x1f\x7f]',
            '[:digit:]': '[0-9]',
            '[:graph:]': '[\x21-\x7e]',
            '[:lower:]': '[a-z]',
            '[:print:]': '[\x20-\x7e]',
            '[:punct:]': '[!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~]',
            '[:space:]': '[ \t\n\r]',
            '[:upper:]': '[A-Z]',
            '[:xdigit:]': '[0-9A-Fa-f]',
        }
        for k, v in posix_mapping.items():
            pattern = pattern.replace(k, v)
        return pattern

    def handle_x_chars(self, pattern: str):
        for i1 in range(0, 10):
            for i2 in range(0, 10):
                pattern = pattern.replace(f'\\x{i1}{i2}', r'\x{0}{1}'.format(i1, i2))
        return pattern

    def handle_backslash(self, command: str):
        match command:
            case '{':
                return None
            case '(':
                return None
            case 's':
                return self.handle_bracket_expression(' \t\r\n\v\f')
            case 'S':
                return self.handle_bracket_expression('^ \t\r\n\v\f')
            case 'w':
                return self.handle_bracket_expression('A-Za-z0-9_')
            case 'W':
                return self.handle_bracket_expression('^A-Za-z0-9_')
            case 'a':
                return self.handle_bracket_expression('A-Za-z')
            case 's':
                return self.handle_bracket_expression(' \t')
            case 'd':
                return self.handle_bracket_expression('0-9')
            case 'D':
                return self.handle_bracket_expression('^0-9')
            case _:
                return z3.Re(z3.StringVal(command, ctx=self._z3_context))

    def handle_group(self, sub_pattern: str):
        sub_pattern = sub_pattern.removesuffix('\\')

        res = self.handle_root(sub_pattern)
        return z3.Union(
            res,
            z3.Concat(
                z3.Re(z3.StringVal('(', ctx=self._z3_context), ctx=self._z3_context),
                res,
                z3.Re(z3.StringVal(')', ctx=self._z3_context), ctx=self._z3_context),
            ),
        )

    def handle_bracket_expression(self, sub_pattern: str):
        results = []
        expressions = []

        is_prev_backslash = False
        is_prev_dash = False
        is_negate = sub_pattern.startswith('^')
        cursor = 0

        if is_negate:
            sub_pattern = sub_pattern[1::]

        for index, char in enumerate(sub_pattern):
            if index < cursor:
                continue

            if is_prev_backslash:
                results.append(char)
                cursor += 1
                continue
            if is_prev_dash:
                expressions.append(z3.Range(results.pop(-1), char, ctx=self._z3_context))
                is_prev_dash = False
                cursor += 1
                continue

            if char == '-':
                is_prev_dash = True
                cursor += 1
                continue
            if char == '\\':
                is_prev_backslash = True
                cursor += 1
                continue

            if char == '[':
                group_start = index + 1
                group_end = self.find_closure(sub_pattern, '[', group_start)
                cursor = group_end + 1
                expressions.append(self.handle_bracket_expression(sub_pattern[group_start:group_end]))
                continue

            results.append(char)
            cursor += 1

        if results or expressions:
            result = z3.Union(*[z3.Re(c, ctx=self._z3_context) for c in results] + expressions)
        else:
            result = z3.Re('', ctx=self._z3_context)
        if is_negate:
            result = z3.Diff(self.any_char, result, ctx=self._z3_context)
        return result

    def handle_at_least(self, sub_pattern: str, element):
        sub_pattern = sub_pattern.removesuffix('\\')
        expressions = [z3.Concat(element, z3.Re(f'{{{sub_pattern}}}', ctx=self._z3_context))]

        if ',' in sub_pattern:
            at_least, not_more_than = sub_pattern.split(',')
            expressions.append(
                z3.Loop(
                    element, z3.IntVal(at_least, ctx=self._z3_context), z3.IntVal(not_more_than, ctx=self._z3_context)
                )
            )
        else:
            at_least = int(sub_pattern)
            expressions.append(z3.Concat(*[element for _ in range(at_least)]))

        return z3.Union(*expressions)

    def find_closure(self, text: str, open_symbol: str, start: int):
        closures_mapping = {'(': ')', '{': '}', '[': ']', '<': '>'}
        assert open_symbol in closures_mapping.keys()
        closure_symbol = closures_mapping[open_symbol]

        text = text[start:]
        balance = 1
        is_prev_backslash = False
        for index, c in enumerate(text):
            if is_prev_backslash:
                is_prev_backslash = False
                continue
            if c == '\\' and open_symbol not in ['(', '{']:
                is_prev_backslash = True
                continue

            if c == open_symbol:
                balance += 1
            if c == closure_symbol:
                balance -= 1
            if balance == 0:
                return start + index
        raise ValueError('No closure found')

    def handle_root(self, sub_pattern: str):
        results = []
        unions = []
        cursor = 0

        for index, char in enumerate(sub_pattern):
            if index < cursor:
                continue

            match char:
                case '\\':
                    result = self.handle_backslash(command=sub_pattern[index + 1])
                    if result is not None:
                        results.append(result)
                        cursor += 2
                    else:
                        cursor += 1
                case '(':
                    group_start = index + 1
                    group_end = self.find_closure(sub_pattern, '(', group_start)
                    cursor = group_end + 1
                    results.append(self.handle_group(sub_pattern[group_start:group_end]))
                case '[':
                    group_start = index + 1
                    group_end = self.find_closure(sub_pattern, '[', group_start)
                    cursor = group_end + 1
                    results.append(self.handle_bracket_expression(sub_pattern[group_start:group_end]))
                case '|':
                    if not results:
                        unions.append(z3.Re('', ctx=self._z3_context))
                    elif len(results) > 1:
                        unions.append(z3.Concat(*results))
                    else:
                        unions.append(results[0])
                    results.clear()
                    cursor += 1
                case '*':
                    if not results:
                        raise ValueError('Quantifier * is used without preceding character class or character set')
                    results.append(z3.Star(results.pop(-1)))
                    cursor += 1
                case '{':
                    if not results:
                        raise ValueError('Quantifier { is used without preceding character class or character set')
                    group_start = index + 1
                    group_end = self.find_closure(sub_pattern, '{', group_start)
                    cursor = group_end + 1
                    results.append(
                        self.handle_at_least(sub_pattern=sub_pattern[group_start:group_end], element=results.pop(-1))
                    )
                case '.':
                    results.append(self.any_char)
                    cursor += 1
                case '?':
                    if not results:
                        raise ValueError('Quantifier ? is used without preceding character class or character set')
                    cursor += 1
                    results.append(z3.Option(z3.StringVal(results.pop(-1), ctx=self._z3_context)))
                case '+':
                    if not results:
                        raise ValueError('Quantifier + is used without preceding character class or character set')
                    cursor += 1
                    results.append(z3.Plus(results.pop(-1)))
                case _:
                    cursor += 1
                    if self.is_case_sensitive:
                        results.append(z3.Re(z3.StringVal(char, ctx=self._z3_context)))
                    else:
                        results.append(
                            z3.Union(
                                z3.Re(z3.StringVal(char.lower(), ctx=self._z3_context)),
                                z3.Re(z3.StringVal(char.upper(), ctx=self._z3_context)),
                            )
                        )

        if len(results) > 1:
            unions.append(z3.Concat(*results))
        elif results:
            unions.append(results[0])

        return z3.Union(*unions) if unions else z3.Re('', ctx=self._z3_context)

    def check_no_unsupported_quantifiers(self, pattern: str):
        greedy_quantifiers = ['*?', '+?', '}?']
        possessive_quantifiers = ['*+', '?+', '++', '}+']
        for quantifier in greedy_quantifiers + possessive_quantifiers:
            if pattern.count(f'\\{quantifier}') != pattern.count(quantifier):
                raise ValueError(f'Quantifier {quantifier} is not supported')

    def convert(self):
        pattern = self.handle_posix_character_groups(self.ere_pattern)
        pattern = self.handle_x_chars(pattern)
        self.check_no_unsupported_quantifiers(pattern)
        return self.handle_root(pattern)
