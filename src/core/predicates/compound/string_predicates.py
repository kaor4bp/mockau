from enum import Enum
from typing import Literal

from core.predicates.base_predicate import BaseCompoundPredicate


class AvailableTemplate(Enum):
    IP_V4 = 'ip_v4'
    IP_V6 = 'ip_v6'
    UUID = 'uuid'
    UUID_V1 = 'uuid_v1'
    UUID_V2 = 'uuid_v2'
    UUID_V3 = 'uuid_v3'
    UUID_V4 = 'uuid_v4'
    UUID_V5 = 'uuid_v5'
    UUID_V6 = 'uuid_v6'
    UUID_V7 = 'uuid_v7'
    UUID_V8 = 'uuid_v8'


class StringTemplate(BaseCompoundPredicate):
    type_of: Literal['$-mockau-str-template'] = '$-mockau-str-template'
    template: AvailableTemplate

    @property
    def compiled_value(self):
        from core.predicates import StringPattern

        match self.template:
            case AvailableTemplate.IP_V4:
                return StringPattern(
                    pattern='((25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])\.){3}(25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])',
                    var=self.var,
                )
            case AvailableTemplate.IP_V6:
                return StringPattern(pattern='[0-9a-fA-F:]+', var=self.var)
            case AvailableTemplate.UUID:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case AvailableTemplate.UUID_V1:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?1[0-9a-fA-F]{3}-?[89ab][0-9a-fA-F]{3}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case AvailableTemplate.UUID_V2:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?2[0-9a-fA-F]{3}-?[89ab][0-9a-fA-F]{3}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case AvailableTemplate.UUID_V3:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?3[0-9a-fA-F]{3}-?[89ab][0-9a-fA-F]{3}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case AvailableTemplate.UUID_V4:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?4[0-9a-fA-F]{3}-?[89ab][0-9a-fA-F]{3}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case AvailableTemplate.UUID_V5:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?5[0-9a-fA-F]{3}-?[89ab][0-9a-fA-F]{3}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case AvailableTemplate.UUID_V6:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?6[0-9a-fA-F]{3}-?[89ab][0-9a-fA-F]{3}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case AvailableTemplate.UUID_V7:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?7[0-9a-fA-F]{3}-?[89ab][0-9a-fA-F]{3}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case AvailableTemplate.UUID_V8:
                return StringPattern(
                    pattern='[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?8[0-9a-fA-F]{3}-?[89ab][0-9a-fA-F]{3}-?[0-9a-fA-F]{12}',
                    var=self.var,
                )
            case _:
                raise ValueError(f'Unknown template {self.template}')
