from schemas.base_schema import BaseSchema
from schemas.modifiers.string_modifier import t_StringModifier


class HttpRequestModify(BaseSchema):
    path: t_StringModifier | None = None
    # query_params: list[HttpRequestModifyQueryParam] | None = None
    # socket_address: HttpRequestModifySocketAddress | None = None
    # method: HttpMethod | None = None
    # headers: HttpRequestModifyHeaders | None = None
    # body: t_HttpRequestModifyContent | None = Field(default=None, discriminator='type_of')
