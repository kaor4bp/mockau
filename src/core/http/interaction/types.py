from core.http.interaction.schemas import (
    HttpBinaryContent,
    HttpContentEmpty,
    HttpJsonContent,
    HttpTextContent,
    HttpXmlContent,
)

t_Content = HttpBinaryContent | HttpJsonContent | HttpXmlContent | HttpTextContent | HttpContentEmpty
