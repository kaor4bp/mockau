FROM python:3.12.3


WORKDIR /code
EXPOSE 8000
ENV PYTHONPATH=/code/src:/code

COPY poetry.lock pyproject.toml /code/
RUN python3.12 -m pip install --disable-pip-version-check poetry==1.8.2 && \
    poetry install --no-ansi --no-interaction

COPY . /code/

ENTRYPOINT poetry run uvicorn main:app --port 8000 --host 0.0.0.0 --workers 5 --log-level warning
