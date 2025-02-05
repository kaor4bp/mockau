FROM python:3.12-slim-bookworm
RUN pip --disable-pip-version-check install poetry==1.8.2

WORKDIR /code
COPY ./poetry.lock ./pyproject.toml /code/
RUN poetry config virtualenvs.in-project true && \
    poetry install --no-ansi --no-interaction --no-root

EXPOSE 8000
COPY . /code/
WORKDIR /code/src
ENTRYPOINT poetry run python -m uvicorn main:app --port 8000 --host 0.0.0.0 --workers 5
