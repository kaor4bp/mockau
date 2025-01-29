FROM python:3.11-bookworm


COPY ./requirements.txt /code/requirements.txt
RUN python3 -m pip install -r /code/requirements.txt

EXPOSE 8000
COPY . /code/
WORKDIR /code/src
ENTRYPOINT python3 -m uvicorn main:app --port 8000 --host 0.0.0.0 --workers 5
