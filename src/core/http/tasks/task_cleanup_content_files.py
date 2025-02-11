import os
import pathlib
import time
from datetime import timedelta

from celery_once import QueueOnce

from celery_worker import celery_app
from settings import MockauSettings


@celery_app.task(base=QueueOnce, once={"graceful": True})
def task_cleanup_content_files():
    outdated_mtime = time.time() - timedelta(hours=2).total_seconds()

    for f in os.listdir(pathlib.Path(MockauSettings.path.content).resolve()):
        file_path = pathlib.Path(MockauSettings.path.content).joinpath(f)

        if os.path.isfile(file_path):
            file_mtime = os.path.getmtime(file_path)

            if file_mtime < outdated_mtime:
                os.remove(file_path)
