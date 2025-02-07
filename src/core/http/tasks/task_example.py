from celery_once import QueueOnce

from celery_worker import celery_app


@celery_app.task(base=QueueOnce, once={"graceful": True})
def task_example():
    pass
