from celery.app import Celery

from settings import MockauSettings

celery_app = Celery(
    __name__,
    broker=MockauSettings.redis.uri,
    backend=MockauSettings.redis.uri,
)
celery_app.conf.update(
    task_serializer="json",
    accept_content=["json"],
    result_backend=MockauSettings.redis.uri,
    timezone="UTC",
    enable_utc=True,
    broker_connection_retry_on_startup=True,
    ONCE={
        'backend': 'celery_once.backends.Redis',
        'settings': {
            'url': MockauSettings.redis.uri,
            "default_timeout": 60 * 5,
        },
    },
)

celery_app.autodiscover_tasks(["core.http.tasks"])
