import elasticsearch

from settings import MockauSettings
from utils.mongo import MongoClient

mongo_events_client = MongoClient(collection='mockau_events')
mongo_actions_client = MongoClient(collection='mockau_actions')
mongo_settings_client = MongoClient(collection='mockau_settings')

elasticsearch_client = elasticsearch.AsyncElasticsearch(
    hosts=MockauSettings.elk.uri,
)
