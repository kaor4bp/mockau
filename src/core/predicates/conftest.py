# import pytest
# from pympler import muppy, summary, asizeof
# import gc
#
#
# @pytest.fixture(autouse=True, scope='function')
# def memory_profiler():
#     """
#     Фикстура для профилирования памяти:
#     делает снимок до теста и печатает разницу после.
#     """
#     gc.collect()
#     # Снимок до теста
#     all_objects_before = muppy.get_objects()
#     summary_before = summary.summarize(all_objects_before)
#     print("\n--- Начальное состояние памяти ---")
#     summary.print_(summary_before)
#
#     yield  # Тест выполняется здесь
#
#     # Снимок после теста
#     gc.collect()
#     all_objects_after = muppy.get_objects()
#     summary_after = summary.summarize(all_objects_after)
#
#     # Вывод разницы
#     diff_summary = summary.get_diff(summary_before, summary_after)
#     print("\n--- Отчет pympler о разнице в памяти после теста ---")
#     summary.print_(diff_summary)
#     print("--------------------------------------------------")
#
#     # Опционально: можно добавить логику для провала теста при обнаружении "утечек"
#     # Например, если появились новые объекты определенного типа или общий объем памяти вырос сверх порога.
#     # Простейшая проверка:
#     total_added_size = 0
#     for s in diff_summary:
#         if s[0] == 'TOTAL':
#             total_added_size = s[2]  # s[2] - это добавленный размер
#
#     # Здесь можно добавить assert, например, если появилось больше 10 МБ новых данных:
#     # assert total_added_size < 10 * 1024 * 1024, f"Объем памяти вырос на {total_added_size / (1024*1024):.2f} MB!"
#
