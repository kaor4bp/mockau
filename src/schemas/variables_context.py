from copy import deepcopy


class VariablesContext(dict):
    pass


def variables_context_transaction(fn):
    def wrapper(*args, context, **kwargs):
        orig_context = deepcopy(context)
        try:
            res = fn(*args, context=context, **kwargs)
        except Exception:
            context.clear()
            for k, v in orig_context.items():
                context[k] = v
            raise
        if res is False:
            context.clear()
            for k, v in orig_context.items():
                context[k] = v
        return res

    return wrapper
