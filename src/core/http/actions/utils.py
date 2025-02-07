from core.http.actions.types import t_HttpActionModel
from schemas.variables import VariablesContext


def verify_http_actions_integrity(actions: list[t_HttpActionModel]) -> None:
    for verified_action in actions:
        verified_action_context = VariablesContext(variables_group=verified_action.variables_group)
        verified_action_plain_matcher = verified_action.http_request.to_plain_matcher(context=verified_action_context)

        print(f'    Check HttpAction {verified_action.id} collision with:')

        is_found = False
        for action in actions:
            if is_found is False and action.id != verified_action.id:
                continue
            if action.id == verified_action.id:
                is_found = True
                continue

            print(f'        - HttpAction {action.id}')

            action_context = VariablesContext(variables_group=action.variables_group)
            action_plain_matcher = action.http_request.to_plain_matcher(context=action_context)

            if action_plain_matcher.is_subset(verified_action_plain_matcher):
                raise AssertionError(f'Action {action.id} is subset of {verified_action.id}')
