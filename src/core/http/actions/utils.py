from core.http.actions.types import t_HttpActionModel
from schemas.variables import VariablesContext


def verify_http_actions_integrity(actions: list[t_HttpActionModel]) -> None:
    if len(actions) == 0:
        print('    No actions found, skip checking')
        return
    if len(actions) == 1:
        print('    Action is home alone, skip checking')
        return

    for verified_action in actions:
        verified_action_plain_matcher = verified_action.http_request.to_plain_matcher(
            context=VariablesContext(variables_group=verified_action.variables_group)
        )
        print(f'    Check HttpAction {verified_action.id} collision with:')

        is_found = False
        for action in actions:
            if is_found is False and action.id != verified_action.id:
                continue
            if action.id == verified_action.id:
                is_found = True
                continue

            print(f'        - HttpAction {action.id}')

            action_plain_matcher = action.http_request.to_plain_matcher(
                context=VariablesContext(variables_group=verified_action.variables_group)
            )
            if action_plain_matcher.is_subset(verified_action_plain_matcher):
                raise AssertionError(f'Action {action.id} is subset of {verified_action.id}')
