from core.http.actions.types import t_HttpActionModel
from schemas.variables import VariablesContext


def verify_http_actions_consistency(actions: list[t_HttpActionModel]) -> None:
    if len(actions) == 0:
        print('    No actions found, skip consistency checking')
        return
    if len(actions) == 1:
        print('    Action is home alone, skip consistency checking')
        return

    action_plain_matchers_mapping = {
        action.id: action.http_request.to_predicate(context=VariablesContext(variables_group=action.variables_group))
        for action in actions
    }

    for verified_action in actions[0 : len(actions) - 1]:
        verified_action_plain_matcher = action_plain_matchers_mapping[verified_action.id]
        print(f'    Check HttpAction {verified_action.id} collision with:')

        is_found = False
        for action in actions:
            if is_found is False and action.id != verified_action.id:
                continue
            if action.id == verified_action.id:
                is_found = True
                continue

            print(f'        - HttpAction {action.id}')

            action_plain_matcher = action_plain_matchers_mapping[action.id]
            if action_plain_matcher.is_subset_of(verified_action_plain_matcher):
                raise AssertionError(f'Action {action.id} is subset of {verified_action.id}')
