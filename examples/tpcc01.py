from typing import Dict

from iconfluence import *

from .parser import get_checker

num_districts = 20
num_servers = 3
num_txns_per_var = 2

checker = get_checker()
if isinstance(checker, StratifiedChecker):
    stratum = checker.stratum('stratum')
variables: Dict[str, EVar] = dict()

# District sums.
district_sum = coerce(0)
per_server_district_sum = {s: coerce(0) for s in range(num_servers)}
for server_id in range(num_servers):
    for district_id in range(num_districts):
        name = f'd_{district_id}_{server_id}'
        var = checker.int_max(name, 0)

        variables[name] = var
        checker.add_invariant(f'{name}_geq_0', var >= 0)
        if isinstance(checker, StratifiedChecker):
            stratum.add_invariant(var >= 0)
        district_sum += var
        per_server_district_sum[server_id] += var
        for x in range(num_txns_per_var):
            checker.add_transaction(f'{name}_plus_{x}', [var.assign(var + x)])
            if isinstance(checker, StratifiedChecker):
                stratum.add_transaction(f'{name}_plus_{x}')

# Warehouse sums.
warehouse_sum = coerce(0)
for server_id in range(num_servers):
    name = f'w_{server_id}'
    var = checker.int_max(name, 0)

    variables[name] = var
    checker.add_invariant(f'{name}_geq_0', var >= 0)
    checker.add_invariant(f'per_server_{server_id}_eq',
                          var.eq(per_server_district_sum[server_id]))
    if isinstance(checker, StratifiedChecker):
        stratum.add_invariant(var >= 0)
        stratum.add_invariant(var.eq(per_server_district_sum[server_id]))
    warehouse_sum = warehouse_sum + var

checker.add_invariant('sum_eq', warehouse_sum.eq(district_sum))
if isinstance(checker, StratifiedChecker):
    stratum.add_invariant(warehouse_sum.eq(district_sum))

checker.check()

if isinstance(checker, StratifiedChecker):
    for server_id in range(num_servers):
        lhs_vars: List[EVar] = []
        rhs_vars: List[EVar] = []
        for district_id in range(num_districts):
            name = f'd_{district_id}_{server_id}'
            var = variables[name]
            lhs_var, rhs_var = stratum.checker.split(var)
            lhs_vars.append(lhs_var)
            rhs_vars.append(rhs_var)

        lhs_leq_rhs = coerce(True)
        lhs_geq_rhs = coerce(True)
        for (l, r) in zip(lhs_vars, rhs_vars):
            lhs_leq_rhs = lhs_leq_rhs & (l <= r)
            lhs_geq_rhs = lhs_geq_rhs & (l >= r)
        stratum.checker.refine_coreachable(lhs_leq_rhs | lhs_geq_rhs)
