from iconfluence import *

checker = InteractiveChecker(verbose=True)
XA = checker.set_union('XA', TInt(), EEmptySet(TInt()))
XR = checker.set_union('XR', TInt(), EEmptySet(TInt()))
YA = checker.set_union('YA', TInt(), EEmptySet(TInt()))
YR = checker.set_union('YR', TInt(), EEmptySet(TInt()))
checker.add_invariant(
    'X_subset_Y',
    XA.diff(XR).subseteq(YA.diff(YR)))
for i in range(5):
    checker.add_transaction(f'X_add_{i}', [XA.assign(XA.union({i}))])
    checker.add_transaction(f'X_sub_{i}', [XR.assign(XR.union({i}))])
    checker.add_transaction(f'Y_add_{i}', [YA.assign(YA.union({i}))])
    checker.add_transaction(f'Y_sub_{i}', [YR.assign(YR.union({i}))])
