ty  : Type
tm  : Type
vl : Type

int : ty
unit : ty
arr  : ty -> ty -> ty 

n : vl
vunit : vl
lam : ty -> (bind tm in tm) -> vl
app : tm -> tm -> tm
add : tm -> tm -> tm

vt : vl -> tm
