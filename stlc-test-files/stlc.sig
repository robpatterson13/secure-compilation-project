ty  : Type
tm  : Type

bool : ty
arr  : ty -> ty -> ty 

true : tm
false : tm

ifthenelse : tm -> tm -> tm -> tm
lam : ty -> (bind tm in tm) -> tm
app : tm -> tm -> tm

nat : Type
num  : nat -> tm