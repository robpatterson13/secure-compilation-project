ty : Type
tm : Type
vl : Type

bool : ty
arr : ty -> ty -> ty
all : (bind ty in ty) -> ty
exist : (bind ty in ty) -> ty

app  : tm -> tm -> tm
tapp : tm -> ty -> tm
vt   : vl -> tm

true : vl
false : vl
lam  : ty -> (bind vl in tm) -> vl
tlam : (bind ty in tm) -> vl