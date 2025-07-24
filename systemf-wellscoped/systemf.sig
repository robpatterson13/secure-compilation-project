ty : Type
tm : Type
vl : Type

bool : ty
arr : ty -> ty -> ty
all : (bind ty in ty) -> ty
ex : (bind ty in ty) -> ty

app  : tm -> tm -> tm
tapp : tm -> ty -> tm
vt   : vl -> tm
unpack : tm -> (bind ty, vl in tm) -> tm

false : vl
true : vl
lam  : ty -> (bind vl in tm) -> vl
tlam : (bind ty in tm) -> vl
pack : ty -> vl -> vl