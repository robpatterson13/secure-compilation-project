nat : Type
list : Functor
Lcarrier : Type

label : Type
constr : Type
ty : Type
tm : Type
cond_sym : Type
binary : Type

bzero : binary -> binary
bone : binary -> binary
bend : binary

leq : cond_sym
geq : cond_sym
gt : cond_sym
lt : cond_sym

nleq : cond_sym
ngeq : cond_sym
ngt : cond_sym
nlt : cond_sym

condition : cond_sym -> label -> label -> constr

adv : label
latl : Lcarrier -> label
ljoin : label -> label -> label
lmeet : label -> label -> label

Any : ty
Unit : ty
Data : label -> ty
Ref : ty -> ty
arr : ty -> ty -> ty
prod : ty -> ty -> ty
sum : ty -> ty -> ty
all : ty -> (bind ty in ty) -> ty
ex : ty -> (bind ty in ty) -> ty
all_l : cond_sym -> label -> (bind label in ty) -> ty
t_if : constr -> ty -> ty -> ty

error : tm
skip : tm
bitstring : binary -> tm
loc : nat -> tm
fixlam : (bind tm, tm in tm) -> tm
tlam : tm -> tm
l_lam : (bind label in tm) -> tm

op : tm -> "list" (tm) -> tm

zero : tm -> tm
app : tm -> tm -> tm
alloc : tm -> tm
dealloc : tm -> tm
assign : tm -> tm -> tm
tm_pair : tm -> tm -> tm
left_tm : tm -> tm
right_tm : tm -> tm
inl : tm -> tm
inr : tm -> tm
case : tm -> (bind tm in tm) -> (bind tm in tm) -> tm
tapp : tm -> tm
lapp : tm -> label -> tm
pack : tm -> tm
unpack : tm -> (bind tm in tm) -> tm
if_tm : tm -> tm -> tm -> tm
if_c : constr -> tm -> tm -> tm
sync : tm -> tm