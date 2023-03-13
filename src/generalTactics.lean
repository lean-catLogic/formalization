import meta.expr

open tactic
open nat
  open interactive (parse)
  open lean.parser (ident)  
  open lean.parser (tk)
  open tactic.interactive («have»)

-- Tactic for print-debugging
meta def trace_goal (iden : string) : tactic unit :=
  do  
    tactic.trace ("-- GOAL @ " ++ iden ++ " --"),
    tactic.trace_state

/- Takes a list of names, introduces new variables by those names,
   and then returns a list of the names and corresponding expr's
   paired together. 
   REQUIRES: goal is a Pi type of at least n args, where n is
    the length of the input list   
-/
meta def repeat_assume_pair : list name → tactic (list (name × expr))
| [] := return []
| (nm::nms) :=
  (do
    temp_nm ← mk_fresh_name,
    e ← intro temp_nm,
    rest ← repeat_assume_pair nms,
    return $ (nm,e)::rest)
  -- <|> (return [])


/- Takes a list of names, introduces new variables by those names,
   and then returns unit. 
   REQUIRES: goal is a Pi type of at least n args, where n is
    the length of the input list   
-/
meta def repeat_assume : list name → tactic unit :=
  list.foldr (λ nm rest, intro nm >> rest) skip 

/- Takes a list N=[nm_0,nm_1,...,nm_{|N|-1}] of names, and
   1. does |N| introductions to get e_0,e_1,...,e_{|N|-1},
   2. does tactic T
   3. does `induction e_i with nm_i` for each i,
   4. returns unit.

   REQUIRES: goal is a Pi type of at least |N| args, each of which can
   have induction applied. Also T must work after the introductions
   Will only attach nm_i to the first induction arg of e_i.

   EXAMPLE: If goal is of the form
      ⊢ ∀ (x_0,...,x_n : X) (y : Y), Q
   then doing 
      repeat_assume_then_induct `[ assume y ] [`φ0,...,`φn]
    will have the same effect as
      assume x0 ... xn,
      assume y,
      induction x0 with φ0,
      ...
      induction xn with φn,
    So the assumption of y is outside the induction. If it's not
    important to assume y before inducting, then the repeat_assume_induct
    tactic can be used, followed by assume y.
-/
meta def repeat_assume_then_induct (T : tactic unit) (N : list name) : tactic unit :=
  do
    assumptionList ← repeat_assume_pair N,
    T,
    let cmb := λ nm e (res : tactic unit), (induction e [nm]) >> res,
    list.foldr (function.uncurry cmb) skip assumptionList

meta def repeat_assume_induct : list name →  tactic unit :=
  repeat_assume_then_induct skip

/-
  Assumes premises with each name from N, and then "applies" the
  operation named F to each premise.
-/
meta def repeat_assume_replace (F : parse ident) (N : list name) : tactic unit :=
do
  f ← resolve_name F,
  assumptionList ← repeat_assume_pair N,
  let cmb := λ (nm : name) (e : expr) (res:tactic unit),
    (do
      «have» nm none ``(%%f %%e),
      clear e,
      res),
  list.foldr (function.uncurry cmb) skip assumptionList


/-
  gen_nameList takes a "base name" nm and will generate n
  unique names: nm0, nm1, ...
  More user-readable way of generating fresh names
-/
def varFormat (baseName : name) (i : nat) : name :=
  name.append_suffix baseName (nat.has_repr.repr i)
def gen_nameList (baseName : name) (n : nat) : list name := 
  list.map (varFormat baseName) (list.range n)


run_cmd add_interactive [`repeat_assume_replace]
