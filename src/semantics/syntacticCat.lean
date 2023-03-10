import semantics.syntacticPoset categoryTheory.CCC category_theory.category.preorder
open category_theory
open deduction_basic

namespace synCat
  open synPoset

  variable {Form : Type}

  -- Form the category out of this poset
  def syn_cat [Der : has_struct_derives Form] : thin_cat (Form _eq)
    := thin_cat.from_preorder synPoset.syn_eq_pre
  instance [Der : has_struct_derives Form] : thin_cat (Form _eq) := syn_cat

  -- Methods for directly turning formulas into objects and derivations into morphisms
  def syn_obj [Der : has_struct_derives Form] (φ : Form) : Form _eq := 
    Form_eq_in φ
  def syn_hom [Der : has_struct_derives Form] : 
      ∀ {φ ψ : Form}, (φ ⊢ ψ) → (syn_obj φ ⟶ syn_obj ψ) 
  := begin
    assume φ ψ h,
    apply hom_of_le,
    exact h,
  end 

  def derives_of_hom [Der : has_struct_derives Form] {φ ψ : Form} (f : syn_obj φ ⟶ syn_obj ψ) : 
    Der.derives {φ} ψ :=
    le_of_hom f

end synCat

namespace synCat_tactics
  open tactic
  open interactive (parse)
  open lean.parser (ident)  
  open lean.parser (tk)

  /-
  Tactic for doing constructions in syn_cat which are actually just
  the derivation rules lifted onto equivalence classes
  First two arguments are the number of objects and morphisms to assume
  Tactic input should be of the form `[ apply XXX ]
  where XXX is a derivation rule of Der
 -/

  meta def lift_derive_syn_cat_init (numobjs : nat) (nummor : nat)
  : tactic unit :=
  do
    /- Assume objects and morphisms, 
      use induction to get that every object is of the form ⦃φ⦄ for some φ:Form
    -/
    repeat_assume_induct (gen_nameList `φ_ numobjs),
    repeat_assume (gen_nameList `f_ nummor),
    -- Turn the synCat hom goal to a derivation goal
    applyc `synCat.syn_hom,
    trace_goal "BEGIN",
    trace "-- BEGIN USE TACTIC --"
  
  meta def cleanup
    (conclude : parse (optional $ tk "-"))
    : tactic unit :=
  (do
    iterate (
      (applyc `deduction_basic.derive_refl)
      <|> (applyc `synCat.derives_of_hom >> assumption)
    ),
    when conclude.is_none thin_cat.by_thin)

  meta def lift_derive_syn_cat (numobjs : nat) (nummor : nat) 
  (T : tactic unit) : tactic unit :=
  do
    lift_derive_syn_cat_init numobjs nummor,
    -- Use tactic
    T,
    trace "-- END USE TACTIC --",
    trace_goal "END",
    -- Clean up
    cleanup none

  /- Tactic which accepts a type as an expr
     and counts the number of assumed objects and
     morphisms
  -/
  open nat
  meta def mkCount : expr →  tactic (nat × nat)
  | `( Π {_ : _ _eq}, %%newGoal) := 
    do 
      (o,m) ← mkCount newGoal,
      return (succ o,m)
  | `( Π {_ : _ ⟶ _}, %%newGoal) := 
    do 
      (o,m) ← mkCount newGoal,
      return (o,succ m)
  | _ := return (0,0)

  meta def LiftT 
    (debugMode : parse (optional $ tk "?")) 
    (debugPerformTac : parse (optional $ tk "!"))
    (debugCleanup : parse (optional $ tk "!"))
    (T : tactic unit) 
    : tactic unit :=
  do
  
    -- Count & print how many objects and morphisms to assume
    (numobjs,nummor) ← target >>= mkCount,
    trace $ "Objs: " ++ (repr numobjs) ++ ", Morphs: " ++ (repr nummor),
    match (debugMode, debugPerformTac) with 

    -- No debugging args: perform the full tactic
    | (none,_) := lift_derive_syn_cat numobjs nummor T

    -- LiftT? invoked: just do the assume's and syn_hom
    | (some _, none) := lift_derive_syn_cat_init numobjs nummor

    -- LiftT?! invoked: apply the tactic
    | (some _, some _) := lift_derive_syn_cat_init numobjs nummor 
                          >> T
                          -- LiftT?!! invoked: also do the first stage of cleanup
                          >> when debugCleanup.is_some (cleanup $ some ())
    end
    
end synCat_tactics
run_cmd add_interactive [`synCat_tactics.lift_derive_syn_cat,`synCat_tactics.LiftT,`synCat_tactics.cleanup]

