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

  meta def lift_derive_syn_cat (numobjs : nat) (nummor : nat) (T : tactic unit) 
  : tactic unit :=
  do
    /- Assume objects and morphisms, 
      use induction to get that every object is of the form ⦃φ⦄ for some φ:Form
    -/
    repeat_assume_induct (gen_nameList `φ_ numobjs),
    repeat_assume (gen_nameList `f_ nummor),
    -- Turn the synCat hom goal to a derivation goal
    applyc `synCat.syn_hom,
    -- Use tactic
    trace_goal "BEGIN",
    trace "-- BEGIN USE TACTIC --",
    T,
    trace "-- END USE TACTIC --",
    trace_goal "END",
    -- Clean up
    iterate (
      (applyc `deduction_basic.derive_refl)
      <|> (applyc `synCat.derives_of_hom >> assumption)
    ),
    thin_cat.by_thin,
    return ()
    

end synCat_tactics
run_cmd add_interactive [`synCat_tactics.lift_derive_syn_cat]

