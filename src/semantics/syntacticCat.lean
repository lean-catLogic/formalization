import semantics.syntacticPoset categoryTheory.CCC category_theory.category.preorder
open category_theory

namespace synCat
  open synPoset

  variable {Form : Type}

  -- Form the category out of this poset
  def syn_cat [Der : has_derives Form] : thin_cat (Form _eq)
    := thin_cat.from_preorder synPoset.syn_eq_pre
  instance [Der : has_derives Form] : thin_cat (Form _eq) := syn_cat

  -- Methods for directly turning formulas into objects and derivations into morphisms
  def syn_obj [Der : has_derives Form] (φ : Form) : Form _eq := Form_eq_in φ
  def syn_hom [Der : has_derives Form] : ∀ {φ ψ : Form}, (φ ⊢ ψ) → (syn_obj φ ⟶ syn_obj ψ) 
  := begin
    assume φ ψ h,
    apply hom_of_le,
    exact h,
  end 

  def derives_of_hom [Der : has_derives Form] {φ ψ : Form} (f : syn_obj φ ⟶ syn_obj ψ): 
    Der.derives (Der.singleHyp.singleton φ) ψ :=
    le_of_hom f

end synCat



namespace synCat_tactics

  open tactic
  open nat
  /-
    To instantiate these tactics for a specific deductive calculus,
    create a namespace with Form and Der specifically def'd (with
    those exact variable names), and then

    meta def lift_derive_XXX : tactic unit → tactic unit :=
    @synCat_tactics.lift_derive_syn_cat Form Der
  -/
  variable {Form : Type}
  variable [Der : has_derives Form]

  meta def cleanup {Form : Type} [Der : has_derives Form] : tactic unit :=
    `[ 
      repeat {
        apply Der.derive_refl
        <|> {apply @derives_of_hom Form Der, assumption},
        
      }, 
      thin_cat.by_thin ]

  def varFormat (baseName : name) (i : nat) : name :=
    name.append_suffix baseName (nat.has_repr.repr i)

  def gen_nameList (baseName : name) (n : nat) : list name := 
    list.map (varFormat baseName) (list.range n)

  /-
  Tactic for doing constructions in syn_cat which are actually just
  the derivation rules lifted onto equivalence classes
  First two arguments are the number of objects and morphisms to assume
  Tactic input should be of the form `[ apply XXX ]
  where XXX is a derivation rule of Der
  -/
  meta def lift_derive_syn_cat (numobjs : nat) (nummor : nat) (T : tactic unit) : tactic unit :=
  do
    synPoset_tactics.repeat_assume_induct (gen_nameList `φ_ numobjs),
    synPoset_tactics.repeat_assume (gen_nameList `f_ nummor),
    applyc `synCat.syn_hom,
    synPoset_tactics.trace_goal "BEGIN",
    trace "-- BEGIN USE TACTIC --",
    T,
    trace "-- END USE TACTIC --",
    synPoset_tactics.trace_goal "END",
    @cleanup Form Der 

end synCat_tactics
