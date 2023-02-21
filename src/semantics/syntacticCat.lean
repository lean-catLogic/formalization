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
    Exists.fst(thin_cat.preorder_cat_full f)

end synCat



namespace synCat_tactics

  /-
    To instantiate these tactics for a specific deductive calculus,
    create a namespace with Form and Der specifically def'd (with
    those exact variable names), and then

    meta def lift_derive_XXX : tactic unit → tactic unit :=
    @synCat_tactics.lift_derive_syn_cat Form Der
  -/
  variable {Form : Type}
  variable [Der : has_derives Form]

  /-
  Tactic for automatically proving that operations defined by induction
  on Form_eq respect ⊣⊢, because syn_cat is thin and therefore any
  two parallel arrows are equal
  -/ 
  meta def by_syn_thin {Form : Type} [Der : has_derives Form] : tactic unit :=
  `[ repeat{assume _}, repeat{ repeat{ apply funext, assume _},apply thin_cat.K }]

  meta def repeat_assume_Form_eq_induct {Form : Type} [Der : has_derives Form] : tactic unit :=
  `[ 
    assume X : @synPoset.Form_eq Form Der,
    try {repeat_assume_Form_eq_induct},
    induction X with φ
  ]

  /-
  Tactic for doing constructions in syn_cat which are actually just
  the derivation rules lifted onto equivalence classes
  Input should be of the form `[ apply XXX ]
  where XXX is a derivation rule of Der
  -/
  meta def lift_derive_syn_cat 
    (T : tactic unit) : tactic unit :=
  `[ 
    -- Assume all the ℂ_PPC objects, and write them as ⦃φ⦄ for some φ
    @repeat_assume_Form_eq_induct Form Der,
    -- Introduce assumed morphisms
    repeat {assume Y},
    -- Change the goal to be about constructing a derivation instead of a
    -- ℂ_PPC morphism
    apply syn_hom,
    -- Apply the input tactic, proving the derivation
    T, 
    -- Clean up
    repeat {apply PPC_Der.derive_refl},
    repeat {apply @derives_of_hom Form Der, assumption},
    -- Prove this coherent w.r.t the ⊣⊢equiv relation, using thinness of ℂ_PPC 
    @by_syn_thin Form Der 
  ]

end synCat_tactics
