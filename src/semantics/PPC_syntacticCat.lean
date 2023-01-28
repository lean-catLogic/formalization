import semantics.PPC_poset CT.CCC category_theory.category.preorder
open category_theory


-- Form the category out of this poset
def ℂ_PPC : thin_cat (PPC_eq) 
  := thin_cat.from_preorder PPC_eq_pre
instance : thin_cat PPC_eq := ℂ_PPC

-- Methods for directly turning formulas into objects and derivations into morphisms
def ℂ_PPC_obj (φ : PPC_form) : PPC_eq := ⦃φ⦄
def ℂ_PPC_hom : ∀ {φ ψ : PPC_form}, (φ ⊢ ψ) → (ℂ_PPC_obj φ ⟶ ℂ_PPC_obj ψ) 
:= begin
  assume φ ψ h,
  dsimp[ℂ_PPC_obj],
  apply hom_of_le,
  dsimp[(≤),preorder.le,partial_order.le],
  rewrite preorder_lift_rewrite,
  exact h,
end 

def derives_of_hom {φ ψ : PPC_form} (f : ℂ_PPC_obj φ ⟶ ℂ_PPC_obj ψ): φ ⊢ ψ :=
  Exists.fst(thin_cat.preorder_cat_full f)

/-
Tactic for automatically proving that operations defined by induction
on PPC_eq respect ⊣⊢, because ℂ_PPC is thin and therefore any
two parallel arrows are equal
-/ 
meta def by_ℂ_thin : tactic unit :=
`[ repeat{assume _}, repeat{ repeat{ apply funext, assume _},apply thin_cat.K }]

meta def repeat_assume_PPC_eq_induct : tactic unit :=
`[ 
  assume X : PPC_eq,
  try {repeat_assume_PPC_eq_induct},
  induction X with φ
  ]
/-
Tactic for doing constructions in ℂ_PPC which are actually just
the derivation rules of the natural deduction calculus lifted onto
equivalence classes
Input should be of the form `[ apply derives.XXX ]
-/
meta def lift_derive_ℂ_PPC ( T : tactic unit) : tactic unit :=
`[ 
   -- Assume all the ℂ_PPC objects, and write them as ⦃φ⦄ for some φ
   repeat_assume_PPC_eq_induct,
   -- Introduce assumed morphisms
   repeat {assume Y},
   -- Change the goal to be about constructing a derivation instead of a
   -- ℂ_PPC morphism
   apply ℂ_PPC_hom,
   -- Apply the input tactic, proving the derivation
   T, 
   -- Clean up
   repeat {apply derives_x.refl},
   repeat {apply derives_of_hom, assumption},
   -- Prove this coherent w.r.t the ⊣⊢equiv relation, using thinness of ℂ_PPC 
   by_ℂ_thin ]

open specialCats

-- ℂ_PPC has finite products
instance : FP_cat PPC_eq :=
{
  unit := ℂ_PPC_obj PPC_form.top,
  term := by lift_derive_ℂ_PPC `[ apply derives.truth ], -- φ ⊢ ⊤
  unit_η := λ X f, by apply thin_cat.K,
  prod := (&⁼),
  pr1 := by lift_derive_ℂ_PPC `[ apply derives.and_eliml ], -- φ & ψ ⊢ φ
  pr2 := by lift_derive_ℂ_PPC `[ apply derives.and_elimr ], -- φ & ψ ⊢ ψ
                -- If θ ⊢ φ and θ ⊢ ψ, then θ ⊢ φ & ψ
  pair := by lift_derive_ℂ_PPC `[ apply derives.and_intro ],
  prod_β1 := λ X Y Z f g, by apply thin_cat.K,
  prod_β2 := λ X Y Z f g, by apply thin_cat.K,
  prod_η :=  λ X Y, by apply thin_cat.K,
}

-- ℂ_PPC is a cartesian closed category
instance : CC_cat PPC_eq := 
{
  exp := (⊃⁼),
  eval := by lift_derive_ℂ_PPC `[ 
                -- φ⊃ψ & φ ⊢ ψ
                apply derives_x.union_Hyp_and,
                apply derives_x.modus_ponens ],
  curry := by lift_derive_ℂ_PPC `[ 
                -- If φ & ψ ⊢ θ, then φ ⊢ ψ ⊃ θ
                apply derives.impl_intro,
                apply derives_x.and_Hyp_union ],
  curry_β := λ {X Y Z} u, by apply thin_cat.K,
  curry_η := λ {X Y Z} v, by apply thin_cat.K,
}
