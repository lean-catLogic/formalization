import semantics.syntacticCat semantics.PPC_poset CT.CCC category_theory.category.preorder
open category_theory

open PPC_defn
open PPC_defn.PPC_derives
open PPC_synPoset
open synCat


open specialCats

instance ℂ_PPC : thin_cat PPC_eq := syn_cat

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
  -- @lift_derive_syn_cat PPC_Form PPC_Der T
`[ 
   -- Assume all the ℂ_PPC objects, and write them as ⦃φ⦄ for some φ
   repeat_assume_PPC_eq_induct,
   -- Introduce assumed morphisms
   repeat {assume Y},
   -- Change the goal to be about constructing a derivation instead of a
   -- ℂ_PPC morphism
   apply syn_hom,
   -- Apply the input tactic, proving the derivation
   T, 
   -- Clean up
   repeat {apply PPC_Der.derive_refl},
   repeat {apply @derives_of_hom PPC_Form PPC_Der, assumption},
   -- Prove this coherent w.r.t the ⊣⊢equiv relation, using thinness of ℂ_PPC 
   by_ℂ_thin ]


-- ℂ_PPC has finite products
instance : FP_cat PPC_eq :=
{
  unit := syn_obj PPC_Form.top,
  term := by lift_derive_ℂ_PPC `[ apply truth ], -- φ ⊢ ⊤
  unit_η := λ X f, by apply thin_cat.K,
  prod := (&⁼),
  pr1 := by lift_derive_ℂ_PPC `[ apply and_eliml ], -- φ & ψ ⊢ φ
  pr2 := by lift_derive_ℂ_PPC `[ apply and_elimr ], -- φ & ψ ⊢ ψ
                -- If θ ⊢ φ and θ ⊢ ψ, then θ ⊢ φ & ψ
  pair := by lift_derive_ℂ_PPC `[ apply and_intro ],
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
                apply PPC_derives_x.union_Hyp_and,
                apply PPC_derives_x.modus_ponens ],
  curry := by lift_derive_ℂ_PPC `[ 
                -- If φ & ψ ⊢ θ, then φ ⊢ ψ ⊃ θ
                apply impl_intro,
                apply PPC_derives_x.and_Hyp_union ],
  curry_β := λ {X Y Z} u, by apply thin_cat.K,
  curry_η := λ {X Y Z} v, by apply thin_cat.K,
}
