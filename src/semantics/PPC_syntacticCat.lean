import semantics.syntacticCat semantics.PPC_poset CT.CCC category_theory.category.preorder
open category_theory

open PPC_defn
open PPC_defn.PPC_derives
open PPC_synPoset
open synCat


open specialCats

instance ℂ_PPC : thin_cat PPC_eq := syn_cat

namespace ℂ_PPC_tactics

def Form : Type := PPC_Form
def Der : has_derives Form := PPC_Der
/-
Tactic for doing constructions in ℂ_PPC which are actually just
the derivation rules of the natural deduction calculus lifted onto
equivalence classes
Input should be of the form `[ apply XXX ]
where XXX is a rule of PPC_Der
-/
meta def lift_derive_ℂ_PPC : tactic unit → tactic unit :=
  @synCat_tactics.lift_derive_syn_cat Form Der

end ℂ_PPC_tactics

open ℂ_PPC_tactics

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
