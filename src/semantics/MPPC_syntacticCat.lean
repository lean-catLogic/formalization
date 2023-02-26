import semantics.syntacticCat semantics.MPPC_poset categoryTheory.CCC category_theory.category.preorder category_theory.monad.basic
-- open category_theory

open MPPC_defn
open MPPC_defn.MPPC_derives
open MPPC_synPoset
open synCat


open specialCats

instance ℂ_MPPC : thin_cat MPPC_eq := syn_cat

namespace ℂ_MPPC_tactics

def Form : Type := MPPC_Form
def Der : has_derives Form := MPPC_Der
/-
Tactic for doing constructions in ℂ_MPPC which are actually just
the derivation rules of the natural deduction calculus lifted onto
equivalence classes
Input should be of the form `[ apply XXX ]
where XXX is a rule of MPPC_Der
-/
meta def lift_derive_ℂ_MPPC (numobjs nummorphs : nat) : tactic unit → tactic unit :=
  @synCat_tactics.lift_derive_syn_cat Form Der numobjs nummorphs

meta def trace_goal : string → tactic unit :=
  synPoset_tactics.trace_goal

end ℂ_MPPC_tactics

open ℂ_MPPC_tactics

-- ℂ_MPPC has finite products
instance : FP_cat MPPC_eq :=
{
  unit := syn_obj MPPC_Form.top,
  term := by lift_derive_ℂ_MPPC 1 0 `[ apply truth ], -- φ ⊢ ⊤
  unit_η := λ X f, by apply thin_cat.K,
  prod := (&⁼),
  pr1 := by lift_derive_ℂ_MPPC 2 0 `[ apply and_eliml ], -- φ & ψ ⊢ φ
  pr2 := by lift_derive_ℂ_MPPC 2 0 `[ apply and_elimr ], -- φ & ψ ⊢ ψ
                -- If θ ⊢ φ and θ ⊢ ψ, then θ ⊢ φ & ψ
  pair := by lift_derive_ℂ_MPPC 3 2 `[ apply and_intro ],
  prod_β1 := λ X Y Z f g, by apply thin_cat.K,
  prod_β2 := λ X Y Z f g, by apply thin_cat.K,
  prod_η :=  λ X Y, by apply thin_cat.K,
}

-- ℂ_MPPC is a cartesian closed category
instance : CC_cat MPPC_eq := 
{
  exp := (⊃⁼),
  eval := by lift_derive_ℂ_MPPC 2 0 `[ 
                -- φ⊃ψ & φ ⊢ ψ
                trace_goal "eval0",
                apply MPPC_derives_x.union_Hyp_and,
                trace_goal "eval1",
                apply MPPC_derives_x.modus_ponens,
                trace_goal "eval2" ],
  curry := by lift_derive_ℂ_MPPC 3 1 `[ 
                -- If φ & ψ ⊢ θ, then φ ⊢ ψ ⊃ θ
                trace_goal "curry0",
                apply impl_intro,
                trace_goal "curry1",
                apply MPPC_derives_x.and_Hyp_union,
                trace_goal "curry2" ],
  curry_β := λ {X Y Z} u, by apply thin_cat.K,
  curry_η := λ {X Y Z} v, by apply thin_cat.K,
}

-- The ◇ modality defines a monad on ℂ_MPPC 
def diamond_monad : category_theory.monad MPPC_eq := {
  obj := diamond_eq,
  map := by lift_derive_ℂ_MPPC 2 1 `[ apply dmap ],
  η'  := ⟨
          by lift_derive_ℂ_MPPC 1 0 `[ apply dpure ],
          λ X Y f, by apply thin_cat.K,
         ⟩,
  μ' :=  ⟨ 
          by lift_derive_ℂ_MPPC 1 0 `[ apply djoin ],
          λ X Y f, by apply thin_cat.K,
         ⟩,
}