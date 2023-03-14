import semantics.syntacticCat semantics.syntacticPoset_cartesian categoryTheory.CCC category_theory.monad.basic

open deduction_cart
open synPoset_cartesian
open synCat
open specialCats

namespace synCat_cartesian

instance syn_FP_cat {Form : Type} [And : has_and Form] : FP_cat (Form _eq) :=
{
  unit := syn_obj And.top,
  term := by LiftT `[ apply And.truth ],
  unit_η := λ X f, by apply thin_cat.K,
  prod := and_eq,
  pr1 := by LiftT `[ apply And.and_eliml ],
  pr2 := by LiftT `[ apply And.and_elimr ],
  pair := by LiftT `[ apply And.and_intro ],
  prod_β1 := λ X Y Z f g, by apply thin_cat.K,
  prod_β2 := λ X Y Z f g, by apply thin_cat.K,
  prod_η :=  λ X Y, by apply thin_cat.K
}
instance syn_CC_cat {Form : Type} [Impl : has_impl Form] : CC_cat (Form _eq) :=
{
  exp := impl_eq,
  eval := by LiftT `[ apply cart_x.modus_ponens ],
  curry := by LiftT `[ apply cart_x.impl_ε],
  curry_β := λ {X Y Z} u, by apply thin_cat.K,
  curry_η := λ {X Y Z} v, by apply thin_cat.K,
}

end synCat_cartesian

/- Instances -/
namespace PPC_synCat

  open synPoset
  open PPC_defn
  open synPoset_cartesian
  open PPC_synPoset

  def ℂ_PPC : thin_cat PPC_eq := syn_cat 
  instance : FP_cat PPC_eq := synCat_cartesian.syn_FP_cat
  instance : CC_cat PPC_eq := synCat_cartesian.syn_CC_cat

end PPC_synCat

namespace MPPC_synCat

  open synPoset
  open MPPC_defn
  open synPoset_cartesian
  open MPPC_synPoset
  open MPPC_defn.MPPC_derives
  open MPPC_has_derives

  def ℂ_MPPC : thin_cat MPPC_eq := syn_cat 
  instance : FP_cat MPPC_eq := synCat_cartesian.syn_FP_cat
  instance : CC_cat MPPC_eq := synCat_cartesian.syn_CC_cat
-- def derive_refl := MPPC_has_derives.MPPC_Der.derive_refl
  -- The ◇ modality defines a monad on ℂ_MPPC 
def diamond_monad : category_theory.monad MPPC_eq := {
  obj := diamond_eq,
  map := 
    begin
      HeavyLiftT? MPPC_Form MPPC_has_derives.MPPC_Der `[ skip ],
      -- apply @dmap φ_0 φ_1, -- WHY???
      sorry,
      thin_cat.by_thin,
    end,
  η'  := ⟨
          by HeavyLiftT MPPC_Form MPPC_has_derives.MPPC_Der `[ apply dpure ],
          λ X Y f, by apply thin_cat.K,
         ⟩,
  μ' :=  ⟨ 
          by HeavyLiftT MPPC_Form MPPC_has_derives.MPPC_Der `[ apply djoin ],
          λ X Y f, by apply thin_cat.K,
         ⟩,
}

end MPPC_synCat

