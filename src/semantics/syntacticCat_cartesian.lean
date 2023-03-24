import semantics.syntacticCat semantics.syntacticPoset_cartesian categoryTheory.CCC category_theory.monad.basic

open deduction_cart
open deduction_monadic
open synPoset_cartesian
open synPoset_monadic
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

namespace synCat_monadic

-- instance syn_CC_cat_monad {Form : Type} [Diam : has_diamond Form] : 

def diamond_monad {Form : Type} [Diam : has_diamond Form] : category_theory.monad (Form _eq) := 
{
  obj := diamond_eq,
  map := by LiftT `[ apply Diam.dmap ],
  η'  := ⟨
          by LiftT `[ apply Diam.dpure ], 
          λ X Y f, by apply thin_cat.K,
         ⟩,
  μ' :=  ⟨ 
          by LiftT `[ apply Diam.djoin ],
          λ X Y f, by apply thin_cat.K,
         ⟩,
}
end synCat_monadic

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
  def ℂ_MPPC_diamond : category_theory.monad MPPC_eq := synCat_monadic.diamond_monad

end MPPC_synCat

