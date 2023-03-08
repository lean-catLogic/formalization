import generalTactics semantics.syntacticPoset_cartesian semantics.syntacticCat  semantics.syntacticCat_cartesian category_theory.monad.basic
-- open category_theory

open MPPC_defn
open MPPC_defn.MPPC_derives
open MPPC_synPoset
open synCat
open specialCats

-- The ◇ modality defines a monad on ℂ_MPPC 
def diamond_monad : category_theory.monad MPPC_eq := {
  obj := diamond_eq,
  map := by lift_derive_syn_cat 2 1 `[ apply dmap ],
  η'  := ⟨
          by lift_derive_syn_cat 1 0 `[ apply dpure ],
          λ X Y f, by apply thin_cat.K,
         ⟩,
  μ' :=  ⟨ 
          by lift_derive_syn_cat 1 0 `[ apply djoin ],
          λ X Y f, by apply thin_cat.K,
         ⟩,
}