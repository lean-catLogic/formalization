import semantics.syntacticCat_cartesian semantics.syntacticPoset_monadic category_theory.monad.basic

open deduction_monadic
open synPoset_monadic

namespace synCat_monadic
 
#check @has_diamond.dmap
#check @has_diamond.dpure
#check @has_diamond.djoin

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
namespace MPPC_monad

  open MPPC_synPoset

  def MPPC_diamond : category_theory.monad MPPC_eq := synCat_monadic.diamond_monad

end MPPC_monad

