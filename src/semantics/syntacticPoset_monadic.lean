import semantics.syntacticCat_cartesian


namespace synPoset_monadic

open synPoset
open deduction_basic
open deduction_cart
open deduction_monadic

variable {Form : Type}


lemma diamond_liftable [Der : has_diamond Form] : ∀ φ φ' : Form,
  (φ ⊣⊢ φ') → ⦃ ◇φ ⦄ = ⦃◇φ'⦄ :=
  begin
    assume φ φ' h,
    apply quotient.sound,
    cases h with φφ' φ'φ,
    split,
    apply Der.dmap,
    exact φφ',
    apply Der.dmap,
    exact φ'φ,
  end

def diamond_eq [Der : has_diamond Form] : Form _eq → Form _eq :=
  quot.lift (λ φ , ⦃Der.diamond φ⦄) diamond_liftable

end synPoset_monadic
