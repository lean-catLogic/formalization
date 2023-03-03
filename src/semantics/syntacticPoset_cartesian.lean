import semantics.syntacticPoset deduction.deduction_cartesian deduction.PPC_natDeduct deduction.MPPC_natDeduct

namespace synPoset_cartesian

open synPoset
open deduction_basic
open deduction_cart

variable {Form : Type}

  -- ⊤ : Form_eq
  instance [Der : has_ltop Form] : has_top (Form _eq) := ⟨ ⦃Der.top⦄ ⟩ 

  lemma and_liftable1 [Der : has_and Form] : 
    ∀ φ ψ ψ' : Form, (ψ ⊣⊢ ψ') → ⦃φ & ψ⦄ = ⦃φ & ψ'⦄ :=
  begin
    assume φ ψ ψ' h,
    apply quotient.sound,
    cases h with ψψ' ψ'ψ,
    split,
    -- Proof that φ&ψ ⊢ φ&ψ'
      apply Der.and_intro,
      apply cart_x.and_eliml1,
      apply derive_trans,
      apply cart_x.and_elimr1,
      exact ψψ',
    -- Proof that φ&ψ' ⊢ φ&ψ
      apply Der.and_intro,
      apply cart_x.and_eliml1,
      apply derive_trans,
      apply cart_x.and_elimr1,
      exact ψ'ψ,
  end

  lemma and_liftable2 [Der : has_and Form] :
    ∀ φ φ' ψ : Form, (φ ⊣⊢ φ') → ⦃φ & ψ⦄ = ⦃φ' & ψ⦄ := 
  begin
      assume φ φ' ψ h,
      apply quotient.sound,
      cases h with φφ' φ'φ,
      split,
      -- Proof that φ&ψ ⊢ φ'&ψ
        apply Der.and_intro,
        apply derive_trans,
        apply cart_x.and_eliml1,
        exact φφ',
        apply cart_x.and_elimr1,
      -- Proof that φ'&ψ ⊢ φ&ψ
        apply Der.and_intro,
        apply derive_trans,
        apply cart_x.and_eliml1,
        exact φ'φ,
        apply cart_x.and_elimr1,
  end

  def and_eq [Der : has_and Form] : Form _eq → Form _eq → Form _eq :=
    quot.lift₂ (λ φ ψ, ⦃φ & ψ⦄) (@and_liftable1 Form Der) and_liftable2 

  -- ⊓ : Form_eq → Form_eq → Form_eq
  instance [Der : has_and Form] : has_inf (Form _eq) := ⟨ and_eq ⟩ 



  lemma impl_liftable1 [Der : has_impl Form] : 
    ∀ φ ψ ψ' : Form, (ψ ⊣⊢ ψ') → ⦃φ ⊃ ψ⦄ = ⦃φ ⊃ ψ'⦄ :=
  begin 
      assume φ ψ ψ' h,
      apply quotient.sound,
      cases h with ψψ' ψ'ψ,
      constructor,
      -- Proof that φ ⊃ ψ ⊢ φ ⊃ ψ'
        apply Der.impl_intro,
        apply Der.derive_Trans ψ,
        apply cart_x.and_internal,
        exact cart_x.modus_ponens,
        exact ψψ',
      -- Proof that φ ⊃ ψ' ⊢ φ ⊃ ψ
        apply Der.impl_intro,
        apply Der.derive_Trans ψ',
        apply cart_x.and_internal,
        exact cart_x.modus_ponens,
        exact ψ'ψ,
  end 

  lemma impl_liftable2 [Der : has_impl Form] : 
    ∀ φ φ' ψ : Form, (φ ⊣⊢ φ') → ⦃φ ⊃ ψ⦄ = ⦃φ' ⊃ ψ⦄ := 
  begin 
      assume φ φ' ψ h,
      apply quotient.sound,
      cases h with φφ' φ'φ,
      constructor,
      -- Proof that φ ⊃ ψ ⊢ φ' ⊃ ψ
        apply Der.impl_intro,
        apply Der.impl_elim φ,
        apply Der.weak1,
        apply derive_refl,
        apply cart_x.insert_trans,
        exact φ'φ,
      -- Proof that φ' ⊃ ψ ⊢ φ ⊃ ψ
        apply Der.impl_intro,
        apply Der.impl_elim φ',
        apply Der.weak1,
        apply derive_refl,
        apply cart_x.insert_trans,
        exact φφ',
  end 


  def impl_eq [Der : has_impl Form] : Form _eq → Form _eq → Form _eq :=
    quot.lift₂ (λ φ ψ, ⦃φ ⊃ ψ⦄) (@impl_liftable1 Form Der) impl_liftable2 

  -- ⇨ : Form_eq → Form_eq → Form_eq
  instance [Der : has_impl Form] : has_himp (Form _eq) := ⟨ impl_eq ⟩ 

end synPoset_cartesian

/- Instances -/
namespace PPC_synPoset 

  open synPoset
  open PPC_defn
  open synPoset_cartesian

  def PPC_eq := @Form_eq PPC_Form PPC_has_derives.PPC_Der

end PPC_synPoset

namespace MPPC_synPoset 

  open synPoset
  open MPPC_defn
  open synPoset_cartesian

  def MPPC_eq := @Form_eq MPPC_Form MPPC_has_derives.MPPC_Der

end MPPC_synPoset