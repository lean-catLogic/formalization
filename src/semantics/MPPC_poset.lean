import semantics.syntacticPoset deduction.MPPC_natDeduct

namespace MPPC_synPoset

open MPPC_defn
open MPPC_defn.MPPC_derives
open MPPC_has_derives
open synPoset

def MPPC_Der := MPPC_has_derives.MPPC_Der
def derive_refl := MPPC_Der.derive_refl
def derive_trans := MPPC_Der.derive_trans

def MPPC_eq := @Form_eq MPPC_Form MPPC_Der

lemma and_liftable1 : ∀ φ ψ ψ' : MPPC_Form, 
  (ψ ⊣⊢ ψ') → ⦃φ & ψ⦄ = ⦃φ & ψ'⦄ :=
  begin
    assume φ ψ ψ' h,
    apply quotient.sound,
    cases h with ψψ' ψ'ψ,
    constructor,
    -- Proof that φ&ψ ⊢ φ&ψ'
      apply and_intro,
      -- φ&ψ ⊢ φ
      apply and_eliml,
      apply derive_refl, -- φ&ψ ⊢ φ&ψ
      -- φ&ψ ⊢ ψ'
      apply derive_trans,
      apply and_elimr,
      apply derive_refl, -- φ&ψ ⊢ φ&ψ
      exact ψψ',
    -- Proof that φ&ψ' ⊢ φ&ψ
      apply and_intro,
      -- φ&ψ ⊢ φ
      apply and_eliml,
      apply derive_refl, -- φ&ψ' ⊢ φ&ψ'
      -- φ&ψ' ⊢ ψ
      apply derive_trans,
      apply and_elimr,
      apply derive_refl, -- φ&ψ' ⊢ φ&ψ'
      exact ψ'ψ,
end

lemma and_liftable2 : ∀ φ φ' ψ : MPPC_Form, 
  (φ ⊣⊢ φ') → ⦃φ & ψ⦄ = ⦃φ' & ψ⦄ := 
begin
    assume φ φ' ψ h,
    apply quotient.sound,
    cases h with φφ' φ'φ,
    constructor,
    -- Proof that φ&ψ ⊢ φ'&ψ
      apply and_intro,
      apply derive_trans,
      apply and_eliml,
      apply derive_refl, -- φ&ψ ⊢ φ&ψ
      exact φφ',
      apply and_elimr,
      apply derive_refl, -- φ&ψ ⊢ φ&ψ
    -- Proof that φ'&ψ ⊢ φ&ψ
      apply and_intro,
      apply derive_trans,
      apply and_eliml,
      apply derive_refl, -- φ'&ψ ⊢ φ'&ψ
      exact φ'φ,
      apply and_elimr,
      apply derive_refl, -- φ'&ψ ⊢ φ'&ψ
end

def and_eq : Form_eq → Form_eq → Form_eq :=
  quot.lift₂ (λ φ ψ, ⦃φ & ψ⦄) and_liftable1 and_liftable2 

notation (name := and_eq) X `&⁼` Y := and_eq X Y

lemma impl_liftable1 : ∀ φ ψ ψ' : MPPC_Form, 
  (ψ ⊣⊢ ψ') → ⦃φ ⊃ ψ⦄ = ⦃φ ⊃ ψ'⦄ :=
begin 
    assume φ ψ ψ' h,
    apply quotient.sound,
    cases h with ψψ' ψ'ψ,
    constructor,
      apply impl_intro,
      apply MPPC_derives_x.trans_hyp,
      rw MPPC_Hyp_x.insert_is_union_singleton,
      apply MPPC_derives_x.modus_ponens,
      exact ψψ',
      apply impl_intro,
      apply MPPC_derives_x.trans_hyp,
      rw MPPC_Hyp_x.insert_is_union_singleton,
      apply MPPC_derives_x.modus_ponens,
      exact ψ'ψ,
end 

lemma impl_liftable2 : ∀ φ φ' ψ : MPPC_Form, 
  (φ ⊣⊢ φ') → ⦃φ ⊃ ψ⦄ = ⦃φ' ⊃ ψ⦄ := 
begin 
    assume φ φ' ψ h,
    apply quotient.sound,
    cases h with φφ' φ'φ,
    constructor,
      apply impl_elim,
      apply MPPC_derives_x.hypo_syll',
      apply impl_intro,
      apply weak,
      exact φ'φ,
      ---
      apply impl_elim,
      apply MPPC_derives_x.hypo_syll',
      apply impl_intro,
      apply weak,
      exact φφ',
end 


def impl_eq : MPPC_eq → MPPC_eq → MPPC_eq :=
  quot.lift₂ (λ φ ψ, ⦃φ ⊃ ψ⦄) impl_liftable1 impl_liftable2 

notation (name := impl_eq) X `⊃⁼` Y := impl_eq X Y


lemma diamond_liftable : ∀ φ φ' : MPPC_Form,
  (φ ⊣⊢ φ') → ⦃◇φ⦄ = ⦃◇φ'⦄ :=
  begin
    assume φ φ' h,
    apply quotient.sound,
    cases h with φφ' φ'φ,
    constructor,
    apply dmap,
    exact φφ',
    apply dmap,
    exact φ'φ,
  end

def diamond_eq : MPPC_eq → MPPC_eq :=
  quot.lift (λ φ , ⦃◇φ⦄) diamond_liftable

notation (name := diamond_eq) `◇⁼` X := diamond_eq X


end MPPC_synPoset
