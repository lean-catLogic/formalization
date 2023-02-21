import semantics.syntacticPoset languages.PPC_natDeduct

namespace PPC_synPoset

open PPC_defn
open PPC_defn.PPC_derives
open PPC_has_derives
open synPoset

def PPC_Der := PPC_has_derives.PPC_Der
def derive_refl := PPC_Der.derive_refl
def derive_trans := PPC_Der.derive_trans

def PPC_eq := @Form_eq PPC_Form PPC_Der

lemma and_liftable1 : ∀ φ ψ ψ' : PPC_Form, 
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

lemma and_liftable2 : ∀ φ φ' ψ : PPC_Form, 
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

lemma impl_liftable1 : ∀ φ ψ ψ' : PPC_Form, 
  (ψ ⊣⊢ ψ') → ⦃φ ⊃ ψ⦄ = ⦃φ ⊃ ψ'⦄ :=
begin 
    assume φ ψ ψ' h,
    apply quotient.sound,
    cases h with ψψ' ψ'ψ,
    constructor,
      apply impl_intro,
      apply PPC_derives_x.trans_hyp,
      rw PPC_Hyp_x.insert_is_union_singleton,
      apply PPC_derives_x.modus_ponens,
      exact ψψ',
      apply impl_intro,
      apply PPC_derives_x.trans_hyp,
      rw PPC_Hyp_x.insert_is_union_singleton,
      apply PPC_derives_x.modus_ponens,
      exact ψ'ψ,
end 

lemma impl_liftable2 : ∀ φ φ' ψ : PPC_Form, 
  (φ ⊣⊢ φ') → ⦃φ ⊃ ψ⦄ = ⦃φ' ⊃ ψ⦄ := 
begin 
    assume φ φ' ψ h,
    apply quotient.sound,
    cases h with φφ' φ'φ,
    constructor,
      apply impl_elim,
      apply PPC_derives_x.hypo_syll',
      apply impl_intro,
      apply weak,
      exact φ'φ,
      ---
      apply impl_elim,
      apply PPC_derives_x.hypo_syll',
      apply impl_intro,
      apply weak,
      exact φφ',
end 


def impl_eq : PPC_eq → PPC_eq → PPC_eq :=
  quot.lift₂ (λ φ ψ, ⦃φ ⊃ ψ⦄) impl_liftable1 impl_liftable2 

notation (name := impl_eq) X `⊃⁼` Y := impl_eq X Y

end PPC_synPoset