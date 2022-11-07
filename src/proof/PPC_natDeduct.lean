import languages.PPC

@[reducible] def Hyp : Type := set(PPC_form)

notation (name:=set.insert) Φ `U` φ := insert φ Φ

inductive derives : Hyp → PPC_form → Prop 
  | hyp {Φ} {φ : PPC_form} (φ ∈ Φ)    : derives Φ φ
  | truth {Φ}                         : derives Φ ⊤ 
  | and_intro {Φ} {φ ψ : PPC_form}    
      : derives Φ φ → derives Φ ψ → derives Φ (φ & ψ)
  | and_eliml {Φ} {φ ψ : PPC_form}    
      : derives Φ (φ & ψ) → derives Φ φ
  | and_elimr {Φ} {φ ψ : PPC_form}    
      : derives Φ (φ & ψ) → derives Φ ψ
  | impl_intro {Φ : Hyp} {φ ψ : PPC_form}   
      : derives (Φ U φ) ψ → derives Φ (φ ⊃ ψ)
  | impl_elim {Φ : Hyp} {φ ψ : PPC_form} 
      : derives Φ (φ ⊃ ψ) → derives Φ φ → derives Φ ψ
  | weak {Φ} {φ ψ : PPC_form}
      : derives Φ φ → derives (Φ U ψ) φ

def just : PPC_form → Hyp := singleton
infix `⊢`:80 := λ φ ψ, derives (just φ) ψ


--- LEMMAS ---
lemma singleton_insert : ∀ φ : PPC_form, (∅ U φ) = (just φ) :=
begin
    assume φ,
    dsimp[just,set.has_singleton,(U),set.has_insert,set.has_emptyc],
    apply funext,
    assume ψ,
    apply propext,
    constructor,
    assume h,
    cases h,
    exact h,
    cases h,
    assume h,
    left,
    exact h,
end

lemma derive_refl : ∀ φ : PPC_form, φ ⊢ φ :=
begin
    assume φ,
    apply derives.hyp,
    exact φ,
    dsimp[just,set.has_singleton],
    refl,
end
lemma derive_trans : ∀ φ ψ θ : PPC_form, φ ⊢ ψ → ψ ⊢ θ → φ ⊢ θ :=
begin 
    assume φ ψ θ hφψ hψθ,
    have helper : derives (just φ) (ψ ⊃ θ), 
    rewrite← singleton_insert,
    apply derives.weak,
    apply derives.impl_intro,
    rewrite singleton_insert,
    exact hψθ,
    apply derives.impl_elim,
    exact helper,
    exact hφψ,
end 
