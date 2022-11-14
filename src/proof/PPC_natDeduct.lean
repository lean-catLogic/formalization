import languages.PPC --data.set.basic

@[reducible] def Hyp : Type := set(PPC_form)

instance : has_union Hyp := 
{
    union := λ X Y, { φ | φ∈X ∨ φ∈Y}
}
instance : has_singleton PPC_form Hyp := {singleton := λ φ, {φ}}
instance : has_mem PPC_form Hyp := { mem := λ φ Φ, φ ∈ Φ}

def Hinsert (Φ : Hyp) (φ : PPC_form) : Hyp := Φ ∪ {φ}
notation (name:=Hinsert) Φ `U` φ := Hinsert Φ φ


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
  | weak {Φ Ψ : Hyp} {φ : PPC_form}
      : derives Φ φ → derives (Φ ∪ Ψ) φ

infix `⊢`:80 := λ φ ψ, derives {φ} ψ


--- LEMMAS ---
lemma union_comm : ∀ Φ Ψ : Hyp, Φ ∪ Ψ = Ψ ∪ Φ :=
begin 
    assume Φ Ψ,
    apply funext,
    assume φ,
    apply propext,
    constructor,
    assume h, cases h,
    right,
    exact h,
    left,
    exact h,
    assume h, cases h,
    right,
    exact h,
    left,
    exact h,
end
lemma weak1 : ∀ (Φ : Hyp) (φ ψ : PPC_form), derives Φ φ → derives (Φ U ψ) φ :=
begin 
    assume Φ φ ψ h,
    apply derives.weak,
    exact h,
end 

lemma singleton_insert : ∀ φ : PPC_form, (∅ U φ) = {φ} :=
begin
    assume φ,
    dsimp[set.has_singleton,(U),set.has_insert,set.has_emptyc],
    apply funext,
    assume ψ,
    apply propext,
    constructor,
    assume h,
    cases h,
    cases h,
    exact h,
    assume h,
    right,
    exact h,
end

lemma in_U_φ : ∀ (Φ : Hyp) (φ : PPC_form), φ ∈ (Φ U φ) := 
begin 
    assume Φ φ,
    right,
    dsimp[Hyp.has_singleton,set.has_singleton],
    refl,
end 
lemma in_U_Φ : ∀ (Φ : Hyp) (φ ψ : PPC_form), ψ∈Φ → (ψ ∈ (Φ U φ)) :=
begin
    assume Φ φ ψ h,
    left,
    exact h,
end
lemma just_flip : ∀ φ ψ, ({φ} U ψ) = ({ψ} U φ) :=
begin 
    assume φ ψ,
    dsimp[set.has_singleton,(U),set.has_insert],
    apply funext,
    assume θ,
    apply propext,
    constructor,
    assume h,
    cases h with isψ isφ,
    right,
    exact isψ,
    left,
    exact isφ,
    assume h,
    cases h with isφ isψ,
    right,
    exact isφ,
    left,
    exact isψ,
end 

lemma derive_refl : ∀ φ : PPC_form, φ ⊢ φ :=
begin
    assume φ,
    apply derives.hyp,
    exact φ,
    dsimp[Hyp.has_singleton,set.has_singleton],
    refl,
end
lemma derive_trans : ∀ φ ψ θ : PPC_form, φ ⊢ ψ → ψ ⊢ θ → φ ⊢ θ :=
begin 
    assume φ ψ θ hφψ hψθ,
    have helper : derives {φ} (ψ ⊃ θ), 
    rewrite← singleton_insert,
    apply derives.weak,
    apply derives.impl_intro,
    rewrite singleton_insert,
    exact hψθ,
    apply derives.impl_elim,
    exact helper,
    exact hφψ,
end 
lemma derive_trans_hyp : ∀ (Φ : Hyp) (φ ψ: PPC_form), derives Φ φ → φ ⊢ ψ → derives Φ ψ :=
begin 
    -- sorry
    assume Φ φ ψ hΦφ hφψ,
    have helper : derives Φ (φ ⊃ ψ),
    apply derives.impl_intro,
    dsimp[(U)],
    rewrite union_comm,
    apply derives.weak,
    exact hφψ,
    apply derives.impl_elim,
    exact helper,
    exact hΦφ,
end 

lemma modus_ponens : ∀ φ ψ : PPC_form, derives ({φ⊃ψ}∪{φ}) ψ :=
begin 
    assume φ ψ,
    apply derives.impl_elim,
    apply derives.weak,
    apply derive_refl,
    rewrite union_comm,
    apply derives.weak,
    apply derive_refl,
end 

-- lemma hypo_syll : ∀ φ ψ θ, (φ ⊃ ψ) ⊢ ((ψ ⊃ θ) ⊃ (φ ⊃ θ)) := sorry

lemma hypo_syll' : ∀ φ ψ θ, (ψ ⊃ θ) ⊢ ((φ ⊃ ψ) ⊃ (φ ⊃ θ)) :=
begin 
    assume φ ψ θ,
    apply derives.impl_intro,
    apply derives.impl_intro,
    apply derives.impl_elim,
    apply @derives.hyp ({ψ⊃θ} U φ⊃ψ U φ) (ψ ⊃ θ) (ψ ⊃ θ),
    apply in_U_Φ, apply in_U_Φ, rewrite← singleton_insert, apply in_U_φ,
    apply derives.impl_elim,
    apply derives.weak,
    apply @derives.hyp ({ψ⊃θ} U φ⊃ψ) (φ⊃ψ) (φ⊃ψ),
    apply in_U_φ,
    apply @derives.hyp ({ψ⊃θ} U φ⊃ψ U φ) (φ) (φ),
    apply in_U_φ,
end 

lemma union_Hyp_and : ∀ φ ψ θ : PPC_form, derives ({φ}∪{ψ}) θ → ((φ&ψ) ⊢ θ) :=
begin 
    assume φ ψ θ h,
    apply derives.impl_elim,
    apply derives.impl_elim,
    rewrite← singleton_insert,
    apply derives.weak,
    apply derives.impl_intro,
    rewrite singleton_insert,
    apply derives.impl_intro,
    exact h,
    apply derives.and_eliml,
    apply derive_refl,
    apply derives.and_elimr,
    apply derive_refl,
end 

lemma and_Hyp_union : ∀ φ ψ θ : PPC_form, ((φ&ψ) ⊢ θ) → derives ({φ}∪{ψ}) θ :=
begin 
    assume φ ψ θ h,
    apply derives.impl_elim,
    apply derives.weak,
    rewrite← singleton_insert,
    apply derives.weak,
    apply derives.impl_intro,
    rewrite singleton_insert,
    exact h,
    apply derives.and_intro,
    apply derives.weak,
    apply derive_refl,
    rewrite union_comm,
    apply derives.weak,
    apply derive_refl,
end 