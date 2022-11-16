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
--


--- LEMMAS ---
namespace Hyp_x
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
 -- φ ∈ {φ}
lemma in_single : ∀ φ : PPC_form , φ ∈ Hyp.has_singleton.singleton φ :=
begin 
    assume φ,
    dsimp[Hyp.has_singleton,set.has_singleton], refl,
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

end Hyp_x

namespace derives_x

    open derives

lemma weaksucc : ∀ (Φ : Hyp) (φ ψ : PPC_form), derives Φ ψ → derives (Φ U φ) ψ :=
begin 
    assume Φ φ ψ h,
    apply weak,
    exact h,
end
lemma weak1 : ∀ (φ ψ : PPC_form), derives ∅ ψ → φ ⊢ ψ :=
begin 
    assume φ ψ h,
    rewrite← Hyp_x.singleton_insert,
    apply weak,
    exact h,
end
lemma internal1_impl : ∀ {φ ψ : PPC_form}, ψ ⊢ φ → derives ∅ (ψ ⊃ φ) :=
begin 
    assume φ ψ h,
    apply impl_intro,
    rewrite Hyp_x.singleton_insert,
    exact h,
end
lemma refl : ∀ φ : PPC_form, φ ⊢ φ :=
begin
    intro φ,
    apply @hyp {φ} φ,
    apply Hyp_x.in_single, -- φ ∈ {φ}
end
lemma trans : ∀ φ ψ θ : PPC_form, φ ⊢ ψ → ψ ⊢ θ → φ ⊢ θ :=
begin 
    assume φ ψ θ hφψ hψθ,
    have helper : derives {φ} (ψ ⊃ θ), 
    apply weak1,
    apply internal1_impl,
    exact hψθ,
    apply impl_elim,
    exact helper,
    exact hφψ,
end 


lemma trans_hyp : ∀ (Φ : Hyp) (φ ψ: PPC_form), derives Φ φ → φ ⊢ ψ → derives Φ ψ :=
begin 
    -- sorry
    assume Φ φ ψ hΦφ hφψ,
    have helper : derives Φ (φ ⊃ ψ),
    apply impl_intro,
    dsimp[(U)],
    rewrite Hyp_x.union_comm,
    apply weak,
    exact hφψ,
    apply impl_elim,
    exact helper,
    exact hΦφ,
end 

lemma modus_ponens : ∀ φ ψ : PPC_form, derives ({φ⊃ψ}∪{φ}) ψ :=
begin 
    assume φ ψ,
    apply impl_elim,
    apply weak,
    apply derives_x.refl,
    rewrite Hyp_x.union_comm,
    apply weak,
    apply derives_x.refl,
end 

-- lemma hypo_syll : ∀ φ ψ θ, (φ ⊃ ψ) ⊢ ((ψ ⊃ θ) ⊃ (φ ⊃ θ)) := sorry

lemma hypo_syll' : ∀ φ ψ θ, (ψ ⊃ θ) ⊢ ((φ ⊃ ψ) ⊃ (φ ⊃ θ)) :=
begin 
    assume φ ψ θ,
    apply impl_intro,
    apply impl_intro,
    apply impl_elim,
    apply @hyp ({ψ⊃θ} U φ⊃ψ U φ) (ψ ⊃ θ) (ψ ⊃ θ),
    -- ψ⊃θ ∈ {ψ⊃θ , φ⊃ψ , φ}
    apply Hyp_x.in_U_Φ, apply Hyp_x.in_U_Φ, rewrite← Hyp_x.singleton_insert, apply Hyp_x.in_U_φ,
    apply impl_elim,
    apply weak,
    apply @hyp ({ψ⊃θ} U φ⊃ψ) (φ⊃ψ) (φ⊃ψ),
    apply Hyp_x.in_U_φ,
    apply @hyp ({ψ⊃θ} U φ⊃ψ U φ) (φ) (φ),
    apply Hyp_x.in_U_φ,
end 

lemma union_Hyp_and : ∀ φ ψ θ : PPC_form, derives ({φ}∪{ψ}) θ → ((φ&ψ) ⊢ θ) :=
begin 
    assume φ ψ θ h,
    apply impl_elim,
    apply impl_elim,
    apply weak1,
    apply impl_intro,
    rewrite Hyp_x.singleton_insert,
    apply impl_intro,
    exact h,
    apply and_eliml,
    apply derives_x.refl,
    apply and_elimr,
    apply derives_x.refl,
end 

lemma and_Hyp_union : ∀ φ ψ θ : PPC_form, ((φ&ψ) ⊢ θ) → derives ({φ}∪{ψ}) θ :=
begin 
    assume φ ψ θ h,
    apply impl_elim,
    apply weak,
    apply weak1,
    apply internal1_impl,
    exact h,
    apply and_intro,
    apply weak,
    apply derives_x.refl,
    rewrite Hyp_x.union_comm,
    apply derives.weak,
    apply derives_x.refl,
end 

end derives_x