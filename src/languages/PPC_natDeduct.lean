import languages.deductive data.set.basic

-- open deductiveCalc

namespace PPC_defn

inductive PPC_Form : Type
  | top : PPC_Form
  | var : ℕ → PPC_Form
  | and : PPC_Form → PPC_Form → PPC_Form
  | impl : PPC_Form → PPC_Form → PPC_Form


notation (name:=PPC.top) `⊤`:80   := PPC_Form.top
prefix `p`:80     := PPC_Form.var
infix `&`:79      := PPC_Form.and    
notation (name:= PPC_Form.impl) φ `⊃`:80 ψ := PPC_Form.impl φ ψ 


@[reducible] def PPC_Hyp : Type := set (PPC_Form)

instance : has_union PPC_Hyp := 
{
    union := λ X Y, { φ | φ∈X ∨ φ∈Y}
}
instance : has_singleton PPC_Form PPC_Hyp := infer_instance
instance : has_mem PPC_Form PPC_Hyp := infer_instance

instance : has_insert PPC_Form PPC_Hyp := infer_instance

meta def find_it : tactic unit :=
    `[ repeat {{left,refl} <|> right}, try{apply set.mem_singleton}  ]

lemma insert_is_union_singleton : ∀ (Φ : PPC_Hyp) (φ : PPC_Form),
    insert φ Φ = Φ ∪ {φ} :=
    begin
      assume Φ φ,
      apply set.ext,
      assume ψ,
      apply or_comm,
    end
-- notation (name:=Hinsert) Φ `U` φ :=  insert φ Φ

inductive PPC_derives : PPC_Hyp → PPC_Form → Prop 
  | hyp {Φ : PPC_Hyp} (φ : PPC_Form) (φ ∈ Φ)    : PPC_derives Φ φ
  | truth {Φ}                               : PPC_derives Φ ⊤ 
  | and_intro {Φ} {φ ψ : PPC_Form}    
      : PPC_derives Φ φ → PPC_derives Φ ψ → PPC_derives Φ (φ & ψ)
  | and_eliml {Φ} {φ ψ : PPC_Form}    
      : PPC_derives Φ (φ & ψ) → PPC_derives Φ φ
  | and_elimr {Φ} {φ ψ : PPC_Form}    
      : PPC_derives Φ (φ & ψ) → PPC_derives Φ ψ
  | impl_intro {Φ : PPC_Hyp} (φ : PPC_Form) {ψ : PPC_Form}   
      : PPC_derives (insert φ Φ) ψ → PPC_derives Φ (φ ⊃ ψ)
  | impl_elim {Φ : PPC_Hyp} (φ : PPC_Form) {ψ : PPC_Form} 
      : PPC_derives Φ (φ ⊃ ψ) → PPC_derives Φ φ → PPC_derives Φ ψ
  | weak {Φ Ψ : PPC_Hyp} {φ : PPC_Form}
      : PPC_derives Φ φ → PPC_derives (Φ ∪ Ψ) φ
open PPC_derives

end PPC_defn




namespace PPC_has_derives

open PPC_defn
open PPC_defn.PPC_derives

lemma internal1_impl : ∀ {φ ψ : PPC_Form}, PPC_derives {ψ} φ → PPC_derives ∅ (ψ ⊃ φ) :=
begin 
    assume φ ψ h,
    apply impl_intro,
    rw set.is_lawful_singleton.insert_emptyc_eq,
    exact h,
end
lemma empty_union : ∀ φ : PPC_Form, {φ} = ∅ ∪ PPC_Hyp.has_singleton.singleton φ :=
begin
    assume φ,
    symmetry,
    apply set.empty_union,
end
lemma weak1 : ∀ (φ ψ : PPC_Form), PPC_derives ∅ ψ → PPC_derives {φ} ψ :=
begin 
    assume φ ψ h,
    rw empty_union,
    apply weak,
    exact h,
end

instance PPC_Der : has_derives PPC_Form :=
⟨ PPC_Hyp , 
  PPC_derives , 
  begin 
    assume φ,
    apply @hyp {φ} φ,
    apply set.mem_singleton,
  end, 
--   sorry
  begin
    assume φ ψ θ hφψ hψθ,
    have helper : PPC_derives {φ} (ψ ⊃ θ), 
    apply weak1,
    apply internal1_impl,
    exact hψθ,
    apply impl_elim,
    exact helper,
    exact hφψ,
  end
⟩ 


end PPC_has_derives

-- --- LEMMAS ---
-- namespace PPC_Hyp_x
-- open PPC_defn

-- lemma union_comm : ∀ Φ Ψ : PPC_Hyp, Φ ∪ Ψ = Ψ ∪ Φ :=
-- begin 
--     assume Φ Ψ,
--     apply funext,
--     assume φ,
--     apply propext,
--     constructor,
--     assume h, cases h,
--     right,
--     exact h,
--     left,
--     exact h,
--     assume h, cases h,
--     right,
--     exact h,
--     left,
--     exact h,
-- end

-- lemma singleton_insert : ∀ φ : PPC_Form, (∅ U φ) = PPC_Hyp.has_singleton.singleton φ :=
-- begin
--     assume φ,
--     dsimp[set.has_singleton,(U),set.has_insert,set.has_emptyc],
--     apply funext,
--     assume ψ,
--     apply propext,
--     constructor,
--     assume h,
--     cases h,
--     cases h,
--     exact h,
--     cases h,
--     assume h,
--     right,
--     cases h,
-- end
--  -- φ ∈ {φ}
-- lemma in_single : ∀ φ : PPC_Form , φ ∈ PPC_Hyp.has_singleton.singleton φ :=
-- begin 
--     assume φ,
--     dsimp[PPC_Hyp.has_singleton,set.has_singleton], refl,
-- end 
-- lemma in_U_φ : ∀ (Φ : PPC_Hyp) (φ : PPC_Form), φ ∈ (Φ U φ) := 
-- begin 
--     assume Φ φ,
--     right,
--     dsimp[PPC_Hyp.has_singleton,set.has_singleton],
--     refl,
-- end 
-- lemma in_U_Φ : ∀ (Φ : PPC_Hyp) (φ ψ : PPC_Form), ψ∈Φ → (ψ ∈ (Φ U φ)) :=
-- begin
--     assume Φ φ ψ h,
--     left,
--     exact h,
-- end
-- lemma just_flip : ∀ φ ψ, ({φ} U ψ) = ({ψ} U φ) :=
-- begin 
--     assume φ ψ,
--     dsimp[set.has_singleton,(U),set.has_insert],
--     apply funext,
--     assume θ,
--     apply propext,
--     constructor,
--     assume h,
--     cases h with isψ isφ,
--     right,
--     exact isψ,
--     left,
--     exact isφ,
--     assume h,
--     cases h with isφ isψ,
--     right,
--     exact isφ,
--     left,
--     exact isψ,
-- end 

-- end PPC_Hyp_x

namespace PPC_derives_x
    open PPC_defn
    open PPC_defn.PPC_derives
    open PPC_has_derives

-- lemma weaksucc : ∀ (Φ : PPC_Hyp) (φ ψ : PPC_Form), PPC_derives Φ ψ → PPC_derives (Φ U φ) ψ :=
-- begin 
--     assume Φ φ ψ h,
--     apply weak,
--     exact h,
-- end
-- lemma internal1_impl : ∀ {φ ψ : PPC_Form}, ψ ⊢ φ → PPC_derives ∅ (ψ ⊃ φ) :=
-- begin 
--     assume φ ψ h,
--     apply impl_intro,
--     rewrite PPC_Hyp_x.singleton_insert,
--     exact h,
-- end
-- lemma refl : ∀ φ : PPC_Form, φ ⊢ φ :=
-- begin
--     intro φ,
--     apply @hyp {φ} φ,
--     apply PPC_Hyp_x.in_single, -- φ ∈ {φ}
-- end
-- lemma trans : ∀ φ ψ θ : PPC_Form, φ ⊢ ψ → ψ ⊢ θ → φ ⊢ θ :=
-- begin 
--     assume φ ψ θ hφψ hψθ,
--     have helper : PPC_derives {φ} (ψ ⊃ θ), 
--     apply weak1,
--     apply internal1_impl,
--     exact hψθ,
--     apply impl_elim,
--     exact helper,
--     exact hφψ,
-- end 


lemma trans_hyp : ∀ (Φ : PPC_Hyp) (φ ψ: PPC_Form), PPC_derives Φ φ → φ ⊢ ψ → PPC_derives Φ ψ :=
begin 
    assume Φ φ ψ hΦφ hφψ,
    have helper : PPC_derives Φ (φ ⊃ ψ),
    apply impl_intro,
    rewrite insert_is_union_singleton, 
    rewrite set.union_comm,
    apply weak,
    exact hφψ,
    apply impl_elim,
    exact helper,
    exact hΦφ,
end 

lemma modus_ponens : ∀ φ ψ : PPC_Form, PPC_derives ({φ⊃ψ}∪{φ}) ψ :=
begin 
    assume φ ψ,
    apply impl_elim,
    apply weak,
    apply PPC_has_derives.PPC_Der.derive_refl,
    rewrite set.union_comm,
    apply weak,
    apply PPC_has_derives.PPC_Der.derive_refl,
end 

-- -- lemma hypo_syll : ∀ φ ψ θ, (φ ⊃ ψ) ⊢ ((ψ ⊃ θ) ⊃ (φ ⊃ θ)) := sorry

lemma hypo_syll' : ∀ φ ψ θ, (ψ ⊃ θ) ⊢ ((φ ⊃ ψ) ⊃ (φ ⊃ θ)) :=
begin 
    assume φ ψ θ,
    apply impl_intro,
    apply impl_intro,
    apply impl_elim ψ,
    apply hyp (ψ ⊃ θ), find_it,
    apply impl_elim φ,
    apply hyp (φ⊃ψ), find_it,
    apply hyp φ, find_it,
end 

-- lemma union_Hyp_and : ∀ φ ψ θ : PPC_Form, PPC_derives ({φ}∪{ψ}) θ → ((φ&ψ) ⊢ θ) :=
-- begin 
--     assume φ ψ θ h,
--     apply impl_elim,
--     apply impl_elim,
--     apply weak1,
--     apply impl_intro,
--     rewrite PPC_Hyp_x.singleton_insert,
--     apply impl_intro,
--     exact h,
--     apply and_eliml,
--     apply PPC_derives_x.refl,
--     apply and_elimr,
--     apply PPC_derives_x.refl,
-- end 

-- lemma and_Hyp_union : ∀ φ ψ θ : PPC_Form, ((φ&ψ) ⊢ θ) → PPC_derives ({φ}∪{ψ}) θ :=
-- begin 
--     assume φ ψ θ h,
--     apply impl_elim,
--     apply weak,
--     apply weak1,
--     apply internal1_impl,
--     exact h,
--     apply and_intro,
--     apply weak,
--     apply PPC_derives_x.refl,
--     rewrite PPC_Hyp_x.union_comm,
--     apply PPC_derives.weak,
--     apply PPC_derives_x.refl,
-- end 

end PPC_derives_x