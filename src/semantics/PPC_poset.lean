import languages.PPC proof.PPC_natDeduct category_theory.category.preorder

-- ⊢ is a preorder on the set of formulas 
instance PPC_preorder : preorder PPC_form :=
{ le := λ φ ψ, φ ⊢ ψ,
  le_refl := derives_x.refl,
  le_trans := derives_x.trans,
}

-- Inter-derivability is an equivalence relation on formulas
instance PPC_setoid : setoid PPC_form :=
{ r := λ φ ψ, φ ⊢ ψ ∧ ψ ⊢ φ, 
  iseqv := ⟨ begin 
              assume φ, constructor, 
              apply derives_x.refl, apply derives_x.refl 
             end, 
            begin
              assume φ ψ h, cases h with φψ ψφ,
              constructor, exact ψφ, exact φψ,
            end,
            begin 
              assume φ ψ θ j k, cases j with φψ ψφ,
              cases k with ψθ θψ, constructor,
              apply derives_x.trans, exact φψ, exact ψθ,
              apply derives_x.trans, exact θψ, exact ψφ,
            end 
            ⟩ 
} 
notation (name:=PPC_setoid.r) φ `⊣⊢` ψ :78 := PPC_setoid.r φ ψ 

-- Quotienting PPC_form by inter-derivability
def PPC_eq : Type := quot (⊣⊢) 

def PPC_eq_in (φ : PPC_form) : PPC_eq := ⟦φ⟧

notation (name:=PPC_eq_in) ⦃φ⦄ := PPC_eq_in φ

-- Lemmas that ⊢ respects ⊣⊢
lemma PPC_preorder_liftable1 :
  ∀ φ ψ θ : PPC_form, ψ ⊣⊢ θ → (φ ⊢ ψ) = (φ ⊢ θ) :=
begin 
  assume φ ψ θ ψiffθ,
  cases ψiffθ with ψθ θψ,
  apply propext,
  constructor,
  assume φψ, apply derives_x.trans, exact φψ, exact ψθ,
  assume φθ, apply derives_x.trans, exact φθ, exact θψ,
end
lemma PPC_preorder_liftable2 :
  ∀ φ ψ θ : PPC_form, φ ⊣⊢ ψ → (φ ⊢ θ) = (ψ ⊢ θ) :=
begin 
  assume φ ψ θ φiffψ,
  cases φiffψ with φψ ψφ,
  apply propext,
  constructor,
  assume φθ, apply derives_x.trans, exact ψφ, exact φθ,
  assume ψθ, apply derives_x.trans, exact φψ, exact ψθ,
end 


-- Preorder on equivalence classes
def PPC_eq_order   : PPC_eq → PPC_eq → Prop 
  := quot.lift₂ PPC_preorder.le PPC_preorder_liftable1 PPC_preorder_liftable2

/- 
  Helpful lemma to allow us to use the natural deduction calculus
  when working on equivalence classes of formulas
-/
lemma preorder_lift_rewrite (φ ψ : PPC_form) 
  : PPC_eq_order ⦃φ⦄ ⦃ψ⦄ = (φ ⊢ ψ) 
  := begin refl end

--  PPC_form / ⊣⊢ is a poset under PPC_eq_order
instance PPC_poset : partial_order (PPC_eq) :=
{ le := PPC_eq_order,
  le_refl := 
                (begin
                  assume a,
                  induction a with φ, 
                  dsimp[(≤),setoid.r,PPC_eq_order],
                  apply derives_x.refl,refl,
                end),
  le_trans := 
                (begin 
                  assume a b c h j,
                  induction a with φ, induction b with ψ, induction c with θ,
                  dsimp[(≤),setoid.r,PPC_eq_order],
                  dsimp[(≤)] at h, dsimp[(≤)] at j, 
                  apply derives_x.trans,
                  exact h, exact j,
                  refl, refl, refl,
                end),
  le_antisymm := ( 
                begin
                  assume a b h j,
                  induction a with φ, induction b with ψ,
                  apply quotient.sound,
                  dsimp[(≈),setoid.r],dsimp[(≤)] at h, dsimp[(≤)] at j,
                  constructor, exact h, exact j, refl, refl,
                end)
}

lemma and_liftable1 : ∀ φ ψ ψ' : PPC_form, 
  (ψ ⊣⊢ ψ') → ⦃φ & ψ⦄ = ⦃φ & ψ'⦄ :=
begin
    assume φ ψ ψ' h,
    apply quotient.sound,
    cases h with ψψ' ψ'ψ,
    constructor,
    -- Proof that φ&ψ ⊢ φ&ψ'
      apply derives.and_intro,
      -- φ&ψ ⊢ φ
      apply @derives.and_eliml {φ&ψ} φ ψ,
      apply derives_x.refl, -- φ&ψ ⊢ φ&ψ
      -- φ&ψ ⊢ ψ'
      apply derives_x.trans,
      apply @derives.and_elimr {φ&ψ} φ ψ,
      apply derives_x.refl, -- φ&ψ ⊢ φ&ψ
      exact ψψ',
    -- Proof that φ&ψ' ⊢ φ&ψ
      apply derives.and_intro,
      -- φ&ψ ⊢ φ
      apply @derives.and_eliml {φ&ψ'} φ ψ',
      apply derives_x.refl, -- φ&ψ' ⊢ φ&ψ'
      -- φ&ψ' ⊢ ψ
      apply derives_x.trans,
      apply @derives.and_elimr {φ&ψ'} φ ψ',
      apply derives_x.refl, -- φ&ψ' ⊢ φ&ψ'
      exact ψ'ψ,
end

lemma and_liftable2 : ∀ φ φ' ψ : PPC_form, 
  (φ ⊣⊢ φ') → ⦃φ & ψ⦄ = ⦃φ' & ψ⦄ := 
begin
    assume φ φ' ψ h,
    apply quotient.sound,
    cases h with φφ' φ'φ,
    constructor,
    -- Proof that φ&ψ ⊢ φ'&ψ
      apply derives.and_intro,
      apply derives_x.trans,
      apply @derives.and_eliml {φ&ψ} φ ψ,
      apply derives_x.refl, -- φ&ψ ⊢ φ&ψ
      exact φφ',
      apply @derives.and_elimr {φ&ψ} φ ψ,
      apply derives_x.refl, -- φ&ψ ⊢ φ&ψ
    -- Proof that φ'&ψ ⊢ φ&ψ
      apply derives.and_intro,
      apply derives_x.trans,
      apply @derives.and_eliml {φ'&ψ} φ' ψ,
      apply derives_x.refl, -- φ'&ψ ⊢ φ'&ψ
      exact φ'φ,
      apply @derives.and_elimr {φ'&ψ} φ' ψ,
      apply derives_x.refl, -- φ'&ψ ⊢ φ'&ψ
end

def and_eq : PPC_eq → PPC_eq → PPC_eq :=
  quot.lift₂ (λ φ ψ, ⦃φ & ψ⦄) and_liftable1 and_liftable2 

notation (name := and_eq) X `&⁼` Y := and_eq X Y

lemma impl_liftable1 : ∀ φ ψ ψ' : PPC_form, 
  (ψ ⊣⊢ ψ') → ⦃φ ⊃ ψ⦄ = ⦃φ ⊃ ψ'⦄ :=
begin 
    assume φ ψ ψ' h,
    apply quotient.sound,
    cases h with ψψ' ψ'ψ,
    constructor,
      apply derives.impl_intro,
      apply derives_x.trans_hyp,
      exact (derives_x.modus_ponens φ ψ),
      exact ψψ',
      apply derives.impl_intro,
      apply derives_x.trans_hyp,
      exact (derives_x.modus_ponens φ ψ'),
      exact ψ'ψ,
end 

lemma impl_liftable2 : ∀ φ φ' ψ : PPC_form, 
  (φ ⊣⊢ φ') → ⦃φ ⊃ ψ⦄ = ⦃φ' ⊃ ψ⦄ := 
begin 
    assume φ φ' ψ h,
    apply quotient.sound,
    cases h with φφ' φ'φ,
    constructor,
      apply derives.impl_elim,
      apply derives_x.hypo_syll',
      apply derives.impl_intro,
      rewrite Hyp_x.just_flip,
      apply derives.weak,
      exact φ'φ,
      ---
      apply derives.impl_elim,
      apply derives_x.hypo_syll',
      apply derives.impl_intro,
      rewrite Hyp_x.just_flip,
      apply derives.weak,
      exact φφ',
end 


def impl_eq : PPC_eq → PPC_eq → PPC_eq :=
  quot.lift₂ (λ φ ψ, ⦃φ ⊃ ψ⦄) impl_liftable1 impl_liftable2 

notation (name := impl_eq) X `⊃⁼` Y := impl_eq X Y

