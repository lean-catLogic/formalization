import languages.PPC proof.PPC_natDeduct category_theory.category.preorder

instance PPC_preorder : preorder PPC_form :=
{ le := λ φ ψ, φ ⊢ ψ,
  le_refl := derive_refl,
  le_trans := derive_trans,
}
instance PPC_setoid : setoid PPC_form :=
{ r := λ φ ψ, φ ⊢ ψ ∧ ψ ⊢ φ, 
  iseqv := ⟨ begin 
              assume φ, constructor, 
              apply derive_refl, apply derive_refl 
             end, 
            begin
              assume φ ψ h, cases h with φψ ψφ,
              constructor, exact ψφ, exact φψ,
            end,
            begin 
              assume φ ψ θ j k, cases j with φψ ψφ,
              cases k with ψθ θψ, constructor,
              apply derive_trans, exact φψ, exact ψθ,
              apply derive_trans, exact θψ, exact ψφ,
            end 
            ⟩ 
} 
notation (name:=PPC_setoid.r) φ `⊣⊢` ψ :78 := PPC_setoid.r φ ψ 

def PPC_equiv_class : Type := quot (⊣⊢) 

lemma PPC_preorder_liftable1 :
  ∀ φ ψ θ : PPC_form, ψ ⊣⊢ θ → (φ ⊢ ψ) = (φ ⊢ θ) :=
begin 
  assume φ ψ θ ψiffθ,
  cases ψiffθ with ψθ θψ,
  apply propext,
  constructor,
  assume φψ, apply derive_trans, exact φψ, exact ψθ,
  assume φθ, apply derive_trans, exact φθ, exact θψ,
end
lemma PPC_preorder_liftable2 :
  ∀ φ ψ θ : PPC_form, φ ⊣⊢ ψ → (φ ⊢ θ) = (ψ ⊢ θ) :=
begin 
  assume φ ψ θ φiffψ,
  cases φiffψ with φψ ψφ,
  apply propext,
  constructor,
  assume φθ, apply derive_trans, exact ψφ, exact φθ,
  assume ψθ, apply derive_trans, exact φψ, exact ψθ,
end 

def PPC_preorder_lifted : PPC_equiv_class → PPC_equiv_class → Prop 
  := quot.lift₂ PPC_preorder.le PPC_preorder_liftable1 PPC_preorder_liftable2
def preorder_lift_rewrite (φ ψ : PPC_form) 
  : PPC_preorder_lifted ⟦φ⟧ ⟦ψ⟧ = (φ ⊢ ψ) 
  := begin refl end

def quotient_monotone : ∀ φ ψ : PPC_form, 
      φ ⊢ ψ → PPC_preorder_lifted ⟦φ⟧ ⟦ψ⟧ :=
begin 
  assume φ ψ h,
  dsimp[PPC_preorder_lifted],
  exact h,
end 
lemma quotient_universal : ∀ φ ψ : PPC_form,
  PPC_preorder_lifted ⟦φ⟧ ⟦ψ⟧ → φ ⊢ ψ :=
begin 
  assume φ ψ h,
  rewrite [preorder_lift_rewrite] at h,
  exact h,
end 

instance PPC_poset : partial_order (PPC_equiv_class) :=
{ le := PPC_preorder_lifted,
  le_refl := (λ a, quotient.induction_on a
                (begin
                  assume φ,
                  dsimp[(≤)],
                  rewrite[preorder_lift_rewrite],
                  apply derive_refl,
                end)),
  le_trans := (λ a b c, quotient.induction_on₃ a b c 
                (begin 
                  assume φ ψ θ h j,
                  dsimp[(≤),⟦_⟧], dsimp[(≤)] at h, dsimp[(≤)] at j,
                  rewrite[preorder_lift_rewrite],
                  rewrite[preorder_lift_rewrite] at h,
                  rewrite[preorder_lift_rewrite] at j,
                  apply derive_trans,
                  exact h, exact j,
                end)),
  le_antisymm := (λ a b, 
                begin
                  apply (quotient.induction_on₂ a b),
                  assume φ ψ h j,
                  apply quotient.sound,
                  dsimp[(≈),setoid.r],dsimp[(≤)] at h, dsimp[(≤)] at j,
                  rewrite[preorder_lift_rewrite] at h,
                  rewrite[preorder_lift_rewrite] at j,
                  constructor, exact h, exact j,
                end)
}

