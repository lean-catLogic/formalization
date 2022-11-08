import languages.PPC proof.PPC_natDeduct category_theory.category.preorder

-- ⊢ is a preorder on the set of formulas 
instance PPC_preorder : preorder PPC_form :=
{ le := λ φ ψ, φ ⊢ ψ,
  le_refl := derive_refl,
  le_trans := derive_trans,
}

-- Inter-derivability is an equivalence relation on formulas
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

-- Quotienting PPC_form by inter-derivability
def PPC_eq : Type := quot (⊣⊢) 

-- Lemmas that ⊢ respects ⊣⊢
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
#check quotient.sound
-- Preorder on equivalence classes
def PPC_eq_order   : PPC_eq → PPC_eq → Prop 
  := quot.lift₂ PPC_preorder.le PPC_preorder_liftable1 PPC_preorder_liftable2
-- := begin
--       assume a b,
--       induction a with φ ψ₀ ψ₁ ψ₂,
--       induction b with ψ φ₀ φ₁ φ₂,
--       exact φ ⊢ ψ,
--       -- proof that this respects ⊣⊢ in φ
--       -- simp[eq.rec],
--       apply propext,
--       dsimp[setoid.r] at φ₂, cases φ₂ with forw rev,
--       constructor, assume φφ₀, exact φφ₀, 
--       --rewrite at φφ₀,
--       apply derive_trans, exact φφ₀,  
--    end

/- 
  Helpful lemma to allow us to use the natural deduction calculus
  when working on equivalence classes of formulas
-/
lemma preorder_lift_rewrite (φ ψ : PPC_form) 
  : PPC_eq_order ⟦φ⟧ ⟦ψ⟧ = (φ ⊢ ψ) 
  := begin refl end

--  PPC_form / ⊣⊢ is a poset under PPC_eq_order
instance PPC_poset : partial_order (PPC_eq) :=
{ le := PPC_eq_order,
  le_refl := 
                (begin
                  assume a,
                  induction a with φ, 
                  dsimp[(≤),setoid.r,PPC_eq_order],
                  apply derive_refl,refl,
                end),
  le_trans := 
                (begin 
                  assume a b c h j,
                  induction a with φ, induction b with ψ, induction c with θ,
                  dsimp[(≤),setoid.r,PPC_eq_order],
                  dsimp[(≤)] at h, dsimp[(≤)] at j, 
                  apply derive_trans,
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

