import languages.deductive category_theory.category.preorder

namespace synPoset

  variable {Form : Type}

  instance syn_preorder [Der : has_derives Form] : preorder Form :=
  { le := λ φ ψ, φ ⊢ ψ,
    le_refl := Der.derive_refl,
    le_trans := Der.derive_trans,
  }

  def inter_der [Der : has_derives Form] : Form → Form → Prop :=
    λ φ ψ,  φ ⊢ ψ ∧ ψ ⊢ φ

  infix `⊣⊢`:78 := inter_der

  instance syn_setoid [Der : has_derives Form] : setoid Form :=
  { r := (⊣⊢), 
    iseqv := ⟨ begin 
                assume φ, constructor, 
                apply Der.derive_refl, apply Der.derive_refl,
              end, 
              begin
                assume φ ψ h, cases h with φψ ψφ,
                constructor, exact ψφ, exact φψ,
              end,
              begin 
                assume φ ψ θ j k, cases j with φψ ψφ,
                cases k with ψθ θψ, constructor,
                apply Der.derive_trans, exact φψ, exact ψθ,
                apply Der.derive_trans, exact θψ, exact ψφ,
              end 
              ⟩ 
  }

  -- notation (name:=syn_setoid.r) φ `⊣⊢` ψ :78 := syn_setoid.r φ ψ 

  def Form_eq [Der : has_derives Form] : Type := @quot Form (⊣⊢)
  def Form_eq_x (F : Type) [Der : has_derives F] : Type := @Form_eq F Der

  notation (name:=Form_eq_explicit) F ` _eq`:max := Form_eq_x F

  def Form_eq_in [Der : has_derives Form] : Form → @Form_eq Form Der := quot.mk (⊣⊢) 

  notation (name:=PPC_eq_in) ⦃φ⦄ := Form_eq_in φ

  -- Lemmas that ⊢ respects ⊣⊢
  lemma syn_preorder_liftable1 [Der : has_derives Form] :
    ∀ φ ψ θ : Form, ψ ⊣⊢ θ → (φ ⊢ ψ) = (φ ⊢ θ) :=
  begin 
    assume φ ψ θ ψiffθ,
    cases ψiffθ with ψθ θψ,
    apply propext,
    constructor,
    assume φψ, apply Der.derive_trans, exact φψ, exact ψθ,
    assume φθ, apply Der.derive_trans, exact φθ, exact θψ,
  end
  lemma syn_preorder_liftable2 [Der : has_derives Form] :
    ∀ φ ψ θ : Form, φ ⊣⊢ ψ → (φ ⊢ θ) = (ψ ⊢ θ) :=
  begin 
    assume φ ψ θ φiffψ,
    cases φiffψ with φψ ψφ,
    apply propext,
    constructor,
    assume φθ, apply Der.derive_trans, exact ψφ, exact φθ,
    assume ψθ, apply Der.derive_trans, exact φψ, exact ψθ,
  end 

  def Form_eq_order [Der : has_derives Form] : @Form_eq Form Der → @Form_eq Form Der → Prop 
    := quot.lift₂ synPoset.syn_preorder.le syn_preorder_liftable1 syn_preorder_liftable2



  instance syn_poset [Der : has_derives Form] : partial_order Form_eq :=
  { le := @Form_eq_order Form Der,
    le_refl := 
      begin
        assume a,
        induction a with φ, 
        dsimp[(≤),setoid.r,Form_eq_order],
        apply Der.derive_refl,refl,
      end,
    le_trans := 
      begin 
        assume a b c h j,
        induction a with φ, induction b with ψ, induction c with θ,
        dsimp[(≤),setoid.r,Form_eq_order],
        dsimp[(≤)] at h, dsimp[(≤)] at j, 
        apply Der.derive_trans,
        exact h, exact j,
        refl, refl, refl,
      end,
    le_antisymm :=  
      begin
        assume a b h j,
        induction a with φ, induction b with ψ,
        apply quotient.sound,
        dsimp[(≈),setoid.r],dsimp[(≤)] at h, dsimp[(≤)] at j,
        constructor, exact h, exact j, refl, refl,
      end
  }

  instance syn_eq_pre {Form : Type} [Der : has_derives Form] : preorder (Form_eq_x Form) :=
    @partial_order.to_preorder (Form_eq_x Form) synPoset.syn_poset

end synPoset


