import generalTactics deduction.deduction category_theory.category.preorder
open deduction_basic

namespace synPoset

  variable {Form : Type}

  instance syn_preorder [Der : has_struct_derives Form] : preorder Form :=
  { le := λ φ ψ, φ ⊢ ψ,
    le_refl := derive_refl,
    le_trans := @derive_trans Form Der.to_has_derives,
  }

  def inter_der [Der : has_struct_derives Form] : Form → Form → Prop :=
    λ φ ψ,  φ ⊢ ψ ∧ ψ ⊢ φ

  infix `⊣⊢`:78 := inter_der

  instance syn_setoid [Der : has_struct_derives Form] : setoid Form :=
  { r := (⊣⊢), 
    iseqv := ⟨ begin 
                assume φ, constructor, 
                apply derive_refl, apply derive_refl,
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

  -- notation (name:=syn_setoid.r) φ `⊣⊢` ψ :78 := syn_setoid.r φ ψ 

  def Form_eq [Der : has_struct_derives Form] : Type := @quot Form (⊣⊢)
  def Form_eq_x (F : Type) [Der : has_struct_derives F] : Type := @Form_eq F Der

  notation (name:=Form_eq_explicit) F ` _eq`:max := Form_eq_x F

  def Form_eq_in [Der : has_struct_derives Form] : Form → Form _eq := quot.mk (⊣⊢) 

  notation (name:=PPC_eq_in) ⦃φ⦄ := Form_eq_in φ

  -- Lemmas that ⊢ respects ⊣⊢
  lemma syn_preorder_liftable1 [Der : has_struct_derives Form] :
    ∀ φ ψ θ : Form, ψ ⊣⊢ θ → (φ ⊢ ψ) = (φ ⊢ θ) :=
  begin 
    assume φ ψ θ ψiffθ,
    cases ψiffθ with ψθ θψ,
    apply propext,
    constructor,
    assume φψ, apply derive_trans, exact φψ, exact ψθ,
    assume φθ, apply derive_trans, exact φθ, exact θψ,
  end
  lemma syn_preorder_liftable2 [Der : has_struct_derives Form] :
    ∀ φ ψ θ : Form, φ ⊣⊢ ψ → (φ ⊢ θ) = (ψ ⊢ θ) :=
  begin 
    assume φ ψ θ φiffψ,
    cases φiffψ with φψ ψφ,
    apply propext,
    constructor,
    assume φθ, apply derive_trans, exact ψφ, exact φθ,
    assume ψθ, apply derive_trans, exact φψ, exact ψθ,
  end 

  def Form_eq_order [Der : has_struct_derives Form] : @Form_eq Form Der → @Form_eq Form Der → Prop 
    := quot.lift₂ synPoset.syn_preorder.le syn_preorder_liftable1 syn_preorder_liftable2

  instance syn_poset [Der : has_struct_derives Form] : partial_order Form_eq :=
  { le := @Form_eq_order Form Der,
    le_refl := 
      begin
        repeat_assume_induct [`φ],
        dsimp[(≤),setoid.r,Form_eq_order],
        apply derive_refl,refl,
      end,
    le_trans := 
      begin 
        repeat_assume_then_induct `[ assume h j ] [`φ,`ψ,`θ],
        dsimp[(≤),setoid.r,Form_eq_order],
        dsimp[(≤)] at h, dsimp[(≤)] at j, 
        apply derive_trans,
        exact h, exact j,
        refl, refl, refl,
      end,
    le_antisymm :=  
      begin
        repeat_assume_then_induct `[ assume h j ] [`φ,`ψ],
        apply quotient.sound,
        dsimp[(≈),setoid.r],dsimp[(≤)] at h, dsimp[(≤)] at j,
        constructor, exact h, exact j, refl, refl,
      end
  }

  instance syn_eq_pre {Form : Type} [Der : has_struct_derives Form] : preorder (Form _eq) :=
    @partial_order.to_preorder (Form _eq) synPoset.syn_poset

end synPoset


