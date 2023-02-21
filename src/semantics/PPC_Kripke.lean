import deduction.PPC_natDeduct category_theory.category.preorder

namespace forcing_notation
class has_forcing (X : Type) (Form : Type) :=
  (force : X → Form → Prop)

notation (name := force) k `⊩` φ := has_forcing.force k φ
end forcing_notation


namespace PPC_KripkeModels

  open PPC_defn

  class KripkeModel (K : Type) extends partial_order K :=
    (forces_p : ℕ → K → Prop)
    (down_closed : ∀ (n : ℕ) (j k : K), j ≤ k → forces_p n k → forces_p n j)

  def forces {K : Type} [KripkeModel K] : K → PPC_Form → Prop
  | k ⊤ := true
  | k (p i) := KripkeModel.forces_p i k
  | k (φ & ψ) := (forces k φ) ∧ (forces k ψ)
  | k (φ ⊃ ψ) := ∀ j : K, j ≤ k → forces j φ → forces j ψ

  open forcing_notation
  -- Use ⊩ notation between points of a Kripke model and formulas
  instance pointwiseForcing {K : Type} [KripkeModel K] : has_forcing K PPC_Form := ⟨ forces ⟩ 

  -- Use ⊩ notation to say the whole model forces φ
  instance globalForcing {K : Type} : has_forcing (KripkeModel K) PPC_Form :=
  {
    force := λ K_struct φ, ∀ k : K, @forces K K_struct k φ
  }

  -- Use ()⊩φ to say that every model forces φ
  instance universalForcing : has_forcing unit PPC_Form :=
  {
    force := λ _ φ, ∀ (K : Type) (K_struct : KripkeModel K), K_struct ⊩ φ
  }

  lemma top_valid : () ⊩ PPC_Form.top :=
  begin 
    assume K K_struct k,
    constructor,
  end 

end PPC_KripkeModels
