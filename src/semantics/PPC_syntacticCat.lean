import semantics.PPC_poset CT.CCC category_theory.category.preorder
open category_theory



-- Form the category out of this poset
def ℂ_PPC : category (PPC_eq) 
  := preorder.small_category PPC_eq 

-- Methods for directly turning formulas into objects and derivations into morphisms
def ℂ_PPC_obj (φ : PPC_form) : PPC_eq := ⦃φ⦄
def ℂ_PPC_hom : ∀ {φ ψ : PPC_form}, (φ ⊢ ψ) → (ℂ_PPC_obj φ ⟶ ℂ_PPC_obj ψ) 
:= begin
  assume φ ψ h,
  dsimp[ℂ_PPC_obj],
  apply hom_of_le,
  dsimp[(≤),preorder.le,partial_order.le],
  rewrite preorder_lift_rewrite,
  exact h,
end

-- All ℂ_PPC morphisms come from PPC derivations
lemma ℂ_PPC_full : ∀ {φ ψ : PPC_form} (f : ℂ_PPC_obj φ ⟶ ℂ_PPC_obj ψ),
  ∃ h : φ ⊢ ψ, f = ℂ_PPC_hom h :=
begin 
  assume φ ψ f,
  existsi (le_of_hom f),
  symmetry,
  apply hom_of_le_le_of_hom,
end 

-- ℂ_PPC is a thin category
theorem ℂ_PPC_thin : ∀ {X Y : PPC_eq} {f g : X ⟶ Y}, f = g 
:=
begin 
  assume X Y f g,
  induction X with φ, induction Y with ψ,
  cases (ℂ_PPC_full f) with hf pf,
  cases (ℂ_PPC_full g) with hg pg,
  rewrite pf, rewrite pg,
  refl,refl,
end 

open specialCats

-- ℂ_PPC has finite products
instance : FP_cat PPC_eq :=
{
  unit := ℂ_PPC_obj PPC_form.top,
  term := 
    begin
      -- Actual construction
      assume X,
      induction X with φ,
      change (quot.mk setoid.r φ) with (ℂ_PPC_obj φ),
      apply ℂ_PPC_hom,
      exact derives.truth,
      -- Proving this respects ⊣⊢
      apply ℂ_PPC_thin,
    end,
  unit_η := λ X f, ℂ_PPC_thin,
  prod := (&⁼),
  pr1 :=
    begin
      -- Actual construction
      assume X Y,
      induction X with φ, induction Y with ψ,
      apply ℂ_PPC_hom,
      apply derives.and_eliml,
      apply derive_refl,
      -- Proving this respects ⊣⊢
      apply ℂ_PPC_thin,
      apply ℂ_PPC_thin,
    end,
  pr2 :=
    begin
      -- Actual construction
      assume X Y,
      induction X with φ, induction Y with ψ,
      apply ℂ_PPC_hom,
      apply derives.and_elimr,
      apply derive_refl,
      -- Proving this respects ⊣⊢
      apply ℂ_PPC_thin,
      apply ℂ_PPC_thin,
    end,
  pair :=
    begin
      -- Actual construction
      assume X Y Z f g,
      induction X with φ, induction Y with ψ, induction Z with χ,
      let h : χ ⊢ φ := le_of_hom f,
      let h' : χ ⊢ ψ := le_of_hom g,
      apply ℂ_PPC_hom,
      apply derives.and_intro,
      exact h, exact h',
      -- Proving this respects ⊣⊢
      apply funext, assume _, apply funext, assume _, apply ℂ_PPC_thin,
      apply funext, assume _, apply ℂ_PPC_thin,
      apply funext, assume _, apply ℂ_PPC_thin,
    end,
  prod_β1 := λ X Y Z f g, ℂ_PPC_thin,
  prod_β2 := λ X Y Z f g, ℂ_PPC_thin,
  prod_η :=  λ X Y, ℂ_PPC_thin,
}

instance : CCC PPC_eq := 
{
  exp := (⊃⁼),
  eval := 
    begin 
      -- Actual construction
      assume Y Z,
      induction Y with ψ, induction Z with θ,
      apply ℂ_PPC_hom,
      apply union_Hyp_and,
      apply modus_ponens,
      -- Proving this respects ⊣⊢
      apply ℂ_PPC_thin,
      apply ℂ_PPC_thin,
    end,
  curry := 
    begin 
      -- Actual construction
      assume X Y Z u,
      induction X with φ, induction Y with ψ, induction Z with θ,
      apply ℂ_PPC_hom,
      have h : (φ&ψ) ⊢ θ,
      exact (Exists.fst (ℂ_PPC_full u)),
      apply derives.impl_intro,
      apply and_Hyp_union,
      exact h,
      -- Proving this respects ⊣⊢
      apply funext, assume _, apply ℂ_PPC_thin,
      apply funext, assume _, apply ℂ_PPC_thin,
      apply funext, assume _, apply ℂ_PPC_thin,
    end,
  curry_β := λ {X Y Z} u, ℂ_PPC_thin,
  curry_η := λ {X Y Z} v, ℂ_PPC_thin,
}
