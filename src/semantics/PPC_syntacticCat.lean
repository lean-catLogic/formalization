import languages.PPC proof.PPC_natDeduct CT.CCC category_theory.category.preorder order.category.Preorder 
open category_theory
open category_theory.limits 
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


-- Preorder on equivalence classes
def PPC_eq_order   : PPC_eq → PPC_eq → Prop 
  := quot.lift₂ PPC_preorder.le PPC_preorder_liftable1 PPC_preorder_liftable2

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

-- Form the category out of this poset
def ℂ_PPC : category_theory.small_category (PPC_eq) 
  := preorder.small_category PPC_eq 

-- Methods for directly turning formulas into objects and derivations into morphisms
def ℂ_PPC_obj (φ : PPC_form) : PPC_eq := ⟦φ⟧
def ℂ_PPC_hom : ∀ {φ ψ : PPC_form}, (φ ⊢ ψ) → (ℂ_PPC_obj φ ⟶ ℂ_PPC_obj ψ) 
:= begin
  assume φ ψ h,
  dsimp[ℂ_PPC_obj],
  apply category_theory.hom_of_le,
  dsimp[(≤),preorder.le,partial_order.le],
  rewrite preorder_lift_rewrite,
  exact h,
end

-- All ℂ_PPC morphisms come from PPC derivations
lemma ℂ_PPC_full : ∀ {φ ψ : PPC_form} (f : ℂ_PPC_obj φ ⟶ ℂ_PPC_obj ψ),
  ∃ h : φ ⊢ ψ, f = ℂ_PPC_hom h :=
begin 
  assume φ ψ f,
  existsi (category_theory.le_of_hom f),
  symmetry,
  apply category_theory.hom_of_le_le_of_hom,
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
      assume X,
      induction X with φ,
      change (quot.mk setoid.r φ) with (ℂ_PPC_obj φ),
      apply ℂ_PPC_hom,
      exact derives.truth,
      apply ℂ_PPC_thin,
    end,
  unit_η := λ X f, ℂ_PPC_thin,
  prod := 
    begin 
      assume X Y,
      induction X with φ, induction Y with ψ,
      exact ℂ_PPC_obj (φ & ψ),
      sorry,sorry, --TODO: Prove that lifting `&` onto equiv classes is well-defined
    end 
  ,
  pr1 :=
    begin
      assume X Y,
      induction X with φ, induction Y with ψ,
      apply ℂ_PPC_hom,
      apply derives.and_eliml,
      apply derive_refl,
      apply ℂ_PPC_thin,
      apply ℂ_PPC_thin,
    end,
  pr2 :=
    begin
      assume X Y,
      induction X with φ, induction Y with ψ,
      apply ℂ_PPC_hom,
      apply derives.and_elimr,
      apply derive_refl,
      apply ℂ_PPC_thin,
      apply ℂ_PPC_thin,
    end,
  pair :=
    begin
      assume X Y Z f g,
      induction X with φ, induction Y with ψ, induction Z with χ,
      let h : χ ⊢ φ := category_theory.le_of_hom f,
      let h' : χ ⊢ ψ := category_theory.le_of_hom g,
      apply ℂ_PPC_hom,
      apply derives.and_intro,
      exact h, exact h',
      apply funext, assume x, apply funext, assume x', dsimp, apply ℂ_PPC_thin,
      apply funext, assume x, apply ℂ_PPC_thin,
      apply funext, assume x, apply ℂ_PPC_thin,
    end,
  prod_β1 := λ X Y Z f g, ℂ_PPC_thin,
  prod_β2 := λ X Y Z f g, ℂ_PPC_thin,
  prod_η :=  λ X Y, ℂ_PPC_thin,
}