import categoryTheory.thin
universes v u u₂ v₂
open category_theory

namespace specialCats

set_option pp.structure_projections false

class FP_cat (C : Type u) extends category C :=
  -- Terminal object
  (unit : C) 
  (term : ∀ X : C, X ⟶ unit) 
  (unit_η : ∀ (X : C) (f : X ⟶ unit), f = term X)
  -- Binary products
  (prod : C → C → C)
  (pr1 : ∀ {X Y : C}, (prod X Y) ⟶ X)
  (pr2 : ∀ {X Y : C}, (prod X Y) ⟶ Y)
  (pair : ∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), Z ⟶ (prod X Y))
  (prod_β1 : ∀ {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y}, (pair f g) ≫ pr1 = f)
  (prod_β2 : ∀ {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y}, (pair f g) ≫ pr2 = g)
  (prod_η : ∀ {X Y : C}, pair pr1 pr2 = 𝟙 (prod X Y))

instance {C : Type u} [FP_cat C] : has_one C := 
{
    one := FP_cat.unit
}
instance {C : Type u} [FP_cat C] : has_mul C := 
{
    mul := λ X Y, FP_cat.prod X Y
}

def homprod {C : Type u} [FP_cat C] {W X Y Z : C}
   (f : W ⟶ X) (g : Y ⟶ Z) : W * Y ⟶ X * Z :=
   FP_cat.pair (FP_cat.pr1 ≫ f) (FP_cat.pr2 ≫ g)
notation (name:=homprod) f `***` g := homprod f g 

-- #check category

class CC_cat (C : Type u) extends FP_cat C := 
  (exp : C → C → C)
  (eval : ∀ {Y Z : C}, (exp Y Z) * Y ⟶ Z)
  (curry : ∀ {X Y Z : C}, (X * Y ⟶ Z) → (X ⟶ (exp Y Z)))
  (curry_β : ∀ {X Y Z : C} (u : X * Y ⟶ Z), ((curry u) *** 𝟙 Y) ≫ eval = u)
  (curry_η : ∀ {X Y Z : C} (v : X ⟶ (exp Y Z)), curry((v *** 𝟙 Y) ≫ eval) = v)

notation (name:=exp) X `⟹` Y := CC_cat.exp X Y


end specialCats


namespace downsetCCC

open specialCats

class downsets (P : Type) [partial_order P] : Type :=
  (X : set P)
  (down_closed : ∀ (x x' : P), x ≤ x' → x' ∈ X → x ∈ X)

instance {P : Type}[partial_order P] : has_subset (downsets P) :=
{
  subset := λ A B, ∀ (x ∈ A.X), x ∈ B.X
}

theorem downset_ext {P : Type} [partial_order P] : ∀ {A B : downsets P}, A.X = B.X → A=B
| ⟨_,_⟩ ⟨_,_⟩ rfl := rfl


instance {P : Type}[partial_order P] : has_mem P (downsets P) :=
{
 mem := λ x ⟨A,A_down⟩, x ∈ A
}
def down_closed_external {P : Type}[partial_order P] : 
  ∀ (X : downsets P) (x x' : P), x ≤ x' → x' ∈ X → x ∈ X :=
begin
  assume X x x' xlex' x'inX,
  cases X with A A_down,
  apply A_down,
  exact xlex',
  exact x'inX,
end

instance {P : Type}[partial_order P] : has_inter (downsets P) :=
{
  inter := λ ⟨ A, A_down ⟩ ⟨ B, B_down ⟩, ⟨ A ∩ B ,
  begin
      assume x x' h x'inboth,
      cases x'inboth with inA inB,
      constructor,
      apply A_down,
      exact h,
      exact inA,
      apply B_down,
      exact h,
      exact inB,
  end ⟩
}

#check downset_ext
def down {P : Type} (P_struct : partial_order P) : partial_order (downsets P) :=
{
  le := (⊆),
  le_refl := λ A x h, h,
  le_antisymm := begin 
                  assume A B h1 h2,
                  apply downset_ext,
                  apply set.ext,
                  assume x,
                  constructor,
                  apply h1,
                  apply h2,
                 end,
  le_trans := λ ⟨A,_⟩ ⟨B,_⟩ ⟨C,_⟩ h1 h2 x h, 
            begin apply h2, apply h1, exact h end
}
def down_pre {P : Type} [P_struct : partial_order P] : preorder (downsets P) :=
(@partial_order.to_preorder (downsets P) (down P_struct))

instance {P : Type} [partial_order P] : thin_cat (downsets P) :=
  thin_cat.from_preorder down_pre

def downset_embed {P : Type} [P_struct : partial_order P]: P → downsets P := 
λ p, ⟨ { x ∈ set.univ | x ≤ p } ,
  begin 
    assume x x' xlex' h',
    dsimp,
    constructor, constructor,
    dsimp at h', cases h' with _ h,
    apply le_trans,
    exact xlex',
    exact h,
  end
 ⟩

def down_exp{P : Type} [P_struct : partial_order P] (X Y : downsets P) : downsets P :=
⟨{ x ∈ set.univ | ∀ (z : P), z≤x ∧ z∈X → z∈Y },
  begin 
    assume x x' xlex' h',
    dsimp at h', cases h' with _ h',
    dsimp, constructor, constructor,
    assume z h,
    cases h with zlex zinX,
    apply h',
    constructor,
    apply le_trans, exact zlex, exact xlex',
    exact zinX,
  end
⟩

instance {P : Type} [P_struct : partial_order P] : CC_cat (downsets P) :=
{
  unit := ⟨ set.univ , λ x x' _ _, true.intro ⟩ ,
  term := 
    begin 
      assume X,
      induction X with A A_down,
      apply hom_of_le,
      assume x,
      assume h,
      constructor,
    end,
  unit_η := λ X f, by apply thin_cat.K,
  prod := (∩), 
  pr1 :=
    begin 
      assume X Y,
      cases X with A A_down,
      cases Y with B B_down,
      apply hom_of_le,
      assume x h,
      cases h,
      exact h_left,
    end,
  pr2 :=
    begin 
      assume X Y,
      cases X with A A_down,
      cases Y with B B_down,
      apply hom_of_le,
      assume x h,
      cases h,
      exact h_right,
    end,
  pair := 
    begin 
      assume X Y Z,
      assume F G,
      have k : @partial_order.le (downsets P) (down P_struct) Z X,
      apply @le_of_hom (downsets P) (down_pre) Z X,
      exact F,
      have l : @partial_order.le (downsets P) (down P_struct) Z Y,
      apply @le_of_hom (downsets P) (down_pre) Z Y,
      exact G,
      cases X with A A_down,
      cases Y with B B_down,
      cases Z with C C_down,
      apply hom_of_le,
      assume z h,
      constructor,
      apply k, assumption,
      apply l, assumption,
    end,
  prod_β1 := λ X Y Z f g, by apply thin_cat.K,
  prod_β2 := λ X Y Z f g, by apply thin_cat.K,
  prod_η := λ X Y, by apply thin_cat.K,
  exp := down_exp,
  eval := 
    begin 
      assume X Y,
      cases X with A A_down,
      cases Y with B B_down,
      apply hom_of_le,
      assume z h,
      cases h with zin_exp zin_A,
      dsimp at zin_exp,
      cases zin_exp with _ property,
      apply property,
      constructor,
      apply le_refl,
      exact zin_A,
    end,
  curry := 
    begin 
      assume X Y Z XYleZ,
      suffices betterXYleZ : X ∩ Y ⊆ Z,
      cases X with A A_down,
      cases Y with B B_down,
      cases Z with C C_down,
      apply hom_of_le,
      assume z zinA,
      dsimp[down_exp], constructor, constructor,
      assume z',
      assume h, cases h with z'lez z'inB,
      have z'inA : z'∈A,
      apply A_down,
      exact z'lez,
      exact zinA,
      suffices ABleC : A ∩ B ⊆ C,
      apply ABleC,
      constructor,
      exact z'inA, exact z'inB,
      apply betterXYleZ,
      apply @le_of_hom (downsets P) (down_pre),
      exact XYleZ,
    end,
  curry_β := λ X Y Z u, by apply thin_cat.K,
  curry_η := λ X Y Z v, by apply thin_cat.K
}


end downsetCCC
