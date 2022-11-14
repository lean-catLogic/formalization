import category_theory.category.basic
universes v u u₂ v₂

namespace specialCats

open category_theory

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

class CCC (C : Type u) extends FP_cat C := 
  (exp : C → C → C)
  (eval : ∀ {Y Z : C}, (exp Y Z) * Y ⟶ Z)
  (curry : ∀ {X Y Z : C}, (X * Y ⟶ Z) → (X ⟶ (exp Y Z)))
  (curry_β : ∀ {X Y Z : C} (u : X * Y ⟶ Z), ((curry u) *** 𝟙 Y) ≫ eval = u)
  (curry_η : ∀ {X Y Z : C} (v : X ⟶ (exp Y Z)), curry((v *** 𝟙 Y) ≫ eval) = v)

notation (name:=exp) X `⟹` Y := CCC.exp X Y


end specialCats