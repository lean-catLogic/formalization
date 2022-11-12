import category_theory.category.basic
universes v u u₂ v₂

namespace specialCats

open category_theory

class FP_cat (C : Type u) [category.{v} C] :=
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

#check FP_cat.mk

end specialCats