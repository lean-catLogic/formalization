import category_theory.category.basic data.set.basic category_theory.category.preorder
universes v u u₂ v₂
open category_theory



class thin_cat (C : Type) extends category C :=
  (K : ∀ (X Y : C) (f g : X ⟶ Y), f = g)



namespace thin_cat

  def preorder_cat_full {C : Type} [C_struct : preorder C] {X Y : C} (F : X ⟶ Y)
    : ∃ p : X ≤ Y, F = hom_of_le p :=
    ⟨ le_of_hom F, by { symmetry, apply hom_of_le_le_of_hom}  ⟩ 

  def from_preorder {P : Type} (P_struct : preorder P) : thin_cat P :=
  ⟨ 
    begin 
      assume X Y F G,
      cases (preorder_cat_full F) with p pF,
      cases (preorder_cat_full G) with q qG,
      rewrite pF, rewrite qG,
    end 
  ⟩ 

  meta def by_thin : tactic unit :=
  `[ repeat{assume _}, repeat{ repeat{ apply funext, assume _},apply thin_cat.K }]

end thin_cat
