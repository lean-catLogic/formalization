
class has_derives (Form : Type) :=
  (Hyp : Type)
  [emptyHyp : has_singleton Form Hyp]
  (derives : Hyp → Form → Prop)
  (derive_refl : ∀ φ : Form, derives {φ} φ)
  (derive_trans : ∀ φ ψ θ : Form, derives {φ} ψ → derives {ψ} θ → derives {φ} θ)

def der {Form : Type} [Der : has_derives Form] : Form → Form → Prop :=
  λ φ ψ, has_derives.derives (has_derives.emptyHyp.singleton φ) ψ

meta def has_derives_properties {Form : Type} [Der : has_derives Form] : tactic unit :=
  `[ apply Der.has_derives.derive_refl <|> apply Der.has_derives.derive_trans ]

infix `⊢`:80 := der
  