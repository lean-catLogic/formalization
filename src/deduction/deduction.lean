
namespace deduction_basic
  class has_Hyp (Form : Type) :=
    (Hyp : Type)
    [emptyHyp : has_emptyc Hyp]
    [insertHyp : has_insert Form Hyp]
  instance singleHyp {Form : Type} [hasHyp : has_Hyp Form] : has_singleton Form hasHyp.Hyp := 
    {singleton := λ φ, hasHyp.insertHyp.insert φ hasHyp.emptyHyp.emptyc}
  
  instance lawfulSingleHyp {Form : Type} [hasHyp : has_Hyp Form] : 
  @is_lawful_singleton Form (has_Hyp.Hyp Form) hasHyp.emptyHyp hasHyp.insertHyp deduction_basic.singleHyp := 
  { insert_emptyc_eq := begin assume φ, refl end }

  class has_derives (Form : Type) extends has_Hyp Form := 
    (derives : Hyp → Form → Prop)
    (derive_Trans : ∀ {Φ : Hyp} (ψ) {θ : Form}, derives Φ ψ → derives {ψ} θ → derives Φ θ)

  def der {Form : Type} [Der : has_derives Form] : Form → Form → Prop :=
    λ φ ψ, has_derives.derives {φ} ψ

  infix `⊢`:60 := der

  lemma derive_trans {Form : Type} [Der : has_derives Form] : 
    ∀ {φ : Form} (ψ) {θ}, (φ ⊢ ψ) → (ψ ⊢ θ) → (φ ⊢ θ) :=
  begin
    assume φ,
    apply Der.derive_Trans,
  end

  class has_struct_derives (Form : Type) extends has_derives Form :=
    [memHyp : has_mem Form Hyp]
    (inInsert : ∀ {φ : Form} {Φ : Hyp}, φ ∈ insert φ Φ)
    (hyp : ∀ {Φ} {φ}, (φ ∈ Φ) → derives Φ φ)
    (weak1 : ∀ {Φ} {φ} (ψ), derives Φ φ → derives (insert ψ Φ) φ)

  lemma derive_refl {Form : Type} [Der : has_struct_derives Form] :
    ∀ φ : Form, φ ⊢ φ :=
  begin
    assume φ,
    apply Der.hyp,
    apply Der.inInsert,
  end
  
end deduction_basic

  