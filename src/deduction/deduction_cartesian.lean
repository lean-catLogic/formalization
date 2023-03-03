import deduction.deduction

namespace deduction_cart

open deduction_basic

/- Truth -/
class has_top (Form : Type) extends has_struct_derives Form := 
  (top : Form)
  (truth : ∀ {Φ : Hyp}, derives Φ top)

notation (name:=has_top.top) `⊤`:80   := has_top.top

/- Logical And -/
class has_and (Form : Type) extends has_top Form :=
  (and : Form → Form → Form)
  (and_intro {Φ} {φ ψ : Form}    
        : derives Φ φ → derives Φ ψ → derives Φ (and φ ψ))
  (and_eliml {Φ} {φ ψ : Form}    
        : derives Φ (and φ ψ) → derives Φ φ)
  (and_elimr {Φ} {φ ψ : Form}    
        : derives Φ (and φ ψ) → derives Φ ψ)

infix `&`:79      := has_and.and 

/- Implication -/
class has_impl (Form : Type) extends has_and Form :=
  (impl : Form → Form → Form)
  (impl_intro {Φ} (φ) {ψ}   
        : derives (insert φ Φ) ψ → derives Φ (impl φ ψ))
  (impl_elim {Φ} (φ) {ψ} 
        : derives Φ (impl φ ψ) → derives Φ φ → derives Φ ψ)

notation (name:= has_impl.impl) φ ` ⊃ `:80 ψ := has_impl.impl φ ψ 


/- All three -/
end deduction_cart


namespace cart_x
  open deduction_basic
  open deduction_cart

  lemma and_intro1 {Form : Type} [Der : has_and Form] {φ ψ : Form} : 
    Der.derives (Der.insertHyp.insert ψ {φ}) (φ&ψ) :=
  begin
    apply Der.and_intro,
    apply Der.weak1,
    apply derive_refl,
    apply Der.hyp,
    apply Der.inInsert,
  end

  lemma and_eliml1 {Form : Type} [Der : has_and Form] {φ ψ : Form} : 
    φ & ψ ⊢ φ :=
  begin
    apply Der.and_eliml,
    apply derive_refl,
  end
  lemma and_elimr1 {Form : Type} [Der : has_and Form] {φ ψ : Form} : 
    φ & ψ ⊢ ψ :=
  begin
    apply Der.and_elimr,
    apply derive_refl,
  end

  lemma modus_ponens {Form : Type} [Der : has_impl Form] : 
    ∀ {φ ψ : Form}, (φ ⊃ ψ) & φ ⊢ ψ :=
  begin
    assume φ ψ,
    apply Der.impl_elim φ,
    apply and_eliml1,
    apply and_elimr1,
  end

  lemma impl_ε {Form : Type} [Der : has_impl Form] :
    ∀ {φ ψ θ : Form}, φ & ψ ⊢ θ  →  φ ⊢ ψ ⊃ θ :=
  begin
    assume φ ψ θ h,
    apply Der.impl_intro,
    apply Der.derive_Trans,
    apply and_intro1,
    exact h,
  end
end cart_x