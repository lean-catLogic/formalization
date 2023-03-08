import deduction.deduction

namespace deduction_monadic

open deduction_basic

/- Diamond -/
class has_diamond (Form : Type) extends has_struct_derives Form := 
  (diamond : Form → Form)
  (dmap  : ∀ {φ ψ : Form}, derives {φ} ψ → derives {diamond φ} (diamond ψ))
  (dpure : ∀ {Φ : Hyp} {φ : Form}, derives Φ φ → derives Φ (diamond φ))
  (djoin : ∀ {Φ : Hyp} {φ : Form}, 
    derives Φ (diamond (diamond φ)) → derives Φ (diamond φ))

notation (name:= has_diamond.diamond) `◇`:81 φ := has_diamond.diamond φ 

end deduction_monadic