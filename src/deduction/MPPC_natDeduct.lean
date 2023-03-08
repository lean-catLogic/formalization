import deduction.deduction_cartesian data.set.basic
open deduction_basic



namespace MPPC_defn

    inductive MPPC_Form : Type
    | top : MPPC_Form
    | var : ℕ → MPPC_Form
    | and : MPPC_Form → MPPC_Form → MPPC_Form
    | impl : MPPC_Form → MPPC_Form → MPPC_Form
    | diamond : MPPC_Form → MPPC_Form


    @[reducible] def MPPC_Hyp : Type := set (MPPC_Form)

    instance : has_union MPPC_Hyp := infer_instance
    instance : has_mem MPPC_Form MPPC_Hyp := infer_instance
    instance : has_insert MPPC_Form MPPC_Hyp := infer_instance
    instance : has_emptyc MPPC_Hyp := infer_instance

    inductive isModal : MPPC_Hyp → Prop
    | ModalEmpty : isModal ∅
    | ModalInsert : ∀ (Φ : MPPC_Hyp) (φ : MPPC_Form), 
        isModal Φ → isModal (insert (MPPC_Form.diamond φ) Φ)

    inductive MPPC_derives : MPPC_Hyp → MPPC_Form → Prop 
    | hyp {Φ : MPPC_Hyp} {φ : MPPC_Form}  
        : (φ ∈ Φ) →  MPPC_derives Φ φ
    | truth {Φ}                               
        : MPPC_derives Φ MPPC_Form.top 
    | and_intro {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ φ → MPPC_derives Φ ψ → MPPC_derives Φ (MPPC_Form.and φ ψ)
    | and_eliml {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ (MPPC_Form.and φ ψ) → MPPC_derives Φ φ
    | and_elimr {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ (MPPC_Form.and φ ψ) → MPPC_derives Φ ψ
    | impl_intro {Φ : MPPC_Hyp} (φ : MPPC_Form) {ψ : MPPC_Form}   
        : MPPC_derives (insert φ Φ) ψ → MPPC_derives Φ (MPPC_Form.impl φ ψ)
    | impl_elim {Φ : MPPC_Hyp} (φ : MPPC_Form) {ψ : MPPC_Form} 
        : MPPC_derives Φ (MPPC_Form.impl φ ψ) → MPPC_derives Φ φ → MPPC_derives Φ ψ
    | weak {Φ Ψ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ φ → MPPC_derives (Φ ∪ Ψ) φ
    | dmap {φ ψ : MPPC_Form} 
        : MPPC_derives {φ} ψ → MPPC_derives {φ.diamond} (ψ.diamond)

    -- | Dmap {Φ : MPPC_Hyp} {φ : MPPC_Form}
    --     : isModal Φ → MPPC_derives Φ φ → MPPC_derives Φ (MPPC_Form.diamond φ)
    | dpure {Φ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ φ → MPPC_derives Φ (MPPC_Form.diamond φ)
    | djoin {Φ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ (MPPC_Form.diamond(MPPC_Form.diamond φ)) → MPPC_derives Φ (MPPC_Form.diamond φ)
    open MPPC_derives

notation (name:= MPPC.diamond) `◇`:81 φ := MPPC_Form.diamond φ 

end MPPC_defn


namespace MPPC_has_derives

    open MPPC_defn
    open MPPC_defn.MPPC_derives
    open deduction_basic
    open deduction_cart
    open MPPC_defn.MPPC_Form
    -- open deduction_monadic

    instance MPPC_hasHyp : has_Hyp MPPC_Form :=
      { Hyp := MPPC_Hyp }

    instance MPPC_singleton : has_singleton MPPC_Form MPPC_Hyp :=
      deduction_basic.singleHyp
    @[simp] 
    lemma same_singles : ∀ φ : MPPC_Form, 
        MPPC_has_derives.MPPC_singleton.singleton φ = set.has_singleton.singleton φ :=
    begin 
      assume φ,
      dsimp[MPPC_has_derives.MPPC_singleton,deduction_basic.singleHyp],
      rw set.is_lawful_singleton.insert_emptyc_eq,
    end

    lemma single_union {Φ : MPPC_Hyp} {φ : MPPC_Form}
        : insert φ Φ = {φ} ∪ Φ := by simp


    instance MPPC_Der : has_struct_derives MPPC_Form :=
    {
      derives := MPPC_derives,
      derive_Trans := 
        begin
          assume Φ ψ θ hφψ hψθ,
          have helper : MPPC_derives Φ (MPPC_Form.impl ψ θ),
            apply impl_intro,
            rw single_union,
            apply weak,
            exact hψθ,
          apply impl_elim ψ,
          exact helper,
          exact hφψ,
        end,
      inInsert := set.mem_insert,
      hyp := @hyp,
      weak1 := 
        begin
          assume Φ φ ψ h,
          rw single_union,
          rw set.union_comm,
          apply weak,
          exact h,
        end,
    }

    instance MPPC_top : deduction_cart.has_ltop MPPC_Form :=
    {
      top := MPPC_Form.top,
      truth := @truth,
    }
    instance MPPC_and : deduction_cart.has_and MPPC_Form :=
    {
      and := MPPC_Form.and,
      and_intro := @and_intro,
      and_eliml := @and_eliml,
      and_elimr := @and_elimr,

    }
    instance MPPC_impl : deduction_cart.has_impl MPPC_Form :=
    {
      impl := MPPC_Form.impl,
      impl_intro := @impl_intro,
      impl_elim := @impl_elim,
    }
    -- #check @dmap
    -- def dmap : ∀ φ ψ : MPPC_Form, 
      -- MPPC_has_derives.MPPC_Der.derives {φ} ψ → MPPC_has_derives.MPPC_Der.derives {φ.diamond} (ψ.diamond)
      -- :=
      -- begin
      --   assume φ ψ h,
      --   dsimp[MPPC_has_derives.MPPC_Der],
      --   dsimp[MPPC_has_derives.MPPC_Der] at h,
      --   apply @Dmap {diamond φ} ψ _ _,
      --   apply isModal.ModalInsert,
      --   apply isModal.ModalEmpty,
      --   -- apply derive_trans φ,
        
      --   exact h,
      -- end 

    -- instance MPPC_diamond : deduction_monadic.has_diamond MPPC_Form :=
    -- {
    --   diamond := MPPC_Form.diamond,
    --   dmap := Dmap, --sorry, --λ φ ψ (h:MPPC_derives {φ} ψ), @dmap φ ψ h,
    --   dpure := @dpure,
    --   djoin := @djoin,
    -- }

end MPPC_has_derives
