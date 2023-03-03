import deduction.deduction_cartesian data.set.basic
open deduction_basic

namespace PPC_defn

    inductive PPC_Form : Type
    | top : PPC_Form
    | var : ℕ → PPC_Form
    | and : PPC_Form → PPC_Form → PPC_Form
    | impl : PPC_Form → PPC_Form → PPC_Form

    prefix `p`:80     := PPC_Form.var  


    @[reducible] def PPC_Hyp : Type := set (PPC_Form)

    instance : has_union PPC_Hyp := infer_instance
    instance : has_mem PPC_Form PPC_Hyp := infer_instance
    instance : has_insert PPC_Form PPC_Hyp := infer_instance
    instance : has_emptyc PPC_Hyp := infer_instance


    inductive PPC_derives : PPC_Hyp → PPC_Form → Prop 
    | hyp {Φ : PPC_Hyp} {φ : PPC_Form}  
        : (φ ∈ Φ) →  PPC_derives Φ φ
    | truth {Φ}                               
        : PPC_derives Φ PPC_Form.top
    | and_intro {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ φ → PPC_derives Φ ψ → PPC_derives Φ (PPC_Form.and φ ψ)
    | and_eliml {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ (PPC_Form.and φ ψ) → PPC_derives Φ φ
    | and_elimr {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ (PPC_Form.and φ ψ) → PPC_derives Φ ψ
    | impl_intro {Φ : PPC_Hyp} (φ : PPC_Form) {ψ : PPC_Form}   
        : PPC_derives (insert φ Φ) ψ → PPC_derives Φ (PPC_Form.impl φ ψ)
    | impl_elim {Φ : PPC_Hyp} (φ : PPC_Form) {ψ : PPC_Form} 
        : PPC_derives Φ (PPC_Form.impl φ ψ) → PPC_derives Φ φ → PPC_derives Φ ψ
    | weak {Φ Ψ : PPC_Hyp} {φ : PPC_Form}
        : PPC_derives Φ φ → PPC_derives (Φ ∪ Ψ) φ
    open PPC_derives

end PPC_defn




namespace PPC_has_derives

    open PPC_defn
    open PPC_defn.PPC_derives
    open deduction_basic
    open deduction_cart

    instance PPC_hasHyp : has_Hyp PPC_Form :=
      { Hyp := PPC_Hyp }

    instance PPC_singleton : has_singleton PPC_Form PPC_Hyp :=
      deduction_basic.singleHyp
    @[simp] 
    lemma same_singles : ∀ φ : PPC_Form, 
        PPC_has_derives.PPC_singleton.singleton φ = set.has_singleton.singleton φ :=
    begin 
      assume φ,
      dsimp[PPC_has_derives.PPC_singleton,deduction_basic.singleHyp],
      rw set.is_lawful_singleton.insert_emptyc_eq,
    end

    -- lemma internal1_impl : ∀ {φ ψ : PPC_Form}, 
    --   PPC_derives {ψ} φ → PPC_derives ∅ (PPC_Form.impl ψ φ) :=
    -- begin 
    --     assume φ ψ h,
    --     apply impl_intro,
    --     exact h,
    -- end
    -- lemma weak1 : ∀ (φ ψ : PPC_Form), 
    --   PPC_derives ∅ ψ → PPC_derives {φ} ψ :=
    -- begin 
    --     assume φ ψ h,
    --     rw← set.empty_union {φ},
    --     apply weak,
    --     exact h,
    -- end
    -- lemma weak' {Φ Ψ : PPC_Hyp} {φ : PPC_Form}
    --     : PPC_derives Ψ φ → PPC_derives (Φ ∪ Ψ) φ :=
    -- begin
    --   rw set.union_comm,
    --   apply weak,
    -- end

    lemma single_union {Φ : PPC_Hyp} {φ : PPC_Form}
        : insert φ Φ = {φ} ∪ Φ := by simp


    instance PPC_Der : has_struct_derives PPC_Form :=
    {
      derives := PPC_derives,
      derive_Trans := 
        begin
          assume Φ ψ θ hφψ hψθ,
          have helper : PPC_derives Φ (PPC_Form.impl ψ θ),
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

    instance PPC_top : deduction_cart.has_top PPC_Form :=
    {
      top := PPC_Form.top,
      truth := @truth,
    }
    instance PPC_and : deduction_cart.has_and PPC_Form :=
    {
      and := PPC_Form.and,
      and_intro := @and_intro,
      and_eliml := @and_eliml,
      and_elimr := @and_elimr,

    }
    instance PPC_impl : deduction_cart.has_impl PPC_Form :=
    {
      impl := PPC_Form.impl,
      impl_intro := @impl_intro,
      impl_elim := @impl_elim,
    }

end PPC_has_derives

-- namespace PPC_Hyp_x

--     open PPC_defn
--     open PPC_has_derives


--     lemma insert_is_union_singleton : ∀ (Φ : PPC_Hyp) (φ : PPC_Form),
--         insert φ Φ = Φ ∪ {φ} :=
--       begin
--         assume Φ φ,
--         apply set.ext,
--         assume ψ,
--         simp,
--       end
--     lemma Hyp_twoElt_comm : ∀ (φ ψ : PPC_Form), 
--       insert φ {ψ} = insert ψ (PPC_has_derives.PPC_singleton.singleton φ) :=
--     begin
--         assume φ ψ,
--         apply set.ext,
--         assume θ,
--         simp,
--         apply or.comm,
--     end
-- end PPC_Hyp_x

-- namespace PPC_derives_x
--     open PPC_defn
--     open PPC_defn.PPC_derives
--     open PPC_has_derives
--     open PPC_Hyp_x

--     lemma trans_hyp : ∀ (Φ : PPC_Hyp) (φ ψ: PPC_Form), 
--       PPC_derives Φ φ → φ ⊢ ψ → PPC_derives Φ ψ :=
--     begin 
--         assume Φ φ ψ hΦφ hφψ,
--         have helper : PPC_derives Φ (φ ⊃ ψ),
--         apply impl_intro,
--         rewrite insert_is_union_singleton, 
--         rewrite set.union_comm,
--         apply weak,
--         exact hφψ,
--         apply impl_elim,
--         exact helper,
--         exact hΦφ,
--     end 

--     lemma modus_ponens : ∀ φ ψ : PPC_Form, PPC_derives ({φ⊃ψ}∪{φ}) ψ :=
--     begin 
--         assume φ ψ,
--         apply impl_elim,
--         apply weak,
--         apply PPC_has_derives.PPC_Der.derive_refl,
--         rewrite set.union_comm,
--         apply weak,
--         apply PPC_has_derives.PPC_Der.derive_refl,
--     end 

--     -- -- lemma hypo_syll : ∀ φ ψ θ, (φ ⊃ ψ) ⊢ ((ψ ⊃ θ) ⊃ (φ ⊃ θ)) := sorry

--     lemma hypo_syll' : ∀ (φ ψ θ : PPC_Form), (ψ ⊃ θ) ⊢ ((φ ⊃ ψ) ⊃ (φ ⊃ θ)) :=
--     begin 
--         assume φ ψ θ,
--         apply impl_intro,
--         apply impl_intro,
--         apply impl_elim ψ,
--         apply hyp, find_it,
--         apply impl_elim φ,
--         apply hyp, find_it,
--         apply hyp, find_it,
--     end 

--     lemma union_Hyp_and : ∀ φ ψ θ : PPC_Form, PPC_derives ({φ,ψ}) θ → ((φ&ψ) ⊢ θ) :=
--     begin 
--         assume φ ψ θ h,
--         apply impl_elim φ,
--         apply impl_elim ψ,
--         apply weak1,
--         apply impl_intro ψ,
--         apply impl_intro φ,
--         exact h,
--         apply and_elimr,
--         apply PPC_has_derives.PPC_Der.derive_refl,
--         apply and_eliml,
--         apply PPC_has_derives.PPC_Der.derive_refl,
--     end 

--     lemma and_Hyp_union : ∀ φ ψ θ : PPC_Form, ((φ&ψ) ⊢ θ) → PPC_derives ({ψ,φ}) θ :=
--     begin
--         assume φ ψ θ h,
--         apply impl_elim φ,
--         apply weak,
--         apply weak1,
--         apply internal1_impl,
--         exact h,
--         apply and_intro,
--         rw Hyp_twoElt_comm,
--         apply weak,
--         apply PPC_has_derives.PPC_Der.derive_refl,
--         apply PPC_derives.weak,
--         apply PPC_has_derives.PPC_Der.derive_refl,
--     end 

-- end PPC_derives_x
