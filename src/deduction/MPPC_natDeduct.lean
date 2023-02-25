import deduction.deduction data.set.basic

namespace MPPC_defn

    inductive MPPC_Form : Type
    | top : MPPC_Form
    | var : ℕ → MPPC_Form
    | and : MPPC_Form → MPPC_Form → MPPC_Form
    | impl : MPPC_Form → MPPC_Form → MPPC_Form
    | diamond : MPPC_Form → MPPC_Form


    notation (name:=MPPC.top) `⊤`:80   := MPPC_Form.top
    prefix `p`:80     := MPPC_Form.var
    infix `&`:79      := MPPC_Form.and    
    notation (name:= MPPC_Form.impl) φ `⊃`:80 ψ := MPPC_Form.impl φ ψ 
    notation (name:= MPPC_Form.diamond) `◇`:max φ := MPPC_Form.diamond φ 


    @[reducible] def MPPC_Hyp : Type := set (MPPC_Form)

    instance : has_union MPPC_Hyp := infer_instance
    instance : has_singleton MPPC_Form MPPC_Hyp := infer_instance
    instance : has_mem MPPC_Form MPPC_Hyp := infer_instance
    instance : has_insert MPPC_Form MPPC_Hyp := infer_instance
    instance : has_emptyc MPPC_Hyp := infer_instance
    instance : is_lawful_singleton MPPC_Form MPPC_Hyp := infer_instance

    inductive MPPC_derives : MPPC_Hyp → MPPC_Form → Prop 
    | hyp {Φ : MPPC_Hyp} {φ : MPPC_Form}  
        : (φ ∈ Φ) →  MPPC_derives Φ φ
    | truth {Φ}                               
        : MPPC_derives Φ ⊤ 
    | and_intro {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ φ → MPPC_derives Φ ψ → MPPC_derives Φ (φ & ψ)
    | and_eliml {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ (φ & ψ) → MPPC_derives Φ φ
    | and_elimr {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ (φ & ψ) → MPPC_derives Φ ψ
    | impl_intro {Φ : MPPC_Hyp} (φ : MPPC_Form) {ψ : MPPC_Form}   
        : MPPC_derives (insert φ Φ) ψ → MPPC_derives Φ (φ ⊃ ψ)
    | impl_elim {Φ : MPPC_Hyp} (φ : MPPC_Form) {ψ : MPPC_Form} 
        : MPPC_derives Φ (φ ⊃ ψ) → MPPC_derives Φ φ → MPPC_derives Φ ψ
    | weak {Φ Ψ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ φ → MPPC_derives (Φ ∪ Ψ) φ
    | dmap {φ ψ : MPPC_Form}
        : MPPC_derives {φ} ψ → MPPC_derives {◇φ} ◇ψ
    | dpure {Φ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ φ → MPPC_derives Φ (◇φ)
    | djoin {Φ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ (◇◇φ) → MPPC_derives Φ (◇φ)
    open MPPC_derives


end MPPC_defn





namespace MPPC_has_derives

    open MPPC_defn
    open MPPC_defn.MPPC_derives
    lemma internal1_impl : ∀ {φ ψ : MPPC_Form}, MPPC_derives {ψ} φ → MPPC_derives ∅ (ψ ⊃ φ) :=
    begin 
        assume φ ψ h,
        apply impl_intro,
        rw set.is_lawful_singleton.insert_emptyc_eq,
        exact h,
    end
    lemma empty_union : ∀ φ : MPPC_Form, {φ} = ∅ ∪ MPPC_Hyp.has_singleton.singleton φ :=
    begin
        assume φ,
        symmetry,
        apply set.empty_union,
    end
    lemma weak1 : ∀ (φ ψ : MPPC_Form), MPPC_derives ∅ ψ → MPPC_derives {φ} ψ :=
    begin 
        assume φ ψ h,
        rw empty_union,
        apply weak,
        exact h,
    end
    lemma MPPC_derive_refl : ∀ φ, MPPC_derives {φ} φ :=
      λ φ, hyp (set.mem_singleton φ)

    lemma MPPC_derive_trans : ∀ (φ ψ θ : MPPC_Form),
        MPPC_derives {φ} ψ → MPPC_derives {ψ} θ → MPPC_derives {φ} θ :=
    begin
        assume φ ψ θ hφψ hψθ,
        have helper : MPPC_derives {φ} (ψ ⊃ θ), 
        apply weak1,
        apply internal1_impl,
        exact hψθ,
        apply impl_elim,
        exact helper,
        exact hφψ,
    end


    instance MPPC_Der : has_derives MPPC_Form :=
      ⟨   
        MPPC_Hyp, 
        MPPC_derives, 
        MPPC_derive_refl, 
        MPPC_derive_trans
      ⟩ 

end MPPC_has_derives



namespace MPPC_Hyp_x

    open MPPC_defn

    @[simp] lemma lawful_singleton : ∀ {φ : MPPC_Form},
        MPPC_Hyp.has_insert.insert φ MPPC_Hyp.has_emptyc.emptyc =
        MPPC_Hyp.has_singleton.singleton φ := 
        MPPC_defn.MPPC_Hyp.is_lawful_singleton.insert_emptyc_eq


    meta def find_it : tactic unit :=
        `[ repeat {{left,refl} <|> right}, try{apply set.mem_singleton}  ]

    lemma insert_is_union_singleton : ∀ (Φ : MPPC_Hyp) (φ : MPPC_Form),
        insert φ Φ = Φ ∪ {φ} :=
        begin
        assume Φ φ,
        apply set.ext,
        assume ψ,
        apply or_comm,
        end
    lemma Hyp_twoElt_comm : ∀ (φ ψ : MPPC_Form), insert φ {ψ} = insert ψ (MPPC_Hyp.has_singleton.singleton φ) :=
    begin
        assume φ ψ,
        apply set.ext,
        assume θ,
        apply or_comm,
    end
end MPPC_Hyp_x

namespace MPPC_derives_x
    open MPPC_defn
    open MPPC_defn.MPPC_derives
    open MPPC_has_derives
    open MPPC_Hyp_x

    lemma trans_hyp : ∀ (Φ : MPPC_Hyp) (φ ψ: MPPC_Form), MPPC_derives Φ φ → φ ⊢ ψ → MPPC_derives Φ ψ :=
    begin 
        assume Φ φ ψ hΦφ hφψ,
        have helper : MPPC_derives Φ (φ ⊃ ψ),
        apply impl_intro,
        rewrite insert_is_union_singleton, 
        rewrite set.union_comm,
        apply weak,
        exact hφψ,
        apply impl_elim,
        exact helper,
        exact hΦφ,
    end 

    lemma modus_ponens : ∀ φ ψ : MPPC_Form, MPPC_derives ({φ⊃ψ,φ}) ψ :=
    begin
        assume φ ψ,
        apply impl_elim,
        apply weak,
        apply MPPC_derive_refl,
        rewrite Hyp_twoElt_comm,
        apply weak,
        apply MPPC_derive_refl,
    end 

    -- -- lemma hypo_syll : ∀ φ ψ θ, (φ ⊃ ψ) ⊢ ((ψ ⊃ θ) ⊃ (φ ⊃ θ)) := sorry

    lemma hypo_syll' : ∀ φ ψ θ, (ψ ⊃ θ) ⊢ ((φ ⊃ ψ) ⊃ (φ ⊃ θ)) :=
    begin 
        assume φ ψ θ,
        apply impl_intro,
        apply impl_intro,
        apply impl_elim ψ,
        apply hyp, find_it,
        apply impl_elim φ,
        apply hyp, find_it,
        apply hyp, find_it,
    end 

    lemma union_Hyp_and : ∀ φ ψ θ : MPPC_Form, MPPC_derives ({φ,ψ}) θ → ((φ&ψ) ⊢ θ) :=
    begin 
        assume φ ψ θ h,
        apply impl_elim φ,
        apply impl_elim ψ,
        apply weak1,
        apply impl_intro ψ,
        rw set.is_lawful_singleton.insert_emptyc_eq,
        apply impl_intro φ,
        exact h,
        apply and_elimr,
        apply MPPC_derive_refl,
        apply and_eliml,
        apply MPPC_derive_refl,
    end 

    lemma and_Hyp_union : ∀ φ ψ θ : MPPC_Form, ((φ&ψ) ⊢ θ) → MPPC_derives ({ψ,φ}) θ :=
    begin
        assume φ ψ θ h,
        apply impl_elim,
        apply weak,
        apply weak1,
        apply internal1_impl,
        exact h,
        apply and_intro,
        rw Hyp_twoElt_comm,
        apply weak,
        apply MPPC_derive_refl,
        apply MPPC_derives.weak,
        apply MPPC_derive_refl,
    end 

end MPPC_derives_x


-- open MPPC_defn
-- open MPPC_defn.MPPC_derives
-- open MPPC_has_derives

-- example : ∀ φ, MPPC_has_derives.MPPC_Der.derives ∅ (φ ⊃ ◇φ) :=
-- begin
--     assume φ,
--     apply impl_intro,
--     apply dpure,
--     simp[MPPC_Hyp_x.lawful_singleton],
--     exact (MPPC_derive_refl φ),
-- end