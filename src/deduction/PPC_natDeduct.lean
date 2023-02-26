import deduction.deduction data.set.basic

namespace PPC_defn

    inductive PPC_Form : Type
    | top : PPC_Form
    | var : ℕ → PPC_Form
    | and : PPC_Form → PPC_Form → PPC_Form
    | impl : PPC_Form → PPC_Form → PPC_Form


    notation (name:=PPC.top) `⊤`:80   := PPC_Form.top
    prefix `p`:80     := PPC_Form.var
    infix `&`:79      := PPC_Form.and    
    notation (name:= PPC_Form.impl) φ `⊃`:80 ψ := PPC_Form.impl φ ψ 


    @[reducible] def PPC_Hyp : Type := set (PPC_Form)

    instance : has_union PPC_Hyp := infer_instance
    instance : has_singleton PPC_Form PPC_Hyp := infer_instance
    instance : has_mem PPC_Form PPC_Hyp := infer_instance
    instance : has_insert PPC_Form PPC_Hyp := infer_instance


    inductive PPC_derives : PPC_Hyp → PPC_Form → Prop 
    | hyp {Φ : PPC_Hyp} {φ : PPC_Form} 
        : (φ ∈ Φ) → PPC_derives Φ φ
    | truth {Φ}                               
        : PPC_derives Φ ⊤ 
    | and_intro {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ φ → PPC_derives Φ ψ → PPC_derives Φ (φ & ψ)
    | and_eliml {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ (φ & ψ) → PPC_derives Φ φ
    | and_elimr {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ (φ & ψ) → PPC_derives Φ ψ
    | impl_intro {Φ : PPC_Hyp} (φ : PPC_Form) {ψ : PPC_Form}   
        : PPC_derives (insert φ Φ) ψ → PPC_derives Φ (φ ⊃ ψ)
    | impl_elim {Φ : PPC_Hyp} (φ : PPC_Form) {ψ : PPC_Form} 
        : PPC_derives Φ (φ ⊃ ψ) → PPC_derives Φ φ → PPC_derives Φ ψ
    | weak {Φ Ψ : PPC_Hyp} {φ : PPC_Form}
        : PPC_derives Φ φ → PPC_derives (Φ ∪ Ψ) φ
    open PPC_derives

end PPC_defn




namespace PPC_has_derives

    open PPC_defn
    open PPC_defn.PPC_derives

    lemma internal1_impl : ∀ {φ ψ : PPC_Form}, PPC_derives {ψ} φ → PPC_derives ∅ (ψ ⊃ φ) :=
    begin 
        assume φ ψ h,
        apply impl_intro,
        rw set.is_lawful_singleton.insert_emptyc_eq,
        exact h,
    end
    lemma empty_union : ∀ φ : PPC_Form, {φ} = ∅ ∪ PPC_Hyp.has_singleton.singleton φ :=
    begin
        assume φ,
        symmetry,
        apply set.empty_union,
    end
    lemma weak1 : ∀ (φ ψ : PPC_Form), PPC_derives ∅ ψ → PPC_derives {φ} ψ :=
    begin 
        assume φ ψ h,
        rw empty_union,
        apply weak,
        exact h,
    end

    instance PPC_Der : has_derives PPC_Form :=
    ⟨ PPC_Hyp , 
    PPC_derives , 
    begin 
        assume φ,
        apply @hyp {φ} φ,
        apply set.mem_singleton,
    end, 
    begin
        assume φ ψ θ hφψ hψθ,
        have helper : PPC_derives {φ} (ψ ⊃ θ), 
        apply weak1,
        apply internal1_impl,
        exact hψθ,
        apply impl_elim,
        exact helper,
        exact hφψ,
    end
    ⟩ 


end PPC_has_derives

namespace PPC_Hyp_x

    open PPC_defn

    meta def find_it : tactic unit :=
        `[ repeat {{left,refl} <|> right}, try{apply set.mem_singleton}  ]

    lemma insert_is_union_singleton : ∀ (Φ : PPC_Hyp) (φ : PPC_Form),
        insert φ Φ = Φ ∪ {φ} :=
        begin
        assume Φ φ,
        apply set.ext,
        assume ψ,
        apply or_comm,
        end
    lemma Hyp_twoElt_comm : ∀ (φ ψ : PPC_Form), insert φ {ψ} = insert ψ (PPC_Hyp.has_singleton.singleton φ) :=
    begin
        assume φ ψ,
        apply set.ext,
        assume θ,
        apply or_comm,
    end
end PPC_Hyp_x

namespace PPC_derives_x
    open PPC_defn
    open PPC_defn.PPC_derives
    open PPC_has_derives
    open PPC_Hyp_x

    lemma trans_hyp : ∀ (Φ : PPC_Hyp) (φ ψ: PPC_Form), PPC_derives Φ φ → φ ⊢ ψ → PPC_derives Φ ψ :=
    begin 
        assume Φ φ ψ hΦφ hφψ,
        have helper : PPC_derives Φ (φ ⊃ ψ),
        apply impl_intro,
        rewrite insert_is_union_singleton, 
        rewrite set.union_comm,
        apply weak,
        exact hφψ,
        apply impl_elim,
        exact helper,
        exact hΦφ,
    end 

    lemma modus_ponens : ∀ φ ψ : PPC_Form, PPC_derives ({φ⊃ψ, φ}) ψ :=
    begin 
        assume φ ψ,
        apply impl_elim,
        apply weak,
        apply PPC_has_derives.PPC_Der.derive_refl,
        rw Hyp_twoElt_comm,
        apply weak,
        apply PPC_has_derives.PPC_Der.derive_refl,
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

    lemma union_Hyp_and : ∀ φ ψ θ : PPC_Form, PPC_derives ({φ,ψ}) θ → ((φ&ψ) ⊢ θ) :=
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
        apply PPC_has_derives.PPC_Der.derive_refl,
        apply and_eliml,
        apply PPC_has_derives.PPC_Der.derive_refl,
    end 

    lemma and_Hyp_union : ∀ φ ψ θ : PPC_Form, ((φ&ψ) ⊢ θ) → PPC_derives ({ψ,φ}) θ :=
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
        apply PPC_has_derives.PPC_Der.derive_refl,
        apply PPC_derives.weak,
        apply PPC_has_derives.PPC_Der.derive_refl,
    end 

end PPC_derives_x
