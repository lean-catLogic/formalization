import semantics.syntacticPoset categoryTheory.CCC category_theory.category.preorder
open category_theory
open deduction_basic

namespace synCat
  open synPoset

  variable {Form : Type}

  -- Form the category out of this poset
  def syn_cat [Der : has_struct_derives Form] : thin_cat (Form _eq)
    := thin_cat.from_preorder synPoset.syn_eq_pre
  instance [Der : has_struct_derives Form] : thin_cat (Form _eq) := syn_cat

  -- Methods for directly turning formulas into objects and derivations into morphisms
  def syn_obj [Der : has_struct_derives Form] (φ : Form) : Form _eq := 
    Form_eq_in φ
  def syn_hom [Der : has_struct_derives Form] : 
      ∀ {φ ψ : Form}, (φ ⊢ ψ) → (syn_obj φ ⟶ syn_obj ψ) 
  := begin
    assume φ ψ h,
    apply hom_of_le,
    exact h,
  end
  def syn_hom_inv [Der : has_struct_derives Form] : 
      ∀ {φ ψ : Form}, (syn_obj φ ⟶ syn_obj ψ) → (φ ⊢ ψ) :=
  begin
    assume φ ψ H,
    apply @le_of_hom Form synPoset.syn_preorder,
    exact H,
  end

  def derives_of_hom [Der : has_struct_derives Form] {φ ψ : Form} (f : syn_obj φ ⟶ syn_obj ψ) : 
    Der.derives {φ} ψ :=
    le_of_hom f

end synCat

namespace synCat_tactics
  open tactic
  open interactive (parse)
  open lean.parser (ident)  
  open lean.parser (tk)
  open tactic.interactive («have»)


  /- Turns a hypothesis for the form ⦃φ⦄ ⟶ ⦃ψ⦄ into a
     derivation  φ ⊢ ψ -/
  meta def Lower (n : parse ident) : tactic unit 
  := do
    e ← (resolve_name n) >>= tactic.i_to_expr,
    «have» n none ``(synCat.syn_hom_inv %%e),
    tactic.clear e



  /- Tactic which accepts a type as an expr
     and counts the number of assumed objects and
     morphisms
  -/
  open nat
  meta def incrLeft : nat × nat → tactic(nat × nat)
    | (o,m) := return (succ o, m)
  meta def incrRight : nat × nat → tactic(nat × nat)
    | (o,m) := return (o, succ m)

  meta def mkCount : expr →  tactic (nat × nat)
  | `( Π {_ : _ _eq}, %%newGoal) := mkCount newGoal >>= incrLeft
  | `( Π {_ : _ ⟶ _}, %%newGoal) := mkCount newGoal >>= incrRight
  | _ := return (0,0)
  
  /- Like mkCount, but treats any non-morphism as an object -/
  meta def sloppyMkCount : expr →  tactic (nat × nat)
  | `( Π {_ : _ ⟶ _}, %%newGoal) := sloppyMkCount newGoal >>= incrRight
  | `( Π _, %%newGoal) := sloppyMkCount newGoal >>= incrLeft
  | _ := return (0,0)

  meta def doCount (sloppy : parse (optional $ tk "?")) : tactic (nat × nat) :=
    do
    let counter := match sloppy with none := mkCount | _ := sloppyMkCount end,
    (numobjs,nummor) ← target >>= counter,
    trace $ "Objs: " ++ (repr numobjs) ++ ", Morphs: " ++ (repr nummor),
    return (numobjs,nummor)

  /-
  Tactic for doing constructions in syn_cat which are actually just
  the derivation rules lifted onto equivalence classes
  Invoking as LiftT? LiftT?! or LiftT?!! will only partially perform
  the tactic (useful for debugging)
  Tactic input should be of the form `[ apply XXX ]
  where XXX is a derivation rule of Der, though it could be more elaborate
 -/
  meta def LiftT 
    (debugMode : parse (optional $ tk "?")) 
    (debugPerformTac : parse (optional $ tk "!"))
    (debugCleanup : parse (optional $ tk "!"))
    (T : tactic unit) 
    : tactic unit :=
  do
    let proceedLevel := 
      match (debugMode,debugPerformTac,debugCleanup) with 
      | (none,_,_) := 4 -- LiftT    invoked: do everything
      | (_,none,_) := 1 -- LiftT?   invoked: just do the assume's and syn_hom
      | (_,_,none) := 2 -- LiftT?!  invoked: also apply the tactic
      | _ := 3          -- LiftT?!! invoked: also do the first stage of cleanup
      end,
    -- Count & print how many objects and morphisms to assume
    (numobjs,nummor) ← doCount none,
    /- Assume objects and morphisms, 
      - use induction to get that every object is of the form ⦃φ⦄ for some φ:Form 
      - use syn_hom_inv to turn every assumed morphism into a derivation -/
    repeat_assume_induct (gen_nameList `φ_ numobjs),
    repeat_assume_replace `synCat.syn_hom_inv (gen_nameList `f_ nummor),
    -- Turn the synCat hom goal to a derivation goal
    applyc `synCat.syn_hom,
  when (proceedLevel > 1) $ do
    -- Apply the input tactic
    T,
  when (proceedLevel > 2) $ do
    -- Eliminate other goals (first stage of cleanup)
    iterate (
      (applyc `deduction_basic.derive_refl)
      <|> assumption
    ),
  when (proceedLevel > 3) $ do
    -- Prove the coherences
    thin_cat.by_thin

  /- Same as LiftT, but takes in Form and Der as arguments, in case 
     Lean can't deduce them. Uses sloppyMkCount, in case the object
     type isn't exactly (Something _eq) -/
  meta def HeavyLiftT
    (debugMode : parse (optional $ tk "?")) 
    (debugPerformTac : parse (optional $ tk "!"))
    (debugCleanup : parse (optional $ tk "!"))
    (FORM : parse ident)
    (DER : parse ident)
    (T : tactic unit) 
    : tactic unit :=
  do
    Form ← resolve_name FORM,
    Der ← resolve_name DER,
    let proceedLevel := 
      match (debugMode,debugPerformTac,debugCleanup) with 
      | (none,_,_) := 4 -- LiftT    invoked: do everything
      | (_,none,_) := 1 -- LiftT?   invoked: just do the assume's and syn_hom
      | (_,_,none) := 2 -- LiftT?!  invoked: also apply the tactic
      | _ := 3          -- LiftT?!! invoked: also do the first stage of cleanup
      end,
    -- Count & print how many objects and morphisms to assume
    (numobjs,nummor) ← doCount (some()),
    /- Assume objects and morphisms, 
      - use induction to get that every object is of the form ⦃φ⦄ for some φ:Form 
      - use syn_hom_inv to turn every assumed morphism into a derivation -/
    repeat_assume_induct (gen_nameList `φ_ numobjs),
    repeat_assume_replace `synCat.syn_hom_inv (gen_nameList `f_ nummor),
    -- Turn the synCat hom goal to a derivation goal
    applyc `synCat.syn_hom,
  when (proceedLevel > 1) $ do
    -- Apply the input tactic
    T,
  when (proceedLevel > 2) $ do
    -- Eliminate other goals (first stage of cleanup)
    iterate (
      (i_to_expr ``(@deduction_basic.derive_refl %%Form %%Der) >>= apply >> return ())
      <|> assumption
    ),
  when (proceedLevel > 3) $ do
    -- Prove the coherences
    thin_cat.by_thin

end synCat_tactics

run_cmd add_interactive [`synCat_tactics.LiftT,`synCat_tactics.HeavyLiftT,`synCat_tactics.Lower,`synCat_tactics.doCount]

