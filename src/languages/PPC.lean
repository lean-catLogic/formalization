

inductive PPC_form : Type
  | top : PPC_form
  | var : ℕ → PPC_form
  | and : PPC_form → PPC_form → PPC_form
  | impl : PPC_form → PPC_form → PPC_form


notation (name:=PPC.top) `⊤`:80   := PPC_form.top
prefix `p`:80     := PPC_form.var
infix `&`:79      := PPC_form.and    
notation (name:=PPC_form.impl) φ `⊃`:80 ψ := PPC_form.impl φ ψ 

-- ⇨