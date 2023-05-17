import CCCSemantics.Lambda.Ty

inductive Ctx (Base : Type _) : Type _
| nil : Ctx Base
| cons (Γ : Ctx Base) (τ : Ty Base) : Ctx Base

notation "ε" => Ctx.nil
infixl:60 ",," => Ctx.cons

inductive Var {Base} (τ : Ty Base) : Ctx Base → Type _ 
| zero : Var τ (Γ ,, τ)
| succ : Var τ Γ → Var τ (Γ ,, υ) 

syntax "v⟨" term "⟩" : term
open Lean in
macro_rules
| `(v⟨$n:num⟩) => 
  let rec go : Nat → MacroM (TSyntax _)
          | 0 =>`(Var.zero)
          | n+1 => do `(Var.succ $(←go n))
  go n.getNat
| `(v⟨$n:ident⟩) => `(($n : Var _ _))
| `(v⟨$n+1⟩) => `(Var.succ v⟨$n⟩)
