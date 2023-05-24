import CCCSemantics.Library
import CCCSemantics.Lambda.Type

inductive Ctx (σ : Sig) : Type _
| nil : Ctx σ
| cons (Γ : Ctx σ) (τ : Ty σ.types) : Ctx σ

notation "ε" => Ctx.nil
infixl:60 ",," => Ctx.cons

inductive Var {σ} (τ : Ty σ.types) : Ctx σ → Type _ 
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
