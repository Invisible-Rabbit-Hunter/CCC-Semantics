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
