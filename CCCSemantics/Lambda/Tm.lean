import CCCSemantics.Lambda.Ctx

structure Sig where
  types : Type u
  terms : Type v
  typing : terms → Ty types

section
variable (σ : Sig)

inductive Tm (σ : Sig) : Ctx σ.types → Ty σ.types → Type _
| var : Var τ Γ → Tm σ Γ τ
| base (t : σ.terms) : Tm σ Γ (σ.typing t)
| lam : Tm σ (Γ ,, τ) υ → Tm σ Γ (τ.arr υ)
| app : Tm σ Γ (τ.arr υ) → Tm σ Γ τ → Tm σ Γ υ

notation Γ " ⊢ " τ:80 => Tm _ Γ τ

end
