import CCCSemantics.Lambda.Context

inductive Renaming : Ctx Base → Ctx Base → Type _
| done : Renaming ε ε
| keep : Renaming Γ Δ → Renaming (Γ ,, τ) (Δ ,, τ)
| skip : Renaming Γ Δ → Renaming (Γ ,, τ) Δ

namespace Renaming

def ide : ∀ Γ : Ctx Base, Renaming Γ Γ
| ε      => done
| Γ ,, _ => keep (ide Γ)

def trans : Renaming Γ Δ → Renaming Δ Ε → Renaming Γ Ε
| done,    e₂    => e₂
| keep e₁, keep e₂ => keep (trans e₁ e₂)
| keep e₁, skip e₂ => skip (trans e₁ e₂)
| skip e₁, e₂      => skip (e₁.trans e₂)

@[simp]
theorem ide_trans : ∀ {Γ Δ : Ctx α} (e : Renaming Γ Δ), trans (ide Γ) e = e
| ε, ε,      done   => rfl
| _,      _, keep e => congrArg keep (ide_trans e)
| _,      _, skip e => congrArg skip (ide_trans e)

@[simp]
theorem trans_ide : ∀ {Γ Δ : Ctx α} (e : Renaming Γ Δ), trans e  (ide Δ) = e
| ε, ε,      done   => rfl
| _,      _, keep e => congrArg keep (trans_ide e)
| _,      _, skip e => congrArg skip (trans_ide e)

@[simp]
theorem trans_assoc : ∀ (e₁ : Renaming Γ Δ) (e₂ : Renaming Δ Ε) (e₃ : Renaming Ε Θ), trans (trans e₁ e₂) e₃ = trans e₁ (trans e₂ e₃)
| done,    e₂, e₃ => rfl
| keep e₁, keep e₂, keep e₃ => congrArg keep (trans_assoc e₁ e₂ e₃)
| keep e₁, keep e₂, skip e₃ => congrArg skip (trans_assoc e₁ e₂ e₃)
| keep e₁, skip e₂, e₃ => congrArg skip (trans_assoc e₁ e₂ e₃)
| skip e₁, e₂, e₃ => congrArg skip (trans_assoc e₁ e₂ e₃)

def var : Renaming Γ Δ → Var τ Δ → Var τ Γ
| keep e, .zero   => .zero 
| keep e, .succ n => .succ (var e n)
| skip e, v       => .succ (var e v)

def var_ide : ∀ t : Var τ Γ, var (ide Γ) t = t
| v⟨0⟩   => rfl
| v⟨n+1⟩ => congrArg Var.succ (var_ide n)

def bang : ∀ Γ : Ctx α, Renaming Γ ε
| ε => done
| Γ ,, _ => skip (bang Γ)

def bang_unique : (e : Renaming Γ ε) → e = bang Γ
| done   => rfl
| skip e => congrArg skip (bang_unique e)

end Renaming