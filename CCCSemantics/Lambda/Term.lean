import CCCSemantics.Lambda.Renaming

section
variable (σ : Sig)

inductive Tm (σ : Sig) : Ctx σ → Ty σ.types → Type _
| var : Var τ Γ → Tm σ Γ τ
| base (t : σ.terms) : Tm σ Γ (σ.typing t)
| lam : Tm σ (Γ ,, τ) υ → Tm σ Γ (τ.arr υ)
| app : Tm σ Γ (τ.arr υ) → Tm σ Γ τ → Tm σ Γ υ
| unit : Tm σ Γ Ty.unit
| pair : Tm σ Γ τ → Tm σ Γ υ → Tm σ Γ (τ.prod υ)
| fst : Tm σ Γ (τ.prod υ) → Tm σ Γ τ
| snd : Tm σ Γ (Ty.prod τ υ) → Tm σ Γ υ 

notation Γ " ⊢ " τ:80 => Tm _ Γ τ

end

namespace Renaming
def apply : Renaming Γ Δ → Δ ⊢ τ → Γ ⊢ τ
| e, .var v    => .var (var e v)
| _, .base b   => .base b
| e, .lam t    => .lam (apply (.keep e) t)
| e, .app t u  => .app (apply e t) (apply e u)
| e, .pair t u => .pair (e.apply t) (e.apply u)
| e, .fst t    => .fst (e.apply t)
| e, .snd t    => .snd (e.apply t)
| e, .unit     => .unit

@[simp]
theorem apply_ide : ∀ t : Γ ⊢ τ, apply (ide Γ) t = t
| .var v => congrArg Tm.var (var_ide v)
| .base b => rfl
| .lam t => congrArg Tm.lam (apply_ide _)
| .app t u => congrArg₂ Tm.app (apply_ide t) (apply_ide u)
| .pair t u => congrArg₂ Tm.pair (apply_ide t) (apply_ide u)
| .fst t    => congrArg Tm.fst (apply_ide t)
| .snd t    => congrArg Tm.snd (apply_ide t)
| .unit     => rfl

theorem var_trans : ∀ (e₁ : Renaming Γ Δ) (e₂ : Renaming Δ Ε) (t : Var τ Ε),
  var (trans e₁ e₂) t = var e₁ (var e₂ t)
| done, e₂, n => nomatch var e₂ n
| keep e₁, .keep e₂, v⟨0⟩ => rfl
| keep e₁, .keep e₂, v⟨n+1⟩ => congrArg Var.succ (var_trans e₁ e₂ n)
| keep e₁, .skip e₂, n => congrArg Var.succ (var_trans e₁ e₂ n)
| skip e₁, e₂, n => congrArg Var.succ (var_trans e₁ e₂ n)

@[simp]
theorem apply_trans : ∀ (e₁ : Renaming Γ Δ) (e₂ : Renaming Δ Ε) (t : Ε ⊢ τ),
  apply (trans e₁ e₂) t = apply e₁ (apply e₂ t)
| e₁, e₂, .var v => congrArg Tm.var (var_trans e₁ e₂ v)
| _,  _,  .base b => rfl
| e₁, e₂, .lam t => congrArg Tm.lam (apply_trans e₁.keep e₂.keep t)
| e₁, e₂, .app t u => congrArg₂ Tm.app (apply_trans e₁ e₂ t)
                                       (apply_trans e₁ e₂ u)
| e₁, e₂, .pair t u => congrArg₂ Tm.pair (apply_trans e₁ e₂ t)
                                         (apply_trans e₁ e₂ u)
| e₁, e₂, .fst t => congrArg Tm.fst (apply_trans e₁ e₂ t)
| e₁, e₂, .snd t => congrArg Tm.snd (apply_trans e₁ e₂ t)
| _,  _,  .unit => rfl

theorem apply_done : ∀ t : ε ⊢ τ, apply done t = t := apply_ide
end Renaming