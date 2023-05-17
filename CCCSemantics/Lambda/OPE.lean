import Mathlib

import CCCSemantics.Lambda.Tm

inductive OPE : Ctx Base → Ctx Base → Type _
| done : OPE ε ε
| keep : OPE Γ Δ → OPE (Γ ,, τ) (Δ ,, τ)
| skip : OPE Γ Δ → OPE (Γ ,, τ) Δ

namespace OPE

def var : OPE Γ Δ → Var τ Δ → Var τ Γ
| keep e, .zero   => .zero 
| keep e, .succ n => .succ (var e n)
| skip e, v       => .succ (var e v)

def apply : OPE Γ Δ → Δ ⊢ τ → Γ ⊢ τ
| e, .var v   => .var (var e v)
| _, .base b  => .base b
| e, .lam t   => .lam (apply (.keep e) t)
| e, .app t u => .app (apply e t) (apply e u)

def ide : ∀ Γ : Ctx Base, OPE Γ Γ
| ε      => done
| Γ ,, _ => keep (ide Γ)

def trans : OPE Γ Δ → OPE Δ Ε → OPE Γ Ε
| done,    e₂    => e₂
| keep e₁, keep e₂ => keep (trans e₁ e₂)
| keep e₁, skip e₂ => skip (trans e₁ e₂)
| skip e₁, e₂      => skip (e₁.trans e₂)

@[simp]
lemma ide_trans : ∀ {Γ Δ : Ctx α} (e : OPE Γ Δ), trans (ide Γ) e = e
| ε, ε,      done   => rfl
| _,      _, keep e => congrArg keep (ide_trans e)
| _,      _, skip e => congrArg skip (ide_trans e)

@[simp]
lemma trans_ide : ∀ {Γ Δ : Ctx α} (e : OPE Γ Δ), trans e  (ide Δ) = e
| ε, ε,      done   => rfl
| _,      _, keep e => congrArg keep (trans_ide e)
| _,      _, skip e => congrArg skip (trans_ide e)

@[simp]
lemma trans_assoc : ∀ (e₁ : OPE Γ Δ) (e₂ : OPE Δ Ε) (e₃ : OPE Ε Θ), trans (trans e₁ e₂) e₃ = trans e₁ (trans e₂ e₃)
| done,    e₂, e₃ => rfl
| keep e₁, keep e₂, keep e₃ => congrArg keep (trans_assoc e₁ e₂ e₃)
| keep e₁, keep e₂, skip e₃ => congrArg skip (trans_assoc e₁ e₂ e₃)
| keep e₁, skip e₂, e₃ => congrArg skip (trans_assoc e₁ e₂ e₃)
| skip e₁, e₂, e₃ => congrArg skip (trans_assoc e₁ e₂ e₃)

def Emb (σ : Sig) := Ctx σ.types
section
open CategoryTheory
instance : Category (Emb σ) where
  Hom := OPE
  id := ide
  comp := trans

end

def var_ide : ∀ t : Var τ Γ, var (ide Γ) t = t
| v⟨0⟩   => rfl
| v⟨n+1⟩ => congrArg Var.succ (var_ide n)

@[simp]
def apply_ide : ∀ t : Γ ⊢ τ, apply (ide Γ) t = t
| .var v => congrArg Tm.var (var_ide v)
| .base b => rfl
| .lam t => congrArg Tm.lam (apply_ide _)
| .app t u => congrArg₂ Tm.app (apply_ide t) (apply_ide u)

def var_trans : ∀ (e₁ : OPE Γ Δ) (e₂ : OPE Δ Ε) (t : Var τ Ε),
  var (trans e₁ e₂) t = var e₁ (var e₂ t)
| done, e₂, n => nomatch var e₂ n
| keep e₁, .keep e₂, v⟨0⟩ => rfl
| keep e₁, .keep e₂, v⟨n+1⟩ => congrArg Var.succ (var_trans e₁ e₂ n)
| keep e₁, .skip e₂, n => congrArg Var.succ (var_trans e₁ e₂ n)
| skip e₁, e₂, n => congrArg Var.succ (var_trans e₁ e₂ n)

@[simp]
def apply_trans : ∀ (e₁ : OPE Γ Δ) (e₂ : OPE Δ Ε) (t : Ε ⊢ τ),
  apply (trans e₁ e₂) t = apply e₁ (apply e₂ t)
| e₁, e₂, .var v => congrArg Tm.var (var_trans e₁ e₂ v)
| _,  _,  .base b => rfl
| e₁, e₂, .lam t => congrArg Tm.lam (apply_trans e₁.keep e₂.keep t)
| e₁, e₂, .app t u => congrArg₂ Tm.app (apply_trans e₁ e₂ t)
                                       (apply_trans e₁ e₂ u)

def bang : ∀ Γ : Ctx α, OPE Γ ε
| ε => done
| Γ ,, _ => skip (bang Γ)

def bang_unique : (e : OPE Γ ε) → e = bang Γ
| done   => rfl
| skip e => congrArg skip (bang_unique e)

lemma apply_done : ∀ t : ε ⊢ τ, apply done t = t := apply_ide


end OPE