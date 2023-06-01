import CCCSemantics.Lambda.Renaming

open Categories

section
inductive Tm {σ : Sig} : Ctx σ → Ty σ.types → Type _
| var : Var τ Γ → Tm Γ τ
| base (t : σ.terms) : Tm Γ (σ.typing t)
| lam : Tm (Γ ,, τ) υ → Tm Γ (τ.arr υ)
| app : Tm Γ (τ.arr υ) → Tm Γ τ → Tm Γ υ
| unit : Tm Γ Ty.unit
| pair : Tm Γ τ → Tm Γ υ → Tm Γ (τ.prod υ)
| fst : Tm Γ (τ.prod υ) → Tm Γ τ
| snd : Tm Γ (Ty.prod τ υ) → Tm Γ υ 

notation Γ " ⊢ " τ:80 => Tm Γ τ

end

namespace Tm
def rename : Δ ⊢ τ → Renaming Γ Δ → Γ ⊢ τ
| .var v,    e => .var (v.rename e)
| .base b,   _ => .base b
| .lam t,    e => .lam (t.rename (e.keep _))
| .app t u,  e => .app (t.rename e) (u.rename e)
| .pair t u, e => .pair (t.rename e) (u.rename e)
| .fst t,    e => .fst (t.rename e)
| .snd t,    e => .snd (t.rename e)
| .unit,     e => .unit

@[simp]
theorem rename_ide : ∀ t : Γ ⊢ τ, t.rename (Renaming.ide Γ) = t
| .var v => congrArg Tm.var v.rename_ide
| .base b => rfl
| .lam t => congrArg Tm.lam t.rename_ide
| .app t u => congrArg₂ Tm.app t.rename_ide u.rename_ide
| .pair t u => congrArg₂ Tm.pair t.rename_ide u.rename_ide
| .fst t    => congrArg Tm.fst t.rename_ide
| .snd t    => congrArg Tm.snd t.rename_ide
| .unit     => rfl

@[simp]
theorem rename_comp :
  ∀ (t : Ε ⊢ τ) (e₁ : Renaming Δ Ε) (e₂ : Renaming Γ Δ),
  t.rename (e₁.comp e₂) = (t.rename e₁).rename e₂
| .var v ,    e₁, e₂ => congrArg Tm.var (v.rename_comp e₁ e₂)
| .base _,    _,  _  => rfl
| .lam t ,    e₁, e₂ => congrArg (Tm.lam ·) ((congrArg t.rename
                                                       (Renaming.keep_comp_keep e₁
                                                                                e₂
                                                        ).symm).trans
                                             (rename_comp t (e₁.keep _) (e₂.keep _)))
| .app t u,   e₁, e₂ => congrArg₂ Tm.app (t.rename_comp e₁ e₂)
                                         (u.rename_comp e₁ e₂)
| .pair t u , e₁, e₂ => congrArg₂ Tm.pair (t.rename_comp e₁ e₂)
                                          (u.rename_comp e₁ e₂)
| .fst t,     e₁, e₂ => congrArg Tm.fst (t.rename_comp e₁ e₂)
| .snd t,     e₁, e₂ => congrArg Tm.snd (t.rename_comp e₁ e₂)
| .unit,      _,  _  => rfl

end Tm