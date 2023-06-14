import CCCSemantics.Lambda.Context
import CCCSemantics.Categories.Category

inductive Renaming : Ctx Base → Ctx Base → Type _
| nil : Renaming Γ ε
| cons : Renaming Γ Δ → Var τ Γ → Renaming Γ (Δ ,, τ)

def Var.rename : Var τ Δ → Renaming Γ Δ → Var τ Γ
| .zero,   .cons _ v => v 
| .succ v, .cons r _ => v.rename r

namespace Renaming

def drop τ : Renaming Γ Δ → Renaming (Γ ,, τ) Δ
| .nil      => .nil
| .cons r v => .cons (r.drop τ) (.succ v)

def keep τ : Renaming Γ Δ → Renaming (Γ ,, τ) (Δ ,, τ) :=
  λ r => .cons (r.drop τ) .zero

def ide : ∀ Γ : Ctx Base, Renaming Γ Γ
| ε      => nil
| Γ ,, _ => keep _ (ide Γ)

def comp : Renaming Δ Ε → Renaming Γ Δ → Renaming Γ Ε
| .nil,      r₂ => .nil
| cons r₁ v, r₂ => .cons (r₁.comp r₂) (v.rename r₂)

def head : Renaming Γ (Δ ,, τ) → Renaming Γ Δ
| .cons r _ => r

def tail : Renaming Γ (Δ ,, τ) → Var τ Γ
| .cons _ v => v

end Renaming

namespace Var
@[simp]
theorem rename_drop : ∀ (v : Var τ Δ) (r : Renaming Γ Δ) υ,
  v.rename (r.drop υ) = Var.succ (v.rename r)
| .zero,   .cons _ _, _ => rfl
| .succ v, .cons r _, _ => rename_drop v r _

@[simp]
theorem rename_ide : ∀ (v : Var τ Γ), v.rename (Renaming.ide Γ) = v
| .zero   => rfl
| .succ v => (rename_drop v _ _).trans (congrArg _ (rename_ide v))

@[simp]
theorem rename_comp : ∀ (v : Var τ Ε) (r₁ : Renaming Δ Ε) (r₂ : Renaming Γ Δ),
  v.rename (r₁.comp r₂) = (v.rename r₁).rename r₂
| .zero,   .cons _ _, r₂ => rfl
| .succ v, .cons r₁ _, r₂ => rename_comp v r₁ r₂
end Var

namespace Renaming
@[simp]
theorem drop_comp : ∀ (r₁ : Renaming Δ Ε) (r₂ : Renaming Γ (Δ,,τ)), 
  (r₁.drop τ).comp r₂ = (r₁.comp r₂.head)
| .nil,       _         => rfl
| .cons _ _, .cons _ _ => congrArg (cons · _) (drop_comp _ _)

@[simp]
theorem comp_drop : ∀ (r₁ : Renaming Δ Ε) (r₂ : Renaming Γ Δ), 
  r₁.comp (r₂.drop τ) = (r₁.comp r₂).drop τ
| .nil,       _ => rfl
| .cons r₁ v, _ => congrArg₂ cons (comp_drop r₁ _)
                                  (v.rename_drop _ _)

@[simp]
theorem keep_comp_keep : ∀ (r₁ : Renaming Δ Ε) (r₂ : Renaming Γ Δ), 
  (r₁.keep τ).comp (r₂.keep τ) = (r₁.comp r₂).keep τ :=
  λ _ _ => congrArg (cons · _) ((drop_comp _ _).trans (comp_drop _ _))

@[simp]
theorem ide_comp : ∀ {Γ Δ : Ctx σ} (r : Renaming Γ Δ), (ide Δ).comp r = r
| _, .nil,      .nil      => rfl
| _, .cons Δ _, .cons r v =>
  congrArg (cons · v) ((drop_comp (ide Δ) (.cons r v)).trans (ide_comp r))

@[simp]
theorem comp_ide : ∀ {Γ Δ : Ctx σ} (r : Renaming Γ Δ), comp r (ide Γ) = r
| _,      _, .nil      => rfl
| _ ,, _, _, .cons r v =>
  congrArg₂ (cons · ·) (comp_ide r) v.rename_ide

@[simp]
theorem comp_assoc : ∀ (r₁ : Renaming Ε Θ) (r₂ : Renaming Δ Ε) (r₃ : Renaming Γ Δ), comp (comp r₁ r₂) r₃ = comp r₁ (comp r₂ r₃)
| .nil,       _,  r₃       => rfl
| .cons r₁ v, r₂, r₃       =>
  congrArg₂ (cons · ·) (comp_assoc r₁ r₂ r₃)
                       (v.rename_comp r₂ r₃).symm

end Renaming

open Categories in
def REN (σ : Sig) : Category where
  Ob := Ctx σ
  Hom := Renaming
  id := Renaming.ide
  comp := Renaming.comp
  comp_assoc := Renaming.comp_assoc
  comp_id := Renaming.comp_ide
  id_comp := Renaming.ide_comp

unif_hint (Γ Δ : Ctx σ) where
  ⊢ Renaming Γ Δ ≟ (REN σ)[Γ, Δ]
