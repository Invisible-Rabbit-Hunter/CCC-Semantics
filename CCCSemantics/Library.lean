
def congrArg₂
  (f : α → β → γ) : x = x' → y = y' →
  f x y = f x' y' := by
  intro h₁ h₂
  rw [h₁, h₂]

def Path {β : α → Sort v} (h : x = y) (a : β x) (b : β y) : Prop :=
  h ▸ a = b

namespace Path

variable {α : Type u} {β : α → Sort v} {γ : (x : α) → β x → Sort w}

def trans (p : Path h₁ a b) (q : Path h₂ b c) : Path (h₁.trans h₂) a c:= by
  simp [Path]
  cases h₂
  apply Eq.trans p q

end Path

structure Equiv (A B : Type u) where
  toFun : A → B
  invFun : B → A
  leftInv : ∀ x, invFun (toFun x) = x
  rightInv : ∀ x, toFun (invFun x) = x 

namespace Equiv

infixl:90 " ≃ " => Equiv

instance : CoeFun (Equiv α β) (λ _ => α → β) where
  coe := toFun

def refl α : Equiv α α where
  toFun := λ x => x
  invFun := λ x => x
  leftInv := λ _ => Eq.refl _
  rightInv := λ _ => Eq.refl _

def symm (e : Equiv α β) : Equiv β α where
  toFun := e.invFun
  invFun := e.toFun
  leftInv := e.rightInv
  rightInv := e.leftInv 

def trans (e₁ : Equiv α β) (e₂ : Equiv β γ) : Equiv α γ where
  toFun := e₂.toFun ∘ e₁.toFun 
  invFun := e₁.invFun ∘ e₂.invFun
  leftInv := by simp [e₁.leftInv, e₂.leftInv]
  rightInv := by simp [e₁.rightInv, e₂.rightInv]

@[simp]
theorem symm_leftInv (e : Equiv α β) : ∀ x, e.symm (e x) = x := e.leftInv

@[simp]
theorem symm_rightInv (e : Equiv α β) : ∀ x, e (e.symm x) = x := e.rightInv

theorem injective (e : Equiv α β) (p : e x = e y) : x = y :=
  ((e.symm_leftInv x).symm.trans (congrArg _ p)).trans (e.symm_leftInv y)

def prod (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') where
  toFun := λ p => (e₁ p.1, e₂ p.2) 
  invFun := λ p => (e₁.symm p.1, e₂.symm p.2)
  leftInv := λ x => by simp
  rightInv := λ x => by simp

def func (e₁ : α ≃ α') (e₂ : β ≃ β') : (α → β) ≃ (α' → β') where
  toFun := λ f => e₂ ∘ f ∘ e₁.symm   
  invFun := λ f => e₂.symm ∘ f ∘ e₁
  leftInv := λ f => by funext x; simp 
  rightInv := λ f => by funext x; simp 

end Equiv
