import CCCSemantics.Lambda.OPE

inductive Subst {σ : Sig} (Γ : Ctx σ.types) : Ctx σ.types → Type _
| nil : Subst Γ ε
| cons (t : Γ ⊢ τ) (ts : Subst Γ Δ) : Subst Γ (Δ ,, τ)   

namespace Subst

def weaken : OPE Γ Δ → Subst Δ Ε → Subst Γ Ε
| e, .nil      => .nil
| e, .cons t s => .cons (e.apply t) (weaken e s)

def contract : Subst Γ Δ → OPE Δ Ε → Subst Γ Ε
| s,         .done   => .nil
| .cons t s, .keep e => .cons t (contract s e)
| .cons _ s, .skip e => contract s e

def var : Subst Γ Δ → Var τ Δ → Γ ⊢ τ
| .cons t _, .zero   => t
| .cons _ s, .succ n => s.var n

def apply : Subst Γ Δ → Δ ⊢ τ → Γ ⊢ τ
| s, .var v   => s.var v
| _, .base b  => .base b
| s, .lam t   => .lam (
    apply (.cons (.var .zero) (weaken (.skip (.ide _)) s)) t)
| s, .app t u => .app (apply s t) (apply s u)

def comp (s : Subst Γ Δ) : Subst Δ Ε → Subst Γ Ε
| .nil       => .nil
| .cons t s' => .cons (apply s t) (comp s s')

def ide {σ : Sig} : ∀ Γ : Ctx σ.types, Subst Γ Γ
| ε => .nil
| Γ ,, _ => .cons (.var .zero) (weaken (.skip (OPE.ide _)) (ide Γ))

def head : Subst Γ (Δ ,, τ) → Γ ⊢ τ
| .cons t _ => t
def tail : Subst Γ (Δ ,, τ) → Subst Γ Δ
| .cons _ s => s

lemma ide_weaken : weaken (OPE.ide Γ) s = s := by
  induction s with
  | nil => rfl
  | cons t s ih => simp [weaken, ih]

lemma trans_weaken : weaken (OPE.trans e₁ e₂) s = weaken e₁ (weaken e₂ s) := by
  induction s with
  | nil => rfl
  | cons t s ih => simp [weaken, ih]

lemma contract_ide : ∀ s : Subst Γ Δ, contract s (OPE.ide Δ) = s
| .nil      => rfl
| .cons t s => congrArg (cons t) (contract_ide s)

def ofOPE (e : OPE Γ Δ) : Subst Γ Δ := weaken e (ide _)

lemma ofOPE_ide : ofOPE (OPE.ide Γ) = ide Γ := ide_weaken
lemma ofOPE_bang {σ : Sig}: ∀ Γ : Ctx σ.types, ofOPE (OPE.bang Γ) = nil
| ε      => rfl
| _ ,, _ => rfl

lemma var_ope : ∀ {s : Subst Γ Δ} {e : OPE Δ Ε} (v : Var τ Ε),
  var s (OPE.var e v) = var (contract s e) v
| nil,       .done,   v      => nomatch v
| .cons _ _, .keep e, v⟨0⟩   => rfl
| .cons _ _, .keep e, v⟨n+1⟩ => var_ope n
| .cons _ s, .skip e, v      => var_ope (s := s) (e := e) v

lemma contract_weaken : ∀ {e₁ : OPE Γ Δ} {s : Subst Δ Ε} {e₂ : OPE Ε Θ},
  contract (weaken e₁ s) e₂ = weaken e₁ (contract s e₂)
| e₁, nil,      .done    => rfl
| e₁, cons t s, .keep e₂ => by
  simp [contract, weaken]
  apply contract_weaken
| e₁, cons t s, .skip e₂ => by
  simp [contract, weaken]
  apply contract_weaken

@[simp]
lemma apply_contract : ∀ {s : Subst Γ Δ} {e : OPE Δ Ε} (t : Ε ⊢ τ), apply s (OPE.apply e t) = apply (contract s e) t
| s, e, .var v => var_ope v
| s, e, .base b => rfl
| s, e, .lam t => congrArg Tm.lam <| by
    simp [apply, weaken]
    have h := apply_contract (s := cons (.var .zero) (weaken (.skip (OPE.ide Γ)) s))
                             (e := e.keep) t
    apply Eq.trans h
    simp [contract]
    congr
    apply contract_weaken
| s, e, .app t u => congrArg₂ Tm.app (apply_contract t) (apply_contract u)

@[simp]
lemma var_weaken : ∀ (e : OPE Γ Δ) (s : Subst Δ Ε) (n : Var τ Ε), var (weaken e s) n = e.apply (var s n)
| _, .cons _ _, v⟨0⟩   => rfl
| e, .cons _ s, v⟨n+1⟩ =>
  var_weaken e s n

@[simp]
lemma var_ide : ∀ {Γ : Ctx _} (t : Var τ Γ), var (ide Γ) t = .var t
| Γ ,, _, v⟨0⟩ => rfl
| Γ ,, υ, v⟨n+1⟩ => by
  have h := var_ide n
  have t : OPE.apply (.skip (OPE.ide Γ)) (Tm.var n) = Tm.var (n.succ (υ := υ)) :=
    congrArg (Tm.var ∘ Var.succ) (OPE.var_ide n)
  simp [var]
  rw [h]
  assumption

lemma var_ofOPE : ∀ (e : OPE Γ Δ) (v : Var τ Δ), var (ofOPE e) v = Tm.var (OPE.var e v)
| e, v⟨0⟩   => rfl
| e, p@(Var.succ n) => by
  simp [ofOPE, var, weaken, OPE.var]
  simp [OPE.apply, OPE.var, OPE.var_ide]

lemma apply_ofOPE : ∀ (e : OPE Γ Δ) (t : Δ ⊢ τ), apply (ofOPE e) t = OPE.apply e t
| e, .var v   => var_ofOPE e v
| e, .base b  => rfl
| e, .lam t   => congrArg Tm.lam <| by
  have ih := apply_ofOPE (.keep e) t
  apply Eq.trans _ ih
  apply congrArg (apply · t)
  simp [ofOPE, weaken, OPE.apply, OPE.var]
  rw [←trans_weaken, ←trans_weaken]
  simp [OPE.trans]
| e, .app t u => congrArg₂ Tm.app (apply_ofOPE e t) (apply_ofOPE e u)

@[simp]
lemma apply_ide : ∀ t : Γ ⊢ τ, apply (ide Γ) t = t
| .var v => var_ide v
| .base b => rfl
| .lam t => congrArg Tm.lam (apply_ide t)
| .app t u => congrArg₂ Tm.app (apply_ide t) (apply_ide u)

@[simp]
lemma apply_weaken : ∀ (e : OPE Γ Δ) (s : Subst Δ Ε) (t : Ε ⊢ τ),
  apply (weaken e s) t = OPE.apply e (apply s t)
| e, s, .var n => var_weaken e s n
| e, s, .base b => rfl
| e, s, .lam t => congrArg Tm.lam <| by
  simp [OPE.apply, weaken]
  rw [←trans_weaken]
  simp [OPE.trans]
  let h := apply_weaken (.keep e) (cons (.var .zero) (weaken (OPE.skip (OPE.ide Δ)) s)) t
  rw [←h]
  simp [weaken, OPE.apply, OPE.var]
  rw [←trans_weaken, OPE.trans, OPE.trans_ide]
| e, s, .app t u => congrArg₂ Tm.app (apply_weaken e s t) (apply_weaken e s u)

@[simp]
lemma contract_comp_weaken : ∀ {s : Subst Γ Δ} {e : OPE Δ Δ'} {s' : Subst Δ' Ε},
  comp s (weaken e s') = comp (contract s e) s' := by
  intro s e s'
  induction s' with
  | nil => rfl
  | cons t s' ih => simp [comp, ih]

@[simp]
lemma contract_id : ∀ (s : Subst Γ Δ), contract s (OPE.ide Δ) = s
| .nil      => rfl
| .cons t s => congrArg (Subst.cons t) (contract_id s)

lemma comp_id : ∀ s : Subst Γ Δ, comp s (ide Δ) = s
| .nil      => rfl
| .cons t s => by
  have h : comp s (ide _) = s := comp_id s
  simp [comp, apply, var, weaken, contract, h]

lemma id_comp : ∀ s : Subst Γ Δ, comp (ide Γ) s = s 
| .nil      => rfl
| .cons t s => by
  simp [comp, id_comp s]
  
lemma apply_nil : ∀ (s : Subst Γ Δ) (t : ε ⊢ τ), apply nil t = apply s (apply nil t)
  := by
  intro s t
  symm
  rw [←ofOPE_bang]
  rw [apply_ofOPE, apply_contract]
  induction Δ with
  | nil => simp [OPE.bang, contract]
  | cons Δ τ ih =>
    cases s with | cons t s =>
    simp [OPE.bang, contract, ih]

lemma var_comp : ∀ (s₁ : Subst Γ Δ) (s₂ : Subst Δ Ε) (v : Var τ Ε),
  var (comp s₁ s₂) v = apply s₁ (var s₂ v)
| _, .cons _ s₂, v⟨0⟩   => rfl
| s₁, .cons _ s₂, v⟨n+1⟩ => var_comp s₁ s₂ n

lemma weaken_comp :
  ∀ (e : OPE Γ Δ) (s₁ : Subst Δ Ε) (s₂ : Subst Ε Θ), comp (weaken e s₁) s₂ = weaken e (comp s₁ s₂)
| e, s₁, .nil       => rfl
| e, s₁, .cons t s₂ => by
  simp [comp, weaken]
  apply weaken_comp e s₁ s₂

lemma apply_comp : ∀ (s₁ : Subst Γ Δ) (s₂ : Subst Δ Ε) (t : Ε ⊢ τ),
  apply (comp s₁ s₂) t = apply s₁ (apply s₂ t)
| s₁, s₂, .var v   => var_comp s₁ s₂ v
| s₁, s₂, .base b  => rfl
| s₁, s₂, .lam t   => congrArg Tm.lam (by
  rw [←apply_comp _ _ t]
  simp [comp, apply, var, contract]
  rw [weaken_comp]
  )
| s₁, s₂, .app t u => congrArg₂ Tm.app (apply_comp s₁ s₂ t) (apply_comp s₁ s₂ u)


lemma comp_assoc : ∀ (s₁ : Subst Γ Δ) (s₂ : Subst Δ Ε) (s₃ : Subst Ε Θ),
  comp (comp s₁ s₂) s₃ = comp s₁ (comp s₂ s₃)
| _, s₂, nil       => rfl
| s₁, s₂, cons t s₃ =>
  congrArg₂ cons (apply_comp s₁ s₂ t) (comp_assoc s₁ s₂ s₃)

section
open CategoryTheory

instance (σ : Sig) : Category (Ctx σ.types) where
  Hom := Subst
  id := ide
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := comp_assoc
end

def arr : (Γ : Ctx α) → Ty α → Ty α
| ε, ρ => ρ
| Γ ,, τ, ρ => arr Γ (Ty.arr τ ρ)

def exp : Ctx σ → Ctx σ → Ctx σ
| Δ, ε      => ε
| Δ, Γ ,, τ => exp Δ Γ ,, arr Δ τ

def concat : Ctx σ → Ctx σ → Ctx σ
| Γ, ε      => Γ 
| Γ, Δ ,, τ => (concat Γ Δ) ,, τ

instance : Append (Ctx α) where
  append := concat

section
variable {σ : Sig}

def pair : ∀ {Γ Δ Ε : Ctx σ.types}, (Γ ⟶ Δ) → (Γ ⟶  Ε) → (Γ ⟶ (Δ ++ Ε))
| Γ, Δ, ε,      s₁, s₂        => s₁
| Γ, Δ, Ε ,, τ, s₁, cons t s₂ => cons t (pair s₁ s₂)

def proj₁ : ∀ {Γ Δ : Ctx σ.types}, (Γ ++ Δ) ⟶ Γ
| Γ, ε                => ide Γ
| Γ, Δ ,, _ => weaken (.skip (OPE.ide (Γ ++ Δ))) proj₁

def proj₂ : ∀ {Γ Δ : Ctx σ.types}, (Γ ++ Δ) ⟶ Δ
| _, ε                => .nil
| Γ, Δ ,, _ => .cons (.var .zero) (weaken (.skip (OPE.ide (Γ ++ Δ))) proj₂)

instance : Pow (Ctx α) (Ctx α) where
  pow a b := exp b a

def app : ∀ {Γ Δ}, Γ ⊢ arr Δ τ → (Γ ⟶ Δ) → Γ ⊢ τ
| _, ε,      f, .nil      => f
| Γ, Δ ,, υ, f, .cons t s => .app (app f s) t

def apps : ∀ {Γ Δ Ε : Ctx σ.types}, (Γ ⟶ exp Δ Ε) → (Γ ⟶ Δ) → (Γ ⟶ Ε)
| _, _, ε,      _,          _ => .nil
| _, _, _ ,, _, .cons f fs, x => .cons (app f x)
                                       (apps fs x)

def lam' : ∀ {Γ Δ}, (Γ ++ Δ) ⊢ τ → Γ ⊢ arr Δ τ
| _, ε,      t => t
| _, Δ ,, _, t => lam' (Δ := Δ) (.lam t)

def unlam' : ∀ {Γ Δ}, Γ ⊢ arr Δ τ → (Γ ++ Δ) ⊢ τ
| _, ε,      t => t 
| Γ, Δ ,, υ, t => let h := unlam' (Γ := Γ) (Δ := Δ) (τ := .arr υ τ) t
                  .app (OPE.apply (.skip (OPE.ide _)) h) (.var .zero)

def eval' : ∀ {Γ Δ : Ctx σ.types}, (Γ ++ Δ ^ Γ) ⟶ Δ
| Γ, ε      => nil
| Γ, Δ ,, τ =>
  .cons (app (.var .zero) proj₁) (weaken (.skip (OPE.ide _)) (eval' (Γ := Γ) (Δ := Δ)))

def swap : ∀ Γ Δ : Ctx σ.types, Γ ++ Δ ⟶ Δ ++ Γ :=
  λ _ _ => pair (proj₂) (proj₁)

def eval {Γ Δ : Ctx σ.types} : (Δ ^ Γ ++ Γ) ⟶ Δ := swap _ _ ≫ eval'

def lam : ∀ {Γ Δ Ε : Ctx σ.types}, ((Γ ++ Δ) ⟶ Ε) → (Γ ⟶ exp Δ Ε)
| Γ, Δ, ε,      f          => .nil
| Γ, Δ, Ε ,, τ, .cons f fs => .cons (lam' f) (lam fs)

end

end Subst


