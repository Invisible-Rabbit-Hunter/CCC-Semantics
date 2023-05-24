import CCCSemantics.Lambda.Term

inductive Subst {σ : Sig} (Γ : Ctx σ) : Ctx σ → Type _
| nil : Subst Γ ε
| cons (t : Γ ⊢ τ) (ts : Subst Γ Δ) : Subst Γ (Δ ,, τ)   

namespace Subst

def weaken : Renaming Γ Δ → Subst Δ Ε → Subst Γ Ε
| e, .nil      => .nil
| e, .cons t s => .cons (e.apply t) (weaken e s)

def contract : Subst Γ Δ → Renaming Δ Ε → Subst Γ Ε
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
| s, .pair t u => .pair (apply s t) (apply s u)
| s, .fst t => .fst (apply s t)
| s, .snd t => .snd (apply s t)
| s, .unit => .unit

def comp (s : Subst Γ Δ) : Subst Δ Ε → Subst Γ Ε
| .nil       => .nil
| .cons t s' => .cons (apply s t) (comp s s')

def ide {σ : Sig} : ∀ Γ : Ctx σ, Subst Γ Γ
| ε => .nil
| Γ ,, _ => .cons (.var .zero) (weaken (.skip (Renaming.ide _)) (ide Γ))

def head : Subst Γ (Δ ,, τ) → Γ ⊢ τ
| .cons t _ => t
def tail : Subst Γ (Δ ,, τ) → Subst Γ Δ
| .cons _ s => s

theorem ide_weaken : weaken (Renaming.ide Γ) s = s := by
  induction s with
  | nil => rfl
  | cons t s ih => simp [weaken, ih]

theorem trans_weaken : weaken (Renaming.trans e₁ e₂) s = weaken e₁ (weaken e₂ s) := by
  induction s with
  | nil => rfl
  | cons t s ih => simp [weaken, ih]

theorem contract_ide : ∀ s : Subst Γ Δ, contract s (Renaming.ide Δ) = s
| .nil      => rfl
| .cons t s => congrArg (cons t) (contract_ide s)

def ofOPE (e : Renaming Γ Δ) : Subst Γ Δ := weaken e (ide _)

theorem ofOPE_ide : ofOPE (Renaming.ide Γ) = ide Γ := ide_weaken
theorem ofOPE_bang {σ : Sig}: ∀ Γ : Ctx σ, ofOPE (Renaming.bang Γ) = nil
| ε      => rfl
| _ ,, _ => rfl

theorem var_ope : ∀ {s : Subst Γ Δ} {e : Renaming Δ Ε} (v : Var τ Ε),
  var s (Renaming.var e v) = var (contract s e) v
| nil,       .done,   v      => nomatch v
| .cons _ _, .keep e, v⟨0⟩   => rfl
| .cons _ _, .keep e, v⟨n+1⟩ => var_ope n
| .cons _ s, .skip e, v      => var_ope (s := s) (e := e) v

theorem contract_weaken : ∀ {e₁ : Renaming Γ Δ} {s : Subst Δ Ε} {e₂ : Renaming Ε Θ},
  contract (weaken e₁ s) e₂ = weaken e₁ (contract s e₂)
| e₁, nil,      .done    => rfl
| e₁, cons t s, .keep e₂ => by
  simp [contract, weaken]
  apply contract_weaken
| e₁, cons t s, .skip e₂ => by
  simp [contract, weaken]
  apply contract_weaken

@[simp]
theorem apply_contract : ∀ {s : Subst Γ Δ} {e : Renaming Δ Ε} (t : Ε ⊢ τ), apply s (Renaming.apply e t) = apply (contract s e) t
| s, e, .var v => var_ope v
| s, e, .base b => rfl
| s, e, .lam t => congrArg Tm.lam <| by
    simp [apply, weaken]
    have h := apply_contract (s := cons (.var .zero) (weaken (.skip (Renaming.ide Γ)) s))
                             (e := e.keep) t
    apply Eq.trans h
    simp [contract]
    congr
    apply contract_weaken
| s, e, .app t u => congrArg₂ Tm.app (apply_contract t) (apply_contract u)
| s, e, .pair t u => congrArg₂ Tm.pair (apply_contract t) (apply_contract u)
| s, e, .fst t => congrArg Tm.fst (apply_contract t)
| s, e, .snd t => congrArg Tm.snd (apply_contract t)
| s, e, .unit => rfl

@[simp]
theorem var_weaken : ∀ (e : Renaming Γ Δ) (s : Subst Δ Ε) (n : Var τ Ε), var (weaken e s) n = e.apply (var s n)
| _, .cons _ _, v⟨0⟩   => rfl
| e, .cons _ s, v⟨n+1⟩ =>
  var_weaken e s n

@[simp]
theorem var_ide : ∀ {Γ : Ctx _} (t : Var τ Γ), var (ide Γ) t = .var t
| Γ ,, _, v⟨0⟩ => rfl
| Γ ,, υ, v⟨n+1⟩ => by
  have h := var_ide n
  have t : Renaming.apply (.skip (Renaming.ide Γ)) (Tm.var n) = Tm.var (n.succ (υ := υ)) :=
    congrArg (Tm.var ∘ Var.succ) (Renaming.var_ide n)
  simp [var]
  rw [h]
  assumption

theorem var_ofOPE : ∀ (e : Renaming Γ Δ) (v : Var τ Δ), var (ofOPE e) v = Tm.var (Renaming.var e v)
| e, v⟨0⟩   => rfl
| e, p@(Var.succ n) => by
  simp [ofOPE, var, weaken, Renaming.var]
  simp [Renaming.apply, Renaming.var, Renaming.var_ide]

theorem apply_ofOPE : ∀ (e : Renaming Γ Δ) (t : Δ ⊢ τ), apply (ofOPE e) t = Renaming.apply e t
| e, .var v   => var_ofOPE e v
| e, .base b  => rfl
| e, .lam t   => congrArg Tm.lam <| by
  have ih := apply_ofOPE (.keep e) t
  apply Eq.trans _ ih
  apply congrArg (apply · t)
  simp [ofOPE, weaken, Renaming.apply, Renaming.var]
  rw [←trans_weaken, ←trans_weaken]
  simp [Renaming.trans]
| e, .app t u => congrArg₂ Tm.app (apply_ofOPE e t) (apply_ofOPE e u)
| e, .pair t u => congrArg₂ Tm.pair (apply_ofOPE e t) (apply_ofOPE e u)
| e, .fst t => congrArg Tm.fst (apply_ofOPE e t)
| e, .snd t => congrArg Tm.snd (apply_ofOPE e t)
| e, .unit => rfl

@[simp]
theorem apply_ide : ∀ t : Γ ⊢ τ, apply (ide Γ) t = t
| .var v => var_ide v
| .base b => rfl
| .lam t => congrArg Tm.lam (apply_ide t)
| .app t u => congrArg₂ Tm.app (apply_ide t) (apply_ide u)
| .pair t u => congrArg₂ Tm.pair (apply_ide t) (apply_ide u)
| .fst t => congrArg Tm.fst (apply_ide t)
| .snd t => congrArg Tm.snd (apply_ide t)
| .unit => rfl

@[simp]
theorem apply_weaken : ∀ (e : Renaming Γ Δ) (s : Subst Δ Ε) (t : Ε ⊢ τ),
  apply (weaken e s) t = Renaming.apply e (apply s t)
| e, s, .var n => var_weaken e s n
| e, s, .base b => rfl
| e, s, .lam t => congrArg Tm.lam <| by
  simp [Renaming.apply, weaken]
  rw [←trans_weaken]
  simp [Renaming.trans]
  let h := apply_weaken (.keep e) (cons (.var .zero) (weaken (Renaming.skip (Renaming.ide Δ)) s)) t
  rw [←h]
  simp [weaken, Renaming.apply, Renaming.var]
  rw [←trans_weaken, Renaming.trans, Renaming.trans_ide]
| e, s, .app t u => congrArg₂ Tm.app (apply_weaken e s t) (apply_weaken e s u)
| e, s, .pair t u => congrArg₂ Tm.pair (apply_weaken e s t) (apply_weaken e s u)
| e, s, .fst t => congrArg Tm.fst (apply_weaken e s t)
| e, s, .snd t => congrArg Tm.snd (apply_weaken e s t)
| e, s, .unit => rfl

@[simp]
theorem contract_comp_weaken : ∀ {s : Subst Γ Δ} {e : Renaming Δ Δ'} {s' : Subst Δ' Ε},
  comp s (weaken e s') = comp (contract s e) s' := by
  intro s e s'
  induction s' with
  | nil => rfl
  | cons t s' ih => simp [comp, ih]

@[simp]
theorem contract_id : ∀ (s : Subst Γ Δ), contract s (Renaming.ide Δ) = s
| .nil      => rfl
| .cons t s => congrArg (Subst.cons t) (contract_id s)

theorem comp_id : ∀ s : Subst Γ Δ, comp s (ide Δ) = s
| .nil      => rfl
| .cons t s => by
  have h : comp s (ide _) = s := comp_id s
  simp [comp, apply, var, weaken, contract, h]

theorem id_comp : ∀ s : Subst Γ Δ, comp (ide Γ) s = s 
| .nil      => rfl
| .cons t s => by
  simp [comp, id_comp s]
  
theorem apply_nil : ∀ (s : Subst Γ Δ) (t : ε ⊢ τ), apply nil t = apply s (apply nil t)
  := by
  intro s t
  apply Eq.symm
  rw [←ofOPE_bang]
  rw [apply_ofOPE, apply_contract]
  induction Δ with
  | nil => simp [Renaming.bang, contract]
  | cons Δ τ ih =>
    cases s with | cons t s =>
    simp [Renaming.bang, contract, ih]

theorem var_comp : ∀ (s₁ : Subst Γ Δ) (s₂ : Subst Δ Ε) (v : Var τ Ε),
  var (comp s₁ s₂) v = apply s₁ (var s₂ v)
| _, .cons _ s₂, v⟨0⟩   => rfl
| s₁, .cons _ s₂, v⟨n+1⟩ => var_comp s₁ s₂ n

theorem weaken_comp :
  ∀ (e : Renaming Γ Δ) (s₁ : Subst Δ Ε) (s₂ : Subst Ε Θ), comp (weaken e s₁) s₂ = weaken e (comp s₁ s₂)
| e, s₁, .nil       => rfl
| e, s₁, .cons t s₂ => by
  simp [comp, weaken]
  apply weaken_comp e s₁ s₂

theorem apply_comp : ∀ (s₁ : Subst Γ Δ) (s₂ : Subst Δ Ε) (t : Ε ⊢ τ),
  apply (comp s₁ s₂) t = apply s₁ (apply s₂ t)
| s₁, s₂, .var v   => var_comp s₁ s₂ v
| s₁, s₂, .base b  => rfl
| s₁, s₂, .lam t   => congrArg Tm.lam (by
  rw [←apply_comp _ _ t]
  simp [comp, apply, var, contract]
  rw [weaken_comp]
  )
| s₁, s₂, .app t u => congrArg₂ Tm.app (apply_comp s₁ s₂ t) (apply_comp s₁ s₂ u)
| s₁, s₂, .pair t u => congrArg₂ Tm.pair (apply_comp s₁ s₂ t) (apply_comp s₁ s₂ u)
| s₁, s₂, .fst t => congrArg Tm.fst (apply_comp s₁ s₂ t)
| s₁, s₂, .snd t => congrArg Tm.snd (apply_comp s₁ s₂ t)
| s₁, s₂, .unit => rfl


theorem comp_assoc : ∀ (s₁ : Subst Γ Δ) (s₂ : Subst Δ Ε) (s₃ : Subst Ε Θ),
  comp (comp s₁ s₂) s₃ = comp s₁ (comp s₂ s₃)
| _, s₂, nil       => rfl
| s₁, s₂, cons t s₃ =>
  congrArg₂ cons (apply_comp s₁ s₂ t) (comp_assoc s₁ s₂ s₃)

-- section
-- open CategoryTheory

-- instance (σ : Sig) : Category (Ctx σ) where
--   Hom := Subst
--   id := ide
--   comp := comp
--   comp_id := comp_id
--   id_comp := id_comp
--   assoc := comp_assoc
-- end

-- def arr : (Γ : Ctx σ) → Ty σ.types → Ty σ.types
-- | ε, ρ => ρ
-- | Γ ,, τ, ρ => arr Γ (Ty.arr τ ρ)

-- def exp : Ctx σ → Ctx σ → Ctx σ
-- | Δ, ε      => ε
-- | Δ, Γ ,, τ => exp Δ Γ ,, arr Δ τ

-- def concat : Ctx σ → Ctx σ → Ctx σ
-- | Γ, ε      => Γ 
-- | Γ, Δ ,, τ => (concat Γ Δ) ,, τ

-- instance : Append (Ctx α) where
--   append := concat

-- section
-- variable {σ : Sig}

-- def pair : ∀ {Γ Δ Ε : Ctx σ}, (Γ ⟶ Δ) → (Γ ⟶  Ε) → (Γ ⟶ (Δ ++ Ε))
-- | Γ, Δ, ε,      s₁, s₂        => s₁
-- | Γ, Δ, Ε ,, τ, s₁, cons t s₂ => cons t (pair s₁ s₂)

-- def proj₁ : ∀ {Γ Δ : Ctx σ}, (Γ ++ Δ) ⟶ Γ
-- | Γ, ε                => ide Γ
-- | Γ, Δ ,, _ => weaken (.skip (Renaming.ide (Γ ++ Δ))) proj₁

-- def proj₂ : ∀ {Γ Δ : Ctx σ}, (Γ ++ Δ) ⟶ Δ
-- | _, ε                => .nil
-- | Γ, Δ ,, _ => .cons (.var .zero) (weaken (.skip (Renaming.ide (Γ ++ Δ))) proj₂)

-- instance : Pow (Ctx α) (Ctx α) where
--   pow a b := exp b a

-- def app : ∀ {Γ Δ : Ctx σ}, Γ ⊢ arr Δ τ → (Γ ⟶ Δ) → Γ ⊢ τ
-- | _, ε,      f, .nil      => f
-- | Γ, Δ ,, υ, f, .cons t s => .app (app f s) t

-- def apps : ∀ {Γ Δ Ε : Ctx σ}, (Γ ⟶ exp Δ Ε) → (Γ ⟶ Δ) → (Γ ⟶ Ε)
-- | _, _, ε,      _,          _ => .nil
-- | _, _, _ ,, _, .cons f fs, x => .cons (app f x)
--                                        (apps fs x)

-- def lam' : ∀ {Γ Δ}, (Γ ++ Δ) ⊢ τ → Γ ⊢ arr Δ τ
-- | _, ε,      t => t
-- | _, Δ ,, _, t => lam' (Δ := Δ) (.lam t)

-- def unlam' : ∀ {Γ Δ}, Γ ⊢ arr Δ τ → (Γ ++ Δ) ⊢ τ
-- | _, ε,      t => t 
-- | Γ, Δ ,, υ, t => let h := unlam' (Γ := Γ) (Δ := Δ) (τ := .arr υ τ) t
--                   .app (Renaming.apply (.skip (Renaming.ide _)) h) (.var .zero)

-- def eval' : ∀ {Γ Δ : Ctx σ}, (Γ ++ Δ ^ Γ) ⟶ Δ
-- | Γ, ε      => nil
-- | Γ, Δ ,, τ =>
--   .cons (app (.var .zero) proj₁) (weaken (.skip (Renaming.ide _)) (eval' (Γ := Γ) (Δ := Δ)))

-- def swap : ∀ Γ Δ : Ctx σ, Γ ++ Δ ⟶ Δ ++ Γ :=
--   λ _ _ => pair (proj₂) (proj₁)

-- def eval {Γ Δ : Ctx σ} : (Δ ^ Γ ++ Γ) ⟶ Δ := swap _ _ ≫ eval'

-- def lam : ∀ {Γ Δ Ε : Ctx σ}, ((Γ ++ Δ) ⟶ Ε) → (Γ ⟶ exp Δ Ε)
-- | Γ, Δ, ε,      f          => .nil
-- | Γ, Δ, Ε ,, τ, .cons f fs => .cons (lam' f) (lam fs)
-- end

end Subst


