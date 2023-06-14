import CCCSemantics.Lambda.Term

inductive Subst {σ : Sig} (Γ : Ctx σ) : Ctx σ → Type _
| nil : Subst Γ ε
| cons (ts : Subst Γ Δ) (t : Γ ⊢ τ) : Subst Γ (Δ ,, τ)   

def Var.subst : Var τ Δ → Subst Γ Δ → Γ ⊢ τ
| .zero,   .cons _ t => t
| .succ n, .cons s _ => n.subst s


namespace Subst

def weaken : Subst Δ Ε → Renaming Γ Δ → Subst Γ Ε
| .nil     , e => .nil
| .cons s t, e => .cons (weaken s e) (t.rename e)

def contract : Renaming Δ Ε → Subst Γ Δ → Subst Γ Ε
| .nil     , s  => .nil
| .cons e v, s => .cons (contract e s) (v.subst s)

def drop τ : Subst Γ Δ → Subst (Γ ,, τ) Δ
| .nil      => .nil
| .cons s t => .cons (s.drop τ) (t.rename ((Renaming.ide _).drop _))

def keep τ : Subst Γ Δ → Subst (Γ ,, τ) (Δ ,, τ) :=
  λ s => .cons (s.drop _) (.var .zero)

end Subst

def Tm.subst : Δ ⊢ τ → Subst Γ Δ → Γ ⊢ τ
| .var v,    s => v.subst s
| .base b,   _ => .base b
| .lam t,    s => .lam (t.subst (s.keep _))
| .app t u,  s => .app (t.subst s) (u.subst s)
| .pair t u, s => .pair (t.subst s) (u.subst s)
| .fst t,    s => .fst (t.subst s)
| .snd t,    s => .snd (t.subst s)
| .unit,     s => .unit

namespace Subst
def comp  : Subst Δ Ε → Subst Γ Δ → Subst Γ Ε
| .nil,       s₂ => .nil
| .cons s₁ t, s₂ => .cons (s₁.comp s₂) (t.subst s₂)

def ofRenaming : Renaming Γ Δ → Subst Γ Δ
| .nil => .nil
| .cons r v => .cons (ofRenaming r) (.var v)

def ide (Γ : Ctx σ) : Subst Γ Γ :=
  ofRenaming (Renaming.ide Γ)

def head : Subst Γ (Δ ,, τ) → Subst Γ Δ
| .cons s _ => s
def tail : Subst Γ (Δ ,, τ) → Γ ⊢ τ
| .cons _ t => t

theorem _root_.Var.subst_renaming :
  ∀ (v : Var τ Δ) (r : Renaming Γ Δ),
    v.subst (ofRenaming r) = .var (v.rename r)
| .zero,   .cons _ _ => rfl
| .succ v, .cons r _ => v.subst_renaming r

theorem ofRenaming_drop : ∀ (r : Renaming Γ Δ) τ, ofRenaming (r.drop τ) =
  (ofRenaming r).drop τ
| .nil,      τ => rfl
| .cons r v, τ =>
  congrArg₂ cons (ofRenaming_drop r τ)
                 (congrArg Tm.var
                           ((v.rename_drop _ _).trans
                            (congrArg Var.succ (v.rename_ide))).symm)

theorem ofRenaming_keep : ∀ (r : Renaming Γ Δ) τ, ofRenaming (r.keep τ) =
  (ofRenaming r).keep τ :=
  λ r τ => congrArg (cons · _) (ofRenaming_drop r τ)

theorem _root_.Tm.subst_renaming :
  ∀ (t : Δ ⊢ τ) (r : Renaming Γ Δ),
    t.subst (ofRenaming r) = t.rename r
| .var v, r => v.subst_renaming r
| .base _, r => rfl
| .lam t, r => congrArg Tm.lam ((congrArg t.subst (ofRenaming_keep r _).symm).trans (t.subst_renaming (r.keep _)))
| .app t u, r => congrArg₂ Tm.app (t.subst_renaming r) (u.subst_renaming r)
| .pair t u, r => congrArg₂ Tm.pair (t.subst_renaming r) (u.subst_renaming r)
| .fst t, r => congrArg Tm.fst (t.subst_renaming r)
| .snd t, r => congrArg Tm.snd (t.subst_renaming r)
| .unit, r => rfl

theorem weaken_eq_comp_ofRenaming :
  ∀ (s : Subst Δ Ε) (r : Renaming Γ Δ) ,
    s.weaken r = s.comp (ofRenaming r)
| .nil,      r => rfl
| .cons s t, r => congrArg₂ cons (weaken_eq_comp_ofRenaming s r)
                                 (t.subst_renaming r).symm

theorem contract_eq_ofRenaming_comp :
  ∀ (r : Renaming Δ Ε) (s : Subst Γ Δ) ,
    s.contract r = (ofRenaming r).comp s
| .nil,      s => rfl
| .cons r _, s => congrArg (cons · _) (contract_eq_ofRenaming_comp r s)

theorem weaken_ide : ∀ s : Subst Γ Δ, s.weaken (Renaming.ide Γ) = s
| .nil      => rfl
| .cons s t => congrArg₂ cons s.weaken_ide t.rename_ide

theorem weaken_comps : weaken s (Renaming.comp r₁ r₂) = (s.weaken r₁).weaken r₂ := by
  induction s with
  | nil => rfl
  | cons t s ih => simp [weaken, ih]

@[simp]
theorem _root_.Var.subst_succ : ∀ (v : Var τ Δ) (s : Subst Γ (Δ ,, υ)),
v.succ.subst s = v.subst s.head
| _, .cons _ _ => rfl

theorem drop_contract : ∀ (r : Renaming Δ Ε) (s : Subst Γ (Δ ,, τ)), contract (r.drop τ) s = contract r s.head
| .nil,       r => rfl
| .cons s t, r => by simp [drop, contract, drop_contract]

theorem ide_contract : ∀ {Γ Δ : Ctx σ} (s : Subst Γ Δ), contract (Renaming.ide Δ) s = s
| _, ε,      .nil      => rfl
| _, _ ,, _, .cons s _ => congrArg (cons · _)
                                   ((drop_contract _ _).trans
                                    (ide_contract s))

theorem _root_.Var.subst_weaken : ∀ (v : Var τ Ε) (s : Subst Δ Ε) (r : Renaming Γ Δ),
  v.subst (s.weaken r) = (v.subst s).rename r
| .zero,   .cons _ _, r => rfl
| .succ v, .cons s _, r => v.subst_weaken s r

theorem _root_.Var.subst_contract :
  ∀ (t : Var τ Ε) (r : Renaming Δ Ε) (s : Subst Γ Δ),
  t.subst (contract r s) = (t.rename r).subst s
| .zero,   .cons _ _, _ => rfl
| .succ v, .cons r _, s => v.subst_contract r s

theorem contract_weaken : ∀ (r₁ : Renaming Ε Θ) (s : Subst Δ Ε) (r₂ : Renaming Γ Δ),
  contract r₁ (s.weaken r₂) = (contract r₁ s).weaken r₂
| .nil,       _, r₂ => rfl
| .cons r₁ v, s, r₂ => congrArg₂ cons (contract_weaken r₁ s r₂)
                                      (v.subst_weaken s r₂)

theorem drop_weaken : ∀ (s : Subst Δ Ε) (r : Renaming Γ (Δ ,, τ)), weaken (s.drop τ) r = weaken s r.head
| .nil,       r => rfl
| .cons s t, r => by
  simp [drop, weaken, drop_weaken]
  rw [←Tm.rename_comp, Renaming.drop_comp, Renaming.ide_comp]

theorem weaken_drop : ∀ (s : Subst Δ Ε) (r : Renaming Γ Δ),
  weaken s (r.drop τ) = (weaken s r).drop τ
| .nil,       r => rfl
| .cons s t, r => congrArg₂ cons (weaken_drop s r)
                                 (by rw [←Renaming.comp_ide (r.drop _),
                                         Renaming.drop_comp,
                                         Tm.rename_comp]
                                     rfl)

theorem keep_weaken_keep : ∀ (s : Subst Δ Ε) (r : Renaming Γ Δ ),
  weaken (s.keep τ) (r.keep τ) = (weaken s r).keep τ :=
  λ _ _ => congrArg (cons · _) ((drop_weaken _ _).trans (weaken_drop _ _))

theorem contract_drop : ∀ (r : Renaming Δ Ε) (s : Subst Γ Δ),
  contract r (s.drop τ) = (contract r s).drop τ
| .nil,      s => rfl
| .cons r v, s => congrArg₂ cons (contract_drop r s)
                                 (by rw [←Var.subst_weaken, weaken_drop,
                                          weaken_ide])
theorem keep_contract_keep : ∀ (r : Renaming Δ Ε) (s : Subst Γ Δ),
  contract (r.keep τ) (s.keep τ) = (contract r s).keep τ :=
  λ _ _ => congrArg (cons · _) ((drop_contract _ _).trans (contract_drop _ _))

theorem _root_.Tm.subst_weaken :
  ∀ (t : Ε ⊢ τ) (s : Subst Δ Ε) (r : Renaming Γ Δ),
  t.subst (s.weaken r) = (t.subst s).rename r := by
  intro t
  revert Γ Δ
  induction t <;>
    (intro Δ Γ s r; simp [Tm.subst, Tm.rename]; try constructor)
  any_goals (revert Δ Γ s r; assumption)
  case var v => apply v.subst_weaken
  case lam Γ τ υ t ih =>
    rw [←ih, keep_weaken_keep]

theorem _root_.Tm.subst_contract :
  ∀ (t : Ε ⊢ τ) (r : Renaming Δ Ε) (s : Subst Γ Δ),
  t.subst (contract r s) = (t.rename r).subst s := by
  intro t
  revert Γ Δ
  induction t <;>
    (intro Δ Γ s r; simp [Tm.subst, Tm.rename]; try constructor)
  any_goals (revert Δ Γ s r; assumption)
  case var v => apply v.subst_contract
  case lam Γ τ υ t ih =>
    rw [←ih, keep_contract_keep]


@[simp]
theorem _root_.Var.subst_ide : ∀ {Γ : Ctx _} (v : Var τ Γ), v.subst (ide Γ) = .var v
  := λ v => (v.subst_renaming _).trans (congrArg Tm.var v.rename_ide)

@[simp]
theorem _root_.Tm.subst_ide : ∀ t : Γ ⊢ τ, t.subst (ide Γ) = t :=
  λ t => (t.subst_renaming _).trans t.rename_ide

@[simp]
theorem _root_.Var.subst_drop : ∀ (v : Var τ Δ) (s : Subst Γ Δ),
  v.subst (s.drop υ) = (v.subst s).rename ((Renaming.ide Γ).drop υ)
| .zero,   .cons _ _ => rfl
| .succ v, .cons s _ => v.subst_drop s

@[simp]
theorem _root_.Tm.subst_drop : ∀ (t : Δ ⊢ τ) (s : Subst Γ Δ),
  t.subst (s.drop υ) = (t.subst s).rename ((Renaming.ide Γ).drop υ)
| .var v, s => v.subst_drop s
| .base b, s => rfl
| .lam t, s => congrArg Tm.lam (by rw [←Tm.subst_weaken,
                                        keep_weaken_keep,
                                        weaken_drop,
                                        weaken_ide])
| .app t u, s => congrArg₂ Tm.app (t.subst_drop s) (u.subst_drop s)
| .pair t u, s => congrArg₂ Tm.pair (t.subst_drop s) (u.subst_drop s)
| .fst t, s => congrArg Tm.fst (t.subst_drop s)
| .snd t, s => congrArg Tm.snd (t.subst_drop s)
| .unit, s => rfl

theorem drop_comp : ∀ (s₁ : Subst Δ Ε) (s₂ : Subst Γ (Δ ,, τ)), comp (s₁.drop τ) s₂ = comp s₁ s₂.head
| .nil,       s₂ => rfl
| .cons s₁ t, s₂ => by
  simp [drop, comp, drop_comp]
  rw [←t.subst_contract, drop_contract, t.subst_contract, t.rename_ide]

theorem comp_drop : ∀ (s₁ : Subst Δ Ε) (s₂ : Subst Γ Δ),
  comp s₁ (s₂.drop τ) = (comp s₁ s₂).drop τ
| .nil,       s₂ => rfl
| .cons s₁ t, s₂ => congrArg₂ cons (comp_drop s₁ s₂)
                                   (t.subst_drop s₂)

theorem keep_comp_keep : ∀ (s₁ : Subst Δ Ε) (s₂ : Subst Γ Δ ),
  comp (s₁.keep τ) (s₂.keep τ) = (comp s₁ s₂).keep τ :=
  λ _ _ => congrArg (cons · _) ((drop_comp _ _).trans (comp_drop _ _))

theorem comp_ide : ∀ s : Subst Γ Δ, s.comp (ide Γ) = s
| .nil      => rfl
| .cons s t => congrArg₂ cons (comp_ide s) t.subst_ide

theorem ide_comp : ∀ s : Subst Γ Δ, (ide Δ).comp s = s 
| .nil      => rfl
| .cons s t => congrArg (cons · t)
                        ((congrArg (comp · (cons s t))
                                           (ofRenaming_drop (Renaming.ide _) _)
                                      ).trans (by
                                        rw [←ofRenaming_drop, ←contract_eq_ofRenaming_comp,
                                            drop_contract, ide_contract, head]))

theorem _root_.Var.subst_comp : ∀ (v : Var τ Ε) (s₁ : Subst Δ Ε) (s₂ : Subst Γ Δ),
  v.subst (s₁.comp s₂) = (v.subst s₁).subst s₂
| .zero,   .cons _ _,  _  => rfl
| .succ v, .cons s₁ _, s₂ => v.subst_comp s₁ s₂

theorem _root_.Tm.subst_comp : ∀ (t : Ε ⊢ τ) (s₁ : Subst Δ Ε) (s₂ : Subst Γ Δ),
  t.subst (s₁.comp s₂) = (t.subst s₁).subst s₂
| .var v,    s₁, s₂ => v.subst_comp s₁ s₂
| .base _,   _,  s₂ => rfl
| .lam t,    s₁, s₂ => congrArg Tm.lam
                                ((congrArg _ (s₁.keep_comp_keep s₂).symm).trans
                                 (t.subst_comp (s₁.keep _) (s₂.keep _)))
| .app t u,  s₁, s₂ => congrArg₂ Tm.app (t.subst_comp s₁ s₂) (u.subst_comp s₁ s₂)
| .pair t u, s₁, s₂ => congrArg₂ Tm.pair (t.subst_comp s₁ s₂) (u.subst_comp s₁ s₂)
| .fst t,    s₁, s₂ => congrArg Tm.fst (t.subst_comp s₁ s₂)
| .snd t,    s₁, s₂ => congrArg Tm.snd (t.subst_comp s₁ s₂)
| .unit,     _,  s₂ => rfl

theorem comp_assoc : ∀ (s₁ : Subst Ε Θ) (s₂ : Subst Δ Ε) (s₃ : Subst Γ Δ),
  comp (comp s₁ s₂) s₃ = comp s₁ (comp s₂ s₃)
| .nil,       _,  _  => rfl
| .cons s₁ t, s₂, s₃ => congrArg₂ cons (comp_assoc s₁ s₂ s₃) (t.subst_comp s₂ s₃).symm

section
open Categories

def SUB (σ : Sig) : Category where
  Ob :=  Ctx σ
  Hom := Subst
  id := ide
  comp := comp
  comp_id := comp_ide
  id_comp := ide_comp
  comp_assoc := comp_assoc

def concat : Ctx σ → Ctx σ → Ctx σ
| Γ, ε      => Γ 
| Γ, Δ ,, τ => (concat Γ Δ) ,, τ

instance : Append (Ctx σ) where
  append := concat

@[simp]
theorem nil_concat : ε ++ Δ = Δ := by
  induction Δ <;> congr
  apply congrArg (·,,_); assumption

@[simp]
theorem concat_nil : Γ ++ ε = Γ := rfl
@[simp]
theorem concat_cons : Γ ++ (Δ ,, τ) = (Γ ++ Δ) ,, τ := rfl

def arr : (Γ : Ctx σ) → Ty σ.types → Ty σ.types
| ε, ρ => ρ
| Γ ,, τ, ρ => arr Γ (Ty.arr τ ρ)

def exp : Ctx σ → Ctx σ → Ctx σ
| _, ε      => ε
| Δ, Γ ,, τ => exp Δ Γ ,, arr Δ τ

instance : Pow (Ctx σ) (Ctx σ) where
  pow a b := exp b a

@[simp]
theorem nil_pow {Γ : Ctx σ} : (ε : Ctx σ) ^ Γ = ε := rfl
@[simp]
theorem cons_pow {Γ Δ : Ctx σ} : (Δ ,, τ) ^ Γ = (Δ ^ Γ) ,, (arr Γ τ) := rfl

section
variable {σ : Sig}

def pair : ∀ {Γ Δ Ε : Ctx σ}, Subst (Γ) (Δ) → Subst (Γ) (Ε) → Subst (Γ) (Δ ++ Ε)
| _, _, ε,      s₁, _        => s₁
| Γ, Δ, Ε ,, τ, s₁, cons s₂ t => cons (pair s₁ s₂)  t

def proj₁ : ∀ {Γ Δ : Ctx σ}, Subst (Γ ++ Δ) (Γ)
| Γ, ε      => ide Γ
| _, _ ,, τ => proj₁.drop τ

def proj₂ : ∀ {Γ Δ : Ctx σ}, Subst (Γ ++ Δ) (Δ)
| _, ε      => .nil
| _, _ ,, τ => proj₂.keep τ

@[simp]
theorem pair_nil : pair s .nil = s := rfl
@[simp]
theorem pair_cons : pair s₁ (.cons s₂ t) = .cons (pair s₁ s₂) t := by rw [pair]

@[simp]
theorem proj₁_nil : proj₁ (Δ := ε) = ide Γ := rfl
@[simp]
theorem proj₁_cons {Γ Δ : Ctx σ} : proj₁ ( Γ:= Γ) (Δ := Δ ,, τ) = (proj₁ (Δ := Δ)).drop τ 
  := rfl

@[simp]
theorem proj₂_nil : proj₂ (Γ:= Γ) (Δ := ε) = nil := rfl
@[simp]
theorem proj₂_cons {Γ Δ : Ctx σ} : proj₂ (Γ:= Γ) (Δ := Δ ,, τ) =
  (proj₂ (Δ := Δ)).keep τ 
  := rfl

@[simp]
theorem cons_proj₂ {Γ Δ : Ctx σ} : proj₂ (Γ:= Γ) (Δ := Δ ,, τ) =
  (proj₂ (Δ := Δ)).keep τ 
  := rfl


def par : ∀ {Γ Δ Γ' Δ' : Ctx σ}, Subst Γ Δ → Subst Γ' Δ' → Subst (Γ ++ Γ') (Δ ++ Δ')
| _, _, _, _, s₁, s₂ => pair (s₁.comp proj₁) (s₂.comp proj₂)

def app : ∀ {Γ Δ : Ctx σ}, Γ ⊢ arr Δ τ → Subst (Γ) (Δ) → Γ ⊢ τ
| _, ε,      f, .nil      => f
| Γ, Δ ,, υ, f, .cons s t => .app (app f s) t

def apps : ∀ {Γ Δ Ε : Ctx σ}, Subst (Γ) (exp Δ Ε) → Subst (Γ) (Δ) → Subst (Γ) (Ε)
| _, _, ε,      _,          _ => .nil
| _, _, _ ,, _, .cons fs f, x => .cons (apps fs x) (app f x)

def lam' : ∀ {Γ Δ}, (Γ ++ Δ) ⊢ τ → Γ ⊢ arr Δ τ
| _, ε,      t => t
| _, Δ ,, _, t => lam' (Δ := Δ) (.lam t)

def eval {Γ Δ : Ctx σ} : Subst (Δ ^ Γ ++ Γ) (Δ) :=
  apps proj₁ proj₂

def lam : ∀ {Γ Δ Ε : Ctx σ}, Subst (Γ ++ Δ) (Ε) → Subst (Γ) (exp Δ Ε)
| _, _, ε,      _          => .nil
| _, _, _ ,, _, .cons fs f => .cons (lam fs) (lam' f)
end

theorem proj₁_pair {f : Subst X Γ} {g : Subst X Δ} : proj₁.comp (pair f g) = f := by
  induction Δ with
  | nil => cases g; simp [(·++·), Append.append, concat, proj₁, pair]; rw [ide_comp]
  | cons Δ τ ih =>
    cases g; simp [(·++·), Append.append, concat, proj₁, pair]
    simp [drop_comp, head, ih]

theorem proj₂_pair {f : Subst X Γ} {g : Subst X Δ} : proj₂.comp (pair f g) = g := by
  induction Δ with
  | nil => cases g; rfl
  | cons Δ τ ih =>
    cases g; simp [(·++·), Append.append, concat, proj₂, pair]
    simp [keep, comp, Tm.subst, Var.subst, head, drop_comp, ih]

theorem pair_unique {f : Subst X Γ} {g : Subst X Δ} {fg : Subst X (Γ ++ Δ)} :
  proj₁.comp fg = f → proj₂.comp fg = g → pair f g = fg := by
  intro h₁ h₂
  induction Δ with
  | nil => cases g; simp [(·++·), Append.append, concat, comp, proj₁, ide_comp] at h₁; exact h₁.symm
  | cons Δ τ ih =>
    cases fg; cases g;
    simp [keep, comp, drop_comp, head, Tm.subst, Var.subst] at h₁ h₂
    simp
    have ⟨h₂₁, h₂₂⟩ := h₂
    constructor
    · apply ih
      rw [h₁]
      rw [h₂₁]
    · rw [h₂₂]
