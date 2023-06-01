import CCCSemantics.Lambda.Substitution

inductive TmEquiv : ∀ (Γ : Ctx σ) τ, Γ ⊢ τ → Γ ⊢ τ → Prop
| refl t : TmEquiv _ _ t t
| symm : TmEquiv _ _ t u → TmEquiv _ _ u t
| trans : TmEquiv _ _ s t → TmEquiv _ _ t u → TmEquiv _ _ s u
| app_congr : TmEquiv _ _ t t' → TmEquiv _ _ u u' → TmEquiv _ _ (.app t u) (.app t' u') 
| lam_congr : TmEquiv _ _ t t' → TmEquiv _ _ (.lam t) (.lam t') 
| pair_congr : TmEquiv _ _ t t' → TmEquiv _ _ u u' → TmEquiv _ _ (.pair t u) (.pair t' u') 
| fst_congr : TmEquiv _ _ t t' → TmEquiv _ _ (.fst t) (.fst t') 
| snd_congr : TmEquiv _ _ t t' → TmEquiv _ _ (.snd t) (.snd t') 
| arr_β : TmEquiv _ _ (.app (.lam t) u) (t.subst ((Subst.ide _).cons u))
| arr_η : TmEquiv _ _ t (.lam (.app (t.rename ((Renaming.ide _).drop _))
                    (.var .zero)))
| prod_β₁ : TmEquiv _ _ (.fst (.pair t u)) t
| prod_β₂ : TmEquiv _ _ (.snd (.pair t u)) u
| prod_η : TmEquiv _ _ t (.pair (.fst t) (.snd t))
| unit_η : TmEquiv _ _ t .unit

instance (Γ : Ctx σ) (τ : Ty _) : Equivalence (TmEquiv Γ τ) where
  refl := .refl
  symm := .symm
  trans := .trans

instance (Γ : Ctx σ) τ : Setoid (Γ ⊢ τ) where
  r := TmEquiv Γ τ
  iseqv := instEquivalenceTmTmEquiv Γ τ

inductive SubEquiv : ∀ Γ Δ : Ctx σ, Subst Γ Δ → Subst Γ Δ → Prop where
| nil : SubEquiv Γ ε .nil .nil
| cons : SubEquiv Γ Δ s s' → TmEquiv Γ τ t t' →  SubEquiv Γ (Δ ,, τ) (s.cons t) (s'.cons t')

def SubEquiv.refl (s : Subst Γ Δ) : SubEquiv Γ Δ s s := by
  induction s <;> (constructor <;> (try {constructor}; try assumption))

def SubEquiv.symm (r : SubEquiv Γ Δ s₁ s₂) : SubEquiv Γ Δ s₂ s₁ := by
  induction r <;> (constructor <;> (try {constructor}; try assumption))
  apply TmEquiv.symm
  assumption
def SubEquiv.trans (r₁ : SubEquiv Γ Δ s₁ s₂) (r₂ : SubEquiv Γ Δ s₂ s₃) :
  SubEquiv Γ Δ s₁ s₃ := by
  induction r₁
  assumption
  case cons _ rt ih =>
    cases r₂ with | cons r₂ rt' =>
    simp
    constructor
    apply ih r₂
    apply TmEquiv.trans rt rt'

instance (Γ Δ : Ctx σ) : Equivalence (SubEquiv Γ Δ) where
  refl := SubEquiv.refl
  symm := SubEquiv.symm
  trans := SubEquiv.trans
  
instance (Γ Δ : Ctx σ) : Setoid (Subst Γ Δ) where
  r := SubEquiv Γ Δ
  iseqv := instEquivalenceSubstSubEquiv Γ Δ 

theorem TmEquiv.ofEq {Γ : Ctx σ} {τ} {t t' : Γ ⊢ τ} : t = t' → t ≈ t' 
| .refl _ => TmEquiv.refl _

theorem TmEquiv.rename_congr {t t' : Δ ⊢ τ} (r : Renaming Γ Δ) :
  t ≈ t' → t.rename r ≈ t'.rename r := by
  intro e
  revert Γ
  induction e <;> (intro Γ r)
  case refl => apply TmEquiv.refl
  case symm _ _ ih => apply (ih r).symm
  case trans _ _ _ _ ih₁ ih₂ => apply (ih₁ r).trans (ih₂ r)
  case app_congr _ _ ih₁ ih₂ => apply TmEquiv.app_congr (ih₁ r) (ih₂ r)
  case lam_congr _ ih => apply TmEquiv.lam_congr (ih (r.keep _))
  case pair_congr _ _ ih₁ ih₂ => apply TmEquiv.pair_congr (ih₁ r) (ih₂ r)
  case fst_congr _ ih => apply TmEquiv.fst_congr (ih r)
  case snd_congr _ ih => apply TmEquiv.snd_congr (ih r)
  case arr_β t u => apply TmEquiv.trans
                    apply TmEquiv.arr_β
                    apply TmEquiv.ofEq
                    rw [←Tm.subst_contract, Renaming.keep, Subst.contract]
                    simp [Var.subst, Subst.drop_contract, Subst.head,
                          Subst.contract_eq_ofRenaming_comp,
                          Subst.ofRenaming_drop, Subst.drop_comp,
                          Subst.comp_ide]
                    rw [←Tm.subst_weaken]
                    congr
                    rw [Subst.weaken_eq_comp_ofRenaming, Subst.ide_comp]
  case arr_η => apply TmEquiv.trans
                apply TmEquiv.arr_η
                apply TmEquiv.lam_congr
                apply TmEquiv.app_congr
                · simp [←Tm.rename_comp, Renaming.keep, Renaming.head]; apply TmEquiv.refl _
                · apply TmEquiv.refl _
  case prod_β₁ => apply TmEquiv.prod_β₁
  case prod_β₂ => apply TmEquiv.prod_β₂
  case prod_η => apply TmEquiv.prod_η
  case unit_η => apply TmEquiv.unit_η

theorem SubEquiv.drop_congr {s s' : Subst Γ Δ} :
  s ≈ s' → (s.drop τ) ≈ (s'.drop τ) := by
  intro r
  induction r with
  | nil => constructor
  | cons _ rt ih => constructor
                    · assumption
                    · apply TmEquiv.rename_congr _ rt
                  
theorem SubEquiv.keep_congr {s s' : Subst Γ Δ} :
  s ≈ s' → (s.keep τ) ≈ (s'.keep τ) := by
  intro r
  constructor
  · apply SubEquiv.drop_congr r
  · constructor

theorem SubEquiv.tm_subst_congr {t : Δ ⊢ τ} {s s' : Subst Γ Δ} :
  s ≈ s' → t.subst s ≈ t.subst s' := by
  revert Γ
  induction t <;> intro Γ s s' e
  case var v =>
    induction v with
    | zero => cases e; assumption
    | succ v ih => cases e; apply ih; assumption
  case base b => apply Setoid.refl
  case lam t ih => apply TmEquiv.lam_congr; apply ih (SubEquiv.keep_congr e)
  case app _ _ ih₁ ih₂ => apply TmEquiv.app_congr; apply ih₁ e; apply ih₂ e 
  case pair _ _ ih₁ ih₂ => apply TmEquiv.pair_congr; apply ih₁ e; apply ih₂ e 
  case fst t ih => apply TmEquiv.fst_congr; apply ih e
  case snd t ih => apply TmEquiv.snd_congr; apply ih e
  case unit => apply TmEquiv.refl

theorem TmEquiv.subst_congr {t t' : Δ ⊢ τ} {s s' : Subst Γ Δ} :
  t ≈ t' → s ≈ s' → t.subst s ≈ t'.subst s' := by
  intro r₁
  revert Γ
  induction r₁ <;> intro Γ s s' r₂
  case refl t => apply SubEquiv.tm_subst_congr r₂
  case symm r₁ ih => apply TmEquiv.symm (ih (Setoid.symm r₂))
  case trans _ _ _ ih₁ ih₂ => apply TmEquiv.trans (ih₁ r₂) (ih₂ (Setoid.refl _))
  case app_congr r₁₁ r₁₂ ih₁ ih₂ =>
    apply TmEquiv.app_congr
    · apply ih₁ r₂
    · apply ih₂ r₂
  case lam_congr r₁ ih =>
    apply TmEquiv.lam_congr
    apply ih
    apply SubEquiv.keep_congr r₂
  case pair_congr r₁₁ r₁₂ ih₁ ih₂ =>
    apply TmEquiv.pair_congr
    · apply ih₁ r₂
    · apply ih₂ r₂
  case fst_congr r₁ ih => 
    apply TmEquiv.fst_congr
    apply ih r₂
  case snd_congr r₁ ih => 
    apply TmEquiv.snd_congr
    apply ih r₂
  case arr_β => simp [Tm.subst]
                apply TmEquiv.trans
                apply TmEquiv.arr_β
                rw [←Tm.subst_comp, ←Tm.subst_comp]
                apply SubEquiv.tm_subst_congr
                simp [Subst.comp, Subst.drop_comp, Subst.keep, Subst.head, Tm.subst,
                      Var.subst, Subst.ide_comp, Subst.comp_ide]
                constructor; assumption; apply SubEquiv.tm_subst_congr; assumption
  case arr_η => simp [Tm.subst, Var.subst, ←Tm.subst_contract,
                      Subst.drop_contract, Subst.ide_contract,
                      Subst.keep, Subst.head]
                rw [←Tm.subst_weaken, Subst.weaken_drop, Subst.weaken_ide]
                apply TmEquiv.trans TmEquiv.arr_η
                apply TmEquiv.lam_congr; apply TmEquiv.app_congr _ (TmEquiv.refl _)
                rw [←Tm.subst_weaken, Subst.weaken_drop, Subst.weaken_ide]
                apply SubEquiv.tm_subst_congr
                apply SubEquiv.drop_congr r₂
  case prod_β₁ => apply TmEquiv.trans TmEquiv.prod_β₁
                  apply SubEquiv.tm_subst_congr; assumption
  case prod_β₂ => apply TmEquiv.trans TmEquiv.prod_β₂
                  apply SubEquiv.tm_subst_congr; assumption
  case prod_η => apply TmEquiv.trans _ TmEquiv.prod_η
                 apply SubEquiv.tm_subst_congr; assumption
  case unit_η => apply TmEquiv.unit_η

theorem SubEquiv.comp_congr {s₁ s₁' : Subst Δ Ε} {s₂ s₂' : Subst Γ Δ} :
  s₁ ≈ s₁' → s₂ ≈ s₂' → (s₁.comp s₂) ≈ (s₁'.comp s₂') := by
  intro r₁ r₂
  induction r₁ with
  | nil => constructor
  | cons _ rt ih =>
    constructor
    assumption
    apply TmEquiv.subst_congr rt r₂

theorem SubEquiv.ofEq {s s' : Subst Γ Δ} : s = s' → s ≈ s'
| .refl _ => Setoid.refl _

theorem SubEquiv.pair_congr {s₁ s₁' : Subst X Γ} {s₂ s₂' : Subst X Δ} :
  s₁ ≈ s₁' → s₂ ≈ s₂' → Subst.pair s₁ s₂ ≈ Subst.pair s₁' s₂' := by
  intro e₁ e₂
  induction e₂ with
  | nil => exact e₁
  | cons e₂ eₜ ih =>
    simp [Subst.pair]
    apply cons ih eₜ
