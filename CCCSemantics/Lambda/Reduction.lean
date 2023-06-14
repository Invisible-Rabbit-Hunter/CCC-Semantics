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
  case symm _ ih => apply TmEquiv.symm (ih (Setoid.symm r₂))
  case trans _ _ _ ih₁ ih₂ => apply TmEquiv.trans (ih₁ r₂) (ih₂ (Setoid.refl _))
  case app_congr _ _ ih₁ ih₂ =>
    apply TmEquiv.app_congr
    · apply ih₁ r₂
    · apply ih₂ r₂
  case lam_congr _ ih =>
    apply TmEquiv.lam_congr
    apply ih
    apply SubEquiv.keep_congr r₂
  case pair_congr _ _ ih₁ ih₂ =>
    apply TmEquiv.pair_congr
    · apply ih₁ r₂
    · apply ih₂ r₂
  case fst_congr _ ih => 
    apply TmEquiv.fst_congr
    apply ih r₂
  case snd_congr _ ih => 
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

theorem TmEquiv.lam'_congr {s s' : (X ++ Γ) ⊢ τ} :
  s ≈ s' → (Subst.lam' s) ≈ (Subst.lam' s') := by
  revert τ
  induction Γ with
  | nil => intro τ s s' e; exact e
  | cons Γ τ ih => intro τ s s' e; exact ih (TmEquiv.lam_congr e)
    
theorem SubEquiv.lam_congr {s s' : Subst (X ++ Γ) Δ} :
  s ≈ s' → s.lam ≈ s'.lam := by
  intro e
  induction e with
  | nil => apply Setoid.refl
  | cons eₛ eₜ ih => simp [Subst.lam]; apply SubEquiv.cons ih (TmEquiv.lam'_congr eₜ)

@[simp]
theorem pow_nil : Δ ^ ε = Δ := by
  induction Δ with
  | nil => rfl
  | cons Δ τ ih => simp [Subst.arr, ih]

@[simp]
theorem pair_drop {f : Subst X Γ} {g : Subst X Δ}: (f.drop τ).pair (g.drop τ) = (f.pair g).drop τ := by
  induction g with
  | nil => rfl
  | cons g t ih => simp [Subst.drop, ih]

theorem TmEquiv.app_lam' {f : (X ++ Γ) ⊢ Δ} {x : Subst X Γ} :
  Subst.app (Subst.lam' f) x ≈ f.subst ((Subst.ide _).pair x) := by
  revert Δ
  induction x with
  | nil => intro Δ f; simp; apply TmEquiv.refl
  | cons xs x ih =>
      intro Δ f
      simp [Subst.lam', Subst.app, Subst.apps, Subst.comp]
      apply TmEquiv.trans
      · apply TmEquiv.app_congr
        · apply ih
        · apply TmEquiv.refl
      · apply TmEquiv.trans
        · apply TmEquiv.arr_β
        · rw [←Tm.subst_comp]
          simp [Subst.keep, Subst.comp, Subst.drop_comp, Subst.head, Tm.subst, Var.subst,
                Subst.comp_ide]
          apply TmEquiv.refl

theorem SubEquiv.apps_lam {f : Subst (X ++ Γ) Δ} {x : Subst X Γ} :
  Subst.apps (Subst.lam f) x ≈ f.comp ((Subst.ide _).pair x) := by
  induction f with
  | nil => apply Setoid.refl
  | cons fs f ih =>
      simp [Subst.lam, Subst.apps, Subst.comp]
      constructor
      · assumption
      · apply TmEquiv.app_lam'

theorem Subst.app_subst {f : X ⊢ arr Γ τ} {x : Subst X Γ} {g : Subst Y X} :
  (Subst.app f x).subst g = Subst.app (f.subst g) (x.comp g) := by
  revert τ
  induction x with
  | nil => intro τ f; rfl
  | cons xs x ih =>
    intro τ f
    simp [Subst.arr, Subst.app, Subst.comp, Tm.subst]
    apply ih

theorem Subst.apps_comp {f : Subst X (Δ^Γ)} {x : Subst X Γ} {g : Subst Y X} :
  (Subst.apps f x).comp g = Subst.apps (f.comp g) (x.comp g) := by
  induction Δ with
  | nil => rfl
  | cons Δ τ ih =>
    cases f with | cons fs f =>
    simp [Subst.apps, Subst.comp]
    constructor
    · apply ih
    · apply Subst.app_subst

theorem Subst.lam'_subst {f : (X ++ Γ) ⊢ τ} {g : Subst Y X} :
  (Subst.lam' f).subst g = lam' (f.subst (g.par (Subst.ide _))) := by
  revert τ
  induction Γ with
  | nil => intro τ f; simp [lam', par, pair, comp_ide]
  | cons Γ υ ih =>
    intro τ f
    simp [Subst.lam', Subst.comp, Subst.par, ih, Tm.subst]
    apply congrArg lam'
    apply congrArg Tm.lam
    simp [keep,ide_comp, ofRenaming_drop, drop_comp, head, comp_drop, Var.subst]
    rw [←ide, ide_comp]

theorem Subst.lam_comp {f : Subst (X ++ Γ) Δ} {g : Subst Y X} :
  (Subst.lam f).comp g = lam (f.comp (g.par (Subst.ide _))) := by
  induction f with
  | nil => rfl
  | cons fs f ih =>
    simp [Subst.apps, Subst.comp, Subst.lam]
    apply congrArg₂ cons
    · apply ih
    · simp [Subst.lam'_subst]

theorem Subst.par_comp_pair : (Subst.par a b).comp (Subst.pair c d) =
                              Subst.pair (a.comp c) (b.comp d) := by
  simp [Subst.par]
  induction b with
  | nil => simp [Subst.comp, Subst.comp_assoc, proj₁_pair]
  | cons bₛ bₜ ih =>
    simp [comp, pair]
    constructor
    · apply ih
    · rw [←Tm.subst_comp, proj₂_pair]

theorem Subst.pair_proj₁_proj₂ : Subst.pair (Subst.proj₁ (Γ := Γ) (Δ := Δ)) Subst.proj₂ =
  Subst.ide (Γ ++ Δ) := (Subst.pair_unique (Subst.comp_ide _)
                                           (Subst.comp_ide _))

theorem SubEquiv.eval_lam {s : Subst (X ++ Γ) Δ} :
  Subst.eval.comp (s.lam.par (Subst.ide Γ)) ≈ s := by
  simp [Subst.eval, Subst.par]
  rw [Subst.apps_comp, Subst.proj₁_pair, Subst.proj₂_pair]
  rw [Subst.ide_comp, Subst.lam_comp]
  induction s with
  | nil => apply Setoid.refl
  | cons s t ih =>
      simp [Subst.lam, Subst.comp, Subst.apps]
      constructor
      · apply ih
      · apply TmEquiv.trans
        apply TmEquiv.app_lam'
        rw [←Tm.subst_comp, Subst.par_comp_pair, Subst.comp_ide, Subst.ide_comp,
            Subst.pair_proj₁_proj₂, Tm.subst_ide]
        apply TmEquiv.refl
    
theorem TmEquiv.big_arr_η {f : X ⊢ Subst.arr Γ τ}:
  f ≈ Subst.lam' (Subst.app (f.subst Subst.proj₁) (Subst.proj₂)) := by
  revert τ
  induction Γ with
  | nil => intro τ f
           simp [Subst.lam', Subst.app]
           apply TmEquiv.refl
  | cons Γ υ ih =>
    intro τ f
    simp [Subst.lam', Subst.app]
    apply TmEquiv.trans
    · apply ih
    · rw [←Tm.subst_weaken, Subst.weaken_drop, Subst.weaken_ide]
      simp [Subst.arr] at f
      apply lam'_congr (X := X) (Γ := Γ)
      apply TmEquiv.trans
      apply TmEquiv.arr_η
      simp
      rw [←Tm.subst_weaken, Subst.weaken_drop, Subst.weaken_ide]
      apply TmEquiv.lam_congr
      simp [Subst.app, Subst.keep]
      rw [←Tm.subst_weaken, Subst.weaken_drop, Subst.weaken_ide,
         ←Tm.subst_renaming, Subst.app_subst, ←Tm.subst_comp,
         ←Subst.weaken_eq_comp_ofRenaming, Subst.weaken_drop,
         Subst.weaken_ide, ←Subst.weaken_eq_comp_ofRenaming,
         Subst.weaken_drop, Subst.weaken_ide]
      apply TmEquiv.refl

theorem TmEquiv.lam'_unique {f : (X ++ Γ) ⊢ τ} {f' : X ⊢ Subst.arr Γ τ}
  (h : f ≈ Subst.app (Tm.subst f' Subst.proj₁) Subst.proj₂) :
  f' ≈ Subst.lam' f := by
  apply TmEquiv.trans
  apply TmEquiv.big_arr_η
  apply TmEquiv.lam'_congr
  apply Setoid.symm
  assumption

theorem SubEquiv.lam_unique {f : Subst (X ++ Γ) Δ} {f' : Subst X (Δ^Γ)}
  (h : f ≈ Subst.apps (f'.comp Subst.proj₁) Subst.proj₂) :
  f' ≈ Subst.lam f := by
  induction Δ with
  | nil => cases f'; apply SubEquiv.nil
  | cons Δ τ ih =>
    cases f with | cons fs f =>
    cases f' with | cons f's f' =>
    cases h with | cons hₛ hₜ =>
    simp [Subst.lam]
    apply SubEquiv.cons
    · apply ih
      exact hₛ
    · apply TmEquiv.lam'_unique hₜ

theorem SubEquiv.app_congr {s₁ s₁' : Γ ⊢ Subst.arr Δ τ} {s₂ s₂' : Subst Γ Δ} : s₁ ≈ s₁' → s₂ ≈ s₂' → Subst.app s₁ s₂ ≈ Subst.app s₁' s₂' := by
  intro e₁ e₂
  revert τ
  induction e₂ with
  | nil => intro τ s₁ s₂ e₁; exact e₁
  | cons _ e₂ₜ ih =>
    intro τ s₁ s₂ e₁
    simp [Subst.app]
    apply TmEquiv.app_congr
    · apply ih e₁
    · assumption
      
theorem SubEquiv.apps_congr {s₁ s₁' : Subst Γ (Subst.exp Δ Ε)} {s₂ s₂' : Subst Γ Δ} : s₁ ≈ s₁' → s₂ ≈ s₂' → Subst.apps s₁ s₂ ≈ Subst.apps s₁' s₂' := by
  intro e₁ e₂
  induction Ε with
  | nil => apply SubEquiv.nil; 
  | cons Ε τ ih =>
    cases e₁ with | cons e₁ₛ e₁ₜ =>
    apply SubEquiv.cons
    · apply ih e₁ₛ
    · apply SubEquiv.app_congr
      · apply e₁ₜ
      · apply e₂
    