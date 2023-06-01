import CCCSemantics.Categories.CartesianClosed
import CCCSemantics.Categories.CartesianClosed.Types
import CCCSemantics.Lambda.Reduction

open Categories Cartesian CartesianClosed
variable [CartesianClosed 𝒞]

def interpTy (base : α → 𝒞) : Ty α → 𝒞
| .base b => base b
| .arr a b => exp (interpTy base a) (interpTy base b)
| .prod a b => prod (interpTy base a) (interpTy base b)
| .unit => Cartesian.final

structure Struct (σ : Sig) (𝒞) [CartesianClosed 𝒞] where
  types : σ.types → 𝒞
  terms (t : σ.terms) : final ⟶ interpTy types (σ.typing t)

notation "⟦" τ "⟧Ty[" σ "]" => interpTy (Struct.types σ) τ

section
variable [CartesianClosed 𝒞] (Str : Struct σ 𝒞)

def interpCtx : Ctx σ → 𝒞
| ε      => final
| Γ ,, τ => interpCtx Γ ×' (interpTy Str.types τ)

notation "⟦" Γ "⟧Ctx[" s "]" => interpCtx s Γ

def interpVar : ∀ {Γ : Ctx σ}, Var τ Γ → interpCtx Str Γ ⟶ interpTy Str.types τ
| _ ,, _, .zero => proj₂
| _ ,, _, .succ v => interpVar v ⊚ proj₁

notation "⟦" v "⟧Var[" s "]" => interpVar s v

def interpTm :
  Γ ⊢ τ → (interpCtx Str Γ ⟶ interpTy Str.types τ)
| .var v    => interpVar Str v
| .base b   => Str.terms b ⊚ bang
| .lam t    => lam (interpTm t)
| .app t u  => eval ⊚ pair (interpTm t) (interpTm u)
| .pair t u => pair (interpTm t) (interpTm u)
| .fst t    => proj₁ ⊚ interpTm t
| .snd t    => proj₂ ⊚ interpTm t
| .unit     => bang

notation "⟦" t "⟧Tm[" s "]" => interpTm s t

def interpRenaming :
  Renaming Γ Δ → (interpCtx Str Γ ⟶ interpCtx Str Δ)
| .nil      => bang
| .cons r v => pair (interpRenaming r) (interpVar Str v)

notation "⟦" r "⟧Ren[" s "]" => interpRenaming s r

theorem interpVar_renaming : ∀ (v : Var τ Δ) (r : Renaming Γ Δ),
  ⟦ v.rename r ⟧Var[Str] = ⟦ v ⟧Var[Str] ⊚ ⟦ r ⟧Ren[Str]
| .zero,   .cons r v => (proj₂_pair _ _).symm
| .succ v, .cons r _ => by rw [Var.rename, interpVar,
                               interpRenaming, Category.assoc _ proj₁,
                               proj₁_pair, interpVar_renaming]

@[simp]
theorem interpRenaming_drop : ∀ (r : Renaming Γ Δ),
  ⟦ r.drop τ ⟧Ren[Str] = ⟦ r ⟧Ren[Str] ⊚ proj₁
| .nil      => (bang_unique _).symm
| .cons r v => by
  apply pair_unique
  rw [←Category.assoc, interpRenaming, proj₁_pair, interpRenaming_drop]
  rw [←Category.assoc, interpRenaming, proj₂_pair, interpVar]

@[simp]
theorem interpRenaming_ide : ∀ Γ : Ctx σ, ⟦ Renaming.ide Γ ⟧Ren[ Str ] = 𝟙 ⟦Γ⟧Ctx[Str]
| ε      => (bang_unique _).symm
| Γ ,, τ => by
  simp [interpRenaming, interpVar, interpCtx]
  rw [interpRenaming_ide Γ]
  simp

theorem interpTm_renaming : ∀ (t : Δ ⊢ τ) (r : Renaming Γ Δ),
  ⟦ t.rename r ⟧Tm[Str] = ⟦ t ⟧Tm[Str] ⊚ ⟦ r ⟧Ren[Str]
| .var  v,   r => interpVar_renaming Str v r
| .base b,   r => ((Category.assoc _ _ _).trans
                   (congrArg (_⊚·) (bang_unique _))).symm
| .lam  t,   r => by
    simp [Tm.rename, interpTm]
    rw [interpTm_renaming t]
    simp [interpRenaming, interpVar]
    rw [←Category.id_compose proj₂, ←prod.map, prod.lam_of_comp]
| .app  t u, r => by simp [Tm.rename, interpTm]
                     rw [interpTm_renaming t, interpTm_renaming u, pair_comp]
| .pair t u, r => by simp [Tm.rename, interpTm]
                     rw [interpTm_renaming t, interpTm_renaming u, pair_comp]
| .fst  t,   r => by simp [Tm.rename, interpTm]; rw [interpTm_renaming t]
| .snd  t,   r => by simp [Tm.rename, interpTm]; rw [interpTm_renaming t]
| .unit,     r => (bang_unique _).symm

def interpSubst :
  Subst Γ Δ → (interpCtx Str Γ ⟶ interpCtx Str Δ)
| .nil      => bang
| .cons s t => pair (interpSubst s) (interpTm Str t)

notation "⟦" s "⟧Sub[" str "]" => interpSubst str s

theorem interpVar_subst : ∀ (v : Var τ Δ) (s : Subst Γ Δ) ,
  ⟦ v.subst s ⟧Tm[Str] = ⟦ v ⟧Var[Str] ⊚ interpSubst Str s
| .zero,   .cons _ t => by simp [Var.subst, interpSubst, interpVar]
| .succ v, .cons s _ => by simp [Var.subst, interpSubst, interpVar, interpVar_subst]

theorem interpSubst_drop : ∀ (s : Subst Γ Δ),
  ⟦ s.drop τ ⟧Sub[Str] = ⟦ s ⟧Sub[Str] ⊚ proj₁
| .nil      => (bang_unique _).symm
| .cons s t => by
  simp [Subst.drop, interpSubst]
  apply pair_unique
  rw [←Category.assoc, proj₁_pair, interpSubst_drop]
  rw [←Category.assoc, proj₂_pair, interpTm_renaming, interpRenaming_drop]
  simp

theorem interpTm_subst : ∀ (t : Δ ⊢ τ) (s : Subst Γ Δ),
  interpTm Str (t.subst s) = interpTm Str t ⊚ interpSubst Str s
| .var v,    s => interpVar_subst Str v s
| .base b,   s => by
  simp [interpTm]
  congr
  exact (bang_unique _).symm
| .lam t,    s => by
  simp [interpTm]
  apply Eq.symm
  apply lam_unique
  simp [interpTm_subst, interpSubst, interpTm, interpVar]
  rw [prod.map_comp_fst, ←Category.assoc, eval_lam]
  simp [prod.map, interpSubst_drop]
| .app t u,  s => by simp [interpTm, Tm.subst, interpTm_subst]
| .pair t u, s => by simp [interpTm, Tm.subst, interpTm_subst]
| .fst t,    s => by simp [interpTm, Tm.subst, interpTm_subst]
| .snd t,    s => by simp [interpTm, Tm.subst, interpTm_subst]
| .unit,     s => (bang_unique _).symm

@[simp]
theorem interpSubst_ofRenaming : ∀ (r : Renaming Γ Δ),
  ⟦ Subst.ofRenaming r ⟧Sub[Str] = ⟦ r ⟧Ren[Str]
| .nil      => (bang_unique _).symm
| .cons r v => by
  simp [interpSubst, interpRenaming]
  apply pair_unique
  simp [interpSubst_ofRenaming r]
  simp [interpTm]
  
@[simp]
theorem interpSubst_ide : ∀ Γ : Ctx σ, ⟦ Subst.ide Γ ⟧Sub[ Str ] = 𝟙 ⟦Γ⟧Ctx[Str] := by
  simp [Subst.ide]

theorem interpTm_preserves_equiv : t ≈ t' →
  ⟦ t ⟧Tm[Str] = ⟦ t' ⟧Tm[Str] := by
    intro r
    induction r with
    | refl t                 => rfl
    | symm _ ih              => exact ih.symm
    | trans _ _ ih₁ ih₂      => exact ih₁.trans ih₂
    | app_congr _ _ ih₁ ih₂  => exact congrArg₂ (eval ⊚ pair · ·) ih₁ ih₂
    | lam_congr _ ih         => exact congrArg lam ih
    | pair_congr _ _ ih₁ ih₂ => exact congrArg₂ pair ih₁ ih₂
    | fst_congr _ ih         => exact congrArg (proj₁ ⊚ ·) ih
    | snd_congr _ ih         => exact congrArg (proj₂ ⊚ ·) ih
    | arr_β                  => simp [interpTm, interpTm_subst, interpSubst]
                                rw [eval_pair_lam]
    | arr_η                  => simp [interpTm, interpTm_subst, interpSubst]
                                apply lam_unique
                                simp [interpTm_renaming, interpVar, prod.map]
    | prod_β₁                => simp [interpTm]
    | prod_β₂                => simp [interpTm]
    | prod_η                 => simp [interpTm]
                                apply Eq.symm
                                apply Category.id_compose
    | unit_η                 => apply bang_unique

theorem interpSubst_preserves_equiv : s ≈ s' →
  ⟦ s ⟧Sub[Str] = ⟦s'⟧Sub[Str] := by
    intro r
    induction r with
    | nil => rfl
    | cons _ rt ih =>
      apply congrArg₂ pair
      exact ih
      exact interpTm_preserves_equiv _ rt

theorem interpSubst_comp : ⟦ s₁.comp s₂ ⟧Sub[Str] = ⟦s₁⟧Sub[Str] ⊚ ⟦s₂⟧Sub[Str] := by
  induction s₁ with
  | nil => apply Eq.symm; apply bang_unique
  | cons s₁ t ih =>
    simp [Subst.comp, interpSubst, ih, interpTm_subst]


def TmQ (Γ : Ctx σ) τ := Quotient (instSetoidTm Γ τ)

def Syn (Γ Δ : Ctx σ) := Quotient (instSetoidSubst Γ Δ)

def Syn.nil : Syn Γ ε := Quotient.mk' .nil

def Syn.cons : Syn Γ Δ → TmQ Γ τ → Syn Γ (Δ ,, τ) :=
  Quotient.lift₂ (λ s t => Quotient.mk' (Subst.cons s t)) $ by
    intro s₁ t₁ s₂ t₂ eₛ eₜ
    apply Quotient.sound
    apply SubEquiv.cons <;> assumption

-- theorem Syn.cons_lift : Syn Γ Δ → TmQ Γ τ → Syn Γ (Δ ,, τ) :=
--   Quotient.lift₂ (λ s t => Quotient.mk' (Subst.cons s t)) $ by
--     intro s₁ t₁ s₂ t₂ eₛ eₜ
--     apply Quotient.sound
--     apply SubEquiv.cons <;> assumption

def Eq.ap_apply_natural {β : α → Sort _} {γ : (x : α) → (y : β x) → Sort _}
   {a a' : α} (h : a = a') (f : (x : β a) → γ a' (h ▸ x)) :
  ∀ b : β a, f (h ▸ b) = h ▸ f b := by
  intro x
  cases h
  simp

def SynCat (σ : Sig) : Category where
  Ob := Ctx σ
  Hom Γ Δ := Syn Γ Δ
  id A := Quotient.mk' (Subst.ide A)
  comp := Quotient.lift₂ (λ f g => Quotient.mk' (f.comp g)) (by
    intro a₁ b₁ a₂ b₂ r₁ r₂
    apply Quotient.sound
    exact SubEquiv.comp_congr r₁ r₂
    )
  id_comp := Quotient.ind (λ s => Quotient.sound (SubEquiv.ofEq (Subst.ide_comp s)))
  comp_id := Quotient.ind (λ s => Quotient.sound (SubEquiv.ofEq (Subst.comp_ide s)))
  comp_assoc :=
    Quotient.ind λ f =>
    Quotient.ind λ g => 
    Quotient.ind λ h => 
    Quotient.sound (SubEquiv.ofEq (Subst.comp_assoc f g h))

theorem Subst.proj₁_pair {f : Subst X Γ} {g : Subst X Δ} : Subst.proj₁.comp (Subst.pair f g) = f := by
  induction Δ with
  | nil => cases g; simp [(·++·), Append.append, concat, proj₁, pair]; rw [ide_comp]
  | cons Δ τ ih =>
    cases g; simp [(·++·), Append.append, concat, proj₁, pair]
    simp [drop_comp, head, ih]

theorem Subst.proj₂_pair {f : Subst X Γ} {g : Subst X Δ} : Subst.proj₂.comp (Subst.pair f g) = g := by
  induction Δ with
  | nil => cases g; rfl
  | cons Δ τ ih =>
    cases g; simp [(·++·), Append.append, concat, proj₂, pair]
    simp [keep, comp, Tm.subst, Var.subst, head, drop_comp, ih]

theorem Subst.pair_unique {f : Subst X Γ} {g : Subst X Δ} {fg : Subst X (Γ ++ Δ)} :
  proj₁.comp fg = f → proj₂.comp fg = g → Subst.pair f g = fg := by
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
        
instance : Cartesian (SynCat σ) where
  hasTerminal := {
    apex := ε
    universal := Quotient.mk' .nil
    unique := Quotient.ind λ .nil => Quotient.sound (SubEquiv.ofEq rfl)  
  }
  hasProducts (Γ Δ : Ctx σ) := {
    apex := Γ ++ Δ
    is_product := {
      π₁ := Quotient.mk' Subst.proj₁
      π₂ := Quotient.mk' Subst.proj₂
      universal := λ {X} fq gq =>
        Quotient.liftOn₂ fq gq (λ f g => Quotient.mk' $ Subst.pair f g) $ by
              intro s₁ s₂ s₁' s₂' e₁ e₂
              apply Quotient.sound
              apply SubEquiv.pair_congr e₁ e₂
      universal_prop := λ {X} fq gq =>
        by
          simp [Category.compose, SynCat]
          have ⟨f, h_f⟩ := Quotient.exists_rep fq
          have ⟨g, h_g⟩ := Quotient.exists_rep gq
          rw [←h_f, ←h_g]
          constructor <;> apply Quotient.sound
          · apply SubEquiv.ofEq Subst.proj₁_pair
          · apply SubEquiv.ofEq Subst.proj₂_pair
      unique := by
        intro X fq gq fgq h₁ h₂
        have ⟨f, h_f⟩ := Quotient.exists_rep fq
        have ⟨g, h_g⟩ := Quotient.exists_rep gq
        have ⟨fg, h_fg⟩ := Quotient.exists_rep fgq
        rw [←h_f, ←h_g, ←h_fg]
        apply Quotient.sound
        rw [←h_f, ←h_fg] at h₁
        rw [←h_g, ←h_fg] at h₂
        simp [Category.compose, SynCat] at h₁ h₂
        let h₁' := Quotient.exact h₁
        let h₂' := Quotient.exact h₂
        let p := SubEquiv.pair_congr h₁' h₂'
        apply Setoid.trans p
        apply SubEquiv.ofEq
        apply Subst.pair_unique <;> rfl
    }
  }

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

instance : CartesianClosed (SynCat σ) where
  closed Γ Δ := {
    exp := Subst.exp Γ Δ
    is_exponential := {
      lam := Quotient.lift (λ f => Quotient.mk' (Subst.lam f)) λ a b e =>
        Quotient.sound (SubEquiv.lam_congr e)
      eval := Quotient.mk' Subst.eval
      eval_lam := by
        intro X
        apply Quotient.ind
        intro f
        apply Quotient.sound
        apply SubEquiv.eval_lam
      unique := by
        intro X
        apply Quotient.ind₂
        intro f f'
        intro h
        have h := Quotient.exact h
        apply Quotient.sound
        apply SubEquiv.lam_unique
        simp [Subst.eval, Subst.apps_comp, Subst.proj₁_pair, Subst.proj₂_pair, Subst.ide_comp] at h
        assumption
    }
  }

def interpSubst_append.pair :
  ∀ {Γ Δ}, X ⟶ ⟦Γ⟧Ctx[Str] → X ⟶ ⟦Δ⟧Ctx[Str] → X ⟶ ⟦Γ ++ Δ⟧Ctx[Str]
| _, ε,    f, _ => f
| _, _,,_, f, g => Cartesian.pair (pair f (proj₁ ⊚ g)) (proj₂ ⊚ g)

def interpSubst_append : is_product 𝒞 ⟦Γ⟧Ctx[Str] ⟦Δ⟧Ctx[Str] ⟦Γ ++ Δ⟧Ctx[Str] where
  π₁ := ⟦Subst.proj₁⟧Sub[Str]
  π₂ := ⟦Subst.proj₂⟧Sub[Str]
  universal f g := interpSubst_append.pair _ f g
  universal_prop f g := by
    induction Δ with
    | nil => simp [interpSubst_append.pair]
             apply Eq.trans
             apply bang_unique
             apply Eq.symm
             apply bang_unique
    | cons Δ τ ih => simp [interpSubst_append.pair, Subst.keep, interpSubst_drop,
                           interpSubst]
                     let ⟨ih₁, ih₂⟩ := ih (proj₁ ⊚ g)
                     constructor
                     · assumption
                     · simp [interpTm, interpVar]
                       rw [←pair_comp, Category.assoc, proj₁_pair, proj₂_pair]
                       apply pair_unique
                       · assumption
                       · rfl
  unique {X} := by
    revert Γ
    induction Δ with
    | nil =>
      intro Γ f g fg h₁ _
      simp [interpSubst_append.pair]
      simp [interpSubst] at h₁
      apply h₁
    | cons Δ τ ih =>
      intro Γ f g fg h₁ h₂
      simp [interpSubst_append.pair]
      simp [interpSubst_drop, interpSubst, interpTm, interpVar, ←pair_comp] at h₁ h₂
      apply pair_unique
      · let h₂₁ := congrArg (proj₁ ⊚ ·) h₂
        simp at h₂₁
        let p := ih f (proj₁ ⊚ g) (proj₁ ⊚ fg) h₁ h₂₁
        simp at p
        rw [p]
      · let h₂₂ := congrArg (proj₂ ⊚ ·) h₂
        simp at h₂₂
        assumption

def prod.assoc [CartesianClosed 𝒞] (A B C : 𝒞) : Iso 𝒞 (A ×' B ×' C) (A ×' (B ×' C)) where
  to := pair (proj₁ ⊚ proj₁) (pair (proj₂ ⊚ proj₁) proj₂)
  to_isIso := {
    inv := pair (pair proj₁ (proj₁ ⊚ proj₂)) (proj₂ ⊚ proj₂)
    leftInv := by
      simp [←pair_comp]
      rw [Category.id_compose (B := A ×' B) proj₁]
      simp
    rightInv := by
      simp [←pair_comp]
      rw [Category.id_compose (B := B ×' C) proj₂]
      simp
  }
def interpSubst_exp.lam' :
  ∀ {Γ τ}, X ×' ⟦Γ⟧Ctx[Str] ⟶ ⟦τ⟧Ty[Str] → X ⟶ ⟦Subst.arr Γ τ⟧Ty[Str]
| ε,    _, f => f ⊚ pair (𝟙 _) bang 
| Γ,,_, _, f => interpSubst_exp.lam' (Γ := Γ)
  (lam (f ⊚ (prod.assoc _ _ _).to))

def interpSubst_exp.lam :
  ∀ {Γ Δ}, X ×' ⟦Γ⟧Ctx[Str] ⟶ ⟦Δ⟧Ctx[Str] → X ⟶ ⟦Subst.exp Γ Δ⟧Ctx[Str]
| _, ε,    _ => bang
| _, _,,_, f => pair (interpSubst_exp.lam (proj₁ ⊚ f))
                     (interpSubst_exp.lam' Str (proj₂ ⊚ f))

def interpSubst_exp.eval' :
  ∀ {Γ τ}, ⟦Subst.arr Γ τ⟧Ty[Str] ×' ⟦Γ⟧Ctx[Str] ⟶ ⟦τ⟧Ty[Str]
| ε,    _ => proj₁
| Γ,,υ, τ => let p := eval' (Γ := Γ) (τ := υ.arr τ)
             eval ⊚ pair (p ⊚ prod.map (𝟙 _) proj₁) (proj₂ ⊚ proj₂)


theorem interpSubst_exp.eval'_lam' :
  ∀ {X Γ τ} (f : X ×' ⟦Γ⟧Ctx[Str] ⟶ ⟦τ⟧Ty[Str]),
    eval' Str ⊚ prod.map (lam' Str f) (𝟙 _) = f := by
    intro X Γ
    induction Γ with
    | nil => intro τ f
             simp [eval', lam', prod.map]
             rw [←Category.compose_id f, Category.assoc]
             apply congrArg (f ⊚ ·)
             simp [←pair_comp]
             apply pair_unique <;> simp
             apply (bang_unique _).trans (bang_unique _).symm
    | cons Γ τ ih => intro υ f
                     simp [eval', lam', prod.map]
                     simp [←pair_comp, Category.assoc]
                     have p := ih (τ := τ.arr υ)
                                 (CartesianClosed.lam (f ⊚ (prod.assoc _ _ _).to))
                     rw [←prod.map, ←Category.id_compose proj₁,
                         ←Category.compose_id (lam' _ _),
                         prod.map_comp, ←Category.assoc, p]
                     simp [prod.map, prod.assoc]
                     rw [←prod.lam_of_comp, Category.assoc, ←pair_comp]
                     simp [prod.map, ←Category.assoc]
                     rw [←pair_comp, Category.assoc, proj₁_pair, proj₂_pair,
                         ←Category.assoc, proj₂_pair]
                     rw [eval_pair_lam]
                     simp [Category.assoc, ←pair_comp]
                     rw [Category.id_compose (B := (⟦Γ⟧Ctx[Str] ×' interpTy Str.types τ))
                         proj₂, pair_proj₁_proj₂,
                         Category.compose_id (A := (X ×' (⟦Γ⟧Ctx[Str] ×' interpTy Str.types τ))) f]

theorem lam_of_eval [CartesianClosed 𝒞] {A B : 𝒞}:
  lam (eval) = 𝟙 (exp A B) := by
  apply Eq.symm
  apply lam_unique
  simp [prod.map_id]


theorem interpSubst_exp.unique' :
  ∀ {X Γ τ} (f : X ×' ⟦Γ⟧Ctx[Str] ⟶ ⟦τ⟧Ty[Str]) (f' : X ⟶ ⟦Subst.arr Γ τ⟧Ty[Str]),
    eval' Str ⊚ (prod.map f' (𝟙 ⟦Γ⟧Ctx[Str])) = f → f' = lam' Str f := by
    intro X Γ
    induction Γ with
    | nil => intro τ f f' h
             simp [eval', prod.map] at h
             simp [lam', ←h]
    | cons Γ τ ih =>
      intro τ f f' h
      simp [eval', prod.map, ←pair_comp] at h
      simp [lam']
      apply ih
      simp [←h, prod.assoc]
      simp [←pair_comp]
      rw [←Category.assoc, pair_comp, ←Category.assoc,
          ←Category.id_compose proj₂, ←prod.map,
          ←Category.id_compose proj₂, ←prod.map,
          prod.lam_of_comp, lam_of_eval]
      simp

def interpSubst_exp.eval :
  ∀ {Γ Δ}, ⟦Subst.exp Γ Δ⟧Ctx[Str] ×' ⟦Γ⟧Ctx[Str] ⟶ ⟦Δ⟧Ctx[Str]
| _, ε    => bang
| Γ, _,,_ => pair (interpSubst_exp.eval (Γ := Γ) ⊚ (prod.map proj₁ (𝟙 _)))
                  (interpSubst_exp.eval' (Γ := Γ) Str ⊚ prod.map proj₂ (𝟙 _))

def interpSubst_exp : is_exponential 𝒞 ⟦Γ⟧Ctx[Str] ⟦Δ⟧Ctx[Str] ⟦Subst.exp Γ Δ⟧Ctx[Str] where
  lam := interpSubst_exp.lam Str
  eval := interpSubst_exp.eval Str
  eval_lam := by
    revert Γ
    induction Δ with
    | nil => intro Γ X f
             apply Eq.trans
             apply bang_unique
             apply Eq.symm
             apply bang_unique
    | cons Δ τ ih => intro Γ X f
                     simp [interpSubst_exp.eval, interpSubst_exp.eval,
                           interpSubst_exp.lam]
                     rw [←pair_comp]
                     apply pair_unique
                     · simp
                       rw [←prod.map_comp_fst, proj₁_pair]
                       apply ih
                     · simp
                       rw [←prod.map_comp_fst, proj₂_pair]
                       rw [interpSubst_exp.eval'_lam']
  unique := by
    intro X
    induction Δ with
    | nil => intro f f' _
             apply (bang_unique _)
    | cons Δ τ ih =>
      simp [interpSubst_exp.eval, interpSubst_exp.lam]
      intro f f' h
      apply Eq.symm
      apply pair_unique
      · apply Eq.symm
        apply ih
        apply Eq.trans
        apply congrArg (proj₁ ⊚ ·) h
        rw [←Category.assoc, proj₁_pair, Category.assoc, ←prod.map_comp_fst]
      · rw [←pair_comp, Category.assoc, Category.assoc,
            ←prod.map_comp_fst, ←prod.map_comp_fst] at h
        have h' := congrArg (proj₂ ⊚ ·) h
        simp at h'
        have p := interpSubst_exp.unique' Str (proj₂ ⊚ f) (proj₂ ⊚ f') h'.symm
        exact p.symm

@[simp]
theorem SynCat.proj₁_def : proj₁ (𝒞 := SynCat σ) (A := Γ) (B := Δ) =
  Quotient.mk' Subst.proj₁ := rfl

@[simp]
theorem SynCat.proj₂_def : proj₂ (𝒞 := SynCat σ) (A := Γ) (B := Δ) =
  Quotient.mk' Subst.proj₂ := rfl

theorem interpSubst_app :
  ⟦Subst.app (Γ := Γ) (Δ := Δ) (τ := τ) f x⟧Tm[Str] =
    interpSubst_exp.eval' Str ⊚ pair (⟦f⟧Tm[Str]) (⟦x⟧Sub[Str]) := by
  revert τ
  induction x with
  | nil => simp [Subst.app, interpSubst_exp.eval']
  | cons xs x ih =>
    simp [Subst.app, interpTm, Subst.arr, interpSubst_exp.eval']
    intro τ f
    apply congrArg
    rw [←pair_comp, pair_ext]
    constructor
    · rw [ih, Category.assoc, prod.map_comp_pair]
      simp [interpSubst]
    · simp [interpSubst]

theorem interpSubst_apps :
  ⟦Subst.apps (Γ := Γ) (Δ := Δ) (Ε := Ε) f x⟧Sub[Str] =
    interpSubst_exp.eval Str ⊚ pair (⟦f⟧Sub[Str]) (⟦x⟧Sub[Str]) := by
  induction Ε with
  | nil => apply (bang_unique _).symm
  | cons Δ τ ih =>
    cases f with | cons fs f =>
    simp [Subst.apps, interpSubst]
    simp [interpSubst_exp.eval]
    apply pair_unique
    · rw [←pair_comp, Category.assoc, prod.map_comp_pair,
          Category.assoc, prod.map_comp_pair, proj₁_pair, proj₁_pair,
          ih, Category.id_compose]
    · rw [interpSubst_app, ←pair_comp, proj₂_pair,
          Category.assoc, prod.map_comp_pair, proj₂_pair,
          Category.id_compose]

theorem interpSubst_proj₁ :
  ⟦Subst.proj₁ (Γ := Γ) (Δ := Δ)⟧Sub[Str] = (interpSubst_append Str).π₁ := by
  simp [interpSubst_append]

theorem interpSubst_proj₂ :
  ⟦Subst.proj₂ (Γ := Γ) (Δ := Δ)⟧Sub[Str] = (interpSubst_append Str).π₂ := by
  simp [interpSubst_append]

theorem interpSubst_eval :
  ⟦Subst.eval (Γ := Γ) (Δ := Δ)⟧Sub[Str] ⊚ interpSubst_append.pair Str proj₁ proj₂ =
    interpSubst_exp.eval Str := by
  rw [Subst.eval, interpSubst_apps, interpSubst_proj₁, interpSubst_proj₂]
  simp [interpSubst]
  rw [←Category.compose_id (interpSubst_exp.eval Str), Category.assoc]
  apply congrArg
  simp
  let h := ((interpSubst_append Str (Γ := Subst.exp Γ Δ) (Δ := Γ)).universal_prop proj₁ proj₂)
  simp [interpSubst_append] at h
  simp [interpSubst_append]
  rw [←pair_comp]
  apply pair_unique
  · rw [Category.compose_id proj₁ (A := (⟦Subst.exp Γ Δ⟧Ctx[Str] ×' ⟦Γ⟧Ctx[Str])), h.1]
  · rw [Category.compose_id proj₂ (A := (⟦Subst.exp Γ Δ⟧Ctx[Str] ×' ⟦Γ⟧Ctx[Str])), h.2]

def SynCat.prod_ty Γ τ υ : Iso (SynCat σ) (Γ ,, Ty.prod τ υ) (Γ ,, τ ,, υ) where
  to := Quotient.mk' (.cons (.cons (Subst.proj₁ (Δ := ε ,, τ.prod υ))
                                   (.fst (.var .zero)))
                                   (.snd (.var .zero)))
  to_isIso := {
    inv := Quotient.mk' (.cons (Subst.proj₁ (Δ := ε ,, τ ,, υ))
                               (.pair (.var (.succ .zero))
                                      (.var .zero)))
    leftInv := by
      apply Quotient.sound
      apply SubEquiv.cons
      · simp [Subst.drop_comp, Subst.head, Subst.ide_comp, Subst.ofRenaming_drop]
        apply SubEquiv.refl
      · apply TmEquiv.prod_η.symm
    rightInv := by
      apply Quotient.sound
      apply SubEquiv.cons
      · apply SubEquiv.cons
        · simp [Subst.drop_comp, Subst.ide_comp, Subst.head, Subst.ofRenaming_drop]
          apply SubEquiv.refl
        · apply TmEquiv.prod_β₁
      · apply TmEquiv.prod_β₂
  }

def SynCat.unit_ty Γ : Iso (SynCat σ) (Γ ,, Ty.unit) Γ where
  to := Quotient.mk' ((Subst.ide Γ).drop .unit)
  to_isIso := {
    inv := Quotient.mk' (.cons (Subst.ide Γ) .unit)
    leftInv := by
      apply Quotient.sound
      simp [Subst.comp, Subst.ide_comp, Tm.rename]
      apply SubEquiv.cons
      · rw [Subst.ofRenaming_drop]; apply SubEquiv.refl
      · apply TmEquiv.unit_η.symm
    rightInv := by
      apply Quotient.sound
      simp [Subst.drop_comp, Subst.ide_comp, Subst.head]
      apply SubEquiv.refl
  }

def SynCat_equiv_Struct.to (Str : Struct σ 𝒞) : CCFunctor (SynCat σ) 𝒞 where
  obj Γ := ⟦Γ⟧Ctx[Str]
  map := Quotient.lift (⟦·⟧Sub[Str]) λ _ _ => interpSubst_preserves_equiv Str
  map_id {Γ} := by simp [Category.identity, SynCat,
                         Quotient.lift, Quotient.mk', Quotient.mk] 
  map_comp {B} {C} {A} := Quotient.ind₂ λ f g => interpSubst_comp Str
  preserve_terminal := {
    inv := bang 
    leftInv := by
      apply Eq.trans
      apply bang_unique
      apply Eq.symm
      apply bang_unique
    rightInv := by
      apply Eq.trans
      apply bang_unique
      apply Eq.symm
      apply bang_unique
  }
  preserve_products Γ Δ := {
    inv := interpSubst_append.pair _ proj₁ proj₂
    leftInv := is_product_unique.inv (interpSubst_append Str) _
    rightInv := is_product_unique.inv _  (interpSubst_append Str)
  }
  preserve_exponential (Γ : Ctx σ) Δ := {
    inv := is_exponential_unique.to (closed ⟦Γ⟧Ctx[Str] ⟦Δ⟧Ctx[Str]).is_exponential
                                    (interpSubst_exp Str)
    leftInv := by
      let h := is_exponential_unique.inv (interpSubst_exp Str)
                                         (closed ⟦Γ⟧Ctx[Str] ⟦Δ⟧Ctx[Str]).is_exponential
      have p : Quotient.lift (fun x => ⟦x⟧Sub[Str])
          (λ _ _ => interpSubst_preserves_equiv Str)
            (eval : (SynCat σ)[Subst.exp Γ Δ ++ Γ, Δ])
          = ⟦Subst.eval⟧Sub[Str] := by
            simp [Quotient.lift, eval, Quotient.mk, closed, Quotient.mk']
      simp [p]
      apply Eq.trans _ h
      simp [is_exponential_unique.to, interpSubst_exp]
      apply congrArg
      apply Eq.symm
      apply lam_unique
      rw [←lam, eval_lam, interpSubst_eval]
    rightInv := by
      have p : Quotient.lift (fun x => ⟦x⟧Sub[Str])
          (λ _ _ => interpSubst_preserves_equiv Str)
            (eval : (SynCat σ)[Subst.exp Γ Δ ++ Γ, Δ])
          = ⟦Subst.eval⟧Sub[Str] := by
            simp [Quotient.lift, eval, Quotient.mk, closed, Quotient.mk']
      simp [p]
      let h := is_exponential_unique.inv (closed ⟦Γ⟧Ctx[Str] ⟦Δ⟧Ctx[Str]).is_exponential
                                          (interpSubst_exp Str)
      apply Eq.trans _ h
      simp [is_exponential_unique.to, interpSubst_exp]
      rw [←eval, ←lam]
      apply congrArg (· ⊚ interpSubst_exp.lam Str eval)
      apply congrArg
      rw [interpSubst_eval]
  }

def go.lemma_arr [CartesianClosed 𝒞] (M : CCFunctor (SynCat σ) 𝒞)
  (t : Iso 𝒞 (Functor.obj M.toFunctor (ε,,τ))
              (interpTy (fun τ => Functor.obj M.toFunctor (ε,,Ty.base τ)) τ))
  (u : Iso 𝒞 (Functor.obj M.toFunctor (ε,,υ))
              (interpTy (fun τ => Functor.obj M.toFunctor (ε,,Ty.base τ)) υ))
  : Iso 𝒞 (Functor.obj M.toFunctor (ε,,Ty.arr τ υ))
          (interpTy (fun τ => Functor.obj M.toFunctor (ε,,Ty.base τ)) (Ty.arr τ υ))
  :=
  let Me := lam (M.map eval ⊚ (M.preserve_products (exp (ε,,τ) (ε,,υ)) _).inv)
  {
    to := lam (u.to ⊚ eval ⊚ prod.map Me t.to_isIso.inv),
    to_isIso := {
      inv := (M.preserve_exponential (ε,,τ) (ε,,υ)).inv ⊚
              lam (u.to_isIso.inv ⊚ eval ⊚ prod.map (𝟙 _) t.to)
      leftInv := by
        simp
        have h := (M.preserve_exponential (ε,,τ) (ε,,υ)).leftInv
        simp [exp, SynCat, closed, Subst.exp, Subst.arr] at h
        rw [←h]
        apply congrArg
        rw [←prod.lam_of_comp]
        rw [Category.assoc, Category.assoc,
            ←prod.map_comp, Category.id_compose,
            Category.compose_id,
            prod.map, ←prod.lam_of_comp,
            eval_pair_lam, ←Category.assoc,
            ←Category.assoc, ←Category.assoc,
            u.to_isIso.leftInv, Category.id_compose,
            prod.map, ←prod.lam_of_comp,
            eval_pair_lam, Category.assoc,
            Category.assoc, Category.assoc,
            ←Category.assoc (prod.map _ _),
            prod.map_comp_pair]
        simp
        rw [prod.map_comp_pair, ←pair_comp ]
        simp
        rw [←Category.assoc t.to_isIso.inv, t.to_isIso.leftInv,
            Category.id_compose, pair_proj₁_proj₂, Category.compose_id]
        rfl
      rightInv := by
        simp [interpTy, ←prod.lam_of_comp]
        apply Eq.symm
        apply lam_unique
        rw [prod.map, ←prod.lam_of_comp, ←Category.assoc eval, eval_pair_lam,
            prod.map_id, Category.compose_id, Category.assoc, Category.assoc,
            ←Category.assoc (prod.map proj₁ _), prod.map_comp_pair,
            prod.map, ←pair_comp]
        simp
        have h := u.to_isIso.rightInv
        rw [←Category.id_compose (eval (𝒞 := 𝒞)),
            ←h, Category.assoc u.to]
        apply congrArg
        rw [←Category.assoc u.to, u.to_isIso.rightInv]
        simp
        rw [←Category.assoc, ←Category.assoc, ←prod.map]
        have h := (M.preserve_exponential (ε,,τ) (ε,,υ)).rightInv
        rw [←prod.lam_of_comp, ←lam_of_eval] at h
        have h' := lam_injective _ _ h
        rw [←Category.id_compose t.to_isIso.inv,
            prod.map_comp, ←Category.assoc, h',
            ←Category.id_compose t.to_isIso.inv,
            ←Category.compose_id (lam _), prod.map_comp,
            ←Category.assoc, eval_lam, Category.assoc]
        apply congrArg
        rw [Category.assoc, ←prod.map_comp_snd,
            t.to_isIso.rightInv, prod.map_id,
            Category.compose_id]
    }
  }

def go.lemma_prod [CartesianClosed 𝒞] (M : CCFunctor (SynCat σ) 𝒞)
  (t : Iso 𝒞 (Functor.obj M.toFunctor (ε,,τ))
              (interpTy (fun τ => Functor.obj M.toFunctor (ε,,Ty.base τ)) τ))
  (u : Iso 𝒞 (Functor.obj M.toFunctor (ε,,υ))
              (interpTy (fun τ => Functor.obj M.toFunctor (ε,,Ty.base τ)) υ))
  : Iso 𝒞 (Functor.obj M.toFunctor (ε,,Ty.prod τ υ))
          (interpTy (fun τ => Functor.obj M.toFunctor (ε,,Ty.base τ)) (Ty.prod τ υ))
  :=
  {
    to := pair (t.to ⊚ M.map (proj₁ (𝒞 := SynCat σ) (B := ε ,, υ) ⊚
                             (SynCat.prod_ty ε τ υ).to))
               (u.to ⊚ M.map (proj₂ (𝒞 := SynCat σ) (B := ε ,, υ) ⊚
                             (SynCat.prod_ty ε τ υ).to))
    to_isIso := {
      inv := M.map (SynCat.prod_ty ε τ υ).to_isIso.inv ⊚
              (M.preserve_products (ε,,τ) (ε,,υ)).inv ⊚
              prod.map t.to_isIso.inv
                      u.to_isIso.inv
      leftInv := by
        rw [Category.assoc, prod.map_comp_pair, M.map_comp, M.map_comp]
        rw [←Category.assoc t.to, ←Category.assoc,
            ←Category.assoc u.to, ←Category.assoc u.to_isIso.inv,
            pair_comp]
        rw [←M.map_id, ←(SynCat.prod_ty ε τ υ).to_isIso.leftInv,
            M.map_comp, ←Category.assoc ]
        apply congrArg (· ⊚ M.map (SynCat.prod_ty ε τ υ).to)
        rw [←Category.compose_id (M.map (SynCat.prod_ty ε τ υ).to_isIso.inv),
            Category.assoc, Category.assoc]
        apply congrArg
        simp
        have h: (M.preserve_products (ε,,τ) (ε,,υ)).inv ⊚
                  pair (M.map proj₁) (M.map proj₂) = 𝟙 (M.obj (ε,,τ,,υ)) :=
                  (M.preserve_products (ε,,τ) (ε,,υ)).leftInv
        rw [←h]
        apply congrArg
        rw [←Category.assoc, t.to_isIso.leftInv, Category.id_compose,
            ←Category.assoc, u.to_isIso.leftInv, Category.id_compose,
            pair_ext]
        constructor
        · apply congrArg
          apply Quotient.sound
          apply SubEquiv.refl
        · apply congrArg
          apply Quotient.sound
          apply SubEquiv.refl
      rightInv := by
        simp [Syn.cons, Syn.nil, Quotient.mk', Quotient.lift, Quotient.lift₂,
              Quotient.mk, Category.compose, SynCat, SynCat.prod_ty]
        repeat rw [←Category.compose]
        simp [Subst.drop_comp, Subst.ide_comp, Subst.head]
        rw [←pair_comp, Category.assoc t.to,
            ←Category.assoc (M.map _),
            ←M.map_comp ]
        simp [Syn.cons, Syn.nil, Quotient.mk', Quotient.lift, Quotient.lift₂,
              Quotient.mk, Category.compose, SynCat, SynCat.prod_ty,
              Subst.comp, Tm.subst, Var.subst]
        repeat rw [←Category.compose]
        rw [←Category.assoc (M.map _) (M.map _),
            ←M.map_comp ]
        simp [Syn.cons, Syn.nil, Quotient.mk', Quotient.lift, Quotient.lift₂,
              Quotient.mk, Category.compose, SynCat, SynCat.prod_ty,
              Subst.comp, Tm.subst, Var.subst]
        repeat rw [←Category.compose]
        repeat rw [←Category.assoc]
        rw [pair_comp, pair_comp, Category.assoc (pair _ _)]
        simp [interpTy]
        rw [←prod.map_id, ←t.to_isIso.rightInv, ←u.to_isIso.rightInv,
            ←Category.assoc, prod.map_comp]
        apply congrArg (· ⊚ prod.map t.to_isIso.inv u.to_isIso.inv)
        rw [←Category.compose_id (prod.map t.to u.to)]
        simp only [prod]
        rw [←(M.preserve_products (ε,,τ) (ε,,υ)).rightInv, ←Category.assoc]
        apply congrArg (· ⊚ (M.preserve_products (ε,,τ) (ε,,υ)).inv)
        rw [prod.map_comp_pair, pair_ext]
        constructor
        · apply congrArg
          apply congrArg
          apply Quotient.sound
          apply SubEquiv.cons
          · apply SubEquiv.nil
          · apply TmEquiv.prod_β₁
        · apply congrArg
          apply congrArg
          apply Quotient.sound
          apply SubEquiv.cons
          · apply SubEquiv.nil
          · apply TmEquiv.prod_β₂
    }
  }

def go [CartesianClosed 𝒞] (M : CCFunctor (SynCat σ) 𝒞) : ∀ (τ : Ty σ.types),
                    Iso 𝒞 (Functor.obj M.toFunctor (ε,,τ))
                          (interpTy (fun τ => Functor.obj M.toFunctor (ε,,Ty.base τ)) τ)
| .base τ => {
  to := 𝟙 _
  to_isIso := {
    inv := 𝟙 _
    leftInv := Category.compose_id _
    rightInv := Category.compose_id _
  }
}
| .arr τ υ => go.lemma_arr M (go M τ) (go M υ)
| .prod τ υ => go.lemma_prod M (go M τ) (go M υ)
| .unit => {
  to := bang
  to_isIso := {
    inv := M.map (SynCat.unit_ty ε).to_isIso.inv ⊚ M.preserve_terminal.inv
    leftInv := by
      rw [←M.map_id, ←(SynCat.unit_ty ε).to_isIso.leftInv,
          M.map_comp, Category.assoc]
      apply congrArg
      have p := bang_unique (bang ⊚ M.map (SynCat.unit_ty ε).to)
      rw [←p, ←Category.assoc, M.preserve_terminal.leftInv]
      exact Category.id_compose (M.map (SynCat.unit_ty ε).to)
    rightInv := by
      apply Eq.trans
      apply bang_unique
      apply Eq.symm
      apply bang_unique
  }
}

def SynCat_equiv_Struct.inv (M : CCFunctor (SynCat σ) 𝒞) : Struct σ 𝒞 where
  types τ := M.obj (ε ,, .base τ)
  terms t :=
    let t' : Syn ε (ε ,, _) := Syn.cons Syn.nil (Quotient.mk' (.base t))
    let h := M.map t'
    (go M _).to ⊚ h ⊚ M.preserve_terminal.inv
