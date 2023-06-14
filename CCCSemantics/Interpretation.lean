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
