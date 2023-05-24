import CCCSemantics.Categories.CartesianClosed
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

section
variable [CartesianClosed 𝒞] (struct : Struct σ 𝒞)

def interpCtx : Ctx σ → 𝒞
| ε      => final
| Γ ,, τ => interpCtx Γ ×' (interpTy struct.types τ)

def interpVar : ∀ {Γ : Ctx σ}, Var τ Γ → interpCtx struct Γ ⟶ interpTy struct.types τ
| _ ,, _, .zero => proj₂
| _ ,, _, .succ v => interpVar v ⊚ proj₁

def interpTm :
  Γ ⊢ τ → (interpCtx struct Γ ⟶ interpTy struct.types τ)
| .var v    => interpVar struct v
| .base b   => struct.terms b ⊚ bang
| .lam t    => lam (interpTm t)
| .app t u  => eval ⊚ pair (interpTm t) (interpTm u)
| .pair t u => pair (interpTm t) (interpTm u)
| .fst t    => proj₁ ⊚ interpTm t
| .snd t    => proj₂ ⊚ interpTm t
| .unit     => bang

def interpSubst :
  Subst Γ Δ → (interpCtx struct Γ ⟶ interpCtx struct Δ)
| .nil      => bang
| .cons t s => pair (interpSubst s) (interpTm struct t)

theorem interpRenaming :
  Renaming Γ Δ → (interpCtx struct Γ ⟶ interpCtx struct Δ)
| .done => 𝟙 _
| .skip r => interpRenaming r ⊚ proj₁
| .keep r => prod.map (interpRenaming r) (𝟙 _)

theorem interpSubst_var : ∀ (s : Subst Γ Δ) (t : Var τ Δ),
  interpTm struct (s.var t) = interpVar struct t ⊚ interpSubst struct s
| .cons t _, .zero   => by simp [Subst.var, interpSubst, interpVar]
| .cons _ s, .succ v => by simp [Subst.var, interpSubst, interpVar, interpSubst_var]

theorem interpSubst_apply : ∀ (s : Subst Γ Δ) (t : Δ ⊢ τ),
  interpTm struct (s.apply t) = interpTm struct t ⊚ interpSubst struct s
| s, .var v => interpSubst_var struct s v
| s, .base b => by
  simp [interpTm]
  congr
  exact (bang_unique _).symm
| s, .lam t => by
  simp [interpTm]
  apply Eq.symm
  apply lam_unique
  simp [interpSubst_apply, interpSubst, interpTm, interpVar]
  rw [prod.map_comp_fst, ←Category.assoc, eval_lam]
  
| s, .app t u => by simp [interpTm, Subst.apply, interpSubst_apply]
| s, .pair t u => by simp [interpTm, Subst.apply, interpSubst_apply]
| s, .fst t => by simp [interpTm, Subst.apply, interpSubst_apply]
| s, .snd t => by simp [interpTm, Subst.apply, interpSubst_apply]
| s, .unit => (bang_unique _).symm

theorem preserves_reduction : Reduction t t' →
  interpTm struct t = interpTm struct t' := by
    intro r
    induction r with
    | app_left r ih => simp [interpTm, ih]
    | app_right r ih => simp [interpTm, ih]
    | lam r ih => simp [interpTm, ih]
    | pair_left r ih => simp [interpTm, ih]
    | pair_right r ih => simp [interpTm, ih]
    | fst r ih => simp [interpTm, ih]
    | snd r ih => simp [interpTm, ih]
    | fst_pair => simp [interpTm]
    | snd_pair => simp [interpTm]
    | app_lam =>
      simp [interpTm]
