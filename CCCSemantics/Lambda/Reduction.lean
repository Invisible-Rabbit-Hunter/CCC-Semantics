import CCCSemantics.Lambda.Substitution

inductive Reduction : Tm σ Γ τ → Tm σ Γ τ → Type
| app_lam : Reduction (.app (.lam t) u)
                      (Subst.apply (.cons u (Subst.ide _)) t)
| app_left : Reduction t t' → Reduction (.app t u) (.app t' u) 
| app_right : Reduction u u' → Reduction (.app t u) (.app t u')
| lam : Reduction t t' → Reduction (.lam t) (.lam t') 
| fst_pair : Reduction (.fst (.pair t u)) t 
| snd_pair : Reduction (.snd (.pair t u)) u 
| pair_left : Reduction t t' → Reduction (.pair t u) (.pair t' u)
| pair_right : Reduction u u' → Reduction (.pair t u) (.pair t u')
| fst : Reduction t t' → Reduction (.fst t) (.fst t')
| snd : Reduction t t' → Reduction (.snd t) (.snd t')

infix:90 " ⟶β " => Reduction

inductive Reductions : Γ ⊢ τ → Γ ⊢ τ → Type
| rfl : Reductions t t
| step : t ⟶β t' → Reductions t' t'' → Reductions t t''  
infix:90 " ⟶β* " => Reductions

def Normal (t : Γ ⊢ τ) : Prop :=
  ∀ t', (t ⟶β* t') → t = t'

example : Normal (.lam (.var .zero) : Γ ⊢ (Ty.arr τ τ))
| _, .rfl => rfl
| _, .step r _ =>
  match r with
  | .lam x => nomatch x

inductive βηEquiv : Γ ⊢ τ → Γ ⊢ τ → Prop
| refl : βηEquiv t t
| symm : βηEquiv t u → βηEquiv u t
| trans : βηEquiv s t → βηEquiv t u → βηEquiv s u
| reductions : Reductions t t' → βηEquiv t t'

