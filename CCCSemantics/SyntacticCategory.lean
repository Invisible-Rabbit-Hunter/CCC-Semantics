import CCCSemantics.Interpretation

open Categories Cartesian CartesianClosed

variable [CartesianClosed 𝒞] (Str : Struct σ 𝒞)

def Syn (Γ Δ : Ctx σ) := Quotient (instSetoidSubst Γ Δ)

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

@[simp]
theorem SynCat.proj₁_def : proj₁ (𝒞 := SynCat σ) (A := Γ) (B := Δ) =
  Quotient.mk' Subst.proj₁ := rfl

@[simp]
theorem SynCat.proj₂_def : proj₂ (𝒞 := SynCat σ) (A := Γ) (B := Δ) =
  Quotient.mk' Subst.proj₂ := rfl

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
            simp [Quotient.lift, eval, Quotient.mk, closed, Quotient.mk', exponential.eval]
      simp [p]
      apply Eq.trans _ h
      simp [is_exponential_unique.to, interpSubst_exp]
      apply congrArg
      apply Eq.symm
      apply lam_unique
      rw [←exponential.lam, ←lam, eval_lam, interpSubst_eval]
    rightInv := by
      have p : Quotient.lift (fun x => ⟦x⟧Sub[Str])
          (λ _ _ => interpSubst_preserves_equiv Str)
            (eval : (SynCat σ)[Subst.exp Γ Δ ++ Γ, Δ])
          = ⟦Subst.eval⟧Sub[Str] := by
            simp [Quotient.lift, eval, Quotient.mk, closed, Quotient.mk', exponential.eval]
      simp [p]
      let h := is_exponential_unique.inv (closed ⟦Γ⟧Ctx[Str] ⟦Δ⟧Ctx[Str]).is_exponential
                                          (interpSubst_exp Str)
      apply Eq.trans _ h
      simp [is_exponential_unique.to, interpSubst_exp]
      rw [←exponential.eval, ←eval, ←exponential.lam, ←lam]
      apply congrArg (· ⊚ interpSubst_exp.lam Str eval)
      apply congrArg
      rw [interpSubst_eval]
  }

def CCFunctor_interpTy_iso.lemma_arr [CartesianClosed 𝒞] (M : CCFunctor (SynCat σ) 𝒞)
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

def CCFunctor_interpTy_iso.lemma_prod [CartesianClosed 𝒞] (M : CCFunctor (SynCat σ) 𝒞)
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
        have h : (M.preserve_products (ε,,τ) (ε,,υ)).inv ⊚
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
        simp [interpTy]
        rw [←Category.assoc, ←Category.assoc, ←(prod.map_iso t u).rightInv]
        apply congrArg (· ⊚ (prod.map_iso t u).inv)
        rw [←Category.compose_id (prod.map t.to u.to),←prod.map_comp_pair, Category.assoc,
            Category.assoc]
        apply congrArg
        simp [prod]
        rw [←(M.preserve_products (ε,,τ) (ε,,υ)).rightInv, ←Category.assoc]
        apply congrArg (· ⊚ (M.preserve_products (ε,,τ) (ε,,υ)).inv)
        simp [SynCat.prod_ty, Category.compose, SynCat, Quotient.lift₂, Quotient.mk, Quotient.mk',
              Quotient.lift, Subst.comp, Tm.subst, Var.subst, Subst.drop]
        rw [←Category.compose, ←pair_comp, ←M.map_comp, ←M.map_comp, pair_ext]
        constructor
        · apply congrArg
          apply Quotient.sound
          simp [Subst.comp]
          constructor
          · constructor
          · simp [Tm.subst, Tm.rename, Var.subst, Var.rename]
            apply TmEquiv.prod_β₁
        · apply congrArg
          apply Quotient.sound
          simp [Subst.comp]
          constructor
          · constructor
          · simp [Tm.subst, Tm.rename, Var.subst, Var.rename]
            apply TmEquiv.prod_β₂
    }
  }

def CCFunctor_interpTy_iso [CartesianClosed 𝒞] (M : CCFunctor (SynCat σ) 𝒞) : ∀ (τ : Ty σ.types),
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
| .arr τ υ => CCFunctor_interpTy_iso.lemma_arr M (CCFunctor_interpTy_iso M τ) (CCFunctor_interpTy_iso M υ)
| .prod τ υ => CCFunctor_interpTy_iso.lemma_prod M (CCFunctor_interpTy_iso M τ) (CCFunctor_interpTy_iso M υ)
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
    (CCFunctor_interpTy_iso M _).to ⊚ M.map (Quotient.mk' (Subst.nil.cons (.base t))) ⊚ M.preserve_terminal.inv
