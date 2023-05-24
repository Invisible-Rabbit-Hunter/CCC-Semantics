import CCCSemantics.Categories.Functor

namespace Categories

structure NatTrans (F G : Functor 𝒞 𝒟) where
  app (A : 𝒞) : F A ⟶ G A
  naturality (f : A ⟶ B) : app B ⊚ F.map f = G.map f ⊚ app A

infixr:69 " ⟹ " => NatTrans

namespace NatTrans

variable {𝒜 ℬ 𝒞 𝒟 ℰ : Category}
         {F : Functor 𝒞 𝒟}

def id (F : Functor 𝒞 𝒟) : F ⟹ F where
  app A := 𝟙 (F A)
  naturality f := (𝒟.id_comp (F.map f)).trans (𝒟.comp_id (F.map f)).symm

def comp (M : G ⟹ H) (N : F ⟹ G) : F ⟹ H where
  app A := M.app A ⊚ N.app A
  naturality f := by
    simp
    rw [N.naturality, ←Category.assoc, M.naturality, Category.assoc]

def ext {M N : F ⟹ G} (h : ∀ A, M.app A = N.app A) : M = N := by
  cases M with | mk appM natM =>
  cases N with | mk appN natN =>
  simp
  funext x; apply h

def comp_assoc (M : H ⟹ I) (N : G ⟹ H) (O : F ⟹ G) : comp (comp M N) (O) = comp M (comp N O) :=
  ext λ _ => Category.assoc _ _ _

def comp_id (M : F ⟹ G) : comp M (id F) = M :=
  ext λ _ => Category.compose_id _

def id_comp (M : F ⟹ G) : comp (id G) M = M :=
  ext λ _ => Category.id_compose _

def whisker_left (F : Functor 𝒞 𝓓) (N : G ⟹ H) : (F.comp G) ⟹ (F.comp H) where
  app A := F.map (N.app A)
  naturality := by
    intros A B f
    simp [Functor.comp]
    rw [←F.map_comp, ←F.map_comp, N.naturality]

def whisker_right {G H : Functor 𝒟 ℰ} (N : G ⟹ H) (F : Functor 𝒞 𝒟) : (G.comp F) ⟹ (H.comp F) where
  app A := N.app (F A)
  naturality := by
    intros A B f
    simp [Functor.comp]
    rw [N.naturality]

end NatTrans

structure NatIso (F G : Functor 𝒞 𝒟) extends NatTrans F G where
  inv : ∀ A, G A ⟶ F A
  leftInv : ∀ A, inv A ⊚ app A = 𝟙 (F A)
  rightInv : ∀ A, app A ⊚ inv A = 𝟙 (G A)   

namespace NatIso
    
theorem monic (e : NatIso F G) (p : e.app B ⊚ x = e.app B ⊚ y) : x = y := by
  rw [←Category.id_compose x, ←e.leftInv,
      Category.assoc, p, ←Category.assoc, e.leftInv,
      Category.id_compose]

theorem epic (e : NatIso F G) {x y : G A ⟶ X} (p : x ⊚ e.app A = y ⊚ e.app A) : x = y := by
  rw [←Category.compose_id x, ←e.rightInv,
      ←Category.assoc, p, Category.assoc, e.rightInv,
      Category.compose_id]
    
def symm (I : NatIso F G) : NatIso G F where
  app := I.inv
  inv := I.app
  leftInv A := I.rightInv A
  rightInv A := I.leftInv A
  naturality {A} {B} f := by
    apply I.monic
    rw [←Category.assoc, rightInv, Category.id_compose,
        ←Category.assoc, I.naturality, Category.assoc,
        rightInv, Category.compose_id]

def trans (I : NatIso F G) (J : NatIso G H) : NatIso F H where
  toNatTrans := J.comp I.toNatTrans
  inv A := I.inv A ⊚ J.inv A
  leftInv A := by
    simp [NatTrans.comp]
    rw [←Category.assoc (J.inv A), leftInv, Category.id_compose, leftInv]
  rightInv A := by
    simp [NatTrans.comp]
    rw [←Category.assoc (I.app A), rightInv, Category.id_compose, rightInv]

end NatIso

end Categories