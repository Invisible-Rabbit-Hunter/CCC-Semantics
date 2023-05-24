import CCCSemantics.Categories.Instances.Func
import CCCSemantics.Categories.Yoneda

namespace Categories

structure Adjunction (F : 𝒞 ⥤ 𝒟) (G : 𝒟 ⥤ 𝒞) where
  unit : Functor.id 𝒞 ⟹ G.comp F
  counit : F.comp G ⟹ Functor.id 𝒟
  triangle_left : (counit.whisker_right F) ⊚ (unit.whisker_left F) = 𝟙 F
  triangle_right : (counit.whisker_left G) ⊚ (unit.whisker_right G) = 𝟙 G

def Adjunction.ofHomEquiv
  {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞}
  (equiv : ∀ A B, (F A ⟶ B) ≃ (A ⟶ G B))
  (naturality_left : ∀ {A A' B} (f : F A' ⟶ B)  (g : A ⟶ A'),
    equiv _ _ f ⊚ g = equiv _ _ (f ⊚ F.map g))
  (naturality_right_symm : ∀ {A B B'} (f : B ⟶ B') (g : F A ⟶ B),
    equiv _ _ (f ⊚ g) = G.map f ⊚ equiv _ _ g)
  : Adjunction F G :=
  have symm_naturality_left :∀ {A A' B} (f : A' ⟶ G B) (g : A ⟶ A') ,
      (equiv A' B).symm f ⊚ (F.map g) = (equiv A B).symm (f ⊚ g) := by
      intro A A' B f g
      apply Equiv.injective (equiv _ _)
      rw [←naturality_left]
      simp

  have symm_naturality_right_symm :∀ {A B B'} (f : B ⟶ B') (g : A ⟶ G B),
      (equiv A B').symm (G.map f ⊚ g) = f ⊚ (equiv A B).symm g := by
      intro A B B' f g
      apply Equiv.injective (equiv _ _)
      rw [naturality_right_symm]
      simp
  {
    unit := { app := λ A => (equiv A (F A)) (𝟙 (F A))
              naturality := by
                intro A B f
                simp [Functor.id, Functor.comp, naturality_left, naturality_right_symm, G.map_id]
                rw [←naturality_right_symm, Category.compose_id]
            }
    counit := { app := λ A => (equiv (G A) A).symm (𝟙 (G A))
                naturality := by
                  intro A B f
                  simp [Functor.id, Functor.comp, symm_naturality_left, symm_naturality_right_symm, G.map_id]
                  rw [←symm_naturality_right_symm, Category.compose_id]}
    triangle_left := by
      apply NatTrans.ext
      intro A
      simp [NatTrans.whisker_right, NatTrans.whisker_left, NatTrans.comp, Func, NatTrans.id]
      rw [symm_naturality_left (𝟙 (G (F A)))]
      simp [Functor.id]
    triangle_right := by
      apply NatTrans.ext
      intro A
      simp [NatTrans.whisker_right, NatTrans.whisker_left, NatTrans.comp, Func, NatTrans.id]
      rw [←naturality_right_symm _ (𝟙 (F (G A)))]
      simp [Functor.id]
  }

end Categories