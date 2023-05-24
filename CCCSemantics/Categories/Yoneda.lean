import CCCSemantics.Categories.Instances.Func
import CCCSemantics.Categories.Instances.Types
import CCCSemantics.Categories.Instances.Product

namespace Categories

def Prod.pair (F : 𝒞 ⥤ 𝒟) (G : 𝒞 ⥤ ℰ) : 𝒞 ⥤ Prod 𝒟 ℰ where
  obj X := (F X, G X)
  map f := (F.map f, G.map f)
  map_id := by
    intro A
    simp
    rw [F.map_id, G.map_id]
  map_comp f g := by
    simp
    rw [F.map_comp f g, G.map_comp f g]

def Prod.par (F : 𝒞 ⥤ 𝒞') (G : 𝒟 ⥤ 𝒟') : Prod 𝒞 𝒟 ⥤ Prod 𝒞' 𝒟' where
  obj X := (F X.1, G X.2)
  map f := (F.map f.1, G.map f.2)
  map_id := by
    intro A
    simp
    rw [F.map_id, G.map_id]
  map_comp f g := by
    simp
    rw [F.map_comp, G.map_comp]

def homF : Prod 𝒞ᵒᵖ 𝒞 ⥤ Types where
  obj P := 𝒞[P.1, P.2]
  map f g := f.2 ⊚ g ⊚ f.1
  map_id := funext λ _ =>
    (Category.compose_id _).trans (Category.id_compose _)
  map_comp f g := funext λ h => by
    simp [Category.compose, Types, Prod]
    repeat
      rw [←Category.compose]

def yo {𝒞 : Category} : 𝒞 ⥤ 𝒞ᵒᵖ ⥤ Types where
  obj C := {
    obj := λ X => 𝒞[X, C]
    map := λ f g => g ⊚ f
    map_id := funext λ g => Category.compose_id g
    map_comp := λ f g =>  funext λ h => by
      simp [Category.compose, Types]
  }
  map f := {
    app := λ A g => f ⊚ g
    naturality := by
      intro A' B' g
      funext h
      simp at h
      simp [Category.compose, Types]
  }
  map_id := by
    intro A
    apply NatTrans.ext
    intro B
    simp
    funext g
    simp [Category.identity, Func, NatTrans.id, Types]
  map_comp f g := by
    apply NatTrans.ext
    intro B
    simp
    funext h
    simp [Category.identity, Func, NatTrans.comp, Types]

@[simp]
def Types.comp_def (f : Types[β, γ]) (g : α ⟶ β) : (f ⊚ g) x = f (g x) := rfl 

def const 𝒞 {𝒟 : Category} (X : 𝒟) : 𝒞 ⥤ 𝒟 where
  obj _ := X
  map _ := 𝟙 X
  map_id := rfl
  map_comp _ _ := (Category.compose_id _).symm

def Yoneda (F : 𝒞ᵒᵖ ⥤ Types) : NatIso (homF.comp (Prod.pair yo.op (const _ F))) F where
  app C N := N.app C (𝟙 C)
  inv C x := { app := λ A f => F.map f x 
               naturality := by
                intro A B f
                simp [Functor.comp, Prod.pair, yo, Functor.op]
                funext g
                simp [const]
                rw [F.map_comp]
                rfl
             }
  naturality := by
    intro (A : 𝒞) (B : 𝒞) (f : B ⟶ A)
    funext (g : yo A ⟹ F)
    simp [Functor.comp, homF, Prod.pair, const, Functor.op, yo, Category.compose,
          Func, NatTrans.comp]
    rw [←Types.comp_def (F.map f), ←g.naturality]
    simp [yo]
    rfl

  leftInv C := by
    simp [homF, Functor.comp, Functor.op, Prod.pair, const]
    funext N
    apply NatTrans.ext
    intro A
    funext f
    simp [homF, Functor.comp, Functor.op, Prod.pair, const]
    rw [←Types.comp_def (F.map f), ←N.naturality f]
    simp [yo, Category.identity, Category.compose, Types]
  rightInv C := by
    funext x
    simp
    rw [F.map_id]


end Categories