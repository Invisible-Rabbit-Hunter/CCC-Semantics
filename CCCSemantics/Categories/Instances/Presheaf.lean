import CCCSemantics.Categories.CartesianClosed
import CCCSemantics.Categories.CartesianClosed.Types

namespace Categories
open Cartesian CartesianClosed

instance (𝒞 : Category) [Cartesian 𝒟] : Cartesian (𝒞 ⥤ 𝒟) where
  hasProducts F G := {
      apex := {
        obj := λ X => F X ×' G X 
        map := λ f => prod.map (F.map f) (G.map f) 
        map_id := by intro A; simp; rw [F.map_id, G.map_id, prod.map_id]
        map_comp := by
          intro B C A f g
          simp
          rw [F.map_comp, G.map_comp, prod.map_comp]
      }
      is_product := {
        π₁ := {
          app := λ A => proj₁
          naturality := λ f => by simp [prod.map]
        }
        π₂ := {
          app := λ A => proj₂
          naturality := λ f => by simp [prod.map] 
        }
        universal := λ α β => 
          {
            app := λ A => pair (α.app A) (β.app A)
            naturality := by
              intro A B f
              simp
              rw [prod.map_comp_pair, ←pair_comp,
                  α.naturality, β.naturality]
          }
        universal_prop := λ α β => 
          by constructor <;> {
              apply NatTrans.ext
              intro A
              simp [Category.compose, Func, NatTrans.comp]
          }
        
        unique := by
          intro X f g fg h₁ h₂
          simp
          apply NatTrans.ext
          intro A
          simp [h₁, h₂, Category.compose, Func, NatTrans.comp]
      }
  }
  hasTerminal := {
    apex := {
      obj := λ _ => final
      map := λ _ => 𝟙 final
      map_id := rfl 
      map_comp := λ _ _ => (Category.compose_id _).symm
    }
    universal := {
      app := λ A => bang
      naturality := λ f => by
        simp
        apply bang_unique
    }
    unique := λ f => by
      apply NatTrans.ext
      intro A
      simp
      apply bang_unique
  }

namespace Presheaf
universe u
variable {𝒞 : Category.{u,u}} {X A B : 𝒞ᵒᵖ ⥤ Types.{u}}

set_option pp.universes true in
def exp (A B : 𝒞ᵒᵖ ⥤ Types.{u}) : 𝒞ᵒᵖ ⥤ Types.{u} where
  obj := λ (I : 𝒞) => ((yo I ×' A) ⟹ B)
  map := λ {I J : 𝒞} (f : 𝒞[J, I]) F => {
    app := λ (K : 𝒞) p => F.app K (f ⊚ p.1, p.2)
    naturality := by
      intro K L g
      simp [prod, hasProducts]
      funext (h, x)
      simp [yo, prod.map, pair, proj₁, proj₂, hasProducts]
      rw [←Types.comp_def (B.map _),
          ←F.naturality]
      simp [yo, prod, hasProducts, prod.map, pair, proj₁, proj₂]
  }
  map_id := by
    intro (I : 𝒞)
    funext F
    simp
    congr
  map_comp := by
    intro (J : 𝒞) (K : 𝒞) (I : 𝒞) (f : 𝒞[K, J]) (g : 𝒞[J, I])
    funext F
    simp

def lam (F : X ×' A ⟹ B) : X ⟹ exp A B where
  app := λ (I : 𝒞) x => {
    app := λ (J : 𝒞) f => F.app J (X.map f.1 x, f.2)
    naturality := by
      intro (I : 𝒞) (J : 𝒞) (f : 𝒞[J, I])
      funext G
      simp
      rw [←Types.comp_def (B.map _),
          ←F.naturality]
      simp [yo, prod, hasProducts, prod.map, pair, proj₁, proj₂]
      rw [X.map_comp, Types.comp_def]
  }
  naturality := by
    intro (I : 𝒞) (J : 𝒞) (f : 𝒞[J, I])
    funext x
    simp [exp]
    funext K p
    rw [X.map_comp, Types.comp_def]

def eval : exp A B ×' A ⟹ B where
  app := λ (I : 𝒞) P => P.1.app I (𝟙 I, P.2)
  naturality := by
    intro (I : 𝒞) (J : 𝒞) (f : 𝒞[J, I])
    funext P
    simp
    rw [←Types.comp_def (B.map _),
        ←P.1.naturality]
    simp [exp, prod, hasProducts, prod.map, pair, proj₁, proj₂, yo]

def eval_lam (f : X ×' A ⟹ B) : eval ⊚ prod.map (lam f) (𝟙 A) = f := by
  apply NatTrans.ext
  intro (I : 𝒞)
  funext x
  simp [Category.compose, Func, NatTrans.comp, Types, eval,
        prod, prod.map, pair, hasProducts, proj₁, proj₂,
        lam]
  rw [X.map_id]
  simp [Category.identity, Types, NatTrans.id]
  rfl

def unique (F : X ×' A ⟹ B) (F' : X ⟹ exp A B) (hyp : F = eval ⊚ prod.map F' (𝟙 A)) :
  F' = lam F := by
  apply NatTrans.ext
  intro (I : 𝒞)
  funext x
  apply NatTrans.ext
  intro (J : 𝒞)
  funext (⟨(f : 𝒞[J, I]), a⟩)
  simp [lam]
  have p := congrFun (F.naturality f) 
  have hyp' (I : 𝒞) (G : X I × A I) := congrFun (congrFun (congrArg NatTrans.app hyp) I) G
  simp [Category.compose, Types, prod, hasProducts, prod.map,
        pair, proj₁, proj₂] at p 
  simp [Category.compose, Types, prod, hasProducts, prod.map,
        pair, proj₁, proj₂, eval, Func, NatTrans.comp] at hyp'
  rw [hyp']
  simp
  rw [←Types.comp_def (F'.app _), F'.naturality]
  simp [exp, Category.identity, NatTrans.id]

end Presheaf

instance (𝒞 : Category.{u,u}) : CartesianClosed (𝒞ᵒᵖ ⥤ Types.{u}) where
  closed A B := {
    exp := Presheaf.exp A B
    is_exponential := {
      lam := Presheaf.lam
      eval := Presheaf.eval
      eval_lam := Presheaf.eval_lam
      unique := Presheaf.unique
    }
  }

end Categories