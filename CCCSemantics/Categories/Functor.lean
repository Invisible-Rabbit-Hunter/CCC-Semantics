import CCCSemantics.Categories.Category

namespace Categories

structure Functor (𝒞 𝒟 : Category) where
  obj : 𝒞 → 𝒟
  map {A B : 𝒞} : A ⟶ B → obj A ⟶ obj B
  map_id : map (𝟙 A) = 𝟙 (obj A)
  map_comp : ∀ (f : B ⟶ C) (g : A ⟶ B),  map (f ⊚ g) = map f ⊚ map g

namespace Functor

local infixr:80 " ⥤ " => Functor
def id 𝒞 : 𝒞 ⥤ 𝒞 where
  obj A := A
  map f := f
  map_id := rfl
  map_comp _ _ := rfl

def comp (F : ℬ ⥤ 𝒞) (G : 𝒜 ⥤ ℬ) : 𝒜 ⥤ 𝒞 where
  obj A := F.obj (G.obj A)
  map f := F.map (G.map f)
  map_id := (congrArg _ (G.map_id)).trans (F.map_id)
  map_comp f g :=
    (congrArg _ (G.map_comp f g)).trans (F.map_comp (G.map f) (G.map g))

theorem comp_assoc (F : 𝒞 ⥤ 𝓓) (G : ℬ ⥤ 𝒞) (H : 𝒜 ⥤ ℬ) :
  comp (comp F G) H = comp F (comp G H) := rfl
theorem comp_id (F : 𝒞 ⥤ 𝒟) : comp F (id 𝒞) = F := rfl
theorem id_comp (F : 𝒞 ⥤ 𝒟) : comp (id 𝒟) F = F := rfl

instance : CoeFun (𝒞 ⥤ 𝒟) (λ _ => 𝒞 → 𝒟) where
  coe F := Functor.obj F

def ext {F G : 𝒞 ⥤ 𝒟} (obj : ∀ A, F A = G A) (map : ∀ {A} {B} (f : A ⟶ B),
  congrArg (λ H => H A ⟶ H B) (funext obj) ▸ (F.map f) = (G.map f)) : F = G := by

  cases F with | mk objF mapF =>
  cases G with | mk objG mapG =>
  simp
  constructor
  · funext A; exact obj A
  · simp at *
    apply heq_of_eqRec_eq
    case h₁ =>
      have h : objF = objG := funext obj
      rw [h]
    funext A B f
    have h₁ : objF = objG := funext obj
    have h₂ := map f
    cases h₁
    simp at *
    assumption

def op (F : 𝒞 ⥤ 𝒟) : 𝒞ᵒᵖ ⥤ 𝒟ᵒᵖ where
  obj := F
  map f := F.map f
  map_id := F.map_id
  map_comp f g := F.map_comp g f

end Functor


end Categories