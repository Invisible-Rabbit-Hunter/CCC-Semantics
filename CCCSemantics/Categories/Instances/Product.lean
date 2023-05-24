import CCCSemantics.Categories.Category

namespace Categories

def Prod (𝒞 𝒟 : Category) : Category where
  Ob := 𝒞 × 𝒟
  Hom P Q := (P.1 ⟶ Q.1) × (P.2 ⟶ Q.2)
  id P := (𝟙 P.1, 𝟙 P.2)
  comp f g := (f.1 ⊚ g.1, f.2 ⊚ g.2)
  comp_assoc f g h := congrArg₂ (·,·) (Category.assoc f.1 g.1 h.1)
                                      (Category.assoc f.2 g.2 h.2)
  comp_id f := congrArg₂ (·,·) (Category.compose_id f.1) (Category.compose_id f.2)
  id_comp f := congrArg₂ (·,·) (Category.id_compose f.1) (Category.id_compose f.2)

unif_hint (𝒞 𝒟 : Category) (A₁ B₁ : 𝒞) (A₂ B₂ : 𝒟) where
  ⊢ (A₁ ⟶ B₁) × (A₂ ⟶ B₂) ≟ (Prod 𝒞 𝒟).Hom (A₁, A₂) (B₁, B₂) 

unif_hint (𝒞 𝒟 : Category) where
  ⊢ 𝒞.Ob × 𝒟.Ob ≟ Prod 𝒞 𝒟

unif_hint (𝒞 𝒟 : Category) (A₁ : 𝒞) (A₂ : 𝒟) where
  ⊢ (𝟙 A₁, 𝟙 A₂) ≟ 𝟙 (A₁, A₂)

unif_hint (𝒞 𝒟 : Category) (A : Prod 𝒞 𝒟) where
  ⊢ (𝟙 A).fst ≟ 𝟙 A.fst

unif_hint (𝒞 𝒟 : Category) (A : Prod 𝒞 𝒟) where
  ⊢ (𝟙 A).snd ≟ 𝟙 A.snd

unif_hint (𝒞 𝒟 : Category) (A₁ B₁ C₁ : 𝒞) (A₂ B₂ C₂ : 𝒟)
          (f₁ : B₁ ⟶ C₁) (g₁ : A₁ ⟶ B₁) (f₂ : B₂ ⟶ C₂) (g₂ : A₂ ⟶ B₂) where
  ⊢ (f₁ ⊚ g₁, f₂ ⊚ g₂) ≟ (f₁, f₂) ⊚ ((g₁, g₂) : (A₁, A₂) ⟶ (B₁, B₂))

unif_hint (𝒞 𝒟 : Category) (A B C : Prod 𝒞 𝒟) (f : B ⟶ C) (g : A ⟶ B) where
  ⊢ (f ⊚ g).fst ≟ f.fst ⊚ g.fst

unif_hint (𝒞 𝒟 : Category) (A B C : Prod 𝒞 𝒟) (f : B ⟶ C) (g : A ⟶ B) where
  ⊢ (f ⊚ g).snd ≟ f.snd ⊚ g.snd


end Categories