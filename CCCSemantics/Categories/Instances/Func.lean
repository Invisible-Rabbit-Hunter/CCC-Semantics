import CCCSemantics.Categories.NaturalTransformation

namespace Categories

def Func (𝒞 𝒟 : Category) : Category where
  Ob := Functor 𝒞 𝒟
  Hom F G := F ⟹ G
  id F := NatTrans.id F
  comp M N := NatTrans.comp M N
  comp_assoc := NatTrans.comp_assoc
  comp_id := NatTrans.comp_id
  id_comp := NatTrans.id_comp

infixr:75 " ⥤ " => Func

unif_hint (𝒞 𝒟 : Category) where
  ⊢ (𝒞 ⥤ 𝒟).Ob ≟ Functor 𝒞 𝒟

unif_hint (𝒞 𝒟 : Category) (F G : 𝒞 ⥤ 𝒟) where
  ⊢ (F ⟹ G) ≟ (Func 𝒞 𝒟).Hom F G

instance : CoeFun (𝒞 ⥤ 𝒟) (λ _ => 𝒞 → 𝒟) where
  coe F := F.obj

end Categories