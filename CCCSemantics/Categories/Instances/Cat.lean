import CCCSemantics.Categories.Functor

namespace Categories

def Cat : Category where
  Ob := Category
  Hom 𝒞 𝒟 := Functor 𝒞 𝒟
  id := Functor.id
  comp := Functor.comp
  comp_assoc := Functor.comp_assoc
  comp_id := Functor.comp_id
  id_comp := Functor.id_comp

unif_hint (α β : Category) where
  ⊢ Functor α β ≟ Cat.Hom α β

end Categories