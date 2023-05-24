import CCCSemantics.Categories.Instances.Func

namespace Categories

def Types.{u} : Category where
  Ob := Type u
  Hom α β := α → β
  id _ x := x
  comp f g x := f (g x)
  comp_assoc _ _ _ := rfl
  comp_id _ := rfl
  id_comp _ := rfl

unif_hint (α β : Type u) where
  ⊢ α → β ≟ Types.Hom α β

example : Types ⥤ Types where
  obj A := Option A
  map f := Option.map f
  map_id := Option.map_id
  map_comp f g := by funext x; cases x <;> rfl

end Categories
