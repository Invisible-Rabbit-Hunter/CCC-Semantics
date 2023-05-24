import CCCSemantics.CCC

open CategoryTheory
instance : CCC (Type u) where
  one := PUnit
  bang _ := .unit
  bang_uniq := rfl

  prod α β := α × β
  proj₁ := Prod.fst
  proj₂ := Prod.snd
  pair f g x := (f x, g x)
  proj₁_pair _ _ := rfl
  proj₂_pair _ _ := rfl
  pair_ext _ := rfl

  exp α β := α → β 
  lam f x y := f (x, y)
  eval p := p.1 p.2
  lam_eval' _ := rfl
  lam_uniq' h := funext₂ λ a b => congrArg (· (a, b)) h

-- instance [Category 𝒞] : CCC (𝒞 ⥤ Type u) where
--   one := { obj := λ _ => PUnit, map := λ _ => 𝟙 _  }
--   bang := { app := _ }
--   bang_uniq := rfl

--   prod α β := { obj := λ x => α.obj x × β.obj x
--                 map := λ f => CCC.bimap (α.map f) (β.map f)
--                 }
--   proj₁ := { app := λ _ => CCC.proj₁ }
--   proj₂ := { app := λ _ => CCC.proj₂ }
--   pair f g := { app := λ x => CCC.pair (f.app x) (g.app x),
--                 naturality := by {
--                   intros X Y f₂
--                   simp
--                   trans

--                 }
--               }
--   proj₁_pair := _
--   proj₂_pair := _
--   pair_ext := _

--   exp := _ 
--   lam f := _
--   eval := _
--   lam_eval' := _
--   lam_uniq' := _
