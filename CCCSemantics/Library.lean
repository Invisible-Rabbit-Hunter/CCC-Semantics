
def congrArg₂
  (f : α → β → γ) : x = x' → y = y' →
  f x y = f x' y'
| .refl _, .refl _ => rfl

def Path {β : α → Sort v} (h : x = y) (a : β x) (b : β y) : Prop :=
  h ▸ a = b

namespace Path

variable {α : Type u} {β : α → Sort v} {γ : (x : α) → β x → Sort w}

def trans (p : Path h₁ a b) (q : Path h₂ b c) : Path (h₁.trans h₂) a c:= by
  simp [Path]
  cases h₂
  apply Eq.trans p q

end Path

structure Equiv (A B : Type u) where
  toFun : A → B
  invFun : B → A
  leftInv : ∀ x, invFun (toFun x) = x
  rightInv : ∀ x, toFun (invFun x) = x 

namespace Equiv

infixl:90 " ≃ " => Equiv

instance : CoeFun (Equiv α β) (λ _ => α → β) where
  coe := toFun

def symm (e : Equiv α β) : Equiv β α where
  toFun := e.invFun
  invFun := e.toFun
  leftInv := e.rightInv
  rightInv := e.leftInv 

@[simp]
theorem symm_leftInv (e : Equiv α β) : ∀ x, e.symm (e x) = x := e.leftInv

@[simp]
theorem symm_rightInv (e : Equiv α β) : ∀ x, e (e.symm x) = x := e.rightInv

theorem injective (e : Equiv α β) (p : e x = e y) : x = y :=
  ((e.symm_leftInv x).symm.trans (congrArg _ p)).trans (e.symm_leftInv y)

end Equiv

-- universe u v

-- def curry (F : CProd 𝒞 𝒟 ⥤ ℰ) : 𝒞 ⥤ (𝒟 ⥤ ℰ) where
--   obj A := { obj := λ B => F (A, B) 
--              map := λ g => F.map (𝟙 A, g) 
--              map_id := F.map_id
--              map_comp := by
--               intro B B' B'' f g
--               simp
--               rw [←Category.compose_id (𝟙 A), F.map_comp]
--               simp [Category.compose_id]
--            }
--   map f := { app := λ B => F.map (f, 𝟙 B)
--              naturality := by
--               intro B B' g
--               simp
--               rw [←F.map_comp, ←F.map_comp]
--               apply congrArg
--               apply congrArg₂ (·,·)
--               exact (Category.compose_id _).trans (Category.id_compose _).symm
--               exact (Category.id_compose _).trans (Category.compose_id _).symm
--            }
--   map_id := by
--     intro A
--     apply NatTrans.ext
--     intro B
--     simp [Category.identity, Func, NatTrans.id]
--     exact F.map_id
--   map_comp := by
--     intro A₁ A₂ A₃ f g
--     apply NatTrans.ext
--     intro B
--     simp [Category.compose, Func, NatTrans.comp]
--     rw [←Category.compose_id (𝟙 B), F.map_comp]
--     simp [Category.compose_id]

-- def Disc : Types ⥤ Cat where
--   obj α := {
--     Ob := α
--     Hom := λ x y => PLift (x = y)
--     id := λ _ => PLift.up rfl
--     comp := λ p q => PLift.up (q.down.trans p.down)
--     comp_assoc := λ _ _ _ => rfl
--     comp_id := λ _ => rfl
--     id_comp := λ _ => rfl
--   }
--   map f := {
--     obj := f
--     map := λ p => PLift.up (congrArg f p.down)
--     map_id := rfl
--     map_comp := λ _ _ => rfl
--   }
--   map_id := rfl
--   map_comp := λ _ _ => rfl

-- def Ob : Cat ⥤ Types where
--   obj 𝒞 := 𝒞.Ob
--   map F := F.obj
--   map_id := rfl
--   map_comp _ _ := rfl

-- example : Adjunction Ob Disc where
--   unit := {
--     app := λ C x => x
--     naturality := λf => rfl  
--   }
--   counit := {
--     app := λ C => {
--       obj := λ A => A
--       map := λ p => p.down ▸ 𝟙 _
--       map_id := rfl
--       map_comp := λ {A} {B} {C} f g => by
--         cases f.down
--         cases g.down
--         simp
--         apply (Category.comp_id _ _).symm
--     }
--     naturality := λ {A} {B} f => by
--       simp [Category.compose, Cat, Category.identity, CFunctor.id, CFunctor.comp]
--       constructor
--       · simp [Disc, Ob]
--       · simp [Disc, Ob]
--         funext A' B' g
--         cases g.down
--         simp
--         apply f.map_id.symm
--   }

--   triangle_left := by
--     intros
--     apply NatTrans.ext
--     intro A
--     simp [NatTrans.whisker_left, NatTrans.whisker_right, Category.compose,
--           NatTrans.comp, Func, Types, Cat, Ob, Disc, Category.identity,
--           NatTrans.id]
--     rfl
--   triangle_right := by
--     intros
--     apply NatTrans.ext
--     intro α 
--     apply CFunctor.ext
--     simp [NatTrans.whisker_left, NatTrans.whisker_right, Category.compose,
--           NatTrans.comp, Func, Types, Cat, Ob, Disc, Category.identity,
--           NatTrans.id, CFunctor.comp, CFunctor.id]
--     intro A B f
--     cases f.down
--     rfl
--     intro A
--     simp [NatTrans.whisker_left, NatTrans.whisker_right, Category.compose,
--           NatTrans.comp, Func, Types, Cat, Ob, Disc, Category.identity,
--           NatTrans.id, CFunctor.comp, CFunctor.id]


-- end CartesianClosed