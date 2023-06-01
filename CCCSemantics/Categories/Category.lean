import CCCSemantics.Library

namespace Categories

structure Category where
  Ob : Type u
  Hom : Ob → Ob → Type v
  id : ∀ A, Hom A A
  comp (f : Hom B C) (g : Hom A B) : Hom A C
  comp_assoc : ∀ (f : Hom C D) (g : Hom B C) (h : Hom A B),
    comp (comp f g) h = comp f (comp g h)
  comp_id : ∀ f : Hom A B, comp f (id A) = f
  id_comp : ∀ f : Hom A B, comp (id B) f = f

namespace Category

notation 𝒞 "[" A ", " B "]" => Category.Hom 𝒞 A B

instance : CoeSort Category (Type _) where
  coe 𝒞 := 𝒞.Ob

abbrev hom {𝒞 : Category} (A B : 𝒞) := 𝒞.Hom A B
abbrev identity {𝒞 : Category} (A : 𝒞) := 𝒞.id A
abbrev compose {𝒞 : Category} {A B C : 𝒞} (f : 𝒞[B, C]) (g : 𝒞[A, B]) := 𝒞.comp f g

notation "𝟙" => identity
notation "𝟙[" 𝒞 "]" => Category.id 𝒞
notation f:71 " ⊚[" 𝒞 "] " g:70  => Category.comp 𝒞 f g
infixl:70 " ⊚ " => compose
infixr:80 " ⟶ " => hom

unif_hint (𝒞 : Category) (A B : 𝒞) where
  ⊢ 𝒞.Hom A B ≟ A ⟶ B

unif_hint (𝒞 : Category) (A : 𝒞) where
  ⊢ 𝒞.id A ≟ 𝟙 A

unif_hint (𝒞 : Category) (A B C : 𝒞) (f : 𝒞[B, C]) (g : 𝒞[A, B]) where
  ⊢ 𝒞.comp f g ≟ f ⊚ g

@[simp]
theorem assoc (f : C ⟶ D) (g : B ⟶ C) (h : A ⟶ B) : (f ⊚ g) ⊚ h = f ⊚ (g ⊚ h) :=
  Category.comp_assoc _ f g h

@[simp]
theorem compose_id (f : A ⟶ B) : f ⊚ 𝟙 A = f :=
  Category.comp_id _ f

@[simp]
theorem id_compose (f : A ⟶ B) : 𝟙 B ⊚ f = f :=
  Category.id_comp _ f

end Category

structure IsIso {𝒞 : Category} {A B : 𝒞} (f : A ⟶ B) where
  inv : B ⟶ A
  leftInv : inv ⊚ f = 𝟙 A
  rightInv : f ⊚ inv = 𝟙 B

structure Iso (𝒞 : Category) (A B : 𝒞) where
  to : A ⟶ B
  to_isIso : IsIso to
  
structure Mono (𝒞 : Category) (A B : 𝒞) where
  to : A ⟶ B
  monic : ∀ (f g : X ⟶ A), to ⊚ f = to ⊚ g → f = g 

structure Epi (𝒞 : Category) (A B : 𝒞) where
  to : A ⟶ B
  monic : ∀ (f g : B ⟶ X), f ⊚ to  = g ⊚ to → f = g 

def op (𝒞 : Category) : Category where
  Ob := 𝒞
  Hom A B := 𝒞[B, A]
  id := 𝒞.id
  comp f g := 𝒞.comp g f
  comp_assoc f g h := (𝒞.comp_assoc h g f).symm
  comp_id f := 𝒞.id_comp f
  id_comp f := 𝒞.comp_id f

postfix:max "ᵒᵖ" => op

theorem op_op (𝒞 : Category) : 𝒞ᵒᵖᵒᵖ = 𝒞 := rfl

unif_hint (𝒞 : Category) (A B : 𝒞) where
  ⊢ 𝒞ᵒᵖ[A, B] ≟ 𝒞[B, A]

unif_hint (𝒞 : Category) (A: 𝒞) where
  ⊢ 𝒞ᵒᵖ.id A ≟ 𝒞.id A

unif_hint (𝒞 : Category) (A B C : 𝒞) (f : 𝒞ᵒᵖ[B, C]) (g : 𝒞ᵒᵖ[A, B]) where
  ⊢ (f ⊚ g) ≟ 𝒞.comp g f

end Categories