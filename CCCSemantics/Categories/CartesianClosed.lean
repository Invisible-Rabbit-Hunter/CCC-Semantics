import CCCSemantics.Categories.Adjunction

namespace Categories

structure product (𝒞 : Category) (A B : 𝒞) where
  apex : 𝒞
  π₁ : apex ⟶ A
  π₂ : apex ⟶ B
  universal : (f : X ⟶ A) → (g : X ⟶ B) →
    {p : X ⟶ apex // f = π₁ ⊚ p ∧ g = π₂ ⊚ p }
  unique : ∀ (f : X ⟶ A) (g : X ⟶ B)
    (fg : X ⟶ apex), (f = π₁ ⊚ fg) → (g = π₂ ⊚ fg) →
    fg = universal f g

structure terminal (𝒞 : Category) where
  apex : 𝒞
  universal : X ⟶ apex 
  unique : ∀ (f : X ⟶ apex), f = universal

class Cartesian (𝒞 : Category) where
  hasTerminal : terminal 𝒞
  hasProducts : ∀ A B, product 𝒞 A B

instance : Cartesian Types where
  hasTerminal := {
    apex := PUnit
    universal := λ _ => PUnit.unit 
    unique := λ _ => rfl 
  }
  hasProducts A B := {
    apex := A × B
    π₁ := Prod.fst
    π₂ := Prod.snd
    universal := λ f g => ⟨λ x => (f x, g x), ⟨rfl, rfl⟩⟩ 
    unique := λ _ _ _ h₁ h₂ => 
      funext λ x =>
      congrArg₂ (·,·) (congrFun h₁.symm x)
                      (congrFun h₂.symm x)
  }

namespace Cartesian
variable {𝒞} [Cartesian 𝒞]

def prod (A B : 𝒞):= (hasProducts A B).apex
infixl:83 " ×' " => prod

def pair (f : X ⟶ A) (g : X ⟶ B) : 𝒞[X, (hasProducts A B).apex] :=
  (hasProducts A B).universal f g

def proj₁ : 𝒞[(hasProducts A B).apex, A] := (hasProducts A B).π₁
def proj₂ : 𝒞[(hasProducts A B).apex, B] := (hasProducts A B).π₂

@[simp]
theorem proj₁_pair (f : 𝒞[X, A]) (g : 𝒞[X, B]) : proj₁ ⊚ pair f g = f :=
  ((hasProducts A B).universal f g).property.1.symm
@[simp]
theorem proj₂_pair (f : 𝒞[X, A]) (g : 𝒞[X, B]) : proj₂ ⊚ pair f g = g :=
  ((hasProducts A B).universal f g).property.2.symm

theorem pair_unique (f : 𝒞[X, A]) (g : 𝒞[X, B]) (fg : 𝒞[X, A ×' B])
  (h₁ : f = proj₁ ⊚ fg) (h₂ : g = proj₂ ⊚ fg)
  : fg = pair f g := ((hasProducts A B).unique f g fg h₁ h₂)

@[simp]
theorem pair_comp (f : 𝒞[X, A]) (g : 𝒞[X, B]) (h : 𝒞[Y, X]) :
  pair (f ⊚ h) (g ⊚ h) = pair f g ⊚ h := by
  apply Eq.symm
  apply pair_unique <;> {rw [←Category.assoc]; simp}

def prod.map (f : A ⟶ A') (g : B ⟶ B') : prod (A : 𝒞) B ⟶ prod A' B' :=
  pair (f ⊚ proj₁) (g ⊚ proj₂)

@[simp]
def prod.map_id {A B : 𝒞} : prod.map (𝟙 A) (𝟙 B) = 𝟙 (A ×' B) := by
  simp [map]
  apply Eq.symm
  apply pair_unique <;> simp

@[simp]
def prod.map_comp {A A' A'' B B' B'': 𝒞}
  (f₁ : A' ⟶ A'') (g₁ : A ⟶ A')
  (f₂ : B' ⟶ B'') (g₂ : B ⟶ B') :
  prod.map (f₁ ⊚ g₁) (f₂ ⊚ g₂) = prod.map f₁ f₂ ⊚ prod.map g₁ g₂ := by
  simp [map]
  apply Eq.symm
  apply pair_unique
  rw [←Category.assoc proj₁, proj₁_pair, Category.assoc, proj₁_pair]
  rw [←Category.assoc proj₂, proj₂_pair, Category.assoc, proj₂_pair]

def prod.map_comp_fst {A A' A'' B : 𝒞}
  (f : A' ⟶ A'') (g : A ⟶ A') :
  prod.map (f ⊚ g) (𝟙 B) = prod.map f (𝟙 B) ⊚ prod.map g (𝟙 B) := by
  rw [←Category.compose_id (𝟙 B), prod.map_comp, Category.compose_id (𝟙 B)]

def prod.map_comp_snd {A B B' B'' : 𝒞}
  (f : B' ⟶ B'') (g : B ⟶ B') :
  prod.map (𝟙 A) (f ⊚ g) = prod.map (𝟙 A) f ⊚ prod.map (𝟙 A) g := by
  rw [←Category.compose_id (𝟙 A), prod.map_comp, Category.compose_id (𝟙 A)]

def prodF [Cartesian 𝒞] : Prod 𝒞 𝒞 ⥤ 𝒞 where
  obj P := prod P.1 P.2
  map f := prod.map f.1 f.2
  map_id := prod.map_id
  map_comp f g := prod.map_comp f.1 g.1 f.2 g.2

def final : 𝒞 := hasTerminal.apex
def bang : 𝒞[X, final] := hasTerminal.universal
def bang_unique (f : 𝒞[X, final]): f = bang := hasTerminal.unique f

end Cartesian

open Cartesian in
structure exponential (𝒞 : Category) [Cartesian 𝒞] (A B : 𝒞) where
  exp : 𝒞
  lam : X ×' A ⟶ B → X ⟶ exp
  eval : exp ×' A ⟶ B
  eval_lam (f : X ×' A ⟶ B):
    eval ⊚ Cartesian.prod.map (lam f) (𝟙 A) = f
  unique : ∀ (f : X ×' A ⟶ B) (f' : X ⟶ exp), (f = eval ⊚ prod.map f' (𝟙 A)) →
             f' = lam f

class CartesianClosed (𝒞 : Category) extends Cartesian 𝒞 where
  closed : ∀ A B, exponential 𝒞 A B

def diag : 𝒞 ⥤ Prod 𝒞 𝒞 where
  obj X := (X, X)
  map f := (f, f)
  map_id := rfl
  map_comp _ _ := rfl

namespace CartesianClosed
variable [CartesianClosed 𝒞]
open Cartesian

def exp (A B : 𝒞) := (closed A B).exp

def lam (f : 𝒞[X ×' A, B]) := (closed A B).lam f
def eval : 𝒞[exp A B ×' A, B] := (closed A B).eval

@[simp]
theorem eval_lam (f : 𝒞[X ×' A, B]) : eval ⊚ (prod.map (lam f) (𝟙 A)) = f :=
  (closed A B).eval_lam f
theorem lam_unique (f : 𝒞[X ×' A, B]) (f' : 𝒞[X, exp A B])
  (h : f = eval ⊚ prod.map f' (𝟙 A)) : f' = lam f :=
  (closed A B).unique f f' h

def exp.map (f : 𝒞[A', A]) (g : 𝒞[B, B']) :
  𝒞[exp A B, exp A' B'] :=
  lam (g ⊚ eval (A := A) (B := B) ⊚ prod.map (𝟙 _) f)

def exp.map_id {A B : 𝒞} : exp.map (𝟙 A) (𝟙 B) = 𝟙 (exp A B) := by
  simp [map]
  apply Eq.symm
  apply lam_unique
  simp

def exp.map_comp {A A' A'' B B' B'' : 𝒞}
  (f₁ : A' ⟶ A) (g₁ : A'' ⟶ A')
  (f₂ : B' ⟶ B'') (g₂ : B ⟶ B') :
  exp.map (f₁ ⊚ g₁) (f₂ ⊚ g₂) = exp.map g₁ f₂ ⊚ exp.map f₁ g₂ := by
  simp [map]
  apply Eq.symm
  apply lam_unique
  rw [←Category.compose_id (𝟙 A''), prod.map_comp,
      ←Category.assoc eval, eval_lam,
       Category.assoc, Category.assoc, ←prod.map_comp]
  simp
  rw [←Category.id_compose g₁, ←Category.compose_id (lam _),
       prod.map_comp,
      ←Category.assoc eval, eval_lam,
       Category.assoc, Category.assoc, ←prod.map_comp]
  simp

def expF : Prod 𝒞ᵒᵖ 𝒞 ⥤ 𝒞 where
  obj P := exp P.1 P.2
  map f := exp.map f.1 f.2
  map_id := exp.map_id
  map_comp f g := exp.map_comp (𝒞 := 𝒞) g.1 f.1 f.2 g.2

def HomProdAdj [CartesianClosed 𝒞] (X : 𝒞) :
  Adjunction (prodF.comp
                (Prod.pair (Functor.id 𝒞) (const 𝒞 X)))
             (expF.comp
                (Prod.pair (const 𝒞 X) (Functor.id 𝒞))) :=
  Adjunction.ofHomEquiv (λ A B =>{
    toFun := lam 
    invFun := λ f => eval ⊚ prod.map f (𝟙 _)
    leftInv := by
      simp [Functor.comp, Prod.pair, Functor.id, const]
    rightInv := by
      intro f
      apply Eq.symm
      apply lam_unique
      simp [Functor.comp, Prod.pair, Functor.id, const, expF]
  }) (by
    simp [Functor.comp, Prod.pair, Functor.id, const, prodF]
    intro A A' B (f : A' ×' X ⟶ B) g
    apply lam_unique
    rw [←Category.compose_id (𝟙 X), prod.map_comp, ←Category.assoc]
    simp
  ) (by
    simp [Functor.comp, Prod.pair, Functor.id, const, expF]
    intro A B B' f (g : A ×' X ⟶ B)
    simp [exp.map]
    apply Eq.symm
    apply lam_unique
    rw [←Category.compose_id (𝟙 X), prod.map_comp, ←Category.assoc]
    simp
  )

end CartesianClosed

end Categories