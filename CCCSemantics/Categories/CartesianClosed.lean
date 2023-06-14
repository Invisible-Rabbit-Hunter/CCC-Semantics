import CCCSemantics.Categories.Adjunction

namespace Categories

structure is_product (𝒞 : Category) (A B : 𝒞) (apex : 𝒞) where
  π₁ : apex ⟶ A
  π₂ : apex ⟶ B
  universal : X ⟶ A → X ⟶ B → X ⟶ apex
  universal_prop : (f : X ⟶ A) → (g : X ⟶ B) →
    π₁ ⊚ universal f g = f ∧ π₂ ⊚ universal f g = g
  unique : ∀ (f : X ⟶ A) (g : X ⟶ B)
    (fg : X ⟶ apex), (f = π₁ ⊚ fg) → (g = π₂ ⊚ fg) →
    universal f g = fg

def is_product_unique.to (h₁ : is_product 𝒞 A B P₁) (h₂ : is_product 𝒞 A B P₂) :
  P₁ ⟶ P₂ := h₂.universal h₁.π₁ h₁.π₂
   
def is_product_unique.inv (h₁ : is_product 𝒞 A B P₁) (h₂ : is_product 𝒞 A B P₂) :
  is_product_unique.to h₂ h₁ ⊚ is_product_unique.to h₁ h₂ = 𝟙 P₁ := by
  simp [inv, to]
  apply Eq.trans
  · apply Eq.symm
    apply h₁.unique
    · rw [←Category.assoc, (h₁.universal_prop _ _).1,
          (h₂.universal_prop _ _).1]
    · rw [←Category.assoc, (h₁.universal_prop _ _).2,
          (h₂.universal_prop _ _).2]
  · apply h₁.unique
    · exact (Category.compose_id h₁.π₁).symm
    · exact (Category.compose_id h₁.π₂).symm
    
structure product (𝒞 : Category) (A B : 𝒞) where
  apex : 𝒞
  is_product : is_product 𝒞 A B apex

namespace product
variable (P : product 𝒞 A B)
def π₁ : apex P ⟶ A := (is_product P).π₁
def π₂ : apex P ⟶ B := (is_product P).π₂
def universal : (f : X ⟶ A) → (g : X ⟶ B) → X ⟶ apex P := (is_product P).universal
theorem universal_prop (f : X ⟶ A) (g : X ⟶ B) :
  π₁ P ⊚ universal P f g = f ∧ π₂ P ⊚ universal P f g = g := (is_product P).universal_prop f g 
theorem unique : ∀ (f : X ⟶ A) (g : X ⟶ B)
     (fg : X ⟶ apex P), (f = π₁ P ⊚ fg) → (g = π₂ P ⊚ fg) →
     universal P f g = fg := (is_product P).unique
end product

structure terminal (𝒞 : Category) where
  apex : 𝒞
  universal : X ⟶ apex 
  unique : ∀ (f : X ⟶ apex), f = universal

class Cartesian (𝒞 : Category) where
  hasTerminal : terminal 𝒞
  hasProducts : ∀ A B, product 𝒞 A B

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
  ((hasProducts A B).universal_prop f g).1
@[simp]
theorem proj₂_pair (f : 𝒞[X, A]) (g : 𝒞[X, B]) : proj₂ ⊚ pair f g = g :=
  ((hasProducts A B).universal_prop f g).2

theorem pair_unique (f : 𝒞[X, A]) (g : 𝒞[X, B]) (fg : 𝒞[X, A ×' B])
  (h₁ : f = proj₁ ⊚ fg) (h₂ : g = proj₂ ⊚ fg)
  : pair f g = fg := ((hasProducts A B).unique f g fg h₁ h₂)

theorem pair_ext (f f' : 𝒞[X, A]) (g g' : 𝒞[X, B]) :
  pair f g = pair f' g' ↔ (f = f' ∧  g = g') := by
    constructor
    · intro h
      constructor
      rw [←proj₁_pair f g, h, proj₁_pair]
      rw [←proj₂_pair f g, h, proj₂_pair]
    · intro h
      rw [h.1, h.2]

@[simp]
theorem pair_comp (f : 𝒞[X, A]) (g : 𝒞[X, B]) (h : 𝒞[Y, X]) :
  pair (f ⊚ h) (g ⊚ h) = pair f g ⊚ h := by
  apply pair_unique <;> {rw [←Category.assoc]; simp}

def prod.map (f : A ⟶ A') (g : B ⟶ B') : prod (A : 𝒞) B ⟶ prod A' B' :=
  pair (f ⊚ proj₁) (g ⊚ proj₂)

@[simp]
def prod.map_id {A B : 𝒞} : prod.map (𝟙 A) (𝟙 B) = 𝟙 (A ×' B) := by
  simp [map]
  apply pair_unique <;> simp

@[simp]
def prod.map_comp {A A' A'' B B' B'': 𝒞}
  (f₁ : A' ⟶ A'') (g₁ : A ⟶ A')
  (f₂ : B' ⟶ B'') (g₂ : B ⟶ B') :
  prod.map (f₁ ⊚ g₁) (f₂ ⊚ g₂) = prod.map f₁ f₂ ⊚ prod.map g₁ g₂ := by
  simp [map]
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

def prod.map_iso (f : Iso 𝒞 A A') (g : Iso 𝒞 B B') : IsIso (prod.map f.to g.to) where
  inv := prod.map f.to_isIso.inv g.to_isIso.inv
  leftInv := by
    rw [←map_comp, f.to_isIso.leftInv, g.to_isIso.leftInv, map_id]
  rightInv := by
    rw [←map_comp, f.to_isIso.rightInv, g.to_isIso.rightInv, map_id]

def prodF : Prod 𝒞 𝒞 ⥤ 𝒞 where
  obj P := prod P.1 P.2
  map f := prod.map f.1 f.2
  map_id := prod.map_id
  map_comp f g := prod.map_comp f.1 g.1 f.2 g.2

def final : 𝒞 := hasTerminal.apex
def bang : 𝒞[X, final] := hasTerminal.universal
theorem bang_unique (f : 𝒞[X, final]): f = bang := hasTerminal.unique f

@[simp]
theorem pair_proj₁_proj₂ {A B : 𝒞}: pair proj₁ proj₂ = 𝟙 (A ×' B) := by
  apply pair_unique
  exact (Category.compose_id proj₁).symm
  exact (Category.compose_id proj₂).symm

theorem prod.map_comp_pair (f₁ : 𝒞[A, A']) (f₂ : 𝒞[B, B'])
                           (g₁ : 𝒞[X, A])  (g₂ : 𝒞[X, B]) :
  prod.map f₁ f₂ ⊚ pair g₁ g₂ = pair (f₁ ⊚ g₁) (f₂ ⊚ g₂) := by
  simp [map, ←pair_comp]

def prod.assoc (A B C : 𝒞) : Iso 𝒞 (A ×' B ×' C) (A ×' (B ×' C)) where
  to := pair (proj₁ ⊚ proj₁) (pair (proj₂ ⊚ proj₁) proj₂)
  to_isIso := {
    inv := pair (pair proj₁ (proj₁ ⊚ proj₂)) (proj₂ ⊚ proj₂)
    leftInv := by
      simp [←pair_comp]
      rw [Category.id_compose (B := A ×' B) proj₁]
      simp
    rightInv := by
      simp [←pair_comp]
      rw [Category.id_compose (B := B ×' C) proj₂]
      simp
  }
end Cartesian

open Cartesian in
structure is_exponential (𝒞 : Category) [Cartesian 𝒞] (A B exp : 𝒞) where
  lam : X ×' A ⟶ B → X ⟶ exp
  eval : exp ×' A ⟶ B
  eval_lam (f : X ×' A ⟶ B):
    eval ⊚ Cartesian.prod.map (lam f) (𝟙 A) = f
  unique : ∀ (f : X ×' A ⟶ B) (f' : X ⟶ exp), (f = eval ⊚ prod.map f' (𝟙 A)) →
             f' = lam f

def is_exponential_unique.to [Cartesian 𝒞] (h₁ : is_exponential 𝒞 A B E₁)
                                           (h₂ : is_exponential 𝒞 A B E₂)
    : E₁ ⟶ E₂ := h₂.lam h₁.eval

def is_exponential_unique.inv [Cartesian 𝒞] (h₁ : is_exponential 𝒞 A B E₁)
                                            (h₂ : is_exponential 𝒞 A B E₂)
    : is_exponential_unique.to h₂ h₁ ⊚ is_exponential_unique.to h₁ h₂ = 𝟙 E₁ := by
      simp [to]
      apply Eq.symm
      apply Eq.trans
      · apply h₁.unique; simp; rfl
      · apply Eq.symm
        apply h₁.unique
        simp [Cartesian.prod.map_comp_fst]
        rw [←Category.assoc, h₁.eval_lam, h₂.eval_lam]

open Cartesian in
structure exponential (𝒞 : Category) [Cartesian 𝒞] (A B : 𝒞) where
  exp : 𝒞
  is_exponential : is_exponential 𝒞 A B exp

namespace exponential
variable [Cartesian 𝒞] (E : exponential 𝒞 A B)
def lam : (X ×' A ⟶ B) → (X ⟶ exp E) := (is_exponential E).lam
def eval : exp E ×' A ⟶ B := (is_exponential E).eval
def eval_lam (f : X ×' A ⟶ B) : eval E ⊚ Cartesian.prod.map (lam E f) (𝟙 A) = f := (is_exponential E).eval_lam f
theorem unique : ∀ (f : X ×' A ⟶ B) (f' : X ⟶ exp E),
     (f = eval E ⊚ Cartesian.prod.map f' (𝟙 A)) → f' = lam E f := (is_exponential E).unique
end exponential

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

def prod.lam_of_comp (f : 𝒞[X ×' A, B]) (g : 𝒞[Y, X]) :
  lam (f ⊚ prod.map g (𝟙 _)) = lam f ⊚ g := by
  apply Eq.symm
  apply lam_unique
  rw [prod.map_comp_fst, ←Category.assoc, eval_lam]

def exp.map_comp_lam (f : 𝒞[B, C]) (g : 𝒞[X ×' A, B]) :
  lam (f ⊚ g) = exp.map (𝟙 _) f ⊚ lam g := by
    apply Eq.symm
    apply lam_unique
    simp [prod.map, map]
    rw [←prod.lam_of_comp, prod.map_comp_fst, ←Category.assoc,
        Category.assoc f, eval_lam, prod.lam_of_comp, ←Category.id_compose proj₂,
        ←prod.map, eval_lam]

theorem lam_injective (f g : 𝒞[X ×' A, B]) : lam f = lam g → f = g := by
  intro hyp
  rw [←eval_lam f, hyp, eval_lam]

def eval_pair_lam (f : 𝒞[X ×' A, B]) (g : 𝒞[X, A]) :
  eval ⊚ pair (lam f) g = f ⊚ pair (𝟙 X) g := by
  rw [←eval_lam f, Category.assoc, prod.map, ←pair_comp,
      Category.assoc, Category.assoc, proj₁_pair, proj₂_pair,
      ←prod.map, eval_lam, Category.compose_id, Category.id_compose]

theorem lam_of_eval [CartesianClosed 𝒞] {A B : 𝒞}:
  lam (eval) = 𝟙 (exp A B) := by
  apply Eq.symm
  apply lam_unique
  simp [prod.map_id]

end CartesianClosed

open Cartesian CartesianClosed in
structure CCFunctor (𝒞) [CartesianClosed 𝒞] (𝒟) [CartesianClosed 𝒟] extends Functor 𝒞 𝒟 where
  preserve_terminal : IsIso (bang : toFunctor final ⟶ final)

  preserve_products (A B : 𝒞) :
                      IsIso (pair (toFunctor.map (proj₁ (A := A) (B := B)))
                                  (toFunctor.map (proj₂ (A := A) (B := B))))

  preserve_exponential (A B : 𝒞) :
                      IsIso (A := toFunctor (exp A B))
                            (B := exp (toFunctor A) (toFunctor B))
                            (lam (toFunctor.map (eval (A := A)) ⊚
                                  (preserve_products _ _).inv))

end Categories