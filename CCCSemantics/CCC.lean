
open CategoryTheory
open Limits

def withSnd [Category 𝒞] [Category 𝒟] [Category ℰ] (F : 𝒞 × 𝒟 ⥤ ℰ) (X : 𝒟) : 𝒞 ⥤ ℰ where
  obj Y := F.obj (Y, X)
  map f := F.map (f, 𝟙 X)
  map_id Y := F.map_id (Y, X)
  map_comp f g :=
    have h : F.map ((f ≫ g, 𝟙 X) : (_, X) ⟶ (_, X)) = F.map ((f ≫ g, 𝟙 X ≫ 𝟙 X) : (_, X) ⟶ (_, X))
      := congrArg _ (congrArg _ (Category.comp_id (𝟙 X)).symm)
    h.trans (F.map_comp ((f, 𝟙 X) : (_, X) ⟶ (_, X)) ((g, 𝟙 X) : (_, X) ⟶ (_, X)))

class CCC (Ob : Type u) extends Category Ob where
  one : Ob
  bang : A ⟶ one
  bang_uniq : f = bang 

  prod : Ob → Ob → Ob
  proj₁ : prod A B ⟶ A
  proj₂ : prod A B ⟶ B
  pair : (X ⟶ A) → (X ⟶ B) → (X ⟶ prod A B)
  proj₁_pair : ∀ (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ proj₁ = f
  proj₂_pair : ∀ (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ proj₂ = g
  pair_ext : ∀ (f : X ⟶ prod A B), pair (f ≫ proj₁) (f ≫ proj₂) = f

  exp : Ob → Ob → Ob
  lam : (prod A B ⟶ C) → (A ⟶ exp B C)
  eval : prod (exp A B) A ⟶ B 
  lam_eval' (f : prod A B ⟶ C) : pair (proj₁ ≫ lam f) proj₂ ≫ eval = f
  lam_uniq' : pair (proj₁ ≫ g) proj₂ ≫ eval = f → g = lam f

open CCC in
attribute [simp] proj₁_pair proj₂_pair pair_ext lam_eval'

namespace CCC
variable [CCC 𝒞] {A B C D : 𝒞}
                 {A₁ B₁ C₁ D₁ : 𝒞}
                 {A₂ B₂ C₂ D₂ : 𝒞}

lemma prod_ext (f g : A ⟶ prod B C) :
  (f ≫ proj₁ = g ≫ proj₁ ∧ f ≫ proj₂ = g ≫ proj₂) → f = g := by
  intro ⟨p, q⟩
  rw [←pair_ext f, ←pair_ext g]
  congr

lemma comp_pair (f : A ⟶ B) (g : B ⟶ C) (h : B ⟶ D) :
  pair (f ≫ g) (f ≫ h) = f ≫ pair g h := by
    apply prod_ext
    constructor
    · simp [proj₁_pair]
    · simp [proj₂_pair]

theorem prod_is_prod (A B : 𝒞) : IsLimit (BinaryFan.mk (P := prod A B) proj₁ proj₂) where
  lift s := pair (BinaryFan.fst s) (BinaryFan.snd s)
  fac s
  | ⟨.left⟩  => proj₁_pair _ _
  | ⟨.right⟩ => proj₂_pair _ _
  uniq s
  | m, j => by
    simp
    let h₁ := j ⟨.left⟩
    let h₂ := j ⟨.right⟩
    simp at h₁ h₂
    rw [←h₁, ←h₂]
    symm
    apply pair_ext

@[simp]
lemma pair_proj (A B : 𝒞): pair proj₁ proj₂ = 𝟙 (prod A B) := by
  rw [←Category.id_comp proj₁, ←Category.id_comp proj₂, pair_ext]

def bimap (f : A ⟶ B) (g : C ⟶ D) :
  prod A C ⟶ prod B D := pair (proj₁ ≫ f) (proj₂ ≫ g)

@[simp]
def bimap_id : bimap (𝟙 A) (𝟙 B) = 𝟙 (prod A B) := by simp [bimap]

@[simp]
def bimap_comp (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)
               (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) :
               bimap (f₁ ≫ g₁) (f₂ ≫ g₂) = bimap f₁ f₂ ≫ bimap g₁ g₂ := by
  simp [bimap]
  apply prod_ext
  simp
  constructor
  · rw [←Category.assoc _ proj₁ _]  
    simp
  · rw [←Category.assoc _ proj₂ _]  
    simp

@[simp]
lemma lam_eval (f : prod A B ⟶ C) : bimap (lam f) (𝟙 _) ≫ eval = f := by simp [bimap]
lemma lam_uniq (f : prod A B ⟶ C) (g : A ⟶ exp B C) : bimap g (𝟙 _) ≫ eval = f → g = lam f := by
  intro h
  apply lam_uniq'
  rw [←Category.comp_id proj₂]
  assumption

def prodF : 𝒞 × 𝒞 ⥤ 𝒞 where
  obj P := prod P.1 P.2
  map f := bimap f.1 f.2

def dimap (f : A ⟶ B) (g : C ⟶ D) :
  exp B C ⟶ exp A D := lam (bimap (𝟙 _) f ≫ eval ≫ g)

@[simp]
def dimap_id : dimap (𝟙 A) (𝟙 B) = 𝟙 (exp A B) := by
  rw [dimap]
  symm
  apply lam_uniq
  simp

def lam_comp (f : A ⟶ B) (g : prod B C ⟶ D) : f ≫ lam g = lam (bimap f (𝟙 _) ≫ g) := by
  apply lam_uniq
  rw [←Category.comp_id (𝟙 C), bimap_comp]
  simp


@[simp]
def dimap_comp (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)
               (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) :
              dimap (f₁ ≫ g₁) (f₂ ≫ g₂) = dimap g₁ f₂ ≫ dimap f₁ g₂ := by
  simp [dimap]
  rw [lam_comp (lam _)]
  apply lam_uniq
  simp
  rw [←Category.assoc (bimap (lam _) _),
      ←bimap_comp]
  simp
  rw [←Category.comp_id f₁,
      ←Category.id_comp (lam _),
      bimap_comp,
      Category.assoc,
      Category.assoc,
      ←Category.assoc _ eval,
      ←Category.assoc _ eval,
      lam_eval]
  simp
  rw [←Category.comp_id (𝟙 _),
      bimap_comp]
  simp

def expF : 𝒞 × 𝒞ᵒᵖ ⥤ 𝒞 where
  obj P := exp P.2.unop P.1
  map f := dimap f.2.unop f.1
  map_id _ := dimap_id
  map_comp f g := dimap_comp g.2.unop f.2.unop f.1 g.1

@[simp]
theorem lam_comp_dimap [CCC 𝒞] {A B C E : 𝒞} (f : prod A B ⟶ C) (g : C ⟶ E) : 
  lam (f ≫ g) = lam f ≫ dimap (𝟙 B) g := by
  simp [dimap]
  rw [lam_comp, ←Category.assoc, lam_eval]

def prod_exp_adj [CCC 𝒞] : withSnd prodF A ⊣ withSnd expF (Opposite.op A) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := λ X Y => {
      toFun := lam
      invFun := λ f => bimap f (𝟙 _) ≫ eval
      left_inv := by intro f; simp
      right_inv := by intro f
                      symm
                      apply lam_uniq
                      simp
    }
    homEquiv_naturality_left_symm := by
      intro X Y Z f g
      simp
      rw [←Category.assoc]
      congr
      apply (withSnd prodF A).map_comp
    homEquiv_naturality_right := by
      intro X Y Z f g
      simp [withSnd, expF]
  }
  

