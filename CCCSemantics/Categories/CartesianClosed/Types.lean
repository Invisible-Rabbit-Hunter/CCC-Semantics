import CCCSemantics.Categories.CartesianClosed
import CCCSemantics.Categories.Instances.Types

namespace Categories
instance : Cartesian Types.{u} where
  hasTerminal := {
    apex := PUnit
    universal := λ _ => PUnit.unit 
    unique := λ _ => rfl 
  }
  hasProducts A B := {
    apex := A × B
    is_product := {
      π₁ := Prod.fst
      π₂ := Prod.snd
      universal := λ f g x => (f x, g x) 
      universal_prop := λ _ _ => ⟨rfl, rfl⟩
      unique := λ _ _ _ h₁ h₂ => 
        funext λ x =>
        congrArg₂ (·,·) (congrFun h₁ x)
                        (congrFun h₂ x)
    }
  }

instance : CartesianClosed Types where
  closed α β := {
    exp := α → β 
    is_exponential := {
      lam := λ f x a => f (x, a)
      eval := λ (f, x) => f x
      eval_lam := λ f => rfl
      unique := λ f f' h => by
        simp [h]
        rfl
    }
  }

end Categories