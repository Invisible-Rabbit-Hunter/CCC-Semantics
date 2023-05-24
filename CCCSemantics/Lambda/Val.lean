import CCCSemantics.Lambda.Term

inductive Val (σ : Sig) : Ctx σ → Ty σ.types → (neu : Bool) → Type u
| var : Var τ Γ → Val σ Γ τ true
| base : (t : σ.terms) → Val σ Γ (σ.typing t) true
| lam : Val σ (Γ ,, τ) υ false → Val σ Γ (Ty.arr τ υ) false
| app : Val σ Γ (Ty.arr τ υ) true → Val σ Γ τ false → Val σ Γ υ true
| pair : Val σ Γ τ false → Val σ Γ υ false → Val σ Γ (Ty.prod τ υ) false
| fst : Val σ Γ (Ty.prod τ υ) true → Val σ Γ τ true  
| snd : Val σ Γ (Ty.prod τ υ) true → Val σ Γ υ true  
| unit : Val σ Γ Ty.unit true  
| lift : Val σ Γ τ true → Val σ Γ τ false

def NF σ Γ τ := Val σ Γ τ false
def Neu σ Γ τ := Val σ Γ τ true

def Renaming.val : ∀{Γ Δ : Ctx σ}, Renaming Γ Δ → Val σ Δ τ b → Val σ Γ τ b
| _, _, e, .var v => .var (e.var v)
| _, _, e, .base b => .base b
| _, _, e, .app t u => .app (e.val t) (e.val u)
| _, _, e, .lam t => .lam (e.keep.val t)
| _, _, e, .pair t u => .pair (e.val t) (e.val u)
| _, _, e, .fst t => .fst (e.val t)
| _, _, e, .snd t => .snd (e.val t)
| _, _, e, .unit => .unit
| _, _, e, .lift t => .lift (e.val t)


def TyN (σ : Sig.{u}) : Ctx σ → Ty σ.types → Type u
| Γ, .base b   => NF σ Γ (.base b)
| Γ, .arr a b  => ∀ {Δ}, Renaming Δ Γ → TyN σ Δ a → TyN σ Δ b  
| Γ, .prod a b => TyN σ Γ a × TyN σ Γ b 
| Γ, .unit     => NF σ Γ .unit

def TyN.weaken : ∀ {Γ Δ τ}, Renaming Γ Δ → TyN σ Δ τ → TyN σ Γ τ
| Γ, Δ, .base b, e, t => e.val t
| Γ, Δ, .arr a b, e, t => λ e' u => t (e'.trans e) u
| Γ, Δ, .prod a b, e, t => (TyN.weaken e t.1, TyN.weaken e t.2)
| Γ, Δ, .unit, e, t => e.val t

inductive ConN (σ : Sig.{u}) : Ctx σ → Ctx σ → Type _
| nil : ConN σ Γ ε
| cons : ConN σ Γ Δ → TyN σ Γ τ → ConN σ Γ (Δ ,, τ)

def ConN.weaken : ∀ {Γ Δ Ε}, Renaming Γ Δ → ConN σ Δ Ε → ConN σ Γ Ε
| Γ, _, ε,      _, .nil      => .nil
| Γ, Δ, Ε ,, τ, e, .cons c t => .cons (c.weaken e) (t.weaken e)

def ConN.var : ∀ {Γ Δ τ}, Var τ Δ → ConN σ Γ Δ → TyN σ Γ τ
| Γ, _, τ, .zero, .cons _ t => t
| Γ, _, τ, .succ v, .cons c _ => c.var v

mutual
def quote : ∀ {τ}, TyN σ Γ τ → NF σ Γ τ 
| .base _,   t => t
| .arr a b,  t => .lam (quote (t (Renaming.ide Γ).skip (unquote (.var .zero))))
| .prod a b, t => .pair (quote t.1) (quote t.2)
| .unit,     t => t

def unquote : ∀ {τ}, Neu σ Γ τ → TyN σ Γ τ
| .base b,   t => .lift t
| .arr a b,  t => λ e u => unquote (.app (e.val t) (quote u))
| .prod a b, t => (unquote (.fst t), unquote (.snd t))
| .unit,     t => .lift t
end
termination_by
  quote τ _ => τ
  unquote τ _ => τ

def ConN.vars : ∀ Γ, ConN σ Γ Γ
| ε      => .nil
| Γ ,, _ => .cons (ConN.weaken (Renaming.ide Γ).skip (vars Γ)) (unquote <| .var .zero)

def TmN : ∀ {Γ Δ τ}, ConN σ Γ Δ → Tm σ Δ τ → TyN σ Γ τ
| Γ, Δ, τ, c, .var v    => c.var v
| Γ, Δ, _, c, .base b   => unquote (.base b)
| Γ, Δ, _, c, .lam t    => λ e u => TmN (.cons (c.weaken e) u) t 
| Γ, Δ, υ, c, .app t u  => TmN c t (Renaming.ide _) (TmN c u)
| Γ, Δ, _, c, .pair t u => (TmN c t, TmN c u)
| Γ, Δ, _, c, .fst t    => (TmN c t).1
| Γ, Δ, _, c, .snd t    => (TmN c t).2
| Γ, Δ, _, c, .unit     => .lift .unit

def Tm.norm : ConN σ Γ Δ → Tm σ Δ τ → NF σ Γ τ :=
  λ c t => quote (TmN c t)  

def Val.toTm : Val σ Γ Δ b → Tm σ Γ Δ
| .var v => .var v
| .base b => .base b
| .lam t => .lam t.toTm
| .app t u => .app t.toTm u.toTm
| .pair t u => .pair t.toTm u.toTm
| .fst t => .fst t.toTm
| .snd t => .snd t.toTm
| .unit => .unit 
| .lift t => t.toTm

