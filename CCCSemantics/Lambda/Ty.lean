
inductive Ty (Base : Type _) : Type _
| base : Base → Ty Base
| unit : Ty Base
| prod : Ty Base → Ty Base → Ty Base
| arr : Ty Base → Ty Base → Ty Base