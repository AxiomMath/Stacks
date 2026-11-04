module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Additivity after exchanging the arguments of a bifunctor -/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- A bifunctor additive in its second variable is additive after exchanging the variables. -/
instance flip_additive [Preadditive D] [Preadditive E]
    (F : C ⥤ D ⥤ E) [∀ X, (F.obj X).Additive] : F.flip.Additive where
  map_add := NatTrans.ext <| funext fun X ↦ (F.obj X).map_add

/-- Fixing the second variable of an additive bifunctor gives an additive functor. -/
instance flip_obj_additive [Preadditive C] [Preadditive E]
    (F : C ⥤ D ⥤ E) [F.Additive] (Y : D) : (F.flip.obj Y).Additive where
  map_add := NatTrans.congr_app F.map_add Y

end CategoryTheory.Functor

end
