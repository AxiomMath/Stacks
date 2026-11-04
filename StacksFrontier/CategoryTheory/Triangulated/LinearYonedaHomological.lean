module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The linear Yoneda functors of a pretriangulated category are homological

Let `C` be a pretriangulated category which is linear over a ring `k`. For every object `B` the
functor `Hom(-, B) : Cᵒᵖ ⥤ Mod_k` and for every object `A` the functor `Hom(A, -) : C ⥤ Mod_k` are
homological: this is [Stacks, Tag 0149] read through the forgetful functor `Mod_k ⥤ Ab`, which
reflects exactness. Mathlib records the statement for the additive Yoneda functors
`preadditiveYoneda` and `preadditiveCoyoneda`; here it is recorded for `linearYoneda` and
`linearCoyoneda`, the form in which `k`-linear representability statements are phrased.

## Main results

* `CategoryTheory.linearYoneda_obj_isHomological`
* `CategoryTheory.linearCoyoneda_obj_isHomological`

## References

* [Stacks Project, Tag 0149](https://stacks.math.columbia.edu/tag/0149)
-/

@[expose] public section

open CategoryTheory Opposite Limits Pretriangulated Pretriangulated.Opposite

universe w v u

namespace CategoryTheory

variable (k : Type w) [Ring k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **`Hom(-, B)` is homological**, as a functor `Cᵒᵖ ⥤ Mod_k`. -/
instance linearYoneda_obj_isHomological (B : C) : ((linearYoneda k C).obj B).IsHomological where
  exact T hT := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 <|
    (ShortComplex.ab_exact_iff_function_exact _).1
      ((preadditiveYoneda.obj B).map_distinguished_exact T hT)

/-- **`Hom(A, -)` is homological**, as a functor `C ⥤ Mod_k`. -/
@[sga "4½ Etat_0 1.3.2" "more general"]
instance linearCoyoneda_obj_isHomological (A : Cᵒᵖ) :
    ((linearCoyoneda k C).obj A).IsHomological where
  exact T hT := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 <|
    (ShortComplex.ab_exact_iff_function_exact _).1
      ((preadditiveCoyoneda.obj A).map_distinguished_exact T hT)

end CategoryTheory
