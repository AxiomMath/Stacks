module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Moving the degree of a single complex across a shift-commuting functor

Let `Φ : D(A) ⥤ D(B)` be a functor commuting with the shift. A complex concentrated in degree
`d` is a complex concentrated in degree zero shifted by `-d`, the shift passes through `Φ`, and
the shift sequence of `H^0` turns `H^n` of a complex shifted by `-d` into `H^{n-d}`. Together
these give

`single d ⋙ Φ ⋙ H^n  ≅  single 0 ⋙ Φ ⋙ H^{n-d}`.

The same `SingleFunctors.shiftIso` also identifies the shift of a single complex in degree zero
with the single complex in the shifted degree.

The analogous isomorphism for `DerivedCategory.Plus` is
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`.

## Main definitions

* `DerivedCategory.singleCompHomologyShiftIso`: the displayed isomorphism.
* `DerivedCategory.singleShiftIso`: the shift of a module in degree zero is that module in the
  shifted degree.

## References

* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v v' u u' w w'

namespace DerivedCategory

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

/-- **Moving the degree of a single complex across a shift-commuting functor.** For
`Φ : D(A) ⥤ D(B)` commuting with the shift and `n' + d = n`,

`single d ⋙ Φ ⋙ H^n  ≅  single 0 ⋙ Φ ⋙ H^{n'}`.

The three steps are `SingleFunctors.shiftIso`, which writes `single d` as `single 0` shifted by
`-d`, the commutation `Φ.commShiftIso (-d)`, and the shift sequence of `H^0`, which turns `H^n`
of a complex shifted by `-d` into `H^{n'}`. -/
def singleCompHomologyShiftIso (Φ : DerivedCategory A ⥤ DerivedCategory B) [Φ.CommShift ℤ]
    (d n n' : ℤ) (h : n' + d = n) :
    singleFunctor A d ⋙ Φ ⋙ homologyFunctor B n ≅
      singleFunctor A 0 ⋙ Φ ⋙ homologyFunctor B n' :=
  Functor.isoWhiskerRight ((singleFunctors A).shiftIso (-d) d 0 (by omega)).symm
      (Φ ⋙ homologyFunctor B n) ≪≫
    Functor.isoWhiskerLeft (singleFunctor A 0)
      (Functor.isoWhiskerRight (Φ.commShiftIso (-d)) (homologyFunctor B n)) ≪≫
      Functor.isoWhiskerLeft (singleFunctor A 0) (Functor.isoWhiskerLeft Φ
        ((homologyFunctor B 0).shiftIso (-d) n n' (by omega)))

/-- **The shift of an object in degree zero is that object in the shifted degree.** -/
def singleShiftIso (X : A) (m : ℤ) :
    ((singleFunctor A 0).obj X)⟦m⟧ ≅ (singleFunctor A (-m)).obj X :=
  ((singleFunctors A).shiftIso m (-m) 0 (by omega)).app X

end DerivedCategory

end
