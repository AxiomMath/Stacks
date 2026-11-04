module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived

/-! # `Rw(X[0])` lies in `D^{≥ 0}`

Let `A` and `B` be abelian categories with unbounded derived categories, `A` with enough
injectives, let `w : A ⥤ B` be additive and let `Rw : D(A) ⥤ D(B)`, with unit `α`, be a right
derived functor of `w` on the unbounded derived category. Then `Rw` applied to an object placed
in degree `0` has no cohomology in negative degrees.

## Implementation notes

`Rw(X[0])` is computed by the chosen injective resolution: the augmentation `X[0] ⟶ resH X` is a
quasi-isomorphism and the extended resolution is K-injective, so the unit of `Rw` is invertible
there. Hence `Rw(X[0])` is the image in `D(B)` of the complex `w` applied degreewise to the
extended resolution. That complex vanishes in negative degrees, because the extended resolution
does and `w` preserves the zero object; so it lies in `D^{≥ 0}`, and the cohomology of an object
of `D^{≥ 0}` vanishes in negative degrees.

## Main definitions

* `Stacks.DerivedFunctor.resComplex`: `w` applied degreewise to the chosen injective resolution
  of an object, extended by zero to a complex indexed by `ℤ`.
* `Stacks.DerivedFunctor.singleDerivedIsoQResComplex`: `Rw(X[0])` is the image of that complex in
  `D(B)`.

## Main results

* `Stacks.DerivedFunctor.isZero_homologyFunctor_obj_derived_single`: `Hⁿ(Rw(X[0])) = 0` for
  `n < 0`.
* `Stacks.DerivedFunctor.isGE_derived_single`: `Rw(X[0])` lies in `D^{≥ 0}`.

## References

* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (w : A ⥤ B) [w.Additive]

/-- `w` applied degreewise to the chosen injective resolution of `X`, extended by zero to a complex
indexed by `ℤ`. -/
def resComplex (X : A) : CochainComplex B ℤ :=
  (w.mapHomologicalComplex (ComplexShape.up ℤ)).obj (injectiveResolution X).cochainComplex

/-- The complex `resComplex w X` is strictly concentrated in degrees `≥ 0`. -/
instance isStrictlyGE_resComplex (X : A) : (resComplex w X).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  simpa [resComplex] using Functor.map_isZero w
    (((injectiveResolution X).cochainComplex).isZero_of_isStrictlyGE 0 i hi)

variable (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- The isomorphism between `Rw(X[0])` and the image in `D(B)` of `w` applied degreewise to the
chosen injective resolution of `X`, given that every complex admits a quasi-isomorphism to a
K-injective complex. -/
def singleDerivedIsoQResComplex
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (X : A) :
    Rw.obj ((DerivedCategory.singleFunctor A 0).obj X) ≅
      DerivedCategory.Q.obj (resComplex w X) :=
  Rw.mapIso (singleIsoResCompQh.app X) ≪≫
    ((resCompUnitIso w Rw α hres).app X).symm ≪≫
    DerivedCategory.Qh.mapIso
      ((w.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
        (injectiveResolution X).cochainComplex) ≪≫
    (DerivedCategory.quotientCompQhIso B).app (resComplex w X)

include w α in
/-- If every complex admits a quasi-isomorphism to a K-injective complex, then
`Hⁿ(Rw(X[0])) = 0` for `n < 0`. -/
theorem isZero_homologyFunctor_obj_derived_single
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (X : A) (n : ℤ) (hn : n < 0) :
    IsZero ((DerivedCategory.homologyFunctor B n).obj
      (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X))) :=
  (DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj (resComplex w X)) 0 n hn).of_iso
    ((DerivedCategory.homologyFunctor B n).mapIso
      (singleDerivedIsoQResComplex w Rw α hres X))

include w α in
/-- If every complex admits a quasi-isomorphism to a K-injective complex, then `Rw(X[0])` lies
in `D^{≥ 0}`. -/
theorem isGE_derived_single
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (X : A) :
    (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0 :=
  (DerivedCategory.isGE_iff _ 0).2 fun n hn =>
    isZero_homologyFunctor_obj_derived_single w Rw α hres X n hn

end Stacks.DerivedFunctor

end
