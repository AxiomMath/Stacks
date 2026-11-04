module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleIrreducible

/-!
# An affine-space bundle over a reduced base is reduced, and over an integral base is integral

Let `f : X ⟶ Y` be an affine-space bundle of rank `r` in the sense of
`Stacks.Chow.IsAffineSpaceBundle`, so that every point of `Y` has an open neighbourhood `U` over
which `f` is the projection `𝔸^r_U ⟶ U`. This file shows that `X` is reduced as soon as `Y` is,
and — combined with `Stacks.Chow.irreducibleSpace_of_isAffineSpaceBundle` — that `X` is integral
as soon as `Y` is.

## Main results

* `Stacks.Chow.isReduced_of_isAffineSpaceBundle`: **an affine-space bundle of rank `r` over a
  reduced scheme has reduced total space.**
* `Stacks.Chow.isIntegral_of_isAffineSpaceBundle`: **an affine-space bundle of rank `r` over an
  integral scheme has integral total space.**
* `Stacks.LineBundle.Situation.isReduced_totalSpace`,
  `Stacks.LineBundle.Situation.isIntegral_totalSpace`: **the total space of a line bundle over a
  reduced (resp. integral) scheme is reduced (resp. integral).**
* `Stacks.LineBundle.isReduced_lineBundleSpace`, `Stacks.LineBundle.isIntegral_lineBundleSpace`:
  the same at the `lineBundleProj` spelling of [Stacks, Tag 01M2].

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)

/-- **An affine-space bundle of rank `r` over a reduced scheme has reduced total space.** -/
theorem isReduced_of_isAffineSpaceBundle (h : IsAffineSpaceBundle f r) [IsReduced Y] :
    IsReduced X := by
  choose U hmem e _ using h
  have hcover : TopologicalSpace.IsOpenCover fun y : Y ↦ f ⁻¹ᵁ U y :=
    top_le_iff.mp fun x _ ↦ by simpa using ⟨f.base x, hmem (f.base x)⟩
  rw [IsReduced.iff_of_openCover _ (X.openCoverOfIsOpenCover _ hcover)]
  exact fun y ↦ ObjectProperty.prop_of_iso _ (e y).symm inferInstance

/-- **An affine-space bundle of rank `r` over an integral scheme has integral total space.** -/
theorem isIntegral_of_isAffineSpaceBundle (h : IsAffineSpaceBundle f r) [IsIntegral Y] :
    IsIntegral X :=
  have := isReduced_of_isAffineSpaceBundle f r h
  have := irreducibleSpace_of_isAffineSpaceBundle f r h
  isIntegral_of_irreducibleSpace_of_isReduced X

end Stacks.Chow

namespace Stacks.LineBundle

/-- **The total space of a line bundle over a reduced scheme is reduced.** -/
theorem Situation.isReduced_totalSpace (D : Situation.{u}) [IsReduced D.X] :
    IsReduced D.totalSpace :=
  Stacks.Chow.isReduced_of_isAffineSpaceBundle D.totalSpaceToBase 1
    D.isAffineSpaceBundle_totalSpaceToBase

/-- **The total space of a line bundle over an integral scheme is integral.** -/
theorem Situation.isIntegral_totalSpace (D : Situation.{u}) [IsIntegral D.X] :
    IsIntegral D.totalSpace :=
  Stacks.Chow.isIntegral_of_isAffineSpaceBundle D.totalSpaceToBase 1
    D.isAffineSpaceBundle_totalSpaceToBase

variable (Y : Scheme.{u}) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

include hM in
/-- **The total space of the line bundle of an invertible module on a reduced scheme is
reduced**, at the `lineBundleProj` spelling of [Stacks, Tag 01M2]. -/
theorem isReduced_lineBundleSpace [IsReduced Y] : IsReduced (lineBundleSpace Y M) :=
  Stacks.Chow.isReduced_of_isAffineSpaceBundle (lineBundleProj Y M) 1
    (isAffineSpaceBundle_lineBundleProj Y M)

include hM in
/-- **The total space of the line bundle of an invertible module on an integral scheme is
integral**, at the `lineBundleProj` spelling of [Stacks, Tag 01M2]. -/
theorem isIntegral_lineBundleSpace [IsIntegral Y] : IsIntegral (lineBundleSpace Y M) :=
  Stacks.Chow.isIntegral_of_isAffineSpaceBundle (lineBundleProj Y M) 1
    (isAffineSpaceBundle_lineBundleProj Y M)

end Stacks.LineBundle

end
