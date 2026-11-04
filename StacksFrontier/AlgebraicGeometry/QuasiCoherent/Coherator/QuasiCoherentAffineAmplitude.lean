module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Boundedness
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.TruncationTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-coherent sheaf has affine amplitude concentrated in degree zero

Let `X` be a scheme and let `M` be a quasi-coherent `𝒪_X`-module, viewed as an object of `D(𝒪_X)`
in degree zero. For every affine open `U ⊆ X` the hypercohomology `H^i(U, M)` vanishes unless
`i = 0`: in negative degrees because sections over an open are left exact, and in positive
degrees by Serre vanishing, [Stacks, Tag 01XB].

This is the hypothesis `Stacks.Duality.Coherator.AffineAmplitudeIn X 0 0` of [Stacks, Tag 0CSA],
discharged here for a quasi-coherent module in degree zero, which is the input Example
[Stacks, Tag 0CSB] and [Stacks, Tag 0CTD] need.

## Main results

* `Stacks.Duality.Coherator.isZero_homology_derivedSectionsLocallySmall_single_of_neg` — the
  negative-degree half, left exactness of sections.
* `Stacks.Duality.Coherator.isLE_zero_derivedSectionsLocallySmall_single` — the positive-degree
  half, Serre vanishing on an affine open.
* `Stacks.Duality.Coherator.affineAmplitudeIn_zero_zero_single` — the two halves combined.

## Implementation notes

The point of the file is a change of spelling, not a new argument. Serre vanishing is available in
this library as `AlgebraicGeometry.isZero_rightDerived_evaluation_of_isAffineOpen`, which is about
`Functor.rightDerived`, the `ℕ`-indexed classical right derived functor of sections computed from
an injective resolution. `Stacks.Duality.Coherator.AffineAmplitudeIn` is about the homology of
`Stacks.Duality.Coherator.derivedSectionsLocallySmall`, the total right derived functor of
sections on the whole unbounded derived category at the locally small model. The two are bridged
here by two general theorems of the library, instantiated at
`Stacks.Cohomology.sectionsFunctor`:

* `Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj`, the left t-exactness of an
  unbounded total right derived functor, gives the negative degrees with no hypothesis at all;
* `Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj`, which identifies the total right
  derived functor at a bounded below object with the bounded below right derived functor and so
  turns vanishing of the classical `R^pF` into an upper bound, gives the positive degrees.

Both are stated with `HasDerivedCategory` as a binder, so they apply at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` that the coherator vocabulary lives at; this
file declares no `HasDerivedCategory` instance of its own.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0CSB](https://stacks.math.columbia.edu/tag/0CSB)
* [Stacks Project, Tag 0CTD](https://stacks.math.columbia.edu/tag/0CTD)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Duality.Coherator

variable (X : Scheme.{u})

/-- **Sections over an open are left exact**, in the form needed below: the hypercohomology of a
quasi-coherent module placed in degree zero vanishes in negative degrees. No hypothesis on the
module or on the open is needed; this is the left t-exactness of an unbounded total right derived
functor, `Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj`. -/
theorem isZero_homology_derivedSectionsLocallySmall_single_of_neg (U : X.Opens) (M : X.Modules)
    (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj
      ((derivedSectionsLocallySmall X U).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj M))) :=
  Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
    (Stacks.Cohomology.sectionsFunctor X U)
    ((DerivedCategory.singleFunctor X.Modules 0).obj M) 0 i hi

/-- The classical higher right derived functors of sections over an affine open vanish on a
quasi-coherent module, in the `ℤ`-indexed spelling. This is
`AlgebraicGeometry.isZero_rightDerived_evaluation_of_isAffineOpen`, which is [Stacks, Tag 01XB],
transported along `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`. -/
private theorem isZero_rightDerivedPlus_sectionsFunctor_of_isAffineOpen (U : X.Opens)
    (hU : IsAffineOpen U) (M : X.Modules) [M.IsQuasicoherent] (p : ℤ) (hp : 0 < p) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X U).rightDerivedPlus p).obj M) := by
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _
    (show p = (p.toNat : ℤ) by omega) M]
  exact AlgebraicGeometry.isZero_rightDerived_evaluation_of_isAffineOpen X M U hU p.toNat
    (by omega)

/-- **Serre vanishing in the hypercohomology spelling**, [Stacks, Tag 01XB]: the
hypercohomology of a quasi-coherent module placed in degree zero over an affine open vanishes in
positive degrees.

The classical higher right derived functors of sections vanish on a quasi-coherent module over an
affine open, and `Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj` turns that into the
bound on the unbounded total right derived functor; the comparison it asks for is the invertibility
of the unit of `RΓ(U, -)` at a K-injective complex,
`Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective`. -/
theorem isLE_zero_derivedSectionsLocallySmall_single (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] :
    ((derivedSectionsLocallySmall X U).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)).IsLE 0 := by
  have h := Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj
    (Stacks.Cohomology.sectionsFunctor X U) (derivedSectionsLocallySmall X U)
    (derivedSectionsLocallySmallUnit X U)
    (fun I hI => have := hI
      Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
        (Stacks.Cohomology.sectionsFunctor X U) I)
    M 0 (isZero_rightDerivedPlus_sectionsFunctor_of_isAffineOpen X U hU M) 0
  simpa using h

/-- **A quasi-coherent module has affine amplitude in `[0, 0]`.** Placed in degree zero, a
quasi-coherent `𝒪_X`-module has hypercohomology over every affine open of `X` concentrated in
degree zero: this is the vanishing in negative degrees of
`Stacks.Duality.Coherator.isZero_homology_derivedSectionsLocallySmall_single_of_neg` together with
Serre vanishing ([Stacks, Tag 01XB]) in positive degrees.

It is the hypothesis of [Stacks, Tag 0CSA] at `a = b = 0`, which is what Example
[Stacks, Tag 0CSB] feeds that tag. -/
@[stacks 01XB "the vanishing in positive degrees, together with left exactness in negative \
  degrees, in the hypercohomology spelling of Coherator.AffineAmplitudeIn at the locally small \
  model"]
theorem affineAmplitudeIn_zero_zero_single (M : X.Modules) [M.IsQuasicoherent] :
    AffineAmplitudeIn X 0 0 ((DerivedCategory.singleFunctor X.Modules 0).obj M) := by
  intro U i hi
  rcases hi with h | h
  · exact isZero_homology_derivedSectionsLocallySmall_single_of_neg X U.1 M i h
  · have := isLE_zero_derivedSectionsLocallySmall_single X U.1 U.2 M
    exact DerivedCategory.isZero_of_isLE _ 0 i h

end Stacks.Duality.Coherator

end
