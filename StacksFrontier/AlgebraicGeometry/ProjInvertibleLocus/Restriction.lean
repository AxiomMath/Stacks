module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic

/-!
# The restricted site and the open subscheme agree on modules

Let `X` be a scheme and `U` an open of `X`. There are two ways to restrict a sheaf of
`𝒪_X`-modules to `U`:

* `SheafOfModules.over`, the pushforward to the restricted site `Over U` of `Opens ↥X` over the
  sheaf of rings `𝒪_X.over U`; and
* `AlgebraicGeometry.Scheme.Modules.pullback U.ι` (equivalently
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`), on the site `Opens ↥U.toScheme` of
  the open subscheme.

The two agree, by Mathlib's `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. This file
records the two consequences that a statement phrased on one side needs in order to be used on
the other: triviality, hence invertibility, transports, and so does invertibility of a morphism.

Both directions of Tag 01MU's goodness condition need this, because Tag 01MS and Tag 01MU's own
trivializations are naturally constructed on the restricted site — the sections of a sheaf on
`Over U` over an object `V ⟶ U` are literally the sections over `V`, with the untwisted scalar
action — whereas Tag 01MU states invertibility on the open subscheme.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit`: a module trivial
  on the restricted site has trivial restriction to the open subscheme.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.pullbackIsoUnitOfOverIsoUnit`: the same in the
  `AlgebraicGeometry.Scheme.Modules.pullback` spelling, as a named isomorphism `U.ι^*M ≅ 𝒪_U`.
  This is the bridge an inverse-image statement needs, the trivialisations this repository
  produces all living on the restricted site; `pullbackIsoUnitOfOverIsoUnit_hom` splits it into
  its two factors so that a consumer can read it on sections.

## Main results

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_restrictFunctor_of_iso_unit` and
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_pullback_of_iso_unit`: a module
  trivial on the restricted site has invertible restriction to the open subscheme.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isIso_restrictFunctor_map_of_isIso_over` and
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isIso_pullback_map_of_isIso_over`: a morphism
  whose restriction to the restricted site is an isomorphism restricts to an isomorphism on the
  open subscheme.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U` is the natural isomorphism
`overFunctor 𝒪_X U ⋙ (overEquiv U).functor ≅ restrictFunctor U.ι`, and
`TopologicalSpace.Opens.sheafOfModulesEquivOverUnit` says the equivalence takes the unit object
to the unit object (it is `Iso.refl`). Composing the two is all that is needed; no sections are
computed anywhere in this file.

The morphism statement goes through `CategoryTheory.NatIso.isIso_map_iff`, which transports
`IsIso (F.map φ)` along a natural isomorphism of functors. Writing the conjugation out by hand
instead does not work: `AlgebraicGeometry.Scheme.Modules` is a `def` carrying its own `Category`
instance, so `rw` with the naturality square of `overFunctorEquiv U` reports that the target is
"not type-correct under the `implicit` transparency level" — the two `Category` instances on
`X.Modules` and on `SheafOfModules X.ringCatSheaf` are `rfl`-equal but not interchangeable at
that transparency.

The triviality hypotheses are stated as explicit `Iso` arguments rather than as `IsIso`
instances, for the same reason: the caller holds a constructed isomorphism, and asking instance
search to rediscover `IsIso` of its `hom` fails across the `Scheme.Modules` `def`.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}} (U : X.Opens)

/-- The restriction of a module to the open subscheme `U` is its restriction to the site
`Over U`, read through `AlgebraicGeometry.Scheme.Modules.overEquiv`. -/
noncomputable def restrictIsoOverEquiv (M : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      (Scheme.Modules.overEquiv U).functor.obj (M.over U) :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm

/-- A module trivial on the restricted site of `U` restricts to a trivial module on the open
subscheme `U`. -/
noncomputable def restrictIsoUnitOfOverIsoUnit (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  restrictIsoOverEquiv U M ≪≫ (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf

/-- A module trivial on the restricted site of `U` has invertible restriction to the open
subscheme `U`, in the `restrictFunctor` spelling. -/
theorem isInvertible_restrictFunctor_of_iso_unit (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
      ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
  Stacks.InvertibleLocallyFree.isInvertible_of_iso_unit _ _ (restrictIsoUnitOfOverIsoUnit U M e)

/-- **A module trivial on the restricted site of `U` has trivial inverse image along `U.ι`**, as
a named isomorphism `U.ι^*M ≅ 𝒪_U`.

This is the bridge between the two packagings of "restrict to `U`" in the direction a consumer
phrased on the *open subscheme* needs: `SheafOfModules.over` is the restricted site `Over U`,
which is where every trivialisation this repository produces lives, while
`AlgebraicGeometry.Scheme.Modules.pullback U.ι` is what an inverse-image statement is stated at.
`restrictIsoUnitOfOverIsoUnit` crosses the first gap and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` the second, and the unit object of
the open subscheme is the target of both. -/
noncomputable def pullbackIsoUnitOfOverIsoUnit (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    restrictIsoUnitOfOverIsoUnit U M e

/-- The trivialisation of the inverse image is the comparison of the two packagings followed by
the trivialisation on the restricted site. -/
theorem pullbackIsoUnitOfOverIsoUnit_hom (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (pullbackIsoUnitOfOverIsoUnit U M e).hom =
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M ≫
        (restrictIsoUnitOfOverIsoUnit U M e).hom :=
  rfl

/-- A module trivial on the restricted site of `U` has invertible pullback along the open
immersion `U.ι`. This is the form in which Tag 01MU states invertibility. -/
theorem isInvertible_pullback_of_iso_unit (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback U.ι).obj M) :=
  Stacks.InvertibleLocallyFree.isInvertible_of_iso_unit _ _
    (pullbackIsoUnitOfOverIsoUnit U M e)

variable {M N : X.Modules}

/-- A morphism whose restriction to the restricted site of `U` is an isomorphism restricts to an
isomorphism on the open subscheme `U`. -/
theorem isIso_restrictFunctor_map_of_isIso_over (φ : M ⟶ N) (hφ : IsIso (φ.over U)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
  rw [← NatIso.isIso_map_iff (Scheme.Modules.overFunctorEquiv U) φ]
  have := hφ
  exact inferInstanceAs (IsIso ((Scheme.Modules.overEquiv U).functor.map (φ.over U)))

/-- A morphism whose restriction to the restricted site of `U` is an isomorphism has an
isomorphism for its pullback along the open immersion `U.ι`. This is the form in which Tag 01MU
states that the multiplication maps are isomorphisms. -/
theorem isIso_pullback_map_of_isIso_over (φ : M ⟶ N) (hφ : IsIso (φ.over U)) :
    IsIso ((Scheme.Modules.pullback U.ι).map φ) := by
  rw [← NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) φ]
  exact isIso_restrictFunctor_map_of_isIso_over U φ hφ

end Stacks.AlgebraicGeometry.ProjInvertibleLocus

end
