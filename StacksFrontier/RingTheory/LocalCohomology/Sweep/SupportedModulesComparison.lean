module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived category of modules supported in a subset of the spectrum

Let `A` be a commutative ring and `T ⊆ Spec(A)` a subset. The `A`-modules with support in `T`
form a Serre subcategory `Mod_{A,T}` of `A`-modules (Tag 0EEZ), and the complexes of `A`-modules
whose cohomology modules lie in `Mod_{A,T}` form a strictly full saturated triangulated
subcategory `D_T(A)` of `D(A)`. This file constructs the canonical comparison functor
$$ D(\mathrm{Mod}_{A,T}) \longrightarrow D_T(A), $$
namely the functor induced on derived categories by the inclusion of the Serre subcategory,
lifted to `D_T(A)` using the fact that an exact functor commutes with cohomology.

Tag 0EF3 asserts that this comparison is an equivalence when `A` is Noetherian of finite Krull
dimension and `T` is stable under specialization. That theorem is **not** proved here; see the
implementation notes for what it is waiting on.

## Main definitions

* `Stacks.LocalCohomology.derivedCategorySupportedIn` — the full subcategory `D_T(A)` of `D(A)`
  of objects with cohomology supported in `T`.
* `Stacks.LocalCohomology.supportedModulesComparison` — the comparison functor
  `D(Mod_{A,T}) ⥤ D_T(A)`.

## Implementation notes

The inclusion `Mod_{A,T} ⥤ Mod_A` is exact because the subcategory is a weak Serre class, which
gives the two `PreservesFiniteLimits`/`PreservesFiniteColimits` instances below; the induced
functor on derived categories therefore commutes with the cohomology functors
(`StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso`), and that is exactly
what is needed to see that it lands in `D_T(A)`.

Neither Noetherianity nor specialization stability is needed for the construction, so the
definitions are given for an arbitrary commutative ring and subset of the spectrum. The ring
universe `u` and the module universe `v` are independent.

The source's proof of the equivalence rests on two results that are not yet available in this
library: Tag 0EF2 (the bounded-below comparison `D^+(Mod_{A,T}) ⥤ D^+_T(A)` is an equivalence,
which needs the structure of injective modules over a Noetherian ring, Tag 08YA) and Tag 0DXC
(local cohomology with closed support vanishes above the dimension of the ring, giving `H^0_T`
bounded cohomological dimension). Given those, Tag 0EF1 — proved in
`StacksFrontier/RingTheory/LocalCohomology/Sweep/ClosedSupportColimit.lean` — reduces the unbounded
statement to the bounded-below one by a truncation argument.

## References

* [Stacks Project, Tag 0EF3](https://stacks.math.columbia.edu/tag/0EF3)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- The full subcategory of `D(A)` consisting of objects whose cohomology modules are supported
in `T`. -/
abbrev derivedCategorySupportedIn (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :=
  (DerivedCategoryB.derivedCategoryB
    (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A))).FullSubcategory

/-- The canonical functor from the derived category of modules supported in `T` to the
subcategory of `D(A)` consisting of objects with cohomology supported in `T`. -/
def supportedModulesComparison (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    DerivedCategory (ModulesSupportedIn.{u, v} A T) ⥤ derivedCategorySupportedIn.{u, v} A T :=
  (DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A))).lift
    (supportModuleProperty A T).ι.mapDerivedCategory (fun K i ↦
      (supportModuleProperty A T).prop_of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (supportModuleProperty A T).ι i).app K).symm
        ((supportModuleProperty A T).prop_ι_obj
          ((homologyFunctor (ModulesSupportedIn.{u, v} A T) i).obj K)))

end Stacks.LocalCohomology
