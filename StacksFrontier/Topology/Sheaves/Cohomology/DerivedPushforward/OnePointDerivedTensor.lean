module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointSectionsMonoidal

/-!
# The one-point identification is monoidal on derived categories

Let `R` be a commutative ring and let `({*}, R)` be the one-point ringed space.  Sections on the
whole space identify `Γ({*}, 𝒪)`-modules with sheaves of modules there, and that identification
carries the tensor product of modules to the tensor product of sheaves of modules
(`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorIso`).  Both tensor products admit
K-flat resolutions in either variable, so both descend to the unbounded derived categories, and
the abelian comparison descends with them:

`E(x ⊗^𝐋_{Γ({*}, 𝒪)} y) ≅ E x ⊗^𝐋_𝒪 E y`

for `E` the identification read on derived categories, at an arbitrary pair of objects of
`D(Γ({*}, 𝒪))`, with no boundedness and no flatness hypothesis.  Both derived tensor products
are written in the K-flat-descent spelling `CochainComplex.KFlatBifunctor.derivedBifunctor`.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedTensorObjIso` — the comparison at a
  pair of objects of `D(Γ({*}, 𝒪))`, `E(x ⊗^𝐋 y) ≅ E x ⊗^𝐋_𝒪 E y`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CochainComplex.KFlatBifunctor
open Stacks.Cohomology.GlobalKunneth
open Stacks.SheafOfModules.Tensor

universe u

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-! ### The identification at the spelling of the ringed-site tensor product -/

/-- **The one-point identification `Mod(Γ({*}, 𝒪)) ⥤ Mod(𝒪_{({*}, R)})`**, with its target
spelled by the sheaf of rings `Stacks.SheafOfModules.Tensor.ringSheaf` that the ringed-site
tensor product is stated over: the functor of
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence R`. -/
abbrev onePointIdentificationFunctor :
    ModuleCat.{u} (baseRing (onePointRingedSpace R)) ⥤
      SheafOfModules.{u} (ringSheaf.{u, u, u} (onePointRingedSpace R).sheaf) :=
  Equivalence.functor (D := SheafOfModules.{u} (ringSheaf.{u, u, u} (onePointRingedSpace R).sheaf))
    (onePointSectionsEquivalence R)

/-- **Sections on the whole space of `({*}, R)`**, at the spelling of
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointIdentificationFunctor`: the quasi-inverse of
the one-point identification. -/
abbrev onePointIdentificationInverse :
    SheafOfModules.{u} (ringSheaf.{u, u, u} (onePointRingedSpace R).sheaf) ⥤
      ModuleCat.{u} (baseRing (onePointRingedSpace R)) :=
  Equivalence.inverse (D := SheafOfModules.{u} (ringSheaf.{u, u, u} (onePointRingedSpace R).sheaf))
    (onePointSectionsEquivalence R)

/-- The one-point identification is additive, at the spelling of the ringed-site tensor
product. -/
instance onePointIdentificationFunctor_additive :
    (onePointIdentificationFunctor R).Additive :=
  onePointSectionsEquivalence_functor_additive R

/-- Sections on the whole space are additive, at the spelling of the ringed-site tensor
product. -/
instance onePointIdentificationInverse_additive :
    (onePointIdentificationInverse R).Additive :=
  onePointSectionsEquivalence_inverse_additive R

/-- The one-point identification is left exact, at the spelling of the ringed-site tensor
product. -/
instance onePointIdentificationFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (onePointIdentificationFunctor R) :=
  inferInstanceAs (PreservesFiniteLimits (onePointSectionsEquivalence R).functor)

/-- The one-point identification is right exact, at the spelling of the ringed-site tensor
product. -/
instance onePointIdentificationFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (onePointIdentificationFunctor R) :=
  inferInstanceAs (PreservesFiniteColimits (onePointSectionsEquivalence R).functor)

/-! ### The two K-flat localizations on the one-point ringed space -/

/-- **`D(Mod(𝒪_{({*}, R)}))` is the localization of the K-flat complexes of `𝒪`-modules at the
quasi-isomorphisms.** -/
instance onePointKFlatQ_isLocalization :
    (kFlatQ (sheafTensor.{u, u, u, u, u} (onePointRingedSpace R).sheaf)).IsLocalization
      (kFlatQuasiIso (sheafTensor.{u, u, u, u, u} (onePointRingedSpace R).sheaf)) :=
  Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization
    (C := TopologicalSpace.Opens (onePointRingedSpace R).carrier) (onePointRingedSpace R).sheaf

/-- **`D(Mod(𝒪_{({*}, R)}))` is the localization of the complexes of `𝒪`-modules which are
K-flat in the first variable of `⊗_𝒪`.** -/
instance onePointKFlatQLeft_isLocalization :
    (kFlatQLeft (sheafTensor.{u, u, u, u, u} (onePointRingedSpace R).sheaf)).IsLocalization
      (kFlatQuasiIsoLeft (sheafTensor.{u, u, u, u, u} (onePointRingedSpace R).sheaf)) :=
  Stacks.DerivedTensor.RingedSite.kFlatQLeft_isLocalization
    (C := TopologicalSpace.Opens (onePointRingedSpace R).carrier) (onePointRingedSpace R).sheaf

/-! ### The comparison on the derived categories -/

/-- **The one-point identification is monoidal on derived categories**:

`E(x ⊗^𝐋_{Γ({*}, 𝒪)} y) ≅ E x ⊗^𝐋_𝒪 E y`

at a pair of objects of `D(Γ({*}, 𝒪))`, for `E` the identification
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence` read on derived
categories. -/
def onePointDerivedTensorObjIso
    (x y : DerivedCategory (ModuleCat.{u} (baseRing (onePointRingedSpace R)))) :
    (onePointIdentificationFunctor R).mapDerivedCategory.obj
        (((derivedBifunctor
            (curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R))))).obj x).obj y) ≅
      ((derivedBifunctor (sheafTensor.{u, u, u, u, u} (onePointRingedSpace R).sheaf)).obj
          ((onePointIdentificationFunctor R).mapDerivedCategory.obj x)).obj
        ((onePointIdentificationFunctor R).mapDerivedCategory.obj y) :=
  derivedTransportObjIsoOfEquivalence
    (curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R))))
    (sheafTensor.{u, u, u, u, u} (onePointRingedSpace R).sheaf)
    (onePointSectionsEquivalence R)
    (onePointTensorIso R)
    (fun f N => onePointTensorIso_naturality_left R f N)
    (fun M {_ _} g => onePointTensorIso_naturality_right R M g)
    x y

end Stacks.Cohomology.DerivedSectionsOnAPoint

end
