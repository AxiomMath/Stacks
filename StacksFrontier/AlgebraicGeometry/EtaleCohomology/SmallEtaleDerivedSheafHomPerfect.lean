module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ZariskiRingedSiteOfARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackSheafHomMonoidal

/-!
# Stacks 08JP, case (2): duality for a perfect object

Let `S` be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of ringed sites of
Stacks 08H7. Case (2) of Stacks 08JP asserts that for `E` perfect and `F` arbitrary in `D(𝒪_S)`
the canonical map `ε^* RSheafHom(E, F) ⟶ RSheafHom(ε^*E, ε^*F)` of Stacks 08JF is an isomorphism.
The route taken here is duality: a perfect object is dualizable for the derived tensor product,
a monoidal functor carries an internal Hom out of a dualizable object to one out of its image,
and `ε^*` is monoidal on derived categories.

## Main definitions

* `AlgebraicGeometry.SmallEtale.exactPairingDerivedDualZariski`: a perfect object `E` of
  `D(𝒪_S)` and its derived dual form an exact pairing for the derived tensor product
  `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` of the Zariski ringed topos.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal`:
  the map of Stacks 08JF at `ε` is invertible exactly when the comparison of the monoidal functor
  `ε^*` with the derived internal Hom is.
* `AlgebraicGeometry.SmallEtale.isIso_derivedPullbackSheafHomMap_of_isPerfect`: **Stacks 08JP,
  case (2).**

## Implementation notes

The exact pairing of Stacks 0FPC, `Stacks.SheafOfModules.exactPairingDerivedDual`, is stated for
the ringed space underlying `S` and for the re-seated monoidal structure
`Stacks.SheafOfModules.derivedMonoidalStructure`, whose tensor product is the derived tensor
product of Stacks 08DI on the nose. The small Zariski ringed site of `S` is the ringed site of
that ringed space by `rfl`
(`AlgebraicGeometry.Scheme.zariskiRingedSite_eq_ringedSite_toRingedSpace`), and the re-seated
structure is re-seated from `derivedMonoidal`, so the pairing is carried along the monoidal
identity functor `CategoryTheory.MonoidalCategory.reseatMonoidal`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallEtale

variable (S : Scheme.{u})

/-- **A perfect object of `D(𝒪_S)` is dualizable** for the derived tensor product of
Stacks 0FPT: the exact pairing of Stacks 0FPC between `E` and `E^∨ = RSheafHom(E, 𝒪_S)`, carried
from the re-seated monoidal structure of the ringed space of `S` to the structure
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` it is re-seated from, along the monoidal
identity functor. -/
@[instance_reducible]
def exactPairingDerivedDualZariski
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)))
    (hE : S.zariskiRingedSite.IsPerfect E) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal S.zariskiRingedTopos.O
    ExactPairing E (Stacks.SheafOfModules.derivedDual S.sheaf E) :=
  letI := Stacks.SheafOfModules.derivedMonoidalStructure S.sheaf
  letI := Stacks.SheafOfModules.exactPairingDerivedDual S.sheaf E hE
  @ExactPairing.map _ _ _ _ (Stacks.SheafOfModules.derivedMonoidalStructure S.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal S.zariskiRingedTopos.O) (𝟭 _)
    (@MonoidalCategory.reseatMonoidal _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal S.zariskiRingedTopos.O) _ _
      (Stacks.SheafOfModules.derivedTensorMonoidalIso S.sheaf)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso S.sheaf))
    E (Stacks.SheafOfModules.derivedDual S.sheaf E) _


attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.Scheme.zariskiRingedTopos

variable (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- **The map of Stacks 08JF at `ε` is invertible exactly when the comparison of the monoidal
functor `ε^*` is.** The canonical map `ε^* RSheafHom(E, F) ⟶ RSheafHom(ε^* E, ε^* F)` of
Stacks 08JF, for `ε` read on the model of the small étale site, is invertible if and only if the
comparison `AlgebraicGeometry.RingedSite.homComparisonMonoidal` of `ε^*` applied termwise, with
its monoidal structure `derivedPullbackSmallModelMonoidal`, is. -/
theorem isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal
    (E F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O))) :
    letI : (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived
      (toZariskiSmallModelHom B S hS)).Monoidal := derivedPullbackSmallModelMonoidal B S hS
    IsIso (RingedToposSiteHom.derivedPullbackSheafHomMap (toZariskiSmallModelHom B S hS)
        (isMorphismOfSites_toZariskiSmallModelHom_u B S hS) E F) ↔
      IsIso (RingedSite.homComparisonMonoidal (X := S.zariskiRingedSite)
        (Y := (smallModelRingedTopos B S hS).toRingedSite)
        (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived.{u} (toZariskiSmallModelHom B S hS))
        E F) :=
  RingedToposSiteHom.isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal
    (toZariskiSmallModelHom B S hS) (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)
    (kFlat_pullbackTopos_toZariskiSmallModelHom B S hS) E F

/-- **Stacks 08JP, case (2): `ε^*` commutes with `RSheafHom` out of a perfect object.** Let `S`
be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of ringed sites of Stacks 08H7,
read on the model of the small étale site. For `E` perfect and `F` arbitrary in `D(𝒪_S)`, the
canonical map `ε^* RSheafHom(E, F) ⟶ RSheafHom(ε^* E, ε^* F)` of Stacks 08JF,
`AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap`, is an isomorphism.

By `isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal` it is enough that the
comparison of the monoidal functor `ε^*` is invertible at `E`, and it is, `E` being one half of
the exact pairing `exactPairingDerivedDualZariski` with its derived dual. -/
@[stacks 08JP "case (2): E perfect, F arbitrary"]
theorem isIso_derivedPullbackSheafHomMap_of_isPerfect
    (E F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)))
    (hE : S.zariskiRingedSite.IsPerfect E) :
    IsIso (RingedToposSiteHom.derivedPullbackSheafHomMap (toZariskiSmallModelHom B S hS)
      (isMorphismOfSites_toZariskiSmallModelHom_u B S hS) E F) := by
  let : (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived
    (toZariskiSmallModelHom B S hS)).Monoidal := derivedPullbackSmallModelMonoidal B S hS
  let := exactPairingDerivedDualZariski S E hE
  exact (isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal S B hS E F).2
    (RingedSite.isIso_homComparisonMonoidal_of_exactPairing (X := S.zariskiRingedSite)
      (Y := (smallModelRingedTopos B S hS).toRingedSite) _ E
      (Stacks.SheafOfModules.derivedDual S.sheaf E) F)

end AlgebraicGeometry.SmallEtale

end
