module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedPullback

/-!
# Extension by zero of a perfect complex with closed support

Let `(X, 𝒪_X)` be a ringed space, let `j : U → X` be an open subspace and let `T ⊆ U` be a
subset closed in `X`. For an object `E` of the derived category of `𝒪_U`-modules whose
cohomology sheaves are supported on `T`, the two constructions `j_! E` and `Rj_* E` agree, and
if `E` is moreover perfect then the resulting object of the derived category of `𝒪_X`-modules
is perfect.

This is the object written `K' = R(V → X)_* K = R(V → X)_! K` in the proof of
[Stacks, Tag 0GEN], where `K` is the Koszul complex on functions cutting out `X \ U` inside the
affine open `V`.

## Main results

* `Stacks.Cohomology.ExtensionByZeroClosedSupport.isPerfect_jShriek_of_closedSupport`: the
  canonical map `j_! E ⟶ Rj_* E` is an isomorphism, and `j_! E` is perfect.

## Implementation notes

The two halves are [Stacks, Tag 08DF] part (2) and [Stacks, Tag 08DP]; what is new here is
their conjunction, which is what the source's `K'` is: perfectness is proved in Tag 08DP for
the derived pushforward, and it is Tag 08DF that lets the same object be named as an extension
by zero. Only the conjunction gives `j_! E` perfect, which is the description the proof of
[Stacks, Tag 0GEN] goes on to use.

The perfect-complex vocabulary is the ringed-space one, `AlgebraicGeometry.RingedSpace.IsPerfect`
over `StrictlyPerfect.OXMod`, because that is the vocabulary of both inputs; no other spelling of
perfectness has either of them. The closed subset is taken in `X`, as in Tag 08DF and in the
source, and the subset of the open subspace that Tag 08DP asks for is its preimage, whose image
in `X` is again `T` because `T ⊆ U`.

Tag 08DF is used through
`ClosedSupportPerfect.isIso_extensionByZeroToDerivedPushforward_app_of_supported'`,
the form taking the right-derived-functor datum explicitly: the restriction of the structure
sheaf of rings to the open subspace has two definitionally equal but semireducible spellings,
`ExtensionByZeroModules.resRing U (structureSheafRing X)` and
`structureSheafRing (X.restrict U.isOpenEmbedding)`, and instance search does not bridge them.

## References

* [Stacks, Tag 0GEP](https://stacks.math.columbia.edu/tag/0GEP)
* [Stacks, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.PushforwardRestriction (extensionByZeroToDerivedPushforward)
open Stacks.Cohomology.ClosedSupportPerfect
  (isIso_extensionByZeroToDerivedPushforward_app_of_supported'
   isPerfect_derivedPushforward_of_closedSupport)

namespace Stacks.Cohomology.ExtensionByZeroClosedSupport

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.Functor.sheafPushforwardContinuous

/-- **The extension by zero of a perfect complex with closed support.** Let `j : U → X` be an
open subspace of a ringed space and let `T ⊆ U` be closed in `X`. If `E` is a perfect object of
the derived category of `𝒪_U`-modules whose cohomology sheaves are supported on `T`, then the
canonical map `j_! E ⟶ Rj_* E` is an isomorphism, and `j_! E` is a perfect object of the derived
category of `𝒪_X`-modules.

These are the two descriptions of the complex `K'` in the proof of [Stacks, Tag 0GEN]. -/
theorem isPerfect_jShriek_of_closedSupport
    (X : RingedSpace.{u, u}) (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U (structureSheafRing X))) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (αj : (jPush U (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U (structureSheafRing X)))
        (ComplexShape.up ℤ)))
    (E : DerivedCategory (SheafOfModules.{u} (resRing U (structureSheafRing X))))
    (hE : RingedSpace.IsPerfect (X := X.restrict U.isOpenEmbedding) E)
    (hET : AlgebraicGeometry.CohomologySupportedOn (resRing U (structureSheafRing X))
      ((fun x : Usp U ↦ x.1) ⁻¹' T) E) :
    IsIso ((extensionByZeroToDerivedPushforward (structureSheafRing X) U Rj αj).app E) ∧
      RingedSpace.IsPerfect (X := X)
        ((jShriek U (structureSheafRing X)).mapDerivedCategory.obj E) := by
  have hiso := isIso_extensionByZeroToDerivedPushforward_app_of_supported'
    (structureSheafRing X) U T hT hTU Rj αj hRj E hET
  refine ⟨hiso, ?_⟩
  -- The subset of the open subspace that Tag 08DP asks for, and the fact that its image is `T`.
  have himg : (X.ofRestrict U.isOpenEmbedding).hom.base ''
      ((fun x : (X.restrict U.isOpenEmbedding).carrier => x.1) ⁻¹' T) = T := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨⟨x, hTU hx⟩, hx, rfl⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact hy
  exact (isPerfect_derivedPushforward_of_closedSupport X U
    ((fun x : (X.restrict U.isOpenEmbedding).carrier => x.1) ⁻¹' T) (by rwa [himg])
    Rj αj (hRj := hRj) E hE hET).of_iso
    (asIso ((extensionByZeroToDerivedPushforward (structureSheafRing X) U Rj αj).app E)).symm

/-- **Stacks 0GEP.** Let `j : U → X` be an open subspace of a ringed space and let `T ⊆ U` be
closed in `X`. For a perfect object `E` of the derived category of `𝒪_U`-modules whose cohomology
sheaves are supported on `T`, the object `K' = j_! E` satisfies

* `j_! E = Rj_* E`: the canonical map `j_! E ⟶ Rj_* E` is an isomorphism ([Stacks, Tag 08DF]);
* `K'` is a perfect object of `D(𝒪_X)` ([Stacks, Tag 08DP]);
* `K'` is supported on the closed set `T`;
* `K'` restricts to `E` on `U`.

These are the assertions made of the complex `K' = R(V → X)_* K = R(V → X)_! K` in the proof of
[Stacks, Tag 0GEN], where `K` is the Koszul complex on functions cutting out `T = X \ U'`
inside the affine open `V`. -/
@[stacks 0GEP]
theorem isPerfect_jShriek_of_closedSupport_and_restrict
    (X : RingedSpace.{u, u}) (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U (structureSheafRing X))) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (αj : (jPush U (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U (structureSheafRing X)))
        (ComplexShape.up ℤ)))
    (E : DerivedCategory (SheafOfModules.{u} (resRing U (structureSheafRing X))))
    (hE : RingedSpace.IsPerfect (X := X.restrict U.isOpenEmbedding) E)
    (hET : AlgebraicGeometry.CohomologySupportedOn (resRing U (structureSheafRing X))
      ((fun x : Usp U ↦ x.1) ⁻¹' T) E) :
    IsIso ((extensionByZeroToDerivedPushforward (structureSheafRing X) U Rj αj).app E) ∧
      RingedSpace.IsPerfect (X := X)
        ((jShriek U (structureSheafRing X)).mapDerivedCategory.obj E) ∧
      AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) T
        ((jShriek U (structureSheafRing X)).mapDerivedCategory.obj E) ∧
      Nonempty ((jStar U (structureSheafRing X)).mapDerivedCategory.obj
        ((jShriek U (structureSheafRing X)).mapDerivedCategory.obj E) ≅ E) := by
  obtain ⟨h₁, h₂⟩ := isPerfect_jShriek_of_closedSupport X U T hT hTU Rj αj hRj E hE hET
  let := isIso_jShriekAdjunction_unit U (structureSheafRing X)
  exact ⟨h₁, h₂, Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_jShriek
    (structureSheafRing X) U T E hET,
    ⟨(Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedCompIsoId
      (jShriek U (structureSheafRing X)) (jStar U (structureSheafRing X))
      (asIso (jShriekAdjunction U (structureSheafRing X)).unit).symm).app E⟩⟩

end Stacks.Cohomology.ExtensionByZeroClosedSupport

end
