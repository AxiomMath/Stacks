module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional

/-!
# Restricting the derived direct image back along an open immersion

Let `j : U ⟶ X` be an open immersion of schemes. Restricting `Rj_* E` to `U` recovers `E`: the
square with `j` on both vertical sides and identities on top and bottom is Cartesian, so the
base-change isomorphism for derived direct images across a Cartesian square with open immersions
on the sides reads `Lj^* ∘ Rj_* ≅ id`.

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_modulePullback_of_isOpenImmersion` and
  `AlgebraicGeometry.preservesFiniteColimits_modulePullback_of_isOpenImmersion`: degreewise
  pullback of modules along an open immersion of schemes is exact.
* `AlgebraicGeometry.openDerivedPushforwardRestrictionIso`: the isomorphism `Lj^*(Rj_* E) ≅ E`
  for an open immersion of schemes.

## Implementation notes

The derived pullback `Lj^*` is the total left derived functor of degreewise pullback. Degreewise
pullback along an open immersion is exact, so `Lj^*` agrees with the functor that the exact
degreewise pullback induces on derived categories; that identification is
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso`, and it is what lets the base-change
isomorphism be read as a statement about `Lj^*`.

The two horizontal legs of the Cartesian square are identities, so the derived functors asked
for on those legs are the identity functors. Their structure maps are isomorphisms, assembled
from the comparison of the identity functor with the functor it induces on homotopy categories,
and a functor whose structure map inverts the quasi-isomorphisms is a right derived functor.

## References

* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedPushforwardUnit)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- Degreewise pullback of modules along an open immersion of schemes is left exact: it is
isomorphic to restriction, which is computed on sections.

The statement is in the ringed-space spelling of pullback that the derived machinery consumes;
the proof is carried out in the scheme spelling, where the exactness of restriction is already
an instance. -/
theorem preservesFiniteLimits_modulePullback_of_isOpenImmersion {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (modulePullback j.toLRSHom.toShHom) := by
  have h : PreservesFiniteLimits (Scheme.Modules.pullback j) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback j)
  exact h

/-- Degreewise pullback of modules along an open immersion of schemes is right exact, being a
left adjoint. -/
theorem preservesFiniteColimits_modulePullback_of_isOpenImmersion {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (modulePullback j.toLRSHom.toShHom) :=
  let : (modulePullback j.toLRSHom.toShHom).IsLeftAdjoint :=
    (modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).isLeftAdjoint
  inferInstance

/-- **Restriction to an open subscheme undoes the derived direct image.** For an open immersion
of schemes `j : U ⟶ X` the derived pullback of the derived direct image of an object of `D(𝒪_U)`
is that object again.

The square with `𝟙 U` on top and bottom and `j` on both sides is Cartesian with open immersions
on the vertical sides, so this is the base-change isomorphism of [Stacks, Tag 08FE] at that
square. -/
def openDerivedPushforwardRestrictionIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : DerivedCategory U.Modules) :
    (derivedPullback j.toLRSHom.toShHom).obj
      ((derivedPushforward j.toLRSHom.toShHom).obj E) ≅ E := by
  haveI := preservesFiniteLimits_modulePullback_of_isOpenImmersion j
  haveI := preservesFiniteColimits_modulePullback_of_isOpenImmersion j
  let Ur := U.toRingedSpace
  let jR : Ur ⟶ X.toRingedSpace := j.toLRSHom.toShHom
  let iR : Ur ⟶ Ur := 𝟙 Ur
  let P := modulePullback jR
  let Wi := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Ur))
    (ComplexShape.up ℤ)
  let Wj := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (ComplexShape.up ℤ)
  let RId := 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing Ur)))
  let eF : (modulePullback iR).mapHomotopyCategory (ComplexShape.up ℤ) ≅ 𝟭 _ :=
    Stacks.Homology.mapHomotopyCategoryIso
      ((Scheme.Modules.restrictFunctorIsoPullback (𝟙 U)).symm ≪≫ Scheme.Modules.restrictFunctorId)
      (ComplexShape.up ℤ) ≪≫ Functor.mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)
  let eG : (modulePushforward iR).mapHomotopyCategory (ComplexShape.up ℤ) ≅ 𝟭 _ :=
    Stacks.Homology.mapHomotopyCategoryIso (Scheme.Modules.pushforwardId U)
      (ComplexShape.up ℤ) ≪≫ Functor.mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)
  let eFD : DerivedCategory.Qh ⋙ RId ≅
      (modulePullback iR).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight eF.symm DerivedCategory.Qh
  let eGD : DerivedCategory.Qh ⋙ RId ≅
      (modulePushforward iR).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight eG.symm DerivedCategory.Qh
  have hbase : IsPullback iR iR jR jR :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [iR]⟩
  let _ : RId.IsRightDerivedFunctor eFD.inv Wi :=
    Functor.isRightDerivedFunctor_of_inverts Wi RId eFD
  let _ : RId.IsRightDerivedFunctor eGD.inv Wi :=
    Functor.isRightDerivedFunctor_of_inverts Wi RId eGD
  let _ : P.mapDerivedCategory.IsRightDerivedFunctor P.mapDerivedCategoryFactorsh.inv Wj :=
    Functor.isRightDerivedFunctor_of_inverts Wj P.mapDerivedCategory P.mapDerivedCategoryFactorsh
  let eBC := Stacks.Cohomology.derivedPushforwardRestrictIso jR iR jR iR hbase
    (derivedPushforward jR) RId RId P.mapDerivedCategory
    (derivedPushforwardUnit jR) eGD.inv eFD.inv P.mapDerivedCategoryFactorsh.inv
  exact (SpecField.derivedPullbackMapDerivedIso jR).app
    ((derivedPushforward jR).obj E) ≪≫ eBC.app E

end AlgebraicGeometry

end
