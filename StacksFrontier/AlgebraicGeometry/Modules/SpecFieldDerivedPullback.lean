module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-!
# Derived pullback along a morphism of spectra of fields

Pullback of sheaves of modules along `Spec l ⟶ Spec k`, for a homomorphism of fields, is exact
(`AlgebraicGeometry.SpecField.preservesFiniteLimits_pullback`).  Hence its derived pullback is
degreewise pullback, it commutes with the homology functors of the derived categories, and the
dimension of the global sections of the homology is unchanged.

## Main definitions

* `AlgebraicGeometry.derivedHomologyMapIso` identifies the image under an exact functor of the
  homology of an object of the derived category with the homology of its image.
* `AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso` identifies the derived pullback of
  Tag 079W with degreewise pullback, for a morphism along which pullback is exact.

## Main results

* `AlgebraicGeometry.SpecField.finrank_derivedPullback`: for a homomorphism of fields the
  dimension over `l` of the `i`-th homology of the derived pullback equals the dimension over
  `k` of the `i`-th homology.  This is the fibrewise input to the base-change statement of Tag
  0BDI.

## Implementation notes

The identification of the derived pullback with degreewise pullback is uniqueness of left
derived functors: an exact functor inverts quasi-isomorphisms, so `F.mapDerivedCategory` with
`Functor.mapDerivedCategoryFactorsh` is itself a left derived functor of degreewise pullback,
and `CategoryTheory.Functor.leftDerivedUnique` compares it with the chosen one.

`derivedHomologyMapIso` is proved by choosing a complex representing the object, where the
comparison is `CategoryTheory.ShortComplex.mapHomologyIso` of the short complex in degree `i`,
and transporting along the two factorizations of the homology functors through `Q`.

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry

universe w₁ w₂ u

attribute [local instance] HasDerivedCategory.standard

/-- **An exact functor commutes with the homology of the derived category.**  The image under an
exact additive functor of the `i`-th homology of an object of the derived category is the `i`-th
homology of its image. -/
public def derivedHomologyMapIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory C) (i : ℤ) :
    F.obj ((DerivedCategory.homologyFunctor C i).obj E) ≅
      (DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj E) := by
  let K := (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E
  let e := (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objObjPreimageIso E
  let hC := DerivedCategory.homologyFunctor C i
  let hD := DerivedCategory.homologyFunctor D i
  let eH := hC.mapIso e.symm ≪≫ (DerivedCategory.homologyFunctorFactors C i).app K
  exact F.mapIso eH ≪≫ ((K.sc i).mapHomologyIso F).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors D i).app
      ((F.mapHomologicalComplex (.up ℤ)).obj K)).symm ≪≫
    hD.mapIso (asIso ((Functor.mapDerivedCategoryFactors F).hom.app K)).symm ≪≫
    hD.mapIso (F.mapDerivedCategory.mapIso e)

namespace SpecField

/-- **For an exact pullback the derived pullback is degreewise pullback.**  Both are left derived
functors of degreewise pullback followed by localization, so they are canonically isomorphic.

The two models of the derived categories are binders rather than the file's pinned
`HasDerivedCategory.standard`: nothing in the argument looks at the model. -/
public def derivedPullbackMapDerivedIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
    [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]
    [(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))] :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ≅ (modulePullback
      f).mapDerivedCategory :=
  let F := modulePullback f
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)
  let α := Functor.mapDerivedCategoryFactorsh F
  have : F.mapDerivedCategory.IsLeftDerivedFunctor α.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory α
  Functor.leftDerivedUnique F.mapDerivedCategory
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f) α.hom W

section

variable {R S : CommRingCat.{u}} (hR : IsField R) (hS : IsField S) (φ : R ⟶ S)

include hR hS in
/-- Degreewise pullback along a morphism of spectra of fields is left exact, in the
ringed-space spelling that the derived machinery of Tag 079W consumes. -/
public theorem preservesFiniteLimits_modulePullback_SpecMap :
    PreservesFiniteLimits (modulePullback (Spec.map φ).toLRSHom.toShHom) :=
  preservesFiniteLimits_pullback hR hS φ

/-- Degreewise pullback along a morphism of spectra of fields is right exact. -/
public theorem preservesFiniteColimits_modulePullback_SpecMap :
    PreservesFiniteColimits (modulePullback (Spec.map φ).toLRSHom.toShHom) :=
  preservesFiniteColimits_pullback φ

include hR hS in
/-- **The derived pullback along a morphism of spectra of fields exists.**  Degreewise pullback
is exact, so the class of all complexes is a resolving datum for it. -/
public theorem hasLeftDerivedFunctor_pullbackOnHomotopy_SpecMap :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (Spec.map
      φ).toLRSHom.toShHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) (ComplexShape.up ℤ)) :=
  have := preservesFiniteLimits_modulePullback_SpecMap hR hS φ
  have := preservesFiniteColimits_modulePullback_SpecMap φ
  pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
    (Spec.map φ).toLRSHom.toShHom

include hR hS in
/-- **The dimension of the homology of a derived fibre is unchanged under extension of the
field.**  For a homomorphism of fields `R ⟶ S`, the `i`-th homology of the derived pullback has
the same dimension over `S` as the `i`-th homology has over `R`.  This is the fibrewise input
to the base-change formula of Tag 0BDI. -/
public theorem finrank_derivedPullback
    [(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (Spec.map
      φ).toLRSHom.toShHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Spec R).Modules) (i : ℤ) :
    Module.finrank S ((moduleSpecΓFunctor (R := S)).obj
        ((DerivedCategory.homologyFunctor (Spec S).Modules i).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (Spec.map
            φ).toLRSHom.toShHom).obj E))) =
      Module.finrank R ((moduleSpecΓFunctor (R := R)).obj
        ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E)) := by
  have hlim := preservesFiniteLimits_modulePullback_SpecMap hR hS φ
  have hcolim := preservesFiniteColimits_modulePullback_SpecMap φ
  let Eκ := (DerivedCategory.homologyFunctor (Spec R).Modules i).obj E
  let eD := derivedPullbackMapDerivedIso (Spec.map φ).toLRSHom.toShHom
  let FF : (Spec R).Modules ⥤ (Spec S).Modules :=
    modulePullback (Spec.map φ).toLRSHom.toShHom
  have hadd : FF.Additive := modulePullback_additive _
  have hlim' : PreservesFiniteLimits FF := hlim
  have hcolim' : PreservesFiniteColimits FF := hcolim
  let eF := derivedHomologyMapIso FF E i
  let eΓ : (moduleSpecΓFunctor (R := S)).obj
      ((DerivedCategory.homologyFunctor (Spec S).Modules i).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (Spec.map
          φ).toLRSHom.toShHom).obj E)) ≅
      (ModuleCat.extendScalars (CommRingCat.Hom.hom φ)).obj
        ((moduleSpecΓFunctor (R := R)).obj Eκ) :=
    (moduleSpecΓFunctor (R := S)).mapIso
        ((DerivedCategory.homologyFunctor (Spec S).Modules i).mapIso (eD.app E)) ≪≫
      (moduleSpecΓFunctor (R := S)).mapIso eF.symm ≪≫
      pullbackSectionsIso hR φ Eκ
  exact eΓ.toLinearEquiv.finrank_eq.trans (finrank_extendScalars hR hS φ _)

end

end SpecField

end AlgebraicGeometry

end
