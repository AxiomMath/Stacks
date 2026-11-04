module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.MixedDerivedTensorOnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageExactness
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback along a morphism of finite tor dimension

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces such that `𝒪_X` has tor amplitude
in `[-d, ∞)` as a module over `h⁻¹𝒪_Y`. Then `Lh^*` carries an object of `D(𝒪_Y)` whose
cohomology vanishes below `a` to one whose cohomology vanishes below `a - d`. If `𝒪_X` has finite
tor dimension over `h⁻¹𝒪_Y`, then `Lh^*` commutes with derived internal hom out of a
pseudo-coherent object into a locally bounded below one.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.inverseImageRingedSite`: the ringed site
  `(X, h⁻¹𝒪_Y)`.
* `Stacks.Cohomology.DerivedInternalHomPullback.structureSheafOverInverseImage`: `𝒪_X` as an
  `h⁻¹𝒪_Y`-module.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.hasDerivedPullbackAmplitude_of_hasTorAmplitudeGE`:
  `Lh^*` lowers cohomological lower bounds by at most `d`.
* `isIso_derivedPullbackSheafHomMap_of_hasFiniteTorDimensionOverInverseImage`:
  `Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)` is an isomorphism for `K` pseudo-coherent and `M`
  locally bounded below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.MixedDerivedTensor StacksPullbackFactorization
open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- The ringed site `(X, h⁻¹𝒪_Y)`: the site of opens of `X` with the inverse image of the
structure sheaf of `Y`. -/
abbrev inverseImageRingedSite : AlgebraicGeometry.RingedSite.{u, u, u} where
  C := Opens X.carrier
  J := Opens.grothendieckTopology X.carrier
  O := invRing (ringedToposSiteHom h)

/-- `⊗_{h⁻¹𝒪_Y}` is additive in its first variable. -/
local instance sheafTensorInverseImageAdditive :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (invRing (ringedToposSiteHom h))).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive
    (J := Opens.grothendieckTopology X.carrier) _

/-- `F ⊗_{h⁻¹𝒪_Y} -` is additive. -/
local instance sheafTensorInverseImageObjAdditive
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (invRing (ringedToposSiteHom h)))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (invRing (ringedToposSiteHom h))).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
    (J := Opens.grothendieckTopology X.carrier) _ M

/-- The total complexes `Tot(K ⊗_{h⁻¹𝒪_Y} L)` exist. -/
local instance hasMapBifunctorSheafTensorInverseImage
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (invRing (ringedToposSiteHom h)))) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing (ringedToposSiteHom h)))
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := Opens.grothendieckTopology X.carrier) _ K L

/-- `𝒪_X` as a module over `h⁻¹𝒪_Y`, through `h^♯ : h⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[ega "0 4.3.1"]
abbrev structureSheafOverInverseImage :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (invRing (ringedToposSiteHom h))) :=
  (restrictToInvRing (ringedToposSiteHom h)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (ToposBridge.ringedTopos X).O))

/-- `𝒪_X` placed in degree zero, as an object of `D(h⁻¹𝒪_Y)`. -/
abbrev structureSheafOverInverseImageObject :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (invRing (ringedToposSiteHom h)))) :=
  (DerivedCategory.singleFunctor _ 0).obj (structureSheafOverInverseImage h)

/-- **`𝒪_X` has finite tor dimension over `h⁻¹𝒪_Y`**: as a module over `h⁻¹𝒪_Y` through
`h^♯ : h⁻¹𝒪_Y ⟶ 𝒪_X`, placed in degree zero, it has tor amplitude in some interval, for the
derived tensor product of the ringed site `(X, h⁻¹𝒪_Y)` (Tag 08FZ). -/
def HasFiniteTorDimensionOverInverseImage : Prop :=
  Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (inverseImageRingedSite h))
    (structureSheafOverInverseImageObject h)

/-- Sheafification of presheaves of abelian groups on the site of opens of a space. -/
local instance hasSheafifyRingedToposSpace (Z : RingedSpace.{u, u}) :
    HasSheafify (ToposBridge.ringedTopos Z).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u})

/-- The weak equivalences of presheaves of abelian groups on the site of opens of a space are
the locally bijective maps. -/
local instance wEqualsLocallyBijectiveRingedToposSpace (Z : RingedSpace.{u, u}) :
    (ToposBridge.ringedTopos Z).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- Forgetting commutativity preserves sheaves on the site of opens of a space. -/
local instance hasSheafComposeRingedToposSpace (Z : RingedSpace.{u, u}) :
    (ToposBridge.ringedTopos Z).J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstanceAs ((Opens.grothendieckTopology Z.carrier).HasSheafCompose
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The derived inverse image `Lh⁻¹ : D(𝒪_Y) ⥤ D(h⁻¹𝒪_Y)` exists. -/
local instance hasLeftDerivedFunctorPullbackOnHomotopyInverseImage :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
        (auxHomG (ringedToposSiteHom h))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ToposBridge.ringedTopos Y).O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (auxHomG (ringedToposSiteHom h)) (isMorphismOfSites h)

/-- **The derived inverse image `Lh⁻¹` preserves lower bounds on cohomology.** -/
theorem isGE_derivedPullback_auxHomG
    (N : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ToposBridge.ringedTopos Y).O))) (a : ℤ)
    (hN : N.IsGE a) :
    ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback
      (auxHomG (ringedToposSiteHom h))).obj N).IsGE a := by
  have := Stacks.Sheaves.InverseImageExactness.preservesFiniteLimits_pullbackTopos_auxHomG
    (ringedToposSiteHom h) (isMorphismOfSites h)
  have := Stacks.Sheaves.InverseImageExactness.preservesFiniteColimits_pullbackTopos_auxHomG
    (ringedToposSiteHom h)
  exact Stacks.Cohomology.CohomologicalDescent.isGE_derivedPullback_obj
    (auxHomG (ringedToposSiteHom h)) N a hN

/-- A sheaf of `𝒪_X`-modules whose restriction of scalars to `h⁻¹𝒪_Y` is zero is zero. -/
theorem isZero_of_isZero_restrictToInvRing
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ToposBridge.ringedTopos X).O)}
    (hM : IsZero ((restrictToInvRing (ringedToposSiteHom h)).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  have e : (restrictToInvRing (ringedToposSiteHom h)).map (𝟙 M) =
      (restrictToInvRing (ringedToposSiteHom h)).map 0 := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact hM.eq_of_src _ _
  ext U x
  exact congrArg (fun k => k.val.app U x) e

/-- **Restriction of scalars along `h⁻¹𝒪_Y ⟶ 𝒪_X` reflects lower bounds on cohomology.** -/
theorem isGE_of_isGE_derivedRestrictTensor
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ToposBridge.ringedTopos X).O))) (a : ℤ)
    (hK : ((derivedRestrictTensor (ringedToposSiteHom h)).obj K).IsGE a) : K.IsGE a := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  intro i hi
  exact isZero_of_isZero_restrictToInvRing h ((hK i hi).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (restrictToInvRing (ringedToposSiteHom h)) i).app K).symm)

/-- **`Lh^*` along a morphism of finite tor dimension has bounded amplitude.** If `𝒪_X` has tor
amplitude in `[-d, ∞)` over `h⁻¹𝒪_Y`, then `Lh^*` carries an object of `D(𝒪_Y)` whose cohomology
vanishes below `a` to one whose cohomology vanishes below `a - d`. -/
theorem hasDerivedPullbackAmplitude_of_hasTorAmplitudeGE {d : ℤ}
    (hT : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (inverseImageRingedSite h))
      (structureSheafOverInverseImageObject h) (-d)) :
    HasDerivedPullbackAmplitude h d := by
  intro N a hN
  have hW := isGE_derivedPullback_auxHomG h N a hN
  let E' := (derivedRestrictTensor (ringedToposSiteHom h)).obj
    (Stacks.DerivedTensor.RingedSite.unitObject (Stacks.SheafOfModules.ringedSite X.sheaf))
  let eE : E' ≅ structureSheafOverInverseImageObject h :=
    ((restrictToInvRing (ringedToposSiteHom h)).mapDerivedCategorySingleFunctor 0).app _
  have hE := Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE.of_iso hT eE
  have hTen := Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (inverseImageRingedSite h)) E'
    ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback
      (auxHomG (ringedToposSiteHom h))).obj N) (-d) a hE hW
  let e : ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (inverseImageRingedSite h)).tensor.obj E').obj
        ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback
          (auxHomG (ringedToposSiteHom h))).obj N) ≅
      (derivedRestrictTensor (ringedToposSiteHom h)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj N) :=
    ((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso
        (inverseImageRingedSite h)).app E').app _ ≪≫
      ((derivedMixedTensorIso h).app
        (Stacks.DerivedTensor.RingedSite.unitObject (Stacks.SheafOfModules.ringedSite X.sheaf),
          N)).symm ≪≫
      (derivedRestrictTensor (ringedToposSiteHom h)).mapIso
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).leftUnitIso
          (Stacks.SheafOfModules.ringedSite X.sheaf)
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj N))
  rw [show a - d = -d + a by ring]
  exact isGE_of_isGE_derivedRestrictTensor h _ _ (DerivedCategory.TStructure.t.isGE_of_iso e _)

section Clause3

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **Pullback of a derived internal hom along a morphism of finite tor dimension.** Let
`h : X ⟶ Y` be a morphism of ringed spaces such that `𝒪_X` has finite tor dimension over
`h⁻¹𝒪_Y`. For a pseudo-coherent `K ∈ D(𝒪_Y)` and a locally bounded below `M ∈ D(𝒪_Y)`, the
canonical map `Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)` of Tag 08I3 is an isomorphism. -/
@[stacks 0GM7 "clause (3)"]
theorem isIso_derivedPullbackSheafHomMap_of_hasFiniteTorDimensionOverInverseImage
    (hh : HasFiniteTorDimensionOverInverseImage h)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hK : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := Y) K)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hM : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow Y M) :
    IsIso (derivedPullbackSheafHomMap h K M) := by
  obtain ⟨a, b, hab⟩ := hh
  have hT := Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_hasTorAmplitude _ _
    a b hab
  rw [← neg_neg a] at hT
  exact isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_amplitude h
    (hasDerivedPullbackAmplitude_of_hasTorAmplitudeGE h hT) K hK M hM

end Clause3

end Stacks.Cohomology.DerivedInternalHomPullback

end
