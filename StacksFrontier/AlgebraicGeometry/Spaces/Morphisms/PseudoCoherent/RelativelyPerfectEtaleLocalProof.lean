module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEssSurjSquare
public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectBaseChangeStableProof
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.FpqcDescent

/-!
# Relative perfectness is étale local (the two consequences of Stacks 0DKQ used in 0DKW)

Let `f : X ⟶ Y` be a morphism of algebraic spaces, flat and locally of finite presentation.
This file proves the proposition `AlgebraicGeometry.Space.EtaleLocalRelativelyPerfect` that the
square step of Stacks 0DKW carries:

1. for an étale `a : X' ⟶ X`, the derived pullback `La^*K` of a `Y`-perfect `K` is `Y`-perfect
   along `a ≫ f`;
2. for an elementary distinguished square `(U ⊆ W, V ⟶ W)`, an object of `D(𝒪_W)` whose
   restrictions to `U` and to `V` are `Y`-perfect is `Y`-perfect.

## The argument

The pseudo-coherence clause of (1) is Stacks 08H4
(`AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullback`), and that of (2) is
checked on the étale charts of `W` which factor through `U` or through `V`
(`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_charts`): these cover `W` because the two pieces
cover `|W|` (`AlgebraicGeometry.Space.coversTop_edsChart`).

The Tor clause is read at the geometric stalks, as in the proof of Stacks 0DKT for an arbitrary
morphism (`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_pull_of_isPullback_general`):
`E` satisfies it exactly when every object of the small étale site of `X` is covered by objects
over which the stalks of a K-flat model of `E`, read over the stalk rings of `Y`, have Tor
amplitude in one interval (`exists_cover_stalkTorAmplitudeBound`,
`locallyHasFiniteTorDimension_of_cover_stalkTorAmplitudeBound`).  Along an étale `a` the stalk ring
map `𝒪_{X, a(x̄')} ⟶ 𝒪_{X', x̄'}` is bijective (Stacks 05V5 and 04NG), so the stalk of `La^*E`
at `x̄'`, read over `𝒪_{Y, f(a(x̄'))}`, is the stalk of `E` at `a(x̄')`
(`hasTorAmplitudeCanonical_restrictScalars_extendScalars_iff_of_isEtale`); the covers are moved
along `a` by `AlgebraicGeometry.Space.generate_mem_topology_chartsOver_of_cover` for (1) and by
`CategoryTheory.GrothendieckTopology.coversTop_sigma_subtype` for (2).  No quasi-coherence is
needed, and no base change: neither square of (1) nor of (2) is cartesian.

Nothing here is registered.  The library states the same two facts for a general étale square
`a ≫ f = f' ≫ b` as
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale`
and `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_forall_isEtale` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/RelativeEtaleLocal.lean`.  Stacks 0DKQ itself is
registered on `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_tfae_chartDiagram`.

## Main results

* `Space.locallyHasFiniteTorDimension_smallEtaleDerivedModulePullback_of_isEtale`:
  the Tor clause of relative perfectness passes to an étale morphism of the source.
* `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_of_isEtale_family`,
  `AlgebraicGeometry.Space.isPseudoCoherent_of_isEtale_family`: the two clauses descend along a
  family of étale morphisms whose charts cover the space.
* `AlgebraicGeometry.Space.etaleLocalRelativelyPerfect`: the proposition
  `AlgebraicGeometry.Space.EtaleLocalRelativelyPerfect` holds.

## References

* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude
open Stacks.SheafOfModules.DerivedTensorProduct (hasTorAmplitudeCanonical_derivedModuleFiber
  hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
  locallyHasFiniteTorDimension_of_stalkwise_family)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Étale morphisms do not change the stalk rings -/

/-- The homomorphisms of stalk rings of Stacks 05V5 compose, after the identification of the
stalk ring of `X'` with its étale local ring: both sides are the composite of the homomorphisms
of étale local rings of Stacks 04NG along `f` and along `a`. -/
theorem pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap_comp
    {X' X Y : AlgebraicSpaces B S hS} (a : X' ⟶ X) (f : X ⟶ Y) (x' : GeometricPoint B S hS X'.1) :
    (pointStalkRingEquiv B S hS X' x').toRingHom.comp
        (smallEtaleStalkPullbackRingMap B S hS (a ≫ f) x') =
      (pointStalkRingEquiv B S hS X' x').toRingHom.comp
        ((smallEtaleStalkPullbackRingMap B S hS a x').comp
          (smallEtaleStalkPullbackRingMap B S hS f (geometricPointMap a.hom x'))) := by
  rw [pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap, ← RingHom.comp_assoc,
    pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap, RingHom.comp_assoc,
    pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap, ← RingHom.comp_assoc,
    etaleLocalRingMap_comp]
  rfl

/-- **The homomorphisms of stalk rings of Stacks 05V5 compose**: for `a : X' ⟶ X`, `f : X ⟶ Y`
and a geometric point `x̄'` of `X'`, the map `𝒪_{Y, f(a(x̄'))} ⟶ 𝒪_{X', x̄'}` of `a ≫ f` is the
composite of the maps of `f` and of `a`, read on the étale local rings by Stacks 04NG. -/
theorem smallEtaleStalkPullbackRingMap_comp_eq {X' X Y : AlgebraicSpaces B S hS} (a : X' ⟶ X)
    (f : X ⟶ Y) (x' : GeometricPoint B S hS X'.1) :
    smallEtaleStalkPullbackRingMap B S hS (a ≫ f) x' =
      (smallEtaleStalkPullbackRingMap B S hS a x').comp
        (smallEtaleStalkPullbackRingMap B S hS f (geometricPointMap a.hom x')) :=
  RingHom.ext fun r => (pointStalkRingEquiv B S hS X' x').injective
    (RingHom.congr_fun (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap_comp a f x') r)

/-- **The stalk of an étale pullback, read over the base, is the stalk downstairs.**  For an
étale `a : X' ⟶ X`, `f : X ⟶ Y`, a geometric point `x̄'` of `X'` and a complex `N` of
`𝒪_{X, a(x̄')}`-modules, the extension of scalars of `N` to `𝒪_{X', x̄'}`, read over
`𝒪_{Y, f(a(x̄'))}`, has Tor amplitude in `[lo, hi]` exactly when `N` does: the stalk ring map
along `a` is bijective (Stacks 05V5 and 04NG), so extension of scalars along it followed by
restriction of scalars is the identity. -/
theorem hasTorAmplitudeCanonical_restrictScalars_extendScalars_iff_of_isEtale
    {X' X Y : AlgebraicSpaces B S hS} (a : X' ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y)
    (x' : GeometricPoint B S hS X'.1)
    (N : CochainComplex
      (ModuleCat.{u} (structureStalkRing B S hS X (geometricPointMap a.hom x'))) ℤ) (lo hi : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS Y
      (geometricPointMap f.hom (geometricPointMap a.hom x'))))
    HasTorAmplitudeCanonical
        (structureStalkRing B S hS Y (geometricPointMap f.hom (geometricPointMap a.hom x')))
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars.{u}
              (smallEtaleStalkPullbackRingMap B S hS (a ≫ f) x')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars
              (smallEtaleStalkPullbackRingMap B S hS a x')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj N))) lo hi ↔
      HasTorAmplitudeCanonical
        (structureStalkRing B S hS Y (geometricPointMap f.hom (geometricPointMap a.hom x')))
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars.{u}
              (smallEtaleStalkPullbackRingMap B S hS f
                (geometricPointMap a.hom x'))).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj N)) lo hi := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS Y
    (geometricPointMap f.hom (geometricPointMap a.hom x'))))
  let β := smallEtaleStalkPullbackRingMap B S hS a x'
  let ψ := smallEtaleStalkPullbackRingMap B S hS f (geometricPointMap a.hom x')
  have hβ : Function.Bijective β := bijective_smallEtaleStalkPullbackRingMap B S hS a ha x'
  have : ∀ M, IsIso ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} β).unit.app M) := fun M =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (ModuleCat.bijective_extendRestrictScalarsAdj_unit_app β hβ M)
  have : IsIso (ModuleCat.extendRestrictScalarsAdj.{u, u, u} β).unit :=
    NatIso.isIso_of_isIso_app _
  let e : ModuleCat.extendScalars.{u, u, u} β ⋙
        ModuleCat.restrictScalars.{u} (smallEtaleStalkPullbackRingMap B S hS (a ≫ f) x') ≅
      ModuleCat.restrictScalars.{u} ψ :=
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp' ψ β _
        (smallEtaleStalkPullbackRingMap_comp_eq a f x')) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (ModuleCat.extendRestrictScalarsAdj.{u, u, u} β).unit).symm
        _ ≪≫
      Functor.leftUnitor _
  let c : ((ModuleCat.restrictScalars.{u}
        (smallEtaleStalkPullbackRingMap B S hS (a ≫ f) x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u} β).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≅
      ((ModuleCat.restrictScalars.{u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N :=
    HomologicalComplex.Hom.isoOfComponents (fun i => e.app (N.X i))
    (fun i j _ => (e.hom.naturality (N.d i j)).symm)
  exact hasTorAmplitudeCanonical_iff_of_iso (DerivedCategory.Q.mapIso c) lo hi

/-! ### The Tor clause, read at the geometric stalks -/

/-- The stalks at the geometric points of an object `V` of the small étale site of `W` of a
complex `K` of `𝒪_W`-modules, read over the stalk rings of `U` along `q : W ⟶ U`, have Tor
amplitude in one interval. -/
def StalkTorAmplitudeBound {W U : AlgebraicSpaces B S hS} (q : W ⟶ U)
    (K : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) (V : SmallEtale B S hS W.1) : Prop :=
  ∃ a b : ℤ, ∀ (x : GeometricPoint B S hS W.1) (_ : (etaleSitePoint B S hS W.1 x W.2).fiber.obj V),
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (structureStalkRing B S hS U (geometricPointMap q.hom x)))
    HasTorAmplitudeCanonical (structureStalkRing B S hS U (geometricPointMap q.hom x))
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{u}
            (smallEtaleStalkPullbackRingMap B S hS q x)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
            (smallEtaleRingedTopos B S hS W).O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))) a b

/-- The bound `StalkTorAmplitudeBound` is inherited along morphisms of the small étale site. -/
theorem StalkTorAmplitudeBound.of_hom {W U : AlgebraicSpaces B S hS} (q : W ⟶ U)
    (K : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) {V₁ V₂ : SmallEtale B S hS W.1}
    (m : V₂ ⟶ V₁) (h : StalkTorAmplitudeBound q K V₁) : StalkTorAmplitudeBound q K V₂ := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, fun x r => hab x ((etaleSitePoint B S hS W.1 x W.2).fiber.map m r)⟩

/-- **The Tor clause of relative perfectness gives local stalk bounds.**  If `E ≅ K` in
`D(𝒪_W)` and `E`, read over `q⁻¹𝒪_U`, locally has finite Tor dimension, then every object of the
small étale site of `W` is covered by objects over which `StalkTorAmplitudeBound q K` holds
(Stacks 0DJJ (1) at the points of the slices). -/
theorem exists_cover_stalkTorAmplitudeBound {W U : AlgebraicSpaces B S hS} (q : W ⟶ U)
    (K : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) {E : derivedModules B S hS W}
    (eK : DerivedCategory.Q.obj K ≅ E)
    (hE : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS q) ((derivedScalarRestriction B S hS q).obj E))
    (W₀ : SmallEtale B S hS W.1) :
    ∃ R : Presieve W₀, Sieve.generate R ∈ SmallEtale.topology B S hS W.1 W₀ ∧
      ∀ ⦃V₀⦄ (k : V₀ ⟶ W₀), R k → StalkTorAmplitudeBound q K V₀ := by
  let eS : (derivedScalarRestriction B S hS q).obj E ≅
      DerivedCategory.Q.obj
        (((scalarRestriction B S hS q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (derivedScalarRestriction B S hS q).mapIso eK.symm ≪≫
      (derivedScalarRestrictionFactors B S hS q).app K
  obtain ⟨R, hR, hRT⟩ := hE W₀
  refine ⟨R, hR, fun V₀ k hk => ?_⟩
  obtain ⟨a, b, hab⟩ := hRT k hk
  let W' : (inverseImageRingedSite B S hS q).C := V₀
  have hab' : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (canonicalSliceDerivedTensorProduct B S hS q W')
      ((RingedSite.derivedRestriction _ W').obj
        ((derivedScalarRestriction B S hS q).obj E)) a b := hab
  refine ⟨a, b, fun x qW => ?_⟩
  have hX0 := hasTorAmplitudeCanonical_derivedModuleFiber
    (Y := (inverseImageRingedSite B S hS q).over W') _ _ a b hab'
    ((etaleSitePoint B S hS W.1 x W.2).over qW)
  have hX1 := (hasTorAmplitudeCanonical_iff_of_iso
    (Functor.mapIso _ ((RingedSite.derivedRestriction _ W').mapIso eS)) a b).1 hX0
  have hX2 := (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (Z := inverseImageRingedSite B S hS q) W'
    (etaleSitePoint B S hS W.1 x W.2) qW
    (((scalarRestriction B S hS q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a b).1 hX1
  exact (hasTorAmplitudeCanonical_scalarRestriction_stalk_iff B S hS q x K a b).1 hX2

/-- **Local stalk bounds give the Tor clause of relative perfectness.**  If `E ≅ K` in `D(𝒪_W)`
and every object of the small étale site of `W` is covered by objects over which
`StalkTorAmplitudeBound q K` holds, then `E`, read over `q⁻¹𝒪_U`, locally has finite Tor
dimension (Stacks 0DJJ (2) on the conservative families of points of the slices). -/
theorem locallyHasFiniteTorDimension_of_cover_stalkTorAmplitudeBound
    {W U : AlgebraicSpaces B S hS} (q : W ⟶ U)
    (K : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) {E : derivedModules B S hS W}
    (eK : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ W₀ : SmallEtale B S hS W.1, ∃ R : Presieve W₀,
      Sieve.generate R ∈ SmallEtale.topology B S hS W.1 W₀ ∧
        ∀ ⦃V₀⦄ (k : V₀ ⟶ W₀), R k → StalkTorAmplitudeBound q K V₀) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS q)
      ((derivedScalarRestriction B S hS q).obj E) := by
  let eS : (derivedScalarRestriction B S hS q).obj E ≅
      DerivedCategory.Q.obj
        (((scalarRestriction B S hS q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (derivedScalarRestriction B S hS q).mapIso eK.symm ≪≫
      (derivedScalarRestrictionFactors B S hS q).app K
  refine locallyHasFiniteTorDimension_of_stalkwise_family
    (Z := inverseImageRingedSite B S hS q) _ _
    (t := fun V => Σ x : GeometricPoint B S hS W.1,
      (etaleSitePoint B S hS W.1 x W.2).fiber.obj V)
    (fun V k => (etaleSitePoint B S hS W.1 k.1 W.2).over k.2)
    (fun V => isConservativeFamilyOfPoints_etaleSitePointOver B S hS W.2 V) ?_
  intro U'
  obtain ⟨R, hR, hRb⟩ := h U'
  refine ⟨R, hR, fun V' g hg => ?_⟩
  obtain ⟨a, b, hW⟩ := hRb g hg
  refine ⟨a, b, ?_⟩
  rintro ⟨x, r⟩
  refine (hasTorAmplitudeCanonical_iff_of_iso
    (Functor.mapIso _ ((RingedSite.derivedRestriction _ V').mapIso eS)) a b).2 ?_
  refine (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (Z := inverseImageRingedSite B S hS q) V'
    (etaleSitePoint B S hS W.1 x W.2) r _ a b).2 ?_
  exact (hasTorAmplitudeCanonical_scalarRestriction_stalk_iff B S hS q x K a b).2 (hW x r)

/-- Every object of `D(𝒪_X)` is isomorphic to a K-flat complex (Stacks 06YF on the small étale
ringed topos). -/
theorem exists_isKFlat_iso {X : AlgebraicSpaces B S hS} (E : derivedModules B S hS X) :
    ∃ K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ,
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := smallEtaleRingedTopos B S hS X)
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  let K₀ : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ :=
    DerivedCategory.Q.objPreimage E
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize
    (smallEtaleRingedTopos B S hS X).O
  obtain ⟨Dn, α, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize
      (smallEtaleRingedTopos B S hS X).O K₀
  have hDn : HasColimit Dn := inferInstance
  let K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ := (Arrow.mk α).left
  let α' : K ⟶ K₀ := α
  have hQα : IsIso (DerivedCategory.Q.map α') := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  have := Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize
    (smallEtaleRingedTopos B S hS X).O
  have hDn' : HasColimit (show ℕ ⥤ CochainComplex (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u}
        (smallEtaleRingedTopos B S hS X).O)) ℤ from Dn) := hDn
  exact ⟨K, ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
      _ Dn hLE hflat,
      Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize _ Dn hflat⟩,
    ⟨asIso (DerivedCategory.Q.map α') ≪≫ DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-! ### Restriction along an étale morphism -/

/-- **The Tor clause of relative perfectness passes to an étale morphism of the source**, the
Tor clause of the first consequence of Stacks 0DKQ.  For an étale `a : X' ⟶ X` and `f : X ⟶ Y`,
if `E ∈ D(𝒪_X)`, read over `f⁻¹𝒪_Y`, locally has finite Tor dimension, then so does `La^*E`,
read over `(a ≫ f)⁻¹𝒪_Y`.

The same fact for a general étale square is
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale`,
of which this is the case where the étale map of the base is the identity. -/
theorem locallyHasFiniteTorDimension_smallEtaleDerivedModulePullback_of_isEtale
    {X' X Y : AlgebraicSpaces B S hS} (a : X' ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y)
    (E : derivedModules B S hS X)
    (hE : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS f) ((derivedScalarRestriction B S hS f).obj E)) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS (a ≫ f))
      ((derivedScalarRestriction B S hS (a ≫ f)).obj
        ((smallEtaleDerivedModulePullback B S hS a).obj E)) := by
  obtain ⟨K, hKflat, ⟨eK⟩⟩ := exists_isKFlat_iso E
  let eP : (smallEtaleDerivedModulePullback B S hS a).obj E ≅
      DerivedCategory.Q.obj
        (((smallEtaleRingedToposHom B S hS a).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
    (smallEtaleDerivedModulePullback B S hS a).mapIso eK.symm ≪≫
      derivedPullbackObjIsoOfIsKFlat B S hS a K hKflat
  refine locallyHasFiniteTorDimension_of_cover_stalkTorAmplitudeBound (a ≫ f) _ eP.symm
    fun U' => ⟨_, generate_mem_topology_chartsOver_of_cover a (StalkTorAmplitudeBound f K)
      (exists_cover_stalkTorAmplitudeBound f K eK hE)
      (fun m h => StalkTorAmplitudeBound.of_hom f K m h) U', ?_⟩
  rintro V' g ⟨W₀, q₀, hq₀, lo, hi, hW⟩
  refine ⟨lo, hi, fun x' r => ?_⟩
  -- the point of the small étale site of `X` under `x'`, on the slice over `W₀`
  let qW : (etaleSitePoint B S hS X.1 (geometricPointMap a.hom x') X.2).fiber.obj W₀ :=
    ⟨r.1 ≫ q₀, (congrArg (fun α => α.app (Opposite.op x'.val.siteObject) r.1) hq₀).trans
      (congrArg (a.hom.app (Opposite.op x'.val.siteObject)) r.2)⟩
  refine (hasTorAmplitudeCanonical_iff_of_iso
    (DerivedCategory.Q.mapIso (((ModuleCat.restrictScalars.{u}
      (smallEtaleStalkPullbackRingMap B S hS (a ≫ f) x')).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (pullbackModulesStalkComplexIso B S hS a x' K))) lo hi).2 ?_
  exact (hasTorAmplitudeCanonical_restrictScalars_extendScalars_iff_of_isEtale a ha f x' _
    lo hi).2 (hW (geometricPointMap a.hom x') qW)

/-! ### Descent along a family of étale morphisms -/

/-- A lift of a geometric point of `X` into the image `a ∘ V` of an étale chart `V` of `X'`
comes from a lift into `V` of a geometric point of `X'` lying over it.

The same statement is `AlgebraicGeometry.Space.exists_geometricPoint_of_smallEtalePostcomp` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/RelativeEtaleLocal.lean`. -/
theorem exists_geometricPoint_lift_of_smallEtalePostcomp {X' X : AlgebraicSpaces B S hS}
    (a : X' ⟶ X) (ha : IsEtale B S hS a.hom) (V : SmallEtale B S hS X'.1)
    (x : GeometricPoint B S hS X.1)
    (q : (etaleSitePoint B S hS X.1 x X.2).fiber.obj ((smallEtalePostcomp B S hS a ha).obj V)) :
    ∃ (x' : GeometricPoint B S hS X'.1) (_ : (etaleSitePoint B S hS X'.1 x' X'.2).fiber.obj V),
      geometricPointMap a.hom x' = x := by
  obtain ⟨⟨c, cont, tb, v⟩, hx⟩ := x
  obtain ⟨q, hq⟩ := q
  refine ⟨⟨⟨c, cont, tb, V.obj.hom.app _ q⟩, hx⟩, ⟨q, rfl⟩, Subtype.ext ?_⟩
  exact congrArg (fun t => (⟨c, cont, tb, t⟩ : FieldValuedPoint B S hS X.1)) hq

/-- **The Tor clause of relative perfectness descends along a family of étale morphisms whose
charts cover the space.**  Let `aᵢ : Xᵢ ⟶ X` be étale, with the composites with the `aᵢ` of the
étale charts of the `Xᵢ` covering the final object of the small étale site of `X`, and let
`f : X ⟶ Y`.  If every `L(aᵢ)^*E`, read over `(aᵢ ≫ f)⁻¹𝒪_Y`, locally has finite Tor dimension,
then so does `E ∈ D(𝒪_X)`, read over `f⁻¹𝒪_Y`.

The same fact for a general étale square is the Tor half of
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_forall_isEtale`. -/
theorem locallyHasFiniteTorDimension_of_isEtale_family {ι : Type*}
    {X Y : AlgebraicSpaces B S hS} {Xi : ι → AlgebraicSpaces B S hS} (ai : ∀ i, Xi i ⟶ X)
    (ha : ∀ i, IsEtale B S hS (ai i).hom)
    (hcov : (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop
      (fun x : Σ i, (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).C =>
        (smallEtaleRingedSitePostcomp B S hS (ai x.1) (ha x.1)).obj x.2))
    (f : X ⟶ Y) (E : derivedModules B S hS X)
    (hE : ∀ i, Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS (ai i ≫ f))
      ((derivedScalarRestriction B S hS (ai i ≫ f)).obj
        ((smallEtaleDerivedModulePullback B S hS (ai i)).obj E))) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS f)
      ((derivedScalarRestriction B S hS f).obj E) := by
  classical
  obtain ⟨K, hKflat, ⟨eK⟩⟩ := exists_isKFlat_iso E
  let pK : ∀ i, CochainComplex (Modules.{u, u} B S hS (Xi i).1 (Xi i).2) ℤ := fun i =>
    ((smallEtaleRingedToposHom B S hS (ai i)).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  let eP : ∀ i, DerivedCategory.Q.obj (pK i) ≅
      (smallEtaleDerivedModulePullback B S hS (ai i)).obj E := fun i =>
    ((smallEtaleDerivedModulePullback B S hS (ai i)).mapIso eK.symm ≪≫
      derivedPullbackObjIsoOfIsKFlat B S hS (ai i) K hKflat).symm
  let p : ∀ i, (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).C → Prop := fun i V =>
    StalkTorAmplitudeBound (ai i ≫ f) (pK i) V
  have hp : ∀ i (U : (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).C),
      ∃ T : Presieve U, Sieve.generate T ∈ (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).J U ∧
        ∀ ⦃V⦄ (g : V ⟶ U), T g → p i V := fun i U =>
    exists_cover_stalkTorAmplitudeBound (ai i ≫ f) (pK i) (eP i) (hE i) U
  have : ∀ i, (smallEtaleRingedSitePostcomp B S hS (ai i) (ha i)).IsContinuous
      (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).J (smallEtaleRingedSite B S hS X.1 X.2).J :=
    fun i => smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS (ai i) (ha i)
  have hcov' := GrothendieckTopology.coversTop_sigma_subtype
    (fun i => smallEtaleRingedSitePostcomp B S hS (ai i) (ha i))
    (fun i => (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).J)
    (smallEtaleRingedSite B S hS X.1 X.2).J hcov p hp
  refine locallyHasFiniteTorDimension_of_cover_stalkTorAmplitudeBound f K eK fun U => ?_
  let U' : (smallEtaleRingedSite B S hS X.1 X.2).C := U
  let Sv : Sieve U' := Sieve.ofObjects
    (fun x : {x : Σ i, (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).C // p x.1 x.2} =>
      (smallEtaleRingedSitePostcomp B S hS (ai x.1.1) (ha x.1.1)).obj x.1.2) U'
  have hSv : Sieve.generate Sv.arrows ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U' := by
    rw [Sieve.generate_sieve]
    exact hcov' U'
  refine ⟨Sv.arrows, hSv, ?_⟩
  rintro V g ⟨⟨⟨i, W''⟩, lo, hi, hW⟩, ⟨k⟩⟩
  refine ⟨lo, hi, fun x r => ?_⟩
  obtain ⟨x', r', rfl⟩ := exists_geometricPoint_lift_of_smallEtalePostcomp (ai i) (ha i) W'' x
    ((etaleSitePoint B S hS X.1 x X.2).fiber.map k r)
  have hX := (hasTorAmplitudeCanonical_iff_of_iso
    (DerivedCategory.Q.mapIso (((ModuleCat.restrictScalars.{u}
      (smallEtaleStalkPullbackRingMap B S hS (ai i ≫ f) x')).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (pullbackModulesStalkComplexIso B S hS (ai i) x' K))) lo hi).1 (hW x' r')
  exact (hasTorAmplitudeCanonical_restrictScalars_extendScalars_iff_of_isEtale (ai i) (ha i) f
    x' _ lo hi).1 hX

/-- **Pseudo-coherence descends along a family of étale morphisms whose charts cover the
space.**  Let `aᵢ : Xᵢ ⟶ X` be étale, with the composites with the `aᵢ` of the étale charts of
the `Xᵢ` covering the final object of the small étale site of `X`.  If every `L(aᵢ)^*E` is
pseudo-coherent, so is `E ∈ D(𝒪_X)`: it is checked on the charts of `X` factoring through a
chart of some `Xᵢ` (`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_charts`), to which `E`
pulls back through `L(aᵢ)^*E` along étale morphisms.

The same fact for a general étale square is the pseudo-coherence half of
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_forall_isEtale`. -/
theorem isPseudoCoherent_of_isEtale_family {ι : Type*}
    {X : AlgebraicSpaces B S hS} {Xi : ι → AlgebraicSpaces B S hS} (ai : ∀ i, Xi i ⟶ X)
    (ha : ∀ i, IsEtale B S hS (ai i).hom)
    (hcov : (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop
      (fun x : Σ i, (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).C =>
        (smallEtaleRingedSitePostcomp B S hS (ai x.1) (ha x.1)).obj x.2))
    (E : derivedModules B S hS X)
    (hE : ∀ i, (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).IsPseudoCoherent
      ((smallEtaleDerivedModulePullback B S hS (ai i)).obj E)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E := by
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ E).2 fun m => ?_
  refine isPseudoCoherentFrom_of_charts B S hS E m fun U =>
    ⟨(Sieve.ofObjects (fun x : Σ i, (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).C =>
        (smallEtaleRingedSitePostcomp B S hS (ai x.1) (ha x.1)).obj x.2) U).arrows,
      by rw [Sieve.generate_sieve]; exact hcov U, ?_⟩
  rintro V g ⟨⟨i, W''⟩, ⟨k⟩⟩
  have h₁ := (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 (hE i) m
  have h₂ := isPseudoCoherentFrom_smallEtaleDerivedModulePullback_of_isEtale B S hS
    (chartToSpace B S hS (Xi i) W'') (isEtale_chartToSpace B S hS (Xi i) W'') _ m h₁
  have h₃ := isPseudoCoherentFrom_smallEtaleDerivedModulePullback_of_isEtale B S hS
    (chartMap B S hS X k) (isEtale_chartMap B S hS X k) _ m h₂
  have hfac : chartToSpace B S hS X V =
      chartMap B S hS X k ≫ (chartToSpace B S hS (Xi i) W'' ≫ ai i) :=
    (chartMap_comp_chartToSpace B S hS X k).symm
  refine RingedSite.isPseudoCoherentFrom_of_iso _ m h₃ ?_
  exact eqToIso (congrArg (fun t => (smallEtaleDerivedModulePullback B S hS t).obj E) hfac) ≪≫
    ((smallEtaleDerivedPullbackData B S hS).compIso (chartMap B S hS X k)
      (chartToSpace B S hS (Xi i) W'' ≫ ai i)).app E ≪≫
    (smallEtaleDerivedModulePullback B S hS (chartMap B S hS X k)).mapIso
      (((smallEtaleDerivedPullbackData B S hS).compIso (chartToSpace B S hS (Xi i) W'')
        (ai i)).app E)

/-! ### The proposition `EtaleLocalRelativelyPerfect` -/

/-- The composites with the morphisms of the two pieces of an elementary distinguished square of
the étale charts of the pieces cover the final object of the small étale site of the space
(`AlgebraicGeometry.Space.coversTop_edsChart`). -/
theorem coversTop_smallEtaleRingedSitePostcomp_edsCoverMember {W : AlgebraicSpaces B S hS}
    {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) :
    (smallEtaleRingedSite B S hS W.1 W.2).J.CoversTop
      (fun x : Σ b, (smallEtaleRingedSite B S hS (edsCoverMember B S hS hsq b).1
          (edsCoverMember B S hS hsq b).2).C =>
        (smallEtaleRingedSitePostcomp B S hS (edsCoverMemberHom B S hS hsq x.1)
          (isEtale_edsCoverMemberHom B S hS hsq x.1)).obj x.2) := by
  intro U
  refine (SmallEtale.topology B S hS W.1).superset_covering ?_ (coversTop_edsChart B S hS hsq U)
  rintro Z g ⟨b, ⟨k⟩⟩
  cases b
  · exact ⟨⟨false, _⟩, ⟨k⟩⟩
  · exact ⟨⟨true, _⟩, ⟨k⟩⟩

variable (B S hS) in
/-- **Relative perfectness is étale local: the two consequences of Stacks 0DKQ used in the square
step of Stacks 0DKW** (`AlgebraicGeometry.Space.EtaleLocalRelativelyPerfect`, the proposition the
square step takes as its hypothesis `hloc`).

1. Restriction along an étale `a : X' ⟶ X`: the pseudo-coherence clause is Stacks 08H4
   (`AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullback`), the Tor clause
   `Space.locallyHasFiniteTorDimension_smallEtaleDerivedModulePullback_of_isEtale`.
2. Descent along the two pieces of an elementary distinguished square, whose charts cover the
   space: `AlgebraicGeometry.Space.isPseudoCoherent_of_isEtale_family` and
   `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_of_isEtale_family`.

Unregistered.  The same two facts for a general étale square are
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale`
and `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_forall_isEtale` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/RelativeEtaleLocal.lean`. -/
theorem etaleLocalRelativelyPerfect : EtaleLocalRelativelyPerfect B S hS := by
  refine ⟨fun f a _ _ _ _ ha K hK =>
    ⟨isPseudoCoherent_smallEtaleDerivedModulePullback a K hK.1,
      locallyHasFiniteTorDimension_smallEtaleDerivedModulePullback_of_isEtale a ha f K hK.2⟩,
    fun f _ _ Uo V fV hsq _ _ _ _ K hU hV => ⟨?_, ?_⟩⟩
  · exact isPseudoCoherent_of_isEtale_family (edsCoverMemberHom B S hS hsq)
      (isEtale_edsCoverMemberHom B S hS hsq)
      (coversTop_smallEtaleRingedSitePostcomp_edsCoverMember hsq) K
      fun | false => hV.1 | true => hU.1
  · exact locallyHasFiniteTorDimension_of_isEtale_family (edsCoverMemberHom B S hS hsq)
      (isEtale_edsCoverMemberHom B S hS hsq)
      (coversTop_smallEtaleRingedSitePostcomp_edsCoverMember hsq) f K
      fun | false => hV.2 | true => hU.2

end AlgebraicGeometry.Space

end
