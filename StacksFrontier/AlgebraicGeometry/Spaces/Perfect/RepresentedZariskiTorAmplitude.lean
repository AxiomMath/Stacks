module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointOfSpecHom
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiStalk
public import StacksFrontier.Homology.TorAmplitude.StrictHenselizationBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Relative Tor amplitude across `ε : X_étale ⟶ X_Zar` (Stacks 0DK7)

Let `g : T ⟶ T'` be a morphism of the big fppf site over `S`, with underlying morphism of schemes
`g₀ : X ⟶ Y`, and let `h = yoneda.map g` be the represented morphism of algebraic spaces.
The small étale site of the algebraic space `yoneda.obj T` is the small étale site of the scheme
`X` (Stacks 04M0), so `ε : (X_étale, 𝒪_X) ⟶ (X_Zar, 𝒪_X)` of Stacks 08H7 is
`AlgebraicGeometry.Space.representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`, and
`h_small⁻¹𝒪_{Y_étale}` is the sheaf `h⁻¹𝒪` of `AlgebraicGeometry.Space.inverseImageRingedSite`.

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_relativeStalk_representedZariski_iff`: at a
  geometric point `x̄` over `x`, the stalk of `ε^*E` over `(h⁻¹𝒪)_{x̄} = 𝒪_{Y, y}^{sh}` has Tor
  amplitude in `[a, b]` exactly when `E_x` has it over `𝒪_{Y, y}`.
-/

@[expose] public noncomputable section

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

open CategoryTheory CategoryTheory.Limits Opposite StacksDraft.TorAmplitude

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (g : T ⟶ T') (x : GeometricPoint B S hS (yoneda.obj T))

/-- The identity chart of `yoneda.obj T'`, carrying the image of `x̄`, lies under the identity
chart of `yoneda.obj T` along `g`. -/
theorem representedSpaceMap_chart_comm :
    (yonedaIdentityNeighborhood T x).chart.obj.hom ≫ (representedSpaceMap B S hS g).hom =
      yoneda.map g ≫ (yonedaIdentityNeighborhood T'
        (geometricPointMap (representedSpaceMap B S hS g).hom x)).chart.obj.hom := by
  show 𝟙 _ ≫ yoneda.map g = yoneda.map g ≫ 𝟙 _
  simp

/-- The identity chart of `yoneda.obj T'`, pointed by the image of the lift of `x̄`. -/
abbrev representedTargetNeighborhood :
    SmallEtaleNeighborhood (geometricPointMap (representedSpaceMap B S hS g).hom x) :=
  targetNeighborhood B S hS (yonedaIdentityNeighborhood T x)
    (yonedaIdentityNeighborhood T' (geometricPointMap (representedSpaceMap B S hS g).hom x)).chart
    g (representedSpaceMap_chart_comm g x)

/-- The local ring `𝒪_{Y, g₀(x)}` maps to the stalk `(h⁻¹𝒪)_{x̄}` as a strict henselization. -/
abbrev representedTargetStrictHenselizationEquiv :
    (chartHenselizationTower B S hS (yoneda.obj T')
        (representedTargetNeighborhood g x)).strictHenselization ≃+*
      relativeStalkRing (representedSpaceMap B S hS g) x :=
  (chartStrictHenselizationEquiv B S hS (yoneda.obj T')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T')
      (representedTargetNeighborhood g x)).trans
    (relativeStalkRingEquiv (representedSpaceMap B S hS g) x).symm

/-- The square of local rings `𝒪_{Y, y} ⟶ 𝒪_{X, x} ⟶ 𝒪_{X, x̄}` and
`𝒪_{Y, y} ⟶ (h⁻¹𝒪)_{x̄} ⟶ 𝒪_{X, x̄}` commutes. -/
theorem relativeStalkMap_comp_representedTargetStrictHenselizationEquiv :
    (relativeStalkMap (representedSpaceMap B S hS g) x).comp
        ((representedTargetStrictHenselizationEquiv g x).toRingHom.comp
          (algebraMap (chartLocalRing B S hS (yoneda.obj T') (representedTargetNeighborhood g x))
            (chartHenselizationTower B S hS (yoneda.obj T')
              (representedTargetNeighborhood g x)).strictHenselization)) =
      (representedStalkBaseChangeMap x).comp
        (((BigFppfOver.toScheme B S hS).map g).stalkMap (representedPoint x)).hom := by
  refine RingHom.ext fun a => ?_
  apply (pointStalkRingEquiv B S hS (representedSpace T) x).injective
  have hsq := congrArg (fun φ => φ a) (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing
    B S hS (representedSpaceMap B S hS g) x (yonedaIdentityNeighborhood T x)
    (yonedaIdentityNeighborhood T' (geometricPointMap (representedSpaceMap B S hS g).hom x)).chart
    g (representedSpaceMap_chart_comm g x))
  refine (pointStalkRingEquiv_relativeStalkMap (representedSpaceMap B S hS g) x _).trans ?_
  refine Eq.trans ?_ ((hsq.symm).trans ?_)
  · exact congrArg (etaleLocalRingMap _ _ x)
      ((relativeStalkRingEquiv (representedSpaceMap B S hS g) x).apply_symm_apply _)
  · exact ((pointStalkRingEquiv B S hS (representedSpace T) x).apply_symm_apply _).symm

/-- `𝒪_{X, x} ⟶ 𝒪_{X, x̄}` is faithfully flat. -/
theorem faithfullyFlat_representedStalkBaseChangeMap :
    (representedStalkBaseChangeMap x).FaithfullyFlat := by
  let c := chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) (yonedaIdentityNeighborhood T x)
  let p := pointStalkRingEquiv B S hS (representedSpace T) x
  have hc := faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) (yonedaIdentityNeighborhood T x)
  let := c.toAlgebra
  let : Algebra (chartLocalRing B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T x))
      (Stacks.ringFiber (yonedaEtaleSitePoint x)
        (smallEtaleRingedTopos B S hS (representedSpace T)).O.obj) :=
    (representedStalkBaseChangeMap x).toAlgebra
  have : Module.FaithfullyFlat _ _ := hc
  let e : Stacks.ringFiber (yonedaEtaleSitePoint x)
        (smallEtaleRingedTopos B S hS (representedSpace T)).O.obj ≃ₗ[
        chartLocalRing B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T x)]
      etaleLocalRing B S hS (yoneda.obj T) x :=
    { p.toAddEquiv with
      map_smul' := fun r z => by
        show p ((representedStalkBaseChangeMap x) r * z) = c r * p z
        rw [map_mul]
        exact congrArg (· * p z) (p.apply_symm_apply (c r)) }
  exact Module.FaithfullyFlat.of_linearEquiv
    (chartLocalRing B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T x))
    (etaleLocalRing B S hS (yoneda.obj T) x) e

/-- **Stacks 0DK7 at a geometric point.**  For a complex `K` of `𝒪_X`-modules and a geometric
point `x̄` of `yoneda.obj T` over `x ∈ X`, the derived stalk at `x̄` of `ε^*K`, read over
`(h⁻¹𝒪)_{x̄} = 𝒪_{Y, y}^{sh}`, has Tor amplitude in `[a, b]` exactly when `K_x` has Tor
amplitude in `[a, b]` over `𝒪_{Y, y}`, `y = g₀(x)`.  The stalk of `ε^*K` is
`K_x ⊗_{𝒪_{X, x}} 𝒪_{X, x}^{sh}`; Stacks 0DJF along the faithfully flat
`𝒪_{X, x} ⟶ 𝒪_{X, x}^{sh}` and Stacks 0DK0 along `𝒪_{Y, y} ⟶ 𝒪_{Y, y}^{sh}` finish. -/
theorem hasTorAmplitudeCanonical_relativeStalk_representedZariski_iff
    (K : CochainComplex (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules ℤ)
    (a b : ℤ) :
    HasTorAmplitudeCanonical (relativeStalkRing (representedSpaceMap B S hS g) x)
        ((Stacks.derivedModuleFiber
            (etaleSitePoint B S hS (yoneda.obj T) x
              (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
            (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).O).obj
          ((derivedScalarRestriction B S hS (representedSpaceMap B S hS g)).obj
            ((representedZariskiDerivedPullback B S hS T).obj (DerivedCategory.Q.obj K)))) a b ↔
      Scheme.Hom.HasTorAmplitudeAtPoint ((BigFppfOver.toScheme B S hS).map g)
        (DerivedCategory.Q.obj K) (representedPoint x) a b := by
  let εK := (Functor.mapHomologicalComplex
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T)
    (ComplexShape.up ℤ)).obj K
  let M := ((Stacks.ModuleSkyscraper.modulesStalkFunctor
    (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
    (representedPoint x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let e₁ : (representedZariskiDerivedPullback B S hS T).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj εK :=
    (representedZariskiDerivedPullbackIso B S hS T).app _ ≪≫
      (Functor.mapDerivedCategoryFactors
        (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T)).app K
  let e : (Stacks.derivedModuleFiber
        (etaleSitePoint B S hS (yoneda.obj T) x
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
        (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).O).obj
        ((derivedScalarRestriction B S hS (representedSpaceMap B S hS g)).obj
          ((representedZariskiDerivedPullback B S hS T).obj (DerivedCategory.Q.obj K))) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars
            (relativeStalkMap (representedSpaceMap B S hS g) x)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars (representedStalkBaseChangeMap x)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) :=
    (Stacks.derivedModuleFiber
        (etaleSitePoint B S hS (yoneda.obj T) x
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
        (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).O).mapIso
        ((derivedScalarRestriction B S hS (representedSpaceMap B S hS g)).mapIso e₁) ≪≫
      derivedRelativeStalkIso (X := representedSpace T) (representedSpaceMap B S hS g) x εK ≪≫
      DerivedCategory.Q.mapIso (((ModuleCat.restrictScalars
        (relativeStalkMap (representedSpaceMap B S hS g) x)).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso (representedZariskiPullbackStalkComplexIso x K))
  refine Iff.trans
    ⟨AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b,
      AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b⟩ ?_
  rw [Scheme.Hom.hasTorAmplitudeAtPoint_Q_iff]
  exact (hasTorAmplitudeCanonical_restrictScalars_iff_extendScalars_of_henselizationTower
    (chartHenselizationTower B S hS (yoneda.obj T') (representedTargetNeighborhood g x))
    (representedTargetStrictHenselizationEquiv g x)
    (((BigFppfOver.toScheme B S hS).map g).stalkMap (representedPoint x)).hom
    (representedStalkBaseChangeMap x) (faithfullyFlat_representedStalkBaseChangeMap x)
    (relativeStalkMap (representedSpaceMap B S hS g) x)
    (relativeStalkMap_comp_representedTargetStrictHenselizationEquiv g x) M a b).symm

/-- The closed point of the spectrum of an algebraic closure of the residue field of `z` maps to
`z`. -/
private theorem closedPoint_algebraicClosure_residueField_map {Z : Scheme.{u}} (z : Z) :
    (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z)
        (AlgebraicClosure (Z.residueField z)))) ≫ Z.fromSpecResidueField z).base
      (IsLocalRing.closedPoint (AlgebraicClosure (Z.residueField z))) = z :=
  (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)

/-- Every point of the scheme underlying `T` lies under a geometric point of `yoneda.obj T`:
the spectrum of an algebraic closure of its residue field. -/
theorem exists_representedPoint_eq
    (y : representedSchemeRepresentedZariskiRingedToposHom B S hS T) :
    ∃ x : GeometricPoint B S hS (yoneda.obj T), representedPoint x = y := by
  let κ := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).residueField y
  have hΩ : B.Contains (Spec (.of (AlgebraicClosure κ))) :=
    B.contains_spec_algebraicClosure (B.residueField_spec_contains T.left.property y)
  let σ : Spec (.of (AlgebraicClosure κ)) ⟶
      representedSchemeRepresentedZariskiRingedToposHom B S hS T :=
    Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ))) ≫
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).fromSpecResidueField y
  refine ⟨geometricPointOfSpecHom B S hS T hΩ (σ ≫ B.inclusion.map T.hom) σ rfl, ?_⟩
  show σ.base (IsLocalRing.closedPoint (AlgebraicClosure κ)) = y
  exact closedPoint_algebraicClosure_residueField_map y

/-- **The étale side of Stacks 0DK7, at the geometric points.**  An object of `D(h⁻¹𝒪)` has Tor
amplitude in `[a, b]` exactly when its derived stalk at every geometric point of `yoneda.obj T`
does, over the stalk of `h⁻¹𝒪` there (Stacks 0DJJ). -/
theorem hasTorAmplitude_inverseImageRingedSite_iff_forall_relativeStalk
    (Tet : Stacks.SheafOfModules.DerivedTensorProduct
      (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)))
    (F : RingedSite.DerivedModules (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)))
    (a b : ℤ) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude Tet F a b ↔
      ∀ x : GeometricPoint B S hS (yoneda.obj T),
        HasTorAmplitudeCanonical (relativeStalkRing (representedSpaceMap B S hS g) x)
          ((Stacks.derivedModuleFiber
            (etaleSitePoint B S hS (yoneda.obj T) x
              (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
            (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).O).obj F) a b :=
  ⟨fun h _ => Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber
      Tet F a b h _,
    fun h =>
      Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber_family
        Tet F a b _ (isConservativeFamilyOfPoints_etaleSitePoint B S hS (yoneda.obj T)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)) h⟩

/-- The stalk condition of Stacks 0DK7 at a geometric point, for an arbitrary object of
`D(𝒪_X)`. -/
theorem hasTorAmplitudeCanonical_relativeStalk_representedZariski_iff'
    (E : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules)
    (a b : ℤ) :
    HasTorAmplitudeCanonical (relativeStalkRing (representedSpaceMap B S hS g) x)
        ((Stacks.derivedModuleFiber
            (etaleSitePoint B S hS (yoneda.obj T) x
              (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
            (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).O).obj
          ((derivedScalarRestriction B S hS (representedSpaceMap B S hS g)).obj
            ((representedZariskiDerivedPullback B S hS T).obj E))) a b ↔
      Scheme.Hom.HasTorAmplitudeAtPoint ((BigFppfOver.toScheme B S hS).map g) E
        (representedPoint x) a b := by
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let e := (Stacks.derivedModuleFiber
      (etaleSitePoint B S hS (yoneda.obj T) x (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
      (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).O).mapIso
    ((derivedScalarRestriction B S hS (representedSpaceMap B S hS g)).mapIso
      ((representedZariskiDerivedPullback B S hS T).mapIso eK))
  refine Iff.trans
    ⟨AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b,
      AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b⟩ ?_
  exact (hasTorAmplitudeCanonical_relativeStalk_representedZariski_iff g x K a b).trans
    ⟨fun h => h.of_iso _ eK, fun h => h.of_iso _ eK.symm⟩

/-- **Stacks 0DK7, part (1).**  Let `g₀ : X ⟶ Y` be the morphism of schemes underlying a
morphism `g` of the big fppf site, `E ∈ D(𝒪_X)` and `ε^*E` its pullback to the small étale site.
Then `E` read in `D(g₀⁻¹𝒪_Y)` has Tor amplitude in `[a, b]` if and only if `ε^*E` read in
`D(g_{small}⁻¹𝒪_{Y_étale})` has Tor amplitude in `[a, b]`.

The small étale site of `X` is the small étale site of the algebraic space `yoneda.obj T`
(Stacks 04M0), on which `g_{small}⁻¹𝒪_{Y_étale}` is the inverse image of the structure sheaf of
`yoneda.obj T'` along `yoneda.map g` — the sheaf the source names.  An earlier form used
`ε⁻¹g₀⁻¹𝒪_Y` instead; identifying the two needs `g₀ ∘ ε_X = ε_Y ∘ g_{small}` and Stacks 070S, so
that form was not the statement of the source.  The proof is the source's, at the stalks. -/
@[stacks 0DK7 "part (1)"]
theorem hasTorAmplitude_derivedScalarRestriction_iff_representedZariskiDerivedPullback
    (Tet : Stacks.SheafOfModules.DerivedTensorProduct
      (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)))
    (E : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules)
    (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
        (RingedSpace.inverseImage
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T').toRingedSpace
          ((BigFppfOver.toScheme B S hS).map g).base)
        ((Scheme.Hom.derivedScalarRestriction ((BigFppfOver.toScheme B S hS).map g)).obj E) a b ↔
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude Tet
        ((derivedScalarRestriction B S hS (representedSpaceMap B S hS g)).obj
          ((representedZariskiDerivedPullback B S hS T).obj E)) a b := by
  rw [Scheme.Hom.hasTorAmplitude_derivedScalarRestriction_iff_forall_hasTorAmplitudeAtPoint,
    hasTorAmplitude_inverseImageRingedSite_iff_forall_relativeStalk]
  refine ⟨fun h x => (hasTorAmplitudeCanonical_relativeStalk_representedZariski_iff' g x E a b).2
      (h _), fun h y => ?_⟩
  obtain ⟨x, rfl⟩ := exists_representedPoint_eq y
  exact (hasTorAmplitudeCanonical_relativeStalk_representedZariski_iff' g x E a b).1 (h x)

/-! ### Part (2): locally finite Tor dimension -/

section Local

/-- The structure morphism of an étale chart of `yoneda.obj T`, as a morphism of the big fppf
site into `T`. -/
abbrev representedChartMap (V : SmallEtale B S hS (yoneda.obj T)) : V.obj.left ⟶ T :=
  yoneda.preimage V.obj.hom

/-- The morphism of schemes underlying the structure morphism of an étale chart of
`yoneda.obj T`. -/
abbrev representedChartSchemeMap (V : SmallEtale B S hS (yoneda.obj T)) :
    chartScheme V ⟶ representedSchemeRepresentedZariskiRingedToposHom B S hS T :=
  (BigFppfOver.toScheme B S hS).map (representedChartMap V)

/-- An étale chart of `yoneda.obj T` maps to the identity chart. -/
def representedChartToIdentity (V : SmallEtale B S hS (yoneda.obj T)) : V ⟶ idEtaleChart B S hS T :=
  ObjectProperty.homMk (CostructuredArrow.homMk (representedChartMap V) (by
    change yoneda.map (yoneda.preimage V.obj.hom) ≫ 𝟙 _ = V.obj.hom
    rw [Category.comp_id, Functor.map_preimage]))

/-- A lift of a geometric point into an étale chart composes with the structure morphism of the
chart to the defining section of the geometric point. -/
theorem geometricFiber_comp_representedChartMap {V : SmallEtale B S hS (yoneda.obj T)}
    (p : GeometricFiber B S hS (yoneda.obj T) x V) :
    p.1 ≫ representedChartMap V = x.val.value := by
  calc p.1 ≫ representedChartMap V
      = (yoneda.map (representedChartMap V)).app (op x.val.siteObject) p.1 := rfl
    _ = V.obj.hom.app (op x.val.siteObject) p.1 := by rw [Functor.map_preimage]
    _ = x.val.value := p.2

/-- The point under a geometric point lifting to an étale chart is the image of the point of the
chart. -/
theorem representedPoint_eq_of_geometricFiber {V : SmallEtale B S hS (yoneda.obj T)}
    (p : GeometricFiber B S hS (yoneda.obj T) x V) :
    representedPoint x = (representedChartSchemeMap V).base
      (chartPoint B S hS (yoneda.obj T) (⟨V, p.1, p.2⟩ : SmallEtaleNeighborhood x)) := by
  have h := congrArg (fun k : x.val.siteObject ⟶ T => ((BigFppfOver.toScheme B S hS).map k).base
    (IsLocalRing.closedPoint (chartGeometricPoint (yonedaIdentityNeighborhood T x)).residueField))
    (geometricFiber_comp_representedChartMap x p)
  exact h.symm.trans <| congrArg (fun k : (BigFppfOver.toScheme B S hS).obj x.val.siteObject ⟶
      representedSchemeRepresentedZariskiRingedToposHom B S hS T => k.base
        (IsLocalRing.closedPoint
          (chartGeometricPoint (yonedaIdentityNeighborhood T x)).residueField))
    ((BigFppfOver.toScheme B S hS).map_comp p.1 (representedChartMap V))

/-- Every point of an étale chart of `yoneda.obj T` is the point of the chart under a lift of a
geometric point. -/
theorem exists_geometricFiber_chartPoint_eq (V : SmallEtale B S hS (yoneda.obj T))
    (v : chartScheme V) :
    ∃ (x : GeometricPoint B S hS (yoneda.obj T)) (p : GeometricFiber B S hS (yoneda.obj T) x V),
      chartPoint B S hS (yoneda.obj T) (⟨V, p.1, p.2⟩ : SmallEtaleNeighborhood x) = v := by
  let κ := (chartScheme V).residueField v
  have hΩ : B.Contains (Spec (.of (AlgebraicClosure κ))) :=
    B.contains_spec_algebraicClosure (B.residueField_spec_contains V.obj.left.left.property v)
  let σ : Spec (.of (AlgebraicClosure κ)) ⟶ chartScheme V :=
    Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ))) ≫
      (chartScheme V).fromSpecResidueField v
  let tb := (σ ≫ representedChartSchemeMap V) ≫ B.inclusion.map T.hom
  let x := geometricPointOfSpecHom B S hS T hΩ tb (σ ≫ representedChartSchemeMap V) rfl
  let p₁ : x.val.siteObject ⟶ V.obj.left := Over.homMk (ObjectProperty.homMk σ) (by
    apply ObjectProperty.hom_ext
    show σ ≫ (V.obj.left.hom).hom = (σ ≫ representedChartSchemeMap V) ≫ (T.hom).hom
    rw [Category.assoc]
    exact congrArg (fun k => σ ≫ k.hom) (Over.w (representedChartMap V)).symm)
  have hp : V.obj.hom.app (op x.val.siteObject) p₁ = x.val.value := by
    calc V.obj.hom.app (op x.val.siteObject) p₁
        = (yoneda.map (representedChartMap V)).app (op x.val.siteObject) p₁ := by
          rw [Functor.map_preimage]
      _ = x.val.value := by
          apply Over.OverMorphism.ext
          apply ObjectProperty.hom_ext
          rfl
  exact ⟨x, ⟨p₁, hp⟩, closedPoint_algebraicClosure_residueField_map v⟩

end Local

end AlgebraicGeometry.Space

end
