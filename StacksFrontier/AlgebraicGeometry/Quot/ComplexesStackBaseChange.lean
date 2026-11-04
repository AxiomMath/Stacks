module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.StalkwiseFiniteTor
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentPullbackRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeStalks
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StalkPullbackComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StalkRelativeTorAmplitudeBaseChange
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkOverTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Point.StalkKFlatColimit

/-!
# Condition (1) of Stacks 0DLD survives pullback along a morphism of test schemes

In the situation of Stacks 0DLE let `h : T ⟶ T'` be a morphism of test schemes over `Y` and let
`E` be an object of `D(𝒪_{X_{T'}})` perfect relative to `T'`.  Then the derived pullback of `E`
along the morphism of base changes `X_h : X_T ⟶ X_{T'}` is perfect relative to `T`.  This is
the instance of Stacks 0DKT at the cartesian square

```
X_T --X_h--> X_{T'}
 |             |
 v             v
 T  ---h--->   T'
```

and it is the input that the lifting half of Stacks 0DLF needs.

Both clauses of relative perfectness are carried separately.  Pseudo-coherence is Stacks 08H4
for the morphism `X_h`, which is representable, being the base change of a morphism of schemes:
`AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable`.  The
Tor clause is read at the stalks, as in the source's proof of Stacks 0DKD (1).  `E` is represented
by a K-flat complex `K` which is a sequential colimit of bounded above complexes of flat modules
(Stacks 06YS), so `L(X_h)^*E` is the degreewise pullback of `K` (Stacks 06YY) and every stalk of
`K` is K-flat.  Tor amplitude on a slice of the small étale site is read at the points of that
slice (Stacks 0DJJ); at a point lying over a geometric point `x̄'` of `X_T`, the stalk of the
pullback is the extension of scalars of the stalk of `K` at the image `x̄` of `x̄'` (Stacks 05V5),
and the Tor amplitude of the stalk of `K` over the base at `x̄` transfers along the cartesian
square of stalk rings, which is the commutative algebra of
`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_structureStalk_of_cartesian`.  The slices are
covered by base changes along `X_h` of slices of the small étale site of `X_{T'}` on which `E` has
bounded Tor amplitude.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.locallyHasFiniteTorDimension_pull`: the Tor
  clause.
* `AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectBaseChange`: condition (1) of
  Stacks 0DLD survives pullback.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor_isFiberedInGroupoids`:
  **Stacks 0DLF**, the functor `p : Complexes_{X/B} ⥤ (Sch/S)_fppf` is fibred in groupoids.

## References

* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.DerivedTensorProduct (hasTorAmplitudeCanonical_derivedModuleFiber
  hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
  locallyHasFiniteTorDimension_of_stalkwise_family)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

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

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)

/-- **The Tor clause of relative perfectness survives pullback along a morphism of test
schemes**, Stacks 0DKD (1) at the cartesian square defining `X_T`.  If an object `E` of
`D(𝒪_{X_{T'}})`, read over the inverse image of the structure sheaf of `T'`, locally has finite
Tor dimension, then so does its derived pullback along `X_h : X_T ⟶ X_{T'}`, read over the
inverse image of the structure sheaf of `T`.

The condition is checked at the points of the slices of the small étale site of `X_T`, over the
covering by base changes along `X_h` of slices of the small étale site of `X_{T'}` on which `E`
has bounded Tor amplitude.  At such a point the derived stalk is identified with a complex of
modules over the stalk ring of `T`, which is the derived base change of the stalk of a K-flat
representative of `E`, and the bound is transferred along the cartesian square of stalk rings. -/
theorem locallyHasFiniteTorDimension_pull {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (E : derivedModules B S hS (D.space T'))
    (hE : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS (D.projection T'))
      ((derivedScalarRestriction B S hS (D.projection T')).obj E)) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS (D.projection T))
      ((derivedScalarRestriction B S hS (D.projection T)).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E)) := by
  have hg := relativelyRepresentable_baseChangeMap B S hS D.f h
  have hpb := isPullback_baseChangeMap D.f h
  -- a K-flat representative of `E` which is a sequential colimit of bounded above flat complexes
  let K₀ : CochainComplex (Modules.{u, u} B S hS (D.space T').1 (D.space T').2) ℤ :=
    DerivedCategory.Q.objPreimage E
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize
    (smallEtaleRingedTopos B S hS (D.space T')).O
  obtain ⟨Dn, α, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize
      (smallEtaleRingedTopos B S hS (D.space T')).O K₀
  have hDn : HasColimit Dn := inferInstance
  let K : CochainComplex (Modules.{u, u} B S hS (D.space T').1 (D.space T').2) ℤ :=
    (Arrow.mk α).left
  let α' : K ⟶ K₀ := α
  have hQα : IsIso (DerivedCategory.Q.map α') := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hqis
  let eK : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map α') ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have := Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize
    (smallEtaleRingedTopos B S hS (D.space T')).O
  have hKflat : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS (D.space T'))
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
    ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
      _ Dn hLE hflat,
      Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize _ Dn hflat⟩
  have hDn' : HasColimit (show ℕ ⥤ CochainComplex (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u}
        (smallEtaleRingedTopos B S hS (D.space T')).O)) ℤ from Dn) := hDn
  have hstalk : ∀ x, CochainComplex.KFlat.{u, u}
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS (D.space T').1 x (D.space T').2)
        (smallEtaleRingedTopos B S hS (D.space T')).O).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := fun x =>
    Stacks.kFlat_mapHomologicalComplex_sheafModuleFiber_colimit
      (etaleSitePoint B S hS (D.space T').1 x (D.space T').2)
      (smallEtaleRingedTopos B S hS (D.space T')).O _ hLE hflat
  -- the objects of the small étale site of `X_{T'}` on which `E` has bounded Tor amplitude
  have := isContinuous_smallBaseChange B S hS (D.relativeMap h) hg
  have hcov := GrothendieckTopology.coversTop_obj_subtype
    (smallBaseChange B S hS (D.relativeMap h) hg) (SmallEtale.topology B S hS (D.space T').1)
    (SmallEtale.topology B S hS (D.space T).1)
    (coversTop_smallBaseChange B S hS (D.relativeMap h) hg)
    _ hE
  refine locallyHasFiniteTorDimension_of_stalkwise_family
    (Z := inverseImageRingedSite B S hS (D.projection T)) _ _
    (t := fun V => Σ x : GeometricPoint B S hS (D.space T).1,
      (etaleSitePoint B S hS (D.space T).1 x (D.space T).2).fiber.obj V)
    (fun V k => (etaleSitePoint B S hS (D.space T).1 k.1 (D.space T).2).over k.2)
    (fun V => isConservativeFamilyOfPoints_etaleSitePointOver B S hS (D.space T).2 V) ?_
  intro U
  refine ⟨(Sieve.ofObjects _ U).arrows, by rw [Sieve.generate_sieve]; exact hcov U, ?_⟩
  rintro V g ⟨⟨W, hW⟩, ⟨k⟩⟩
  obtain ⟨a, b, hab⟩ := hW
  let W' : (inverseImageRingedSite B S hS (D.projection T')).C := W
  have hab' : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (canonicalSliceDerivedTensorProduct B S hS (D.projection T') W')
      ((RingedSite.derivedRestriction _ W').obj
        ((derivedScalarRestriction B S hS (D.projection T')).obj E)) a b := hab
  refine ⟨a, b, ?_⟩
  rintro ⟨x', q⟩
  -- the point of the small étale site of `X_{T'}` lying under `x'`, on the slice over `W`
  let qW : (etaleSitePoint B S hS (D.space T').1
      (geometricPointMap (D.relativeMap h).hom x') (D.space T').2).fiber.obj W' :=
    (smallBaseChangeFiberMap B S hS (D.relativeMap h) hg x').app W
      ((etaleSitePoint B S hS (D.space T).1 x' (D.space T).2).fiber.map k q)
  have hX0 := hasTorAmplitudeCanonical_derivedModuleFiber
    (Y := (inverseImageRingedSite B S hS (D.projection T')).over W') _ _ a b hab'
    ((etaleSitePoint B S hS (D.space T').1 (geometricPointMap (D.relativeMap h).hom x')
      (D.space T').2).over qW)
  let eS : (derivedScalarRestriction B S hS (D.projection T')).obj E ≅
      DerivedCategory.Q.obj
        (((scalarRestriction B S hS (D.projection T')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
    (derivedScalarRestriction B S hS (D.projection T')).mapIso eK.symm ≪≫
      (derivedScalarRestrictionFactors B S hS (D.projection T')).app K
  have hX1 := (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
    (Functor.mapIso _ ((RingedSite.derivedRestriction _ W').mapIso eS)) a b).1 hX0
  have hX2 := (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (Z := inverseImageRingedSite B S hS (D.projection T')) W'
    (etaleSitePoint B S hS (D.space T').1 (geometricPointMap (D.relativeMap h).hom x')
      (D.space T').2) qW
    (((scalarRestriction B S hS (D.projection T')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) a b).1 hX1
  have hX3 := (hasTorAmplitudeCanonical_scalarRestriction_stalk_iff B S hS (D.projection T')
    (geometricPointMap (D.relativeMap h).hom x') K a b).1 hX2
  -- the stalk of `L(X_h)^* E` at `x'`, read over the base, is the derived base change of the
  -- stalk of `E` at the image of `x'`
  let e2 : (derivedScalarRestriction B S hS (D.projection T)).obj
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E) ≅
      DerivedCategory.Q.obj (((scalarRestriction B S hS (D.projection T)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((((smallEtaleRingedToposHom B S hS (D.relativeMap h)).toModulesHom.pullbackModules
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    (derivedScalarRestriction B S hS (D.projection T)).mapIso
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).mapIso eK.symm ≪≫
        derivedPullbackObjIsoOfIsKFlat B S hS (D.relativeMap h) K hKflat) ≪≫
      (derivedScalarRestrictionFactors B S hS (D.projection T)).app _
  refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
    (Functor.mapIso _ ((RingedSite.derivedRestriction _ V).mapIso e2)) a b).2 ?_
  refine (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (Z := inverseImageRingedSite B S hS (D.projection T)) V
    (etaleSitePoint B S hS (D.space T).1 x' (D.space T).2) q _ a b).2 ?_
  refine (hasTorAmplitudeCanonical_scalarRestriction_stalk_iff B S hS (D.projection T) x' _ a
    b).2 ?_
  let := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS
    ((schemeSpaceFunctor B S hS).obj T.left) (geometricPointMap (D.projection T).hom x')))
  let := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS
    (D.space T') (geometricPointMap (D.relativeMap h).hom x')))
  let := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS
    ((schemeSpaceFunctor B S hS).obj T'.left)
      (geometricPointMap (D.projection T').hom (geometricPointMap (D.relativeMap h).hom x'))))
  refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
    (DerivedCategory.Q.mapIso (((ModuleCat.restrictScalars.{u}
      (smallEtaleStalkPullbackRingMap B S hS (D.projection T) x')).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (pullbackModulesStalkComplexIso B S hS (D.relativeMap h) x' K))) a b).2 ?_
  exact hasTorAmplitudeCanonical_structureStalk_of_cartesian B S hS (D.relativeMap h)
    (D.projection T) (D.projection T') ((schemeSpaceFunctor B S hS).map h.left) hpb
    (D.projection_isFlat T') x' _ (hstalk _) a b
    ((StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
      ((ModuleCat.restrictScalars.{u} (smallEtaleStalkPullbackRingMap B S hS (D.projection T')
        (geometricPointMap (D.relativeMap h).hom x'))).mapDerivedCategoryFactors.app _) a b).2
      hX3)

/-- **Condition (1) of Stacks 0DLD survives pullback along a morphism of test schemes**: the
instance of Stacks 0DKT at the cartesian square defining `X_T`.  The pseudo-coherence clause is
Stacks 08H4 for the representable morphism `X_h`; the Tor clause is
`AlgebraicGeometry.Space.ComplexesSituation.locallyHasFiniteTorDimension_pull`. -/
theorem relativelyPerfectBaseChange : D.RelativelyPerfectBaseChange := fun h E hE =>
  ⟨isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS (D.relativeMap h)
    (relativelyRepresentable_baseChangeMap B S hS D.f h) E hE.1,
    D.locallyHasFiniteTorDimension_pull h E hE.2⟩

/-- **Stacks 0DLF.**  In Situation 0DLE the functor `p : Complexes_{X/B} ⥤ (Sch/S)_fppf`,
`(T, g, E) ↦ T`, is fibred in groupoids: every morphism `h : T ⟶ T'` of schemes over `S` lifts
at every object `(T', g', E')`, to `(T, g' ∘ h, L(h')^*E') ⟶ (T', g', E')` with the identity as
comparison of complexes, and fill-ins exist and are unique.

The lift is an object because both conditions of Stacks 0DLD survive pullback
(`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectBaseChange` and
`AlgebraicGeometry.Space.ComplexesSituation.hasNoNegativeFibreExt_pull`); the fill-in is
`AlgebraicGeometry.Space.ComplexesSituation.fillIn`. -/
@[stacks 0DLF "the functor p : Complexes_{X/B} ⥤ (Sch/S)_fppf, (T, g, E) ↦ T, is fibred in
groupoids"]
theorem complexesFunctor_isFiberedInGroupoids :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    (complexesFunctor D).IsFiberedInGroupoids :=
  let : Category.{u + 1} (ComplexesObject D) := complexesCategory D
  complexesFunctor_isFiberedInGroupoids_of D (relativelyPerfectBaseChange D)

end AlgebraicGeometry.Space.ComplexesSituation

end
