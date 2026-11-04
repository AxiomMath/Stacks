module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesFibreExtBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChange

/-!
# The two conditions of Stacks 0DLD under pullback along a cartesian square

Let

```
Z --φ--> W
|        |
p        q
v        v
V --h--> U
```

be a cartesian square of algebraic spaces with `q` flat and locally of finite presentation and
`φ` representable.  If an object `E` of `D(𝒪_W)` is perfect relative to `U` (Stacks 0DKN), then
its derived pullback `Lφ^*E` is perfect relative to `V`: this is Stacks 0DKT at the square.
`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectBaseChange` proves it at the squares
defining the base changes `X_T` of the situation of Stacks 0DLE; the proof given there uses of
the square only that it is cartesian, that `φ` is representable and that `q` is flat, and it is
carried out here at an arbitrary such square.

Condition (2) of Stacks 0DLD for an object of `Complexes_{X/Y}` is likewise read at *every*
model of a fibre, not only at the chosen base change: that is
`AlgebraicGeometry.Space.ComplexesSituation.HasNoNegativeFibreExt.of_isPullback`.

These are what transports an object of `Complexes_{X'/Y'}` to one of `Complexes_{X/Y}` along the
comparison `X'_T ≅ X_T` of the two base changes, in Remark 0DLI.

## Main results

* `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_pull_of_isPullback`: the Tor clause of
  relative perfectness survives pullback along a cartesian square (Stacks 0DKD (1)).
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_pull_of_isPullback`: relative
  perfectness survives pullback along a cartesian square (Stacks 0DKT).
* `AlgebraicGeometry.Space.ComplexesSituation.HasNoNegativeFibreExt.of_isPullback`: condition (2)
  of Stacks 0DLD holds at every model of a fibre.

## References

* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
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

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The Tor clause of relative perfectness survives pullback along a cartesian square**,
Stacks 0DKD (1).  Let `φ : Z ⟶ W`, `p : Z ⟶ V`, `q : W ⟶ U`, `h : V ⟶ U` be a cartesian square
of algebraic spaces with `φ` representable and `q` flat.  If an object `E` of `D(𝒪_W)`, read over
`q⁻¹𝒪_U`, locally has finite Tor dimension, then so does its derived pullback along `φ`, read over
`p⁻¹𝒪_V`.

This is the proof of `AlgebraicGeometry.Space.ComplexesSituation.locallyHasFiniteTorDimension_pull`
at an arbitrary such square.  The condition is checked at the points of the slices of the small
étale site of `Z`, over the covering by base changes along `φ` of slices of the small étale site
of `W` on which `E` has bounded Tor amplitude.  At such a point the derived stalk is identified
with a complex of modules over the stalk ring of `V`, which is the derived base change of the
stalk of a K-flat representative of `E`, and the bound is transferred along the cartesian square
of stalk rings. -/
theorem locallyHasFiniteTorDimension_pull_of_isPullback {Z W V U : AlgebraicSpaces B S hS}
    {φ : Z ⟶ W} {p : Z ⟶ V} {q : W ⟶ U} {h : V ⟶ U} (hpb : IsPullback φ p q h)
    (hg : yoneda.relativelyRepresentable φ.hom) (hq : IsFlat B S hS q.hom)
    (E : derivedModules B S hS W)
    (hE : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS q) ((derivedScalarRestriction B S hS q).obj E)) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS p)
      ((derivedScalarRestriction B S hS p).obj
        (((smallEtaleDerivedPullbackData B S hS).pull φ).obj E)) := by
  -- a K-flat representative of `E` which is a sequential colimit of bounded above flat complexes
  let K₀ : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ :=
    DerivedCategory.Q.objPreimage E
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize
    (smallEtaleRingedTopos B S hS W).O
  obtain ⟨Dn, α, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize
      (smallEtaleRingedTopos B S hS W).O K₀
  have hDn : HasColimit Dn := inferInstance
  let K : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ := (Arrow.mk α).left
  let α' : K ⟶ K₀ := α
  have hQα : IsIso (DerivedCategory.Q.map α') := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  let eK : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map α') ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have := Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize
    (smallEtaleRingedTopos B S hS W).O
  have hKflat : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS W)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
    ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
      _ Dn hLE hflat,
      Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize _ Dn hflat⟩
  have hDn' : HasColimit (show ℕ ⥤ CochainComplex (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u}
        (smallEtaleRingedTopos B S hS W).O)) ℤ from Dn) := hDn
  have hstalk : ∀ x, CochainComplex.KFlat.{u, u}
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
        (smallEtaleRingedTopos B S hS W).O).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := fun x =>
    Stacks.kFlat_mapHomologicalComplex_sheafModuleFiber_colimit
      (etaleSitePoint B S hS W.1 x W.2) (smallEtaleRingedTopos B S hS W).O _ hLE hflat
  -- the objects of the small étale site of `W` on which `E` has bounded Tor amplitude
  have := isContinuous_smallBaseChange B S hS φ hg
  have hcov := GrothendieckTopology.coversTop_obj_subtype
    (smallBaseChange B S hS φ hg) (SmallEtale.topology B S hS W.1)
    (SmallEtale.topology B S hS Z.1) (coversTop_smallBaseChange B S hS φ hg) _ hE
  refine locallyHasFiniteTorDimension_of_stalkwise_family
    (Z := inverseImageRingedSite B S hS p) _ _
    (t := fun V => Σ x : GeometricPoint B S hS Z.1,
      (etaleSitePoint B S hS Z.1 x Z.2).fiber.obj V)
    (fun V k => (etaleSitePoint B S hS Z.1 k.1 Z.2).over k.2)
    (fun V => isConservativeFamilyOfPoints_etaleSitePointOver B S hS Z.2 V) ?_
  intro U'
  refine ⟨(Sieve.ofObjects _ U').arrows, by rw [Sieve.generate_sieve]; exact hcov U', ?_⟩
  rintro V' g ⟨⟨W₀, a, b, hab⟩, ⟨k⟩⟩
  let W' : (inverseImageRingedSite B S hS q).C := W₀
  have hab' : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (canonicalSliceDerivedTensorProduct B S hS q W')
      ((RingedSite.derivedRestriction _ W').obj
        ((derivedScalarRestriction B S hS q).obj E)) a b := hab
  refine ⟨a, b, ?_⟩
  rintro ⟨x', r⟩
  -- the point of the small étale site of `W` lying under `x'`, on the slice over `W₀`
  let qW : (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x') W.2).fiber.obj W' :=
    (smallBaseChangeFiberMap B S hS φ hg x').app W₀
      ((etaleSitePoint B S hS Z.1 x' Z.2).fiber.map k r)
  have hX0 := hasTorAmplitudeCanonical_derivedModuleFiber
    (Y := (inverseImageRingedSite B S hS q).over W') _ _ a b hab'
    ((etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x') W.2).over qW)
  let eS : (derivedScalarRestriction B S hS q).obj E ≅
      DerivedCategory.Q.obj
        (((scalarRestriction B S hS q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (derivedScalarRestriction B S hS q).mapIso eK.symm ≪≫
      (derivedScalarRestrictionFactors B S hS q).app K
  have hX1 := (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
    (Functor.mapIso _ ((RingedSite.derivedRestriction _ W').mapIso eS)) a b).1 hX0
  have hX2 := (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (Z := inverseImageRingedSite B S hS q) W'
    (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x') W.2) qW
    (((scalarRestriction B S hS q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a b).1 hX1
  have hX3 := (hasTorAmplitudeCanonical_scalarRestriction_stalk_iff B S hS q
    (geometricPointMap φ.hom x') K a b).1 hX2
  -- the stalk of `Lφ^* E` at `x'`, read over the base, is the derived base change of the stalk
  -- of `E` at the image of `x'`
  let e2 : (derivedScalarRestriction B S hS p).obj
      (((smallEtaleDerivedPullbackData B S hS).pull φ).obj E) ≅
      DerivedCategory.Q.obj (((scalarRestriction B S hS p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((((smallEtaleRingedToposHom B S hS φ).toModulesHom.pullbackModules
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    (derivedScalarRestriction B S hS p).mapIso
      (((smallEtaleDerivedPullbackData B S hS).pull φ).mapIso eK.symm ≪≫
        derivedPullbackObjIsoOfIsKFlat B S hS φ K hKflat) ≪≫
      (derivedScalarRestrictionFactors B S hS p).app _
  refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
    (Functor.mapIso _ ((RingedSite.derivedRestriction _ V').mapIso e2)) a b).2 ?_
  refine (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (Z := inverseImageRingedSite B S hS p) V'
    (etaleSitePoint B S hS Z.1 x' Z.2) r _ a b).2 ?_
  refine (hasTorAmplitudeCanonical_scalarRestriction_stalk_iff B S hS p x' _ a b).2 ?_
  let := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS V
    (geometricPointMap p.hom x')))
  let := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS W
    (geometricPointMap φ.hom x')))
  let := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS U
    (geometricPointMap q.hom (geometricPointMap φ.hom x'))))
  refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
    (DerivedCategory.Q.mapIso (((ModuleCat.restrictScalars.{u}
      (smallEtaleStalkPullbackRingMap B S hS p x')).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (pullbackModulesStalkComplexIso B S hS φ x' K))) a b).2 ?_
  exact hasTorAmplitudeCanonical_structureStalk_of_cartesian B S hS φ p q h hpb hq x' _
    (hstalk _) a b
    ((StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
      ((ModuleCat.restrictScalars.{u} (smallEtaleStalkPullbackRingMap B S hS q
        (geometricPointMap φ.hom x'))).mapDerivedCategoryFactors.app _) a b).2 hX3)

/-- **Relative perfectness survives pullback along a cartesian square**, Stacks 0DKT.  Let
`φ : Z ⟶ W`, `p : Z ⟶ V`, `q : W ⟶ U`, `h : V ⟶ U` be a cartesian square of algebraic spaces with
`φ` representable and `p`, `q` flat and locally of finite presentation.  If an object `E` of
`D(𝒪_W)` is perfect relative to `U`, then `Lφ^*E` is perfect relative to `V`.

The pseudo-coherence clause is Stacks 08H4 for the representable morphism `φ`; the Tor clause is
`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_pull_of_isPullback`. -/
theorem isPerfectRelativeToCanonical_pull_of_isPullback {Z W V U : AlgebraicSpaces B S hS}
    {φ : Z ⟶ W} {p : Z ⟶ V} {q : W ⟶ U} {h : V ⟶ U} (hpb : IsPullback φ p q h)
    (hg : yoneda.relativelyRepresentable φ.hom) (hpflat : IsFlat B S hS p.hom)
    (hplfp : IsLocallyOfFinitePresentation B S hS p.hom) (hqflat : IsFlat B S hS q.hom)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q.hom) (E : derivedModules B S hS W)
    (hE : IsPerfectRelativeToCanonical B S hS q hqflat hqlfp E) :
    IsPerfectRelativeToCanonical B S hS p hpflat hplfp
      (((smallEtaleDerivedPullbackData B S hS).pull φ).obj E) :=
  ⟨isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS φ hg E hE.1,
    locallyHasFiniteTorDimension_pull_of_isPullback hpb hg hqflat E hE.2⟩

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-- **Condition (2) of Stacks 0DLD holds at every model of a fibre.**  Let `E` be an object of
`D(𝒪_{X_T})` whose negative self-extensions vanish on the fibres of `X_T ⟶ T` over the points with
values in a field, let `y : T₀ ⟶ T` be such a point, and let `Z` with `p : Z ⟶ X_T` and
`r : Z ⟶ T₀` be any cartesian square over `y`.  Then the negative self-extensions of the derived
pullback of `E` along `p` vanish: `Z` is isomorphic to the chosen base change `X_{T₀}`
compatibly with the morphisms to `X_T`, and the derived pullback along that isomorphism is an
equivalence commuting with the shift. -/
theorem HasNoNegativeFibreExt.of_isPullback {T : SchemesOver D.Y}
    {E : derivedModules B S hS (D.space T)} (hE : D.HasNoNegativeFibreExt T E)
    {T₀ : SchemesOver D.Y} (hT₀ : Stack.IsFieldObject B S hS T₀.left) (y : T₀ ⟶ T)
    {Z : AlgebraicSpaces B S hS} {p : Z ⟶ D.space T}
    {r : Z ⟶ (schemeSpaceFunctor B S hS).obj T₀.left}
    (hpb : IsPullback p r (D.projection T) ((schemeSpaceFunctor B S hS).map y.left)) (i : ℤ)
    (hi : i < 0) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull p).obj E ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull p).obj E)⟦i⟧) := by
  have hT := isPullback_baseChangeMap D.f y
  let φ : Z ≅ D.space T₀ := hpb.isoIsPullback _ _ hT
  have hφ : φ.hom ≫ D.relativeMap y = p := hpb.isoIsPullback_hom_fst _ _ hT
  exact subsingleton_hom_shift_of_iso
    (((smallEtaleDerivedPullbackData B S hS).triangle hφ).app E).symm i
    (subsingleton_hom_shift_pull_of_iso φ _ i (hE T₀ hT₀ y i hi))

end ComplexesSituation

end AlgebraicGeometry.Space

end
