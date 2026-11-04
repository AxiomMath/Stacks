module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesNegativeSelfExt
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectColimitHeld
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback

/-!
# Relative perfectness is stable under arbitrary base change (Stacks 0DKT)

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces with `f` flat and locally of finite presentation.  If
`E ∈ D(𝒪_X)` is `Y`-perfect, then `L(g')^*E` is `Y'`-perfect.  This is Stacks 0DKT, stated
as the proposition `AlgebraicGeometry.Space.RelativelyPerfectBaseChangeStable` (`h0DKT`).
This file proves that proposition, and the consumers of `h0DKT` with it discharged.

`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_pull_of_isPullback` proves the statement
when `g'` is representable.  Representability was used only to cover the small étale site of
`X'` by base changes along `g'` of slices of the small étale site of `X` on which `E` has bounded
Tor amplitude.  Here those base changes are replaced by the étale charts `V'` of `X'` admitting a
morphism over `g'` to such a slice (`exists_chart_over`, `exists_chart_pullback`, as for Stacks
08H4); the bound is read at the geometric points, where it only depends on the image point, and
the stalk computation of the representable case goes through unchanged.  The pseudo-coherence
clause is Stacks 08H4 for an arbitrary morphism of algebraic spaces,
`AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullback`.

Nothing here is registered.  The covering step follows the route of
`generate_mem_topology_of_isPullback_cover` in an independent development of the same result.

## Main results

* `AlgebraicGeometry.Space.generate_mem_topology_chartsOver_of_cover`: the charts of `X'` over
  good objects of the small étale site of `X` cover.
* `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_pull_of_isPullback_general`: the Tor
  clause of relative perfectness survives pullback along any cartesian square.
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_pull_of_isPullback_general`: relative
  perfectness survives pullback along any cartesian square.
* `AlgebraicGeometry.Space.relativelyPerfectBaseChangeStable`: the proposition
  `AlgebraicGeometry.Space.RelativelyPerfectBaseChangeStable` holds.
* `AlgebraicGeometry.Space.RelativeDescentSituation.isStagePerfect_pull_sourceTransition`,
  `isLimitPerfect_pull_sourceProjection`: clauses (1) and (2) of Stacks 0DKW.
* `AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_of_halves`:
  Stacks 0DKW from its two remaining halves, with no Stacks 0DKT input.
* `AlgebraicGeometry.Space.ComplexesSituation.conditions_overBaseChange`: part (a) of
  Stacks 0DLD.

## References

* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.DerivedTensorProduct (hasTorAmplitudeCanonical_derivedModuleFiber
  hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
  locallyHasFiniteTorDimension_of_stalkwise_family)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v

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

/-- **Charts of the source over good objects of the target cover.** Let `g' : X' ⟶ X` be a
morphism of algebraic spaces and `P` a property of the objects of the small étale site of `X`
which is inherited along morphisms and holds on the members of a covering of every object.  Then
every object `U'` of the small étale site of `X'` is covered by the objects `V'` admitting a
morphism over `g'` to an object satisfying `P`. -/
theorem generate_mem_topology_chartsOver_of_cover {X' X : AlgebraicSpaces B S hS} (g' : X' ⟶ X)
    (P : SmallEtale B S hS X.1 → Prop)
    (hP : ∀ U : SmallEtale B S hS X.1, ∃ R : Presieve U,
      Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧ ∀ ⦃V⦄ (k : V ⟶ U), R k → P V)
    (hmono : ∀ {W W' : SmallEtale B S hS X.1} (_ : W' ⟶ W), P W → P W')
    (U' : SmallEtale B S hS X'.1) :
    Sieve.generate (fun (V' : SmallEtale B S hS X'.1) (_ : V' ⟶ U') =>
        ∃ (W : SmallEtale B S hS X.1) (q : V'.1.left ⟶ W.1.left),
          yoneda.map q ≫ W.1.hom = V'.1.hom ≫ g'.hom ∧ P W) ∈
      SmallEtale.topology B S hS X'.1 U' := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro z
  obtain ⟨A₀, a₀, ha₀S, ha₀E⟩ := X.2.exists_atlas
  let W₀ : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a₀, ha₀E⟩
  obtain ⟨V₁, π₁, q₁, hq₁, z₁, hz₁⟩ := exists_chart_over B S hS g' U' W₀ ha₀S z
  obtain ⟨R₀, hR₀, hR₀P⟩ := hP W₀
  obtain ⟨W', m₀, ⟨W'', m', m'', hm'', rfl⟩, w, hw⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 _).1 hR₀
      (((BigFppfOver.toScheme B S hS).map q₁) z₁)
  obtain ⟨T', π, p', hp', -, w', hw'₁, -⟩ :=
    exists_chart_pullback B S hS g' V₁ q₁ hq₁ (m' ≫ m'') z₁ w hw.symm
  refine ⟨T', π ≫ π₁, Sieve.le_generate _ _ _ ⟨W', p', hp', hmono m' (hR₀P m'' hm'')⟩, w', ?_⟩
  rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw'₁, hz₁]

/-- **The Tor clause of relative perfectness survives pullback along any cartesian square**,
Stacks 0DKD (1).  Let `φ : Z ⟶ W`, `p : Z ⟶ V`, `q : W ⟶ U`, `h : V ⟶ U` be a cartesian square
of algebraic spaces with `q` flat.  If an object `E` of `D(𝒪_W)`, read over `q⁻¹𝒪_U`, locally has
finite Tor dimension, then so does its derived pullback along `φ`, read over `p⁻¹𝒪_V`.

This is `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_pull_of_isPullback` without the
representability of `φ`: the covering of the small étale site of `Z` is by the charts of `Z`
over `φ` to slices of the small étale site of `W` on which `E` has bounded Tor amplitude
(`AlgebraicGeometry.Space.generate_mem_topology_chartsOver_of_cover`), and the bound is read at
the geometric points of `W`. -/
theorem locallyHasFiniteTorDimension_pull_of_isPullback_general
    {Z W V U : AlgebraicSpaces B S hS}
    {φ : Z ⟶ W} {p : Z ⟶ V} {q : W ⟶ U} {h : V ⟶ U} (hpb : IsPullback φ p q h)
    (hq : IsFlat B S hS q.hom) (E : derivedModules B S hS W)
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
  let eS : (derivedScalarRestriction B S hS q).obj E ≅
      DerivedCategory.Q.obj
        (((scalarRestriction B S hS q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (derivedScalarRestriction B S hS q).mapIso eK.symm ≪≫
      (derivedScalarRestrictionFactors B S hS q).app K
  -- the objects of the small étale site of `W` over which the stalks of `E`, read over the base,
  -- have Tor amplitude in one interval
  let P : SmallEtale B S hS W.1 → Prop := fun W₀ => ∃ a b : ℤ,
    ∀ (x : GeometricPoint B S hS W.1) (_ : (etaleSitePoint B S hS W.1 x W.2).fiber.obj W₀),
      let := HasDerivedCategory.standard (ModuleCat.{u}
        (((etaleSitePoint B S hS W.1 x W.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS q).O.obj))
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS W.1 x W.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS q).O.obj)
        (DerivedCategory.Q.obj
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
            (inverseImageRingedSite B S hS q).O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((scalarRestriction B S hS q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
        a b
  have hP : ∀ W₀ : SmallEtale B S hS W.1, ∃ R : Presieve W₀,
      Sieve.generate R ∈ SmallEtale.topology B S hS W.1 W₀ ∧ ∀ ⦃V₀⦄ (k : V₀ ⟶ W₀), R k → P V₀ := by
    intro W₀
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
    have hX1 := (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso
      (Functor.mapIso _ ((RingedSite.derivedRestriction _ W').mapIso eS)) a b).1 hX0
    exact (hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
      (Z := inverseImageRingedSite B S hS q) W'
      (etaleSitePoint B S hS W.1 x W.2) qW
      (((scalarRestriction B S hS q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a b).1 hX1
  have hmono : ∀ {W₁ W₂ : SmallEtale B S hS W.1} (_ : W₂ ⟶ W₁), P W₁ → P W₂ :=
    fun m ⟨a, b, hab⟩ => ⟨a, b, fun x r => hab x ((etaleSitePoint B S hS W.1 x W.2).fiber.map m r)⟩
  refine locallyHasFiniteTorDimension_of_stalkwise_family
    (Z := inverseImageRingedSite B S hS p) _ _
    (t := fun V => Σ x : GeometricPoint B S hS Z.1,
      (etaleSitePoint B S hS Z.1 x Z.2).fiber.obj V)
    (fun V k => (etaleSitePoint B S hS Z.1 k.1 Z.2).over k.2)
    (fun V => isConservativeFamilyOfPoints_etaleSitePointOver B S hS Z.2 V) ?_
  intro U'
  refine ⟨_, generate_mem_topology_chartsOver_of_cover φ P hP hmono U', ?_⟩
  rintro V' g ⟨W₀, q₀, hq₀, a, b, hW⟩
  refine ⟨a, b, ?_⟩
  rintro ⟨x', r⟩
  -- the point of the small étale site of `W` under `x'`, on the slice over `W₀`
  let qW : (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x') W.2).fiber.obj W₀ :=
    ⟨r.1 ≫ q₀, (congrArg (fun α => α.app (Opposite.op x'.val.siteObject) r.1) hq₀).trans
      (congrArg (φ.hom.app (Opposite.op x'.val.siteObject)) r.2)⟩
  have hX3 := (hasTorAmplitudeCanonical_scalarRestriction_stalk_iff B S hS q
    (geometricPointMap φ.hom x') K a b).1 (hW _ qW)
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

/-- **Relative perfectness survives pullback along any cartesian square**, Stacks 0DKT.  Let
`φ : Z ⟶ W`, `p : Z ⟶ V`, `q : W ⟶ U`, `h : V ⟶ U` be a cartesian square of algebraic spaces
with `p`, `q` flat and locally of finite presentation.  If an object `E` of `D(𝒪_W)` is perfect
relative to `U`, then `Lφ^*E` is perfect relative to `V`.

This is `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_pull_of_isPullback` without the
representability of `φ`.  The pseudo-coherence clause is Stacks 08H4 for algebraic spaces; the
Tor clause is `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_pull_of_isPullback_general`. -/
theorem isPerfectRelativeToCanonical_pull_of_isPullback_general
    {Z W V U : AlgebraicSpaces B S hS}
    {φ : Z ⟶ W} {p : Z ⟶ V} {q : W ⟶ U} {h : V ⟶ U} (hpb : IsPullback φ p q h)
    (hpflat : IsFlat B S hS p.hom) (hplfp : IsLocallyOfFinitePresentation B S hS p.hom)
    (hqflat : IsFlat B S hS q.hom) (hqlfp : IsLocallyOfFinitePresentation B S hS q.hom)
    (E : derivedModules B S hS W) (hE : IsPerfectRelativeToCanonical B S hS q hqflat hqlfp E) :
    IsPerfectRelativeToCanonical B S hS p hpflat hplfp
      (((smallEtaleDerivedPullbackData B S hS).pull φ).obj E) :=
  ⟨isPseudoCoherent_smallEtaleDerivedModulePullback φ E hE.1,
    locallyHasFiniteTorDimension_pull_of_isPullback_general hpb hqflat E hE.2⟩

variable (B S hS) in
/-- **Stacks 0DKT**, as a proposition
(`AlgebraicGeometry.Space.RelativelyPerfectBaseChangeStable`, `h0DKT`):
for a flat, locally finitely presented `f : X ⟶ Y`, a morphism `g : Y' ⟶ Y` and the cartesian
square `X' = X ×_Y Y'` with projections `g'` and `f'`, the derived pullback `L(g')^*E` of a
`Y`-perfect `E` is `Y'`-perfect.  Unregistered. -/
theorem relativelyPerfectBaseChangeStable : RelativelyPerfectBaseChangeStable B S hS :=
  fun _f _g _g' _f' hpb hflat hlfp hflat' hlfp' E hE =>
    isPerfectRelativeToCanonical_pull_of_isPullback_general hpb hflat' hlfp' hflat hlfp E hE

/-! ### The consumers of Stacks 0DKT with it discharged -/

namespace RelativeDescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- **Clause (1) of Stacks 0DKW**: the transition functors `Lf_{ji}^*` carry `Yᵢ`-perfect
objects to `Yⱼ`-perfect objects.  `isStagePerfect_transition` with `h0DKT` discharged by
`AlgebraicGeometry.Space.relativelyPerfectBaseChangeStable`. -/
theorem isStagePerfect_pull_sourceTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (E : derivedModules B S hS (D.stageSource i)) (hE : D.IsStagePerfect i E) :
    D.IsStagePerfect j (((smallEtaleDerivedPullbackData B S hS).pull
      (D.sourceTransition h)).obj E) :=
  D.isStagePerfect_transition (relativelyPerfectBaseChangeStable B S hS) h E hE

/-- **Clause (2) of Stacks 0DKW**: the comparison functors `Lfᵢ^*` carry `Yᵢ`-perfect objects
to `Y`-perfect objects.  `isLimitPerfect_projection` with `h0DKT` discharged by
`AlgebraicGeometry.Space.relativelyPerfectBaseChangeStable`. -/
theorem isLimitPerfect_pull_sourceProjection (i : D.LaterIndex)
    (E : derivedModules B S hS (D.stageSource i)) (hE : D.IsStagePerfect i E) :
    D.IsLimitPerfect (((smallEtaleDerivedPullbackData B S hS).pull
      (D.sourceProjection i)).obj E) :=
  D.isLimitPerfect_projection (relativelyPerfectBaseChangeStable B S hS) i E hE

/-- **Stacks 0DKW from its two remaining halves**: fullness and faithfulness (`hff`, from
Stacks 0DKV, not yet proved here) and essential surjectivity (`hes`, internal, in progress).
`relativelyPerfectColimit_of_held` with `h0DKT` discharged by
`AlgebraicGeometry.Space.relativelyPerfectBaseChangeStable`. -/
theorem relativelyPerfectColimit_of_halves (hff : D.RelativelyPerfectFullyFaithful)
    (hes : D.RelativelyPerfectEssentiallySurjective) : D.RelativelyPerfectColimit :=
  D.relativelyPerfectColimit_of_held (relativelyPerfectBaseChangeStable B S hS) hff hes

end RelativeDescentSituation

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-- **Part (a) of Stacks 0DLD.** If `E` in `D(𝒪_X)` is `Y`-perfect and its negative
self-extensions vanish on every fibre over a point with values in a field, then for every
algebraic space `V` over `Y` the derived pullback `E_V` of `E` to `X_V` satisfies both
conditions for `X_V ⟶ V`.  `conditions_overBaseChange_of` with `h0DKT` discharged by
`AlgebraicGeometry.Space.relativelyPerfectBaseChangeStable`. -/
theorem conditions_overBaseChange (E : derivedModules B S hS D.X)
    (h1 : IsPerfectRelativeToCanonical B S hS D.f D.flat D.finitePresentation.1 E)
    (h2 : HasNoNegativeFieldFibreExt D.f E) (V : Over D.Y) :
    IsPerfectRelativeToCanonical B S hS (overInclusion D.f V) (D.overInclusion_isFlat V)
        (D.overInclusion_isLocallyOfFinitePresentation V)
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E) ∧
      HasNoNegativeFieldFibreExt (overInclusion D.f V)
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E) :=
  D.conditions_overBaseChange_of (relativelyPerfectBaseChangeStable B S hS) E h1 h2 V

end ComplexesSituation

end AlgebraicGeometry.Space

end
