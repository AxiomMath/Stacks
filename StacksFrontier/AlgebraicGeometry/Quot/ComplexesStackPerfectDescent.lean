module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeFpqcDescentLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands

/-!
# Relative perfectness descends along fppf coverings of the test schemes

In the situation of Stacks 0DLE, let `{T_i ⟶ T}` be an fppf covering of a test scheme `T` over
`Y` and let `E` be an object of `D_QCoh(𝒪_{X_T})` whose derived pullbacks to the `X_{T_i}` are
`T_i`-perfect. Then `E` is `T`-perfect. This is the step of the source's proof of Stacks 0DLH
which uses Stacks 0DL1 and Stacks 0DL2, and it discharges the hypothesis
`AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectDescends` of
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackDescent.lean`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isRelativelyPerfect_of_isFpqcCovering`: the
  descent along a family of test schemes over `T` which is an fpqc covering.
* `AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectDescends`: the hypothesis
  `RelativelyPerfectDescends`, proved.
* `complexesFunctor_isStackInGroupoids_of_remaining_pending`: Stacks 0DLH granted the results
  it still waits for, without the hypothesis on relative perfectness.

## The argument

`T`-perfectness is pseudo-coherence together with locally finite Tor dimension over
`(X_T ⟶ T)⁻¹𝒪_T` (Stacks 0DKN). A sieve of the fppf topology on `T` hands over no fpqc covering
by its generators, but through every point of `T` passes a flat morphism locally of finite
presentation `U_x ⟶ T` of the sieve, which factors through some `T_i`; the family `{U_x ⟶ T}`
is an fppf, hence an fpqc, covering (Stacks 03Y8, Stacks 0DFQ), and the pullback of `E` to each
`X_{U_x}` is `U_x`-perfect by the base change of relative perfectness along `U_x ⟶ T_i`
(the special case of Stacks 0DKT of
`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectBaseChange`). The base changes
`X_{U_x} ⟶ X_T` form an fpqc covering of `X_T`, over which pseudo-coherence descends by
Stacks 0DL1, and the squares `X_{U_x} ⟶ X_T` over `U_x ⟶ T` are cartesian, so locally finite
Tor dimension descends by Stacks 0DL2.

## Tagging

Nothing here carries a `@[stacks]` attribute: Stacks 0DLH is registered once the remaining
pending results (0DLG, 0DLA, 0DLD(b) and 0DLC(1)) land.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : ComplexesSituation B S hS}

attribute [local instance 2000] inverseImageRingedSite_hasWeakSheafify_over
  inverseImageRingedSite_wEqualsLocallyBijective_over

attribute [local instance] inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  inverseImageRingedSite_slice_hasDerivedCategory RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  inverseImageRingedSite_slice_sheafTensor_additive
  inverseImageRingedSite_slice_sheafTensor_obj_additive
  inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  instModulesHasDerivedCategory

/-- **Relative perfectness descends along an fpqc covering of the test scheme.** Let
`{b_j : U_j ⟶ T}` be morphisms of test schemes over `Y` whose underlying morphisms form an fpqc
covering of `T`, and let `E` be an object of `D(𝒪_{X_T})` with quasi-coherent cohomology whose
derived pullbacks to the `X_{U_j}` are `U_j`-perfect. Then `E` is `T`-perfect.

The base changes `X_{U_j} ⟶ X_T` form an fpqc covering of `X_T` (Stacks 03MR), so
pseudo-coherence descends by Stacks 0DL1; the squares `X_{U_j} ⟶ X_T` over `U_j ⟶ T` are
cartesian, so locally finite Tor dimension descends by Stacks 0DL2. -/
theorem isRelativelyPerfect_of_isFpqcCovering {T : SchemesOver D.Y} {J : Type v}
    (U : J → SchemesOver D.Y) (b : ∀ j, U j ⟶ T)
    (hb : IsFpqcCovering B S hS fun j => ((schemeSpaceFunctor B S hS).map (b j).left).hom)
    (E : derivedModules B S hS (D.space T)) (hE : D.HasQuasicoherentCohomology T E)
    (h : ∀ j, D.IsRelativelyPerfect (U j)
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (b j))).obj E)) :
    D.IsRelativelyPerfect T E := by
  have hpb : ∀ j, IsPullback (D.relativeMap (b j)) (D.projection (U j)) (D.projection T)
      ((schemeSpaceFunctor B S hS).map (b j).left) := fun j => isPullback_baseChangeMap D.f (b j)
  have hcov : IsFpqcCovering B S hS fun j => (D.relativeMap (b j)).hom :=
    isFpqcCovering_of_isPullback B S hS _ hb (D.projection T) _ _ hpb
  refine ⟨?_, ?_⟩
  · refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ E).2 fun m => ?_
    exact (isPseudoCoherentFrom_iff_forall_derivedPullback_of_isFpqcCovering B S hS
      (fun j => D.relativeMap (b j)) hcov E hE m).2 fun j =>
      (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 (h j).1 m
  · exact locallyHasFiniteTorDimension_derivedScalarRestriction_of_forall_pullback B S hS _ hb
      (D.projection T) (fun j => D.projection (U j)) (fun j => D.relativeMap (b j)) hpb E
      fun j => (h j).2

variable (D) in
/-- **Relative perfectness descends along an fppf covering of the test scheme** (Stacks 0DL1
with Stacks 0DL2). A complex on `X_T` with quasi-coherent cohomology whose pullbacks to the
members `T_i` of an fppf covering of `T` are `T_i`-perfect is `T`-perfect: this is the
hypothesis `AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectDescends`, proved.

Through every point `x` of `T` passes a flat morphism `q_x : U_x ⟶ T`, locally of finite
presentation, of the covering sieve, which factors through some `T_i`; the `q_x` form an fppf,
hence an fpqc, covering of `T`, the pullback of `E` to `X_{U_x}` is `U_x`-perfect by the base
change of relative perfectness along `U_x ⟶ T_i`, and
`AlgebraicGeometry.Space.ComplexesSituation.isRelativelyPerfect_of_isFpqcCovering` applies. -/
theorem relativelyPerfectDescends : D.RelativelyPerfectDescends := by
  intro T I Ti a hcov E hE hEi
  choose c q hqR hqf hqp hqx using fun x : (BigFppfOver.toScheme B S hS).obj T.left =>
    BigFppfOver.exists_mem_of_mem_topology B S hS hcov x
  choose i g hg using fun x => (Sieve.mem_ofArrows_iff _ _ (q x)).1 (hqR x)
  let U : (BigFppfOver.toScheme B S hS).obj T.left → SchemesOver D.Y := fun x =>
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (q x) ≫ T.hom)
  let b : ∀ x, U x ⟶ T := fun x => CostructuredArrow.homMk (q x) rfl
  let k : ∀ x, U x ⟶ Ti (i x) := fun x => CostructuredArrow.homMk (g x) (by
    have w := CostructuredArrow.w (a (i x))
    change (schemeSpaceFunctor B S hS).map (g x) ≫ (Ti (i x)).hom =
      (schemeSpaceFunctor B S hS).map (q x) ≫ T.hom
    rw [hg x, Functor.map_comp, Category.assoc, w])
  have hk : ∀ x, k x ≫ a (i x) = b x := fun x =>
    CostructuredArrow.hom_ext _ _ (hg x).symm
  have hb : IsFpqcCovering B S hS fun x => ((schemeSpaceFunctor B S hS).map (b x).left).hom :=
    isFpqcCovering_of_isFppfCovering B S hS _ _
      (isFppfCovering_yoneda_map B S hS c q hqf hqp fun x => by
        obtain ⟨y, hy⟩ := hqx x
        exact ⟨x, y, hy⟩)
  exact isRelativelyPerfect_of_isFpqcCovering U b hb E hE fun x => isRelativelyPerfect_of_iso
    ((D.relativeMapComparison (hk x)).symm.app E ≪≫ (D.compComparison (k x) (a (i x))).app E)
    (relativelyPerfectBaseChange D (k x) _ (hEi (i x)))

attribute [local instance] complexesCategory

/-- **Stacks 0DLH, granted the results it still waits for (unregistered).** `Complexes_{X/Y}` is
a stack in groupoids over `(Sch/S)_fppf`. This is
`AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor_isStackInGroupoids_of_pending` with
its hypothesis on the descent of relative perfectness discharged by
`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectDescends` (Stacks 0DL1 with 0DL2).

The hypotheses are the pending results, each at its Stacks content:
* `h0DLG`: Stacks 0DLG, not yet proved here;
* `h0DLA`: Stacks 0DLA (Čech case), not yet proved here;
* `h0DLDb`: Stacks 0DLD(b) at `V = T`, not yet proved here;
* `hfib`: Stacks 0DLC(1), not yet proved here. -/
theorem complexesFunctor_isStackInGroupoids_of_remaining_pending
    (h0DLG : Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D)
        (complexesFunctor_isFiberedInGroupoids D)))
    (h0DLA : D.CechDescent) (h0DLDb : D.HasNoNegativeSelfExt)
    (hfib : D.NoNegativeFibreExtDescends) :
    (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS) :=
  complexesFunctor_isStackInGroupoids_of_pending h0DLG h0DLA h0DLDb
    (relativelyPerfectDescends D) hfib

end AlgebraicGeometry.Space.ComplexesSituation

end
