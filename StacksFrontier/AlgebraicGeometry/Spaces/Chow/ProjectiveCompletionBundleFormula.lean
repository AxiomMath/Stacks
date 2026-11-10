module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaVanishingLocusSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VectorBundlePullbackSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionVectorBundleOpenImmersionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionInfinityZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionSectionRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem

/-!
# The projective bundle formula for a projective completion, from the hyperplane at infinity

Let `X/B` be good, `ℰ` a finite locally free `𝒪_X`-module of rank `m + 1`, `P = 𝐏(ℰ ⊕ 𝒪_X)` its
projective completion with `π : P → X`, `𝒪_P(1)` and the section `s` of `𝒪_P(1)` given by the
summand `𝒪_X`, and `i : Q = 𝐏(ℰ) → P` the hyperplane at infinity, whose image is the zero scheme
`Z(s)`. This file identifies `Q` with `Z(s)` and shows that `Z(s)` is a relative effective Cartier
divisor on `P/X`, so that the top power of Stacks 0ERU passes from `Q` to `P`
(`AlgebraicGeometry.Space.BundleTopPowerIdentity.of_vanishingLocus`), granted the identification
`i^*𝒪_P(1) ≅ 𝒪_Q(1)` of twists.

## Main definitions

* `AlgebraicGeometry.Space.infinityLocusIso`: the morphism `Q ⟶ Z(s)` through which `i` factors;
  it is an isomorphism (`AlgebraicGeometry.Space.isIso_infinityLocusIso`).

## Main results

* `AlgebraicGeometry.Space.isRelativeEffectiveCartierDivisor_projectiveCompletionZeroScheme`:
  `Z(s)` is a relative effective Cartier divisor on `P/X`.
* `AlgebraicGeometry.Space.bundleTopPowerIdentity_projectiveCompletion`: the top power for `P`
  from the one for `Q`.

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0EPP](https://stacks.math.columbia.edu/tag/0EPP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

section Factor

variable {C : Type*} [Category C] {A F : C ⥤ Type u} (f : A ⟶ F) [Mono f] (G : Subfunctor F)
    (hG : Subfunctor.range f = G)

/-- A monomorphism of functors onto a subfunctor `G` factors through `G` by an isomorphism. -/
def liftOfRangeEq : A ⟶ G.toFunctor :=
  G.lift f (hG ▸ le_refl _)

omit [Mono f] in
/-- The factorization `liftOfRangeEq f G hG` followed by the inclusion of `G` is `f`. -/
@[reassoc (attr := simp)]
theorem liftOfRangeEq_ι : liftOfRangeEq f G hG ≫ G.ι = f :=
  G.lift_ι f _

/-- The factorization of a monomorphism through its range is an isomorphism. -/
theorem isIso_liftOfRangeEq : IsIso (liftOfRangeEq f G hG) := by
  have hinj : ∀ X, Function.Injective (f.app X) := fun X =>
    (mono_iff_injective (f.app X)).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance X)
  have happ : ∀ X, IsIso ((liftOfRangeEq f G hG).app X) := fun X =>
    (isIso_iff_bijective _).2 ⟨fun a b h => hinj X (congrArg Subtype.val h), by
      rintro ⟨y, hy⟩
      rw [← hG, Subfunctor.range_obj] at hy
      obtain ⟨a, rfl⟩ := hy
      exact ⟨a, rfl⟩⟩
  exact NatIso.isIso_of_isIso_app _

end Factor

section Completion

variable (D : BaseSpaceDimensionSituation.{u})
    {X : AlgebraicSpaces D.site D.base D.base_mem} (sX : X.1 ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (m : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (m + 1))

include sX hX

/-- The projective completion is good over the base. -/
theorem isGood_projectiveCompletionProj_comp :
    D.IsGood ((projectiveCompletionProj E hr).hom ≫ sX) :=
  @isGood_projectiveBundleProj_comp D X.1 sX hX (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr)

/-- The projective bundle `Q = 𝐏(ℰ)` is good over the base. -/
theorem isGood_projectiveBundleProj_comp_of_rank :
    D.IsGood ((@projectiveBundleProj D.site D.base D.base_mem X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
      hr.isFiniteLocallyFreeOnSite).hom ≫ sX) :=
  @isGood_projectiveBundleProj_comp D X.1 sX hX E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite

omit sX hX in
/-- The image of the hyperplane at infinity is the zero scheme of `s`. -/
theorem range_infinityImmersion_eq :
    Subfunctor.range (projectiveCompletionInfinityImmersion E hr).hom =
      (zeroScheme D.site D.base D.base_mem (projectiveCompletion E hr)
        (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1 :=
  range_projectiveCompletionInfinityImmersion_eq_zeroScheme E hr

/-- The hyperplane at infinity `Q ⟶ P` is a monomorphism of functors. -/
instance mono_infinityImmersion :
    Mono (projectiveCompletionInfinityImmersion E hr).hom :=
  mono_of_isClosedImmersion D.site D.base D.base_mem _
    (isClosedImmersion_projectiveCompletionInfinityImmersion E hr)

/-- **The hyperplane at infinity `𝐏(ℰ) ⟶ Z(s)`**, an isomorphism onto the zero scheme. It takes
the structure morphism `sX` and its goodness `hX`, as every declaration of this section does. -/
def infinityLocusIso :
    (@projectiveBundle D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).1 ⟶
      (zeroScheme D.site D.base D.base_mem (projectiveCompletion E hr)
        (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.toFunctor :=
  have := hX
  liftOfRangeEq _ _ (range_infinityImmersion_eq D E m hr)

/-- The morphism `Q ⟶ Z(s)` is an isomorphism. -/
instance isIso_infinityLocusIso : IsIso (infinityLocusIso D sX hX E m hr) :=
  isIso_liftOfRangeEq _ _ (range_infinityImmersion_eq D E m hr)

/-- The morphism `Q ⟶ Z(s)` followed by the inclusion of `Z(s)` is the hyperplane at infinity. -/
@[reassoc (attr := simp)]
theorem infinityLocusIso_ι :
    infinityLocusIso D sX hX E m hr ≫ (zeroScheme D.site D.base D.base_mem
        (projectiveCompletion E hr) (projectiveCompletionTwist E hr).obj
        (projectiveCompletionSection E hr)).1.ι =
      (projectiveCompletionInfinityImmersion E hr).hom :=
  liftOfRangeEq_ι _ _ (range_infinityImmersion_eq D E m hr)

/-- The zero scheme followed by `π` is the inverse of the hyperplane at infinity followed by the
projection of `𝐏(ℰ)`. -/
theorem zeroScheme_ι_comp_projectiveCompletionProj :
    (zeroScheme D.site D.base D.base_mem (projectiveCompletion E hr)
        (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.ι ≫
        (projectiveCompletionProj E hr).hom =
      inv (infinityLocusIso D sX hX E m hr) ≫
        (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom := by
  rw [IsIso.eq_inv_comp, infinityLocusIso_ι_assoc]
  exact congrArg (fun f => f.hom) (@projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj
    D.site D.base D.base_mem X (addUnit X.2 E) E (isQuasicoherentOnSite_addUnit hr)
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) biprod.fst biprod.inl
    biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr) hr.isFiniteLocallyFreeOnSite)

/-- Over the base, the inverse of the hyperplane at infinity followed by the projection of
`𝐏(ℰ)` is the inclusion of `Z(s)` followed by `π`. -/
private theorem inv_infinityLocusIso_comp_proj_comp :
    inv (infinityLocusIso D sX hX E m hr) ≫
      ((@projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).hom ≫ sX) =
      (zeroScheme D.site D.base D.base_mem (projectiveCompletion E hr)
        (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.ι ≫
        ((projectiveCompletionProj E hr).hom ≫ sX) := by
  rw [← Category.assoc, ← zeroScheme_ι_comp_projectiveCompletionProj, Category.assoc]

/-- **The hyperplane at infinity is a relative effective Cartier divisor on `P/X`.** -/
theorem isRelativeEffectiveCartierDivisor_projectiveCompletionZeroScheme :
    IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk (projectiveCompletionProj E hr).hom :
        (⟨(projectiveCompletion E hr).1,
          (isGood_projectiveCompletionProj_comp D sX hX E m hr).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X.1, hX.1⟩)
      (vanishingLocus D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
        (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)) := by
  refine ⟨(exists_isEffectiveCartierDivisor_zeroScheme_projectiveCompletionSection E hr).choose, ?_⟩
  change IsFlat D.site D.base D.base_mem ((zeroScheme D.site D.base D.base_mem
    (projectiveCompletion E hr) (projectiveCompletionTwist E hr).obj
    (projectiveCompletionSection E hr)).1.ι ≫ (projectiveCompletionProj E hr).hom)
  rw [zeroScheme_ι_comp_projectiveCompletionProj D sX hX E m hr]
  have hZg := isGood_vanishingLocus D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
    (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)
  have hQg := isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr
  have hψ := isFlat_and_hasRelativeDimension_zero_of_isIso D _ hQg
    (inv (infinityLocusIso D sX hX E m hr))
  exact (isFlat_and_hasRelativeDimension_comp D _ hZg _ hQg sX hX _ _
    (inv_infinityLocusIso_comp_proj_comp D sX hX E m hr) rfl 0 m hψ.1 hψ.2
    (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) m hr hr.isFiniteLocallyFreeOnSite)
    (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) m hr
      hr.isFiniteLocallyFreeOnSite)).2.1

/-- The inverse of the hyperplane at infinity onto `Z(s)`, followed by the hyperplane at infinity,
is the inclusion of `Z(s)`, as morphisms of algebraic spaces. -/
theorem inv_infinityLocusIso_comp_infinityImmersion :
    (ObjectProperty.homMk (inv (infinityLocusIso D sX hX E m hr)) :
        (⟨(zeroScheme D.site D.base D.base_mem (projectiveCompletion E hr)
          (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.toFunctor,
          (isGood_vanishingLocus D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
            (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨(@projectiveBundle D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).1,
          (isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr).1⟩) ≫
        projectiveCompletionInfinityImmersion E hr =
      closedSubspaceHom D.site D.base D.base_mem
        (isGood_projectiveCompletionProj_comp D sX hX E m hr).1 _
        (vanishingLocus D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
          (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).2 := by
  refine ObjectProperty.hom_ext _ ?_
  change inv (infinityLocusIso D sX hX E m hr) ≫ (projectiveCompletionInfinityImmersion E hr).hom =
    (zeroScheme D.site D.base D.base_mem (projectiveCompletion E hr)
      (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.ι
  rw [← infinityLocusIso_ι D sX hX E m hr, IsIso.inv_hom_id_assoc]

/-- The twist of `P`, restricted to the hyperplane at infinity and transported to `Q = 𝐏(ℰ)`
along the hyperplane at infinity, is the twist of `Q`, given the comparison
`i^*𝒪_P(1) ≅ 𝒪_Q(1)`. -/
def infinityLocusTwistIso
    (htw : (modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion E hr)).obj (projectiveCompletionTwist E hr).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj) :
    (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk (inv (infinityLocusIso D sX hX E m hr)) :
        (⟨(zeroScheme D.site D.base D.base_mem (projectiveCompletion E hr)
          (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.toFunctor,
          (isGood_vanishingLocus D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
            (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨(@projectiveBundle D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).1,
          (isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr).1⟩)).obj
        (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj ≅
      closedSubspaceModuleRestrict D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
        (projectiveCompletionTwist E hr).obj
        (vanishingLocus D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
          (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)) :=
  (modulePullback D.site D.base D.base_mem _).mapIso htw.symm ≪≫
    (modulePullbackCompIsoOfEq D.site D.base D.base_mem _
      (projectiveCompletionInfinityImmersion E hr)
      (h := closedSubspaceHom D.site D.base D.base_mem
        (isGood_projectiveCompletionProj_comp D sX hX E m hr).1 _
        (vanishingLocus D _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
          (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).2)
      (inv_infinityLocusIso_comp_infinityImmersion D sX hX E m hr)).app _

/-- **The top power of Stacks 0ERU for the projective completion `𝐏(ℰ ⊕ 𝒪)`, from the one for
`𝐏(ℰ)`**, granted `i^*𝒪_P(1) ≅ 𝒪_Q(1)` for the hyperplane at infinity `i`. -/
theorem bundleTopPowerIdentity_projectiveCompletion
    (htw : (modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion E hr)).obj (projectiveCompletionTwist E hr).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj)
    (hQ : BundleTopPowerIdentity D sX hX _ (isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).hom rfl m
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) m hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) m hr
        hr.isFiniteLocallyFreeOnSite)
      (@isProper_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)) :
    BundleTopPowerIdentity D sX hX _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
      (projectiveCompletionProj E hr).hom rfl (m + 1) (isFlat_projectiveCompletionProj E hr)
      (hasRelativeDimension_projectiveCompletionProj E hr) (isProper_projectiveCompletionProj E hr)
      (projectiveCompletionTwist E hr).obj (isInvertibleModule_projectiveCompletionTwist E hr) := by
  refine BundleTopPowerIdentity.of_vanishingLocus D sX hX _
    (isGood_projectiveCompletionProj_comp D sX hX E m hr) _ rfl m _ _ _ _ _
    (projectiveCompletionSection E hr)
    (isRelativeEffectiveCartierDivisor_projectiveCompletionZeroScheme D sX hX E m hr) ?_
  exact BundleTopPowerIdentity.of_iso D sX hX _
    (isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr)
    _ _ _ rfl _ _ m _ _ _ _ _ _ _ _ _ _ (inv (infinityLocusIso D sX hX E m hr))
    (inv_infinityLocusIso_comp_proj_comp D sX hX E m hr)
    (zeroScheme_ι_comp_projectiveCompletionProj D sX hX E m hr).symm
    (infinityLocusTwistIso D sX hX E m hr htw) hQ

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
    (show SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem X) from E)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (show SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem X) from E) (m + 1)]

/-- **The surjectivity half of Stacks 0ERV for the projective completion `𝐏(ℰ ⊕ 𝒪)`, from the one
for `𝐏(ℰ)`**: the complement of the hyperplane at infinity is the vector bundle `𝐕(ℰ)`, along which
flat pullback is surjective (Stacks 0ERG), granted `i^*𝒪_P(1) ≅ 𝒪_Q(1)`. -/
theorem bundleFormulaSurjective_projectiveCompletion
    (htw : (modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion E hr)).obj (projectiveCompletionTwist E hr).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj)
    (hQ : BundleFormulaSurjective D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).hom rfl m
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) m hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) m hr
        hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)) :
    BundleFormulaSurjective D sX hX _ (isGood_projectiveCompletionProj_comp D sX hX E m hr)
      (projectiveCompletionProj E hr).hom rfl (m + 1) (isFlat_projectiveCompletionProj E hr)
      (hasRelativeDimension_projectiveCompletionProj E hr)
      (projectiveCompletionTwist E hr).obj (isInvertibleModule_projectiveCompletionTwist E hr) := by
  have hjq : (projectiveCompletionVectorBundleImmersion E hr).hom ≫
      (projectiveCompletionProj E hr).hom =
        (vectorBundleProjection D.site D.base D.base_mem X E).hom :=
    congrArg (fun f => f.hom)
      (projectiveCompletionVectorBundleImmersion_comp_projectiveCompletionProj E hr)
  have hcompl := range_pointsMap_projectiveCompletionVectorBundleImmersion_eq_compl_zeroScheme E hr
  refine BundleFormulaSurjective.of_vanishingLocus D sX hX _
    (isGood_projectiveCompletionProj_comp D sX hX E m hr) _ rfl m _ _ _ _
    (projectiveCompletionSection E hr)
    (isRelativeEffectiveCartierDivisor_projectiveCompletionZeroScheme D sX hX E m hr)
    _ (isGood_vectorBundle D X E sX hX)
    (isOpenImmersion_projectiveCompletionVectorBundleImmersion E hr)
    (by rw [← Category.assoc, hjq]) (by rw [hcompl, compl_compl]) _ rfl hjq
    (isFlat_vectorBundleProjection D.site D.base D.base_mem X E)
    (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem X E (m + 1))
    (fun k => isFlatPullbackSurjective_vectorBundleProjection D X E (m + 1) sX hX k) ?_
  exact BundleFormulaSurjective.of_iso D sX hX _
    (isGood_projectiveBundleProj_comp_of_rank D sX hX E m hr)
    _ _ _ rfl _ _ m _ _ _ _ _ _ _ _ (inv (infinityLocusIso D sX hX E m hr))
    (inv_infinityLocusIso_comp_proj_comp D sX hX E m hr)
    (zeroScheme_ι_comp_projectiveCompletionProj D sX hX E m hr).symm
    (infinityLocusTwistIso D sX hX E m hr htw) hQ

end Completion

end AlgebraicGeometry.Space

end
