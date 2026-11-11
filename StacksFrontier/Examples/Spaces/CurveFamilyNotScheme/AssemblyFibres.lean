module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Instance.FormalNeighborhood
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.InfiniteFibres
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel

/-!
# The fibres of the blowup of the cubic surface over the affine line

In the construction of [Stacks, Tag 0D5E], `π : Z ⟶ Y` is the blowup of the cubic surface `Y`
at the chosen closed point `y` of the central fibre `Y₀`, `E = π⁻¹(y)` is the exceptional set and
`C` is the strict transform of `Y₀`. This file proves the set-theoretic facts about the fibres of
`Z ⟶ A¹_k` that the non-representability step uses:

* every fibre of `Z ⟶ A¹_k` has infinitely many points outside `C`: off the origin, `π` is a
  bijection onto the fibre of `Y`, which is infinite; over the origin, `E ≅ 𝐏¹_{κ(y)}` is
  infinite and meets `C` in one point;
* the fibre of `Z` over the origin is `E ∪ C`;
* the central fibre `Y₀` has a point other than `y`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.infinite_setOf_cubicBlowup_notMem_strictTransform`.
* `Stacks.Examples.CurveFamilyNotScheme.mem_exceptionalSet_union_of_cubicSurfaceToLine_eq`.
* `Stacks.Examples.CurveFamilyNotScheme.exists_ne_chosenPoint_cubicSurfaceToLine_eq_originPoint`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

/-! ### The projective line over an infinite field is infinite -/

/-- The prime ideal `(X - a)` of `K[X]`. -/
def primeXSubC {K : Type u} [Field K] (a : K) : PrimeSpectrum (Polynomial K) :=
  ⟨Ideal.span {Polynomial.X - Polynomial.C a},
    (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero a)).mpr (Polynomial.prime_X_sub_C a)⟩

/-- Distinct elements give distinct primes `(X - a)`. -/
theorem primeXSubC_injective {K : Type u} [Field K] :
    Function.Injective (primeXSubC (K := K)) := by
  intro a b hab
  have hmem : Polynomial.X - Polynomial.C a ∈ Ideal.span {Polynomial.X - Polynomial.C b} := by
    have h := congrArg PrimeSpectrum.asIdeal hab
    change Ideal.span {Polynomial.X - Polynomial.C a} = Ideal.span {Polynomial.X - Polynomial.C b}
      at h
    rw [← h]
    exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hmem
  exact hmem.symm

/-- **The projective line over an infinite field has infinitely many points.** -/
theorem infinite_projectiveLineProj (K : Type u) [Field K] [Infinite K] :
    Infinite (projectiveLineProj K) := by
  let e := projectiveLineProjChartRingEquiv K 0
  have hinj : Function.Injective fun a : K =>
      (Proj.awayι (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K 1) (MvPolynomial.X 0)
        (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one K 1 0) Nat.one_pos :
          _ ⟶ projectiveLineProj K)
        (PrimeSpectrum.comap e.symm.toRingHom (primeXSubC a)) :=
    (Proj.awayι _ _ _ _).isOpenEmbedding.injective.comp
      ((PrimeSpectrum.comap_injective_of_surjective _ e.symm.surjective).comp
        primeXSubC_injective)
  exact Infinite.of_injective _ hinj

/-! ### The exceptional set of the blowup of the cubic surface -/

variable (k : Type u) [Field k] [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

omit [Uncountable k] in
/-- The residue field of the cubic surface at any point is infinite: it receives the infinite
field `k`. -/
theorem infinite_residueField_stalk_cubicSurface (y : cubicSurface k) :
    Infinite (ResidueField ((cubicSurface k).presheaf.stalk y)) := by
  let φ : k →+* ResidueField ((cubicSurface k).presheaf.stalk y) :=
    (IsLocalRing.residue _).comp (((cubicSurface k).presheaf.Γgerm y).hom.comp
      ((cubicSurfaceToLine k).appTop.hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom.comp Polynomial.C)))
  exact Infinite.of_injective φ φ.injective

/-- **The exceptional set of `Z ⟶ Y` is infinite**: it is a projective line over the infinite
residue field `κ(y)`. -/
theorem infinite_exceptionalSet_chosenPoint :
    (exceptionalSet (chosenPoint k h3) (isClosed_chosenPoint k h3)).Infinite := by
  set y := chosenPoint k h3
  have hy := isClosed_chosenPoint k h3
  have hreg : IsRegularLocalRing ((cubicSurface k).presheaf.stalk y) :=
    (isRegular_cubicSurface k h3).isRegularLocalRing_stalk y
  obtain ⟨e, -⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal y hy hreg
      (ringKrullDim_stalk_cubicSurface k h3 y hy)
  have := infinite_residueField_stalk_cubicSurface k y
  have := infinite_projectiveLineProj (ResidueField ((cubicSurface k).presheaf.stalk y))
  set D := exceptionalIdeal (pointIdeal y hy)
  have hinj : Function.Injective fun w => D.subschemeι (e.hom w) :=
    D.subschemeι.isClosedEmbedding.injective.comp e.hom.isOpenEmbedding.injective
  refine Set.infinite_of_injective_forall_mem hinj fun w => ?_
  have hmem : D.subschemeι (e.hom w) ∈ (D.support : Set (pointBlowup y hy)) := by
    rw [← D.range_subschemeι]
    exact ⟨_, rfl⟩
  exact (mem_exceptionalIdeal_support_iff y hy _).mp hmem

/-- The strict transform `C` meets the exceptional set in at most one point. -/
theorem finite_exceptionalSet_inter_strictTransform :
    (exceptionalSet (chosenPoint k h3) (isClosed_chosenPoint k h3) ∩
      ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3))).Finite := by
  have := isIntegral_subscheme_centralFibreIdeal k h3
  obtain ⟨p, -, -, huniq, -⟩ := exists_strictTransform_inter_exceptional (chosenPoint k h3)
    (isClosed_chosenPoint k h3)
    (isRegular_cubicSurface k h3) (topologicalKrullDim_cubicSurface k h3)
    (ringKrullDim_stalk_cubicSurface k h3 _ (isClosed_chosenPoint k h3))
    (isEffectiveCartierDivisor_centralFibreIdeal k) (isRegular_subscheme_centralFibreIdeal k h3)
    (chosenPoint_mem_support_centralFibreIdeal k h3) (cubicSurfaceCoordinate k) rfl
    (Γgerm_cubicSurfaceCoordinate_chosenPoint_notMem_sq k h3)
  refine (Set.finite_singleton ((strictTransformCentralFibre k h3).subschemeι p)).subset ?_
  rintro z ⟨hzE, hzC⟩
  rw [← (strictTransformCentralFibre k h3).range_subschemeι] at hzC
  obtain ⟨q, rfl⟩ := hzC
  rw [Set.mem_singleton_iff, huniq q hzE]

/-! ### The fibres of `Z ⟶ A¹_k` -/

/-- The strict transform `C` lies over the origin. -/
theorem cubicSurfaceToLine_eq_originPoint_of_mem_strictTransform {z : cubicBlowup k h3}
    (hz : z ∈ ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3))) :
    cubicSurfaceToLine k (pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3) z) =
      originPoint k := by
  rw [coe_support_strictTransformIdeal, strictTransformSet] at hz
  have hcl : IsClosed (pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3) ⁻¹'
      ((centralFibreIdeal k).support : Set (cubicSurface k))) :=
    (centralFibreIdeal k).support.isClosed.preimage (pointBlowupToBase _ _).continuous
  have h := closure_minimal (Set.preimage_mono Set.sdiff_subset) hcl hz
  exact (mem_support_centralFibreIdeal_iff k _).mp h

/-- **Every fibre of `Z ⟶ A¹_k` has infinitely many points outside the strict transform `C` of
the central fibre.** Off the origin, `π : Z ⟶ Y` is a bijection over the (infinite) fibre of `Y`;
over the origin, the exceptional set is infinite and meets `C` in at most one point. -/
theorem infinite_setOf_cubicBlowup_notMem_strictTransform (s : affineLine k) :
    Set.Infinite {z : cubicBlowup k h3 |
      cubicSurfaceToLine k (pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3) z) =
        s ∧ z ∉ ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3))} := by
  set y := chosenPoint k h3
  have hy := isClosed_chosenPoint k h3
  by_cases hs : s = originPoint k
  · subst hs
    refine ((infinite_exceptionalSet_chosenPoint k h3).sdiff
      (finite_exceptionalSet_inter_strictTransform k h3)).mono ?_
    rintro z ⟨hzE, hzEC⟩
    refine ⟨?_, fun hzC => hzEC ⟨hzE, hzC⟩⟩
    rw [pointBlowupToBase_eq_of_mem_exceptionalSet y hy hzE]
    exact cubicSurfaceToLine_chosenPoint k h3
  · refine Set.Infinite.of_image (pointBlowupToBase y hy)
      ((infinite_setOf_cubicSurfaceToLine_eq k s).mono ?_)
    intro w hw
    have hwy : w ∈ complPointOpen y hy := by
      rintro rfl
      exact hs (hw.symm.trans (cubicSurfaceToLine_chosenPoint k h3))
    have := isIso_pointBlowupToBase_restrict_compl y hy
    obtain ⟨z, hz⟩ : ∃ z, (pointBlowupToBase y hy ∣_ complPointOpen y hy) z = ⟨w, hwy⟩ :=
      ((pointBlowupToBase y hy ∣_ complPointOpen y hy).homeomorph.surjective _)
    have hzw : pointBlowupToBase y hy z.1 = w := by
      rw [← morphismRestrict_base_coe, hz]
    refine ⟨z.1, ⟨?_, fun hzC => ?_⟩, hzw⟩
    · rw [hzw]
      exact hw
    · exact hs (hw.symm.trans (hzw ▸ cubicSurfaceToLine_eq_originPoint_of_mem_strictTransform k h3
        hzC))

/-- **The fibre of `Z ⟶ A¹_k` over the origin is `E ∪ C`.** -/
theorem mem_exceptionalSet_union_of_cubicSurfaceToLine_eq (z : cubicBlowup k h3)
    (hz : cubicSurfaceToLine k (pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3) z)
      = originPoint k) :
    z ∈ exceptionalSet (chosenPoint k h3) (isClosed_chosenPoint k h3) ∪
      ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)) := by
  have := isIntegral_subscheme_centralFibreIdeal k h3
  have h := preimage_support_eq_exceptionalSet_union (chosenPoint k h3)
    (isClosed_chosenPoint k h3)
    (isRegular_cubicSurface k h3) (topologicalKrullDim_cubicSurface k h3)
    (ringKrullDim_stalk_cubicSurface k h3 _ (isClosed_chosenPoint k h3))
    (isEffectiveCartierDivisor_centralFibreIdeal k) (isRegular_subscheme_centralFibreIdeal k h3)
    (chosenPoint_mem_support_centralFibreIdeal k h3) (cubicSurfaceCoordinate k) rfl
    (Γgerm_cubicSurfaceCoordinate_chosenPoint_notMem_sq k h3)
  rw [coe_support_strictTransformIdeal, ← h]
  exact (mem_support_centralFibreIdeal_iff k _).mpr hz

/-- **The central fibre `Y₀` has a point other than the chosen point `y`**: it is infinite. -/
theorem exists_ne_chosenPoint_cubicSurfaceToLine_eq_originPoint :
    ∃ y' : cubicSurface k, cubicSurfaceToLine k y' = originPoint k ∧ y' ≠ chosenPoint k h3 := by
  obtain ⟨y', hy', hne⟩ :=
    ((infinite_setOf_cubicSurfaceToLine_eq k (originPoint k)).sdiff
      (Set.finite_singleton (chosenPoint k h3))).nonempty
  exact ⟨y', hy', hne⟩

end Stacks.Examples.CurveFamilyNotScheme

end
