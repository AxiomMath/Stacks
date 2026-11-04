module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLinesGluedAtDoublePoints
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineRigidity

/-!
# The points of two projective lines glued at three double points

Let `k` be a field, `a₀, a₁, a₂ ∈ k` pairwise distinct, `T` the scheme of the three double points
`Spec(k[t]/(t - aᵢ)²)` inside `ℙ¹_k`, and `X = ℙ¹_k ⨿_T ℙ¹_k` the glued curve of
`AlgebraicGeometry.gluedCurve`. This file records the point-set facts about `X` used to study its
automorphisms.

The gluing is an instance of the pushout of Stacks 0E25 along a closed immersion and an integral
morphism, with base `Spec k`: the affineness condition on the fibres holds because `T` lies in
the affine chart `𝔸¹_k ⊂ ℙ¹_k`. Through that presentation the two copies of `ℙ¹_k` cover `X`.
A point of `X` lying on both copies comes from `T`, the square being cartesian (Stacks 0B7M),
and the points of `T` are the three points `x = aᵢ`, since a prime ideal of `k[t]` containing
`∏ᵢ (t - aᵢ)²` contains one of the `t - aᵢ`. In particular the point at infinity of one copy
does not lie on the other copy.

## Main definitions

* `AlgebraicGeometry.gluedCurveSituation`: the presentation of `X` as a pushout of Stacks 0E25
  over `Spec k`.
* `AlgebraicGeometry.gluedCurveIsoPushoutScheme`: the identification of `X` with the pushout
  scheme of that presentation.

## Main results

* `AlgebraicGeometry.gluedCurve_jointly_surjective`: every point of `X` lies on one of the two
  copies of `ℙ¹_k`.
* `AlgebraicGeometry.exists_eq_projectiveLinePoint_of_gluedCurveInl_eq_gluedCurveInr`: a point
  lying on both copies is one of the three points `x = aᵢ` on each.
* `AlgebraicGeometry.gluedCurveInl_infinity_notMem_range_gluedCurveInr`: the point at infinity of
  the first copy is not on the second copy, and symmetrically.

## References

* [Stacks Project, Tag 0DSU](https://stacks.math.columbia.edu/tag/0DSU)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0B7M](https://stacks.math.columbia.edu/tag/0B7M)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

universe u

section PointsOfLine

variable {k : Type u} [Field k]

/-- The point `x = a` of the affine line, the maximal ideal `(x - a)`. -/
def affineLinePointOf (a : k) : Spec (.of k[X]) :=
  ⟨Ideal.span {X - C a}, (Ideal.span_singleton_prime (X_sub_C_ne_zero a)).2 (prime_X_sub_C a)⟩

/-- The ideal `(x - a)` of the polynomial ring `k[x]` is maximal. -/
theorem isMaximal_span_X_sub_C (a : k) : (Ideal.span {X - C a} : Ideal k[X]).IsMaximal := by
  rw [← Polynomial.ker_evalRingHom]
  exact RingHom.ker_isMaximal_of_surjective _ fun r ↦ ⟨C r, by simp⟩

/-- The image of the `k`-point `x = a` is the point `(x - a)` of the first chart. -/
theorem projectiveLineXChartPoint_apply (a : k) (z : Spec (.of k)) :
    (projectiveLineXChartPoint a).base z = (projectiveLineXChart k).base (affineLinePointOf a) := by
  show (projectiveLineXChart k).base
    ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))).base z) = _
  congr 1
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (Polynomial.evalRingHom a) z.asIdeal = Ideal.span {X - C a}
  have := z.isPrime
  rw [Ideal.eq_bot_of_prime z.asIdeal, ← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom]

/-- Two `k`-points of `ℙ¹_k` over `k`, for `k` algebraically closed, with the same image are
equal. -/
theorem projectiveLine_point_ext [IsAlgClosed k] {f g : Spec (.of k) ⟶ projectiveLine k}
    (hf : f ≫ (projectiveLine k ↘ Spec (.of k)) = 𝟙 _)
    (hg : g ≫ (projectiveLine k ↘ Spec (.of k)) = 𝟙 _)
    (h : f.base (IsLocalRing.closedPoint k) = g.base (IsLocalRing.closedPoint k)) : f = g :=
  ext_of_apply_closedPoint_eq (projectiveLine k ↘ Spec (.of k)) hf hg h

end PointsOfLine

section Glued

variable (k : Type u) [Field k] (pts : Fin 3 → k) (hpts : Function.Injective pts)

/-- The three double points map into the first chart of `ℙ¹_k`. -/
theorem doublePointsToProjectiveLine_eq :
    doublePointsToProjectiveLine k pts =
      doublePointsToAffineLine k pts ≫ projectiveLineXChart k := rfl

/-- **The points of the three double points.** Every point of `T` maps to one of the three
points `x = aᵢ` of the first chart. -/
theorem exists_doublePointsToAffineLine_eq (τ : doublePointsScheme k pts) :
    ∃ i, (doublePointsToAffineLine k pts).base τ = affineLinePointOf (pts i) := by
  have hmem : (∏ i, (X - C (pts i)) ^ 2 : k[X]) ∈
      ((doublePointsToAffineLine k pts).base τ).asIdeal := by
    show doublePointsMk pts _ ∈ τ.asIdeal
    have : doublePointsMk pts (∏ i, (X - C (pts i)) ^ 2) = 0 := by
      funext i
      rw [doublePointsMk_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, doublePointIdeal,
        Ideal.mem_span_singleton]
      exact Finset.dvd_prod_of_mem (fun j ↦ (X - C (pts j)) ^ 2) (Finset.mem_univ i)
    rw [this]
    exact zero_mem _
  have := ((doublePointsToAffineLine k pts).base τ).isPrime
  obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
  have hi' := ((doublePointsToAffineLine k pts).base τ).isPrime.mem_of_pow_mem 2 hi
  refine ⟨i, PrimeSpectrum.ext ?_⟩
  exact ((isMaximal_span_X_sub_C (pts i)).eq_of_le
    ((doublePointsToAffineLine k pts).base τ).isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 hi')).symm

/-- **Stacks 0E25 presentation.** The glued curve as a pushout along a closed immersion and an
integral morphism over `Spec k`. -/
def gluedCurveSituation : PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  { S := Spec (.of k)
    X := projectiveLine k
    Y := projectiveLine k
    Z := doublePointsScheme k pts
    pX := projectiveLine k ↘ Spec (.of k)
    pY := projectiveLine k ↘ Spec (.of k)
    pZ := doublePointsToProjectiveLine k pts ≫ (projectiveLine k ↘ Spec (.of k))
    i := doublePointsToProjectiveLine k pts
    j := doublePointsToProjectiveLine k pts
    i_over := rfl
    j_over := rfl
    fiber_preimage_subset_affine := fun _ ↦
      ⟨(projectiveLineXChart k).opensRange, isAffineOpen_opensRange _,
        fun z _ ↦ ⟨(doublePointsToAffineLine k pts).base z, rfl⟩⟩ }

/-- The pushout square of the Stacks 0E25 presentation. -/
theorem isPushout_gluedCurveSituation :
    IsPushout (doublePointsToProjectiveLine k pts) (doublePointsToProjectiveLine k pts)
      (pushoutInl (gluedCurveSituation k pts hpts))
      (pushoutInr (gluedCurveSituation k pts hpts)) :=
  (pushoutAlongClosedImmersionAndIntegral (gluedCurveSituation k pts hpts)).isPushout

/-- The glued curve is the pushout scheme of its Stacks 0E25 presentation. -/
def gluedCurveIsoPushoutScheme :
    pushoutScheme (gluedCurveSituation k pts hpts) ≅ gluedCurve k pts hpts :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  (isPushout_gluedCurveSituation k pts hpts).isoPushout

/-- The identification `gluedCurveIsoPushoutScheme` carries the first inclusion of the pushout
scheme to `gluedCurveInl`. -/
@[reassoc (attr := simp)]
theorem pushoutInl_gluedCurveIsoPushoutScheme_hom :
    pushoutInl (gluedCurveSituation k pts hpts) ≫ (gluedCurveIsoPushoutScheme k pts hpts).hom =
      gluedCurveInl k pts hpts :=
  have := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  IsPushout.inl_isoPushout_hom (isPushout_gluedCurveSituation k pts hpts)

/-- The identification `gluedCurveIsoPushoutScheme` carries the second inclusion of the pushout
scheme to `gluedCurveInr`. -/
@[reassoc (attr := simp)]
theorem pushoutInr_gluedCurveIsoPushoutScheme_hom :
    pushoutInr (gluedCurveSituation k pts hpts) ≫ (gluedCurveIsoPushoutScheme k pts hpts).hom =
      gluedCurveInr k pts hpts :=
  have := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  IsPushout.inr_isoPushout_hom (isPushout_gluedCurveSituation k pts hpts)

/-- **The two copies of `ℙ¹_k` cover the glued curve.** -/
theorem gluedCurve_jointly_surjective (p : gluedCurve k pts hpts) :
    p ∈ Set.range (gluedCurveInl k pts hpts).base ∨
      p ∈ Set.range (gluedCurveInr k pts hpts).base := by
  have h := pushoutInl_inr_jointly_surjective (gluedCurveSituation k pts hpts)
    ((gluedCurveIsoPushoutScheme k pts hpts).inv.base p)
  have hp : p = (gluedCurveIsoPushoutScheme k pts hpts).hom.base
      ((gluedCurveIsoPushoutScheme k pts hpts).inv.base p) := by
    show p = ((gluedCurveIsoPushoutScheme k pts hpts).inv ≫
      (gluedCurveIsoPushoutScheme k pts hpts).hom).base p
    rw [Iso.inv_hom_id]
    rfl
  rcases h with ⟨q, hq⟩ | ⟨q, hq⟩
  · refine Or.inl ⟨q, ?_⟩
    rw [hp, ← hq, ← pushoutInl_gluedCurveIsoPushoutScheme_hom]
    rfl
  · refine Or.inr ⟨q, ?_⟩
    rw [hp, ← hq, ← pushoutInr_gluedCurveIsoPushoutScheme_hom]
    rfl

/-- The two maps of the three double points into the glued curve, through either copy of `ℙ¹_k`,
agree. -/
theorem doublePointsToProjectiveLine_comp_gluedCurveInl :
    doublePointsToProjectiveLine k pts ≫ gluedCurveInl k pts hpts =
      doublePointsToProjectiveLine k pts ≫ gluedCurveInr k pts hpts :=
  (isPushout_gluedCurve k pts hpts).w

/-- **A point on both copies comes from the double points.** If the images of `x` in the first
copy and of `y` in the second copy agree, then both are the same point `x = aᵢ`. -/
theorem exists_eq_projectiveLinePoint_of_gluedCurveInl_eq_gluedCurveInr
    (x y : projectiveLine k)
    (h : (gluedCurveInl k pts hpts).base x = (gluedCurveInr k pts hpts).base y) :
    ∃ i, x = (projectiveLineXChart k).base (affineLinePointOf (pts i)) ∧
      y = (projectiveLineXChart k).base (affineLinePointOf (pts i)) := by
  have := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  have hpb : IsPullback (doublePointsToProjectiveLine k pts) (doublePointsToProjectiveLine k pts)
      (gluedCurveInl k pts hpts) (gluedCurveInr k pts hpts) :=
    isPullback_pushout_of_isClosedImmersion _ _
  have := hpb.hasPullback
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  let τ := hpb.isoPullback.inv.base z
  have h₁ : (doublePointsToProjectiveLine k pts).base τ = x := by
    rw [← hz₁, ← hpb.isoPullback_inv_fst]
    rfl
  have h₂ : (doublePointsToProjectiveLine k pts).base τ = y := by
    rw [← hz₂, ← hpb.isoPullback_inv_snd]
    rfl
  obtain ⟨i, hi⟩ := exists_doublePointsToAffineLine_eq k pts τ
  refine ⟨i, ?_, ?_⟩
  · rw [← h₁, doublePointsToProjectiveLine_eq, Scheme.Hom.comp_base, TopCat.comp_app, hi]
  · rw [← h₂, doublePointsToProjectiveLine_eq, Scheme.Hom.comp_base, TopCat.comp_app, hi]

/-- The point at infinity of the first copy does not lie on the second copy. -/
theorem gluedCurveInl_infinity_notMem_range_gluedCurveInr :
    (gluedCurveInl k pts hpts).base (projectiveLineInfinity k) ∉
      Set.range (gluedCurveInr k pts hpts).base := by
  rintro ⟨y, hy⟩
  obtain ⟨i, hi, -⟩ :=
    exists_eq_projectiveLinePoint_of_gluedCurveInl_eq_gluedCurveInr k pts hpts _ _ hy.symm
  exact projectiveLineInfinity_notMem_range_projectiveLineXChart k ⟨_, hi.symm⟩

/-- The point at infinity of the second copy does not lie on the first copy. -/
theorem gluedCurveInr_infinity_notMem_range_gluedCurveInl :
    (gluedCurveInr k pts hpts).base (projectiveLineInfinity k) ∉
      Set.range (gluedCurveInl k pts hpts).base := by
  rintro ⟨x, hx⟩
  obtain ⟨i, -, hi⟩ :=
    exists_eq_projectiveLinePoint_of_gluedCurveInl_eq_gluedCurveInr k pts hpts _ _ hx
  exact projectiveLineInfinity_notMem_range_projectiveLineXChart k ⟨_, hi.symm⟩

end Glued

end AlgebraicGeometry
