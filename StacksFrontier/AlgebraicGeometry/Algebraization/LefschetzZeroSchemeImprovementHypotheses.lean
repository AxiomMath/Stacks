module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCompletedStalkDepthCriterion
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConsecutiveCharts
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.Proper
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionConstruction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.SpecialFibreSerreCriterion
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ImmediateSpecialization
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hypotheses of Stacks 0EJF along the zero scheme of an ample section

Let `k` be a field, `P` a proper scheme over `k`, `𝓛` an ample invertible `𝒪_P`-module,
`s ∈ Γ(P, 𝓛)` and `Q = Z(s)` with ideal `𝓘`. The proof of [Stacks, Tag 0EL5] applies
[Stacks, Tag 0EJF] with `d = 1` to an object `(𝓕ₙ)` of `Coh(P, 𝓘)` satisfying

`depth((𝓕_q^∧)_𝔭) + dim(𝒪_{P,q}^∧/𝔭) + dim({q}‾) > 2`   (`q ∈ Q`, `𝔭 ∉ V(𝓘𝒪_{P,q}^∧)`)

and to `T' = {q ∈ Q | dim({q}‾) = 0} ⊆ T = {q ∈ Q | dim({q}‾) ≤ 1}`. This file proves the
hypotheses of 0EJF in this situation.

## Main definitions

* `Stacks.Algebraization.zeroSchemeClosureDimLE`: the points of `Q` whose closure has dimension
  at most `e`; the sets `T` and `T'` are the cases `e = 1` and `e = 0`.

## Main results

* `Stacks.Algebraization.stableUnderSpecialization_zeroSchemeClosureDimLE`,
  `Stacks.Algebraization.zeroSchemeClosureDimLE_subset_support`,
  `Stacks.Algebraization.zeroSchemeClosureDimLE_mono`: `T`, `T'` are stable under
  specialization and `T' ⊆ T ⊆ Q`.
* `Stacks.Algebraization.exists_affineOpen_cohomologicalDimension_zeroScheme_le_one`:
  hypothesis (a), `cd ≤ 1` on an affine cover.
* `Stacks.Algebraization.zeroScheme_hypothesis_b`, `Stacks.Algebraization.zeroScheme_hypothesis_c`,
  `Stacks.Algebraization.zeroScheme_hypothesis_d`: hypotheses (b), (c) and (d) from the criterion
  of Stacks 0EL5.
* `Stacks.Algebraization.mem_zeroSchemeClosureDimLE_one_of_isImmediateSpecialization`:
  hypothesis (e).

## References

* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5)
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR), dualizing complexes.
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), the dimension formula.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Algebraization

/-! ### A Noetherian local ring with a principal closed fibre -/

/-- If `R` is Noetherian local, `𝔭` a prime and `a ∈ 𝔪` such that every prime containing `𝔭` and
`a` is `𝔪`, then `dim(R/𝔭) ≤ 1`. -/
@[sga "2 X 2.1" "special case"]
theorem ringKrullDim_quotient_le_one_of_forall_prime_eq {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (p : Ideal R) [p.IsPrime] {a : R}
    (ha : a ∈ maximalIdeal R)
    (h : ∀ Q : Ideal R, Q.IsPrime → p ≤ Q → a ∈ Q → Q = maximalIdeal R) :
    ringKrullDim (R ⧸ p) ≤ 1 := by
  have hpne : p ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hpne
  have : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hmaxmap : ((maximalIdeal R).map (Ideal.Quotient.mk p)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact le_maximalIdeal hpne)
  have hM : maximalIdeal (R ⧸ p) = (maximalIdeal R).map (Ideal.Quotient.mk p) :=
    (IsLocalRing.eq_maximalIdeal hmaxmap).symm
  have hmin : maximalIdeal (R ⧸ p) ∈
      (Ideal.span {Ideal.Quotient.mk p a}).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, fun Q' hQ' _ => ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff, hM]
      exact Ideal.mem_map_of_mem _ ha
    · obtain ⟨hQ'prime, haQ'⟩ := hQ'
      have hQ := h (Q'.comap (Ideal.Quotient.mk p)) (Ideal.IsPrime.comap _)
        (fun x hx => by
          change Ideal.Quotient.mk p x ∈ Q'
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact Q'.zero_mem)
        (haQ' (Ideal.mem_span_singleton_self _))
      rw [hM, ← hQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin

/-! ### Completed local rings along a locally principal ideal sheaf -/

/-- Let `y` be a point of the support of `𝓘` with `𝓘𝒪_{X,y}^∧` principal. If a prime `𝔭` of
`𝒪_{X,y}^∧` meets `V(𝓘𝒪_{X,y}^∧)` only in the maximal ideal, then `dim(𝒪_{X,y}^∧/𝔭) ≤ 1`. -/
theorem ringKrullDim_quotient_le_one_of_adicClosedFibreThrough_eq {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {y : X} (hy : y ∈ I.support)
    {a : completedLocalRing I y} (ha : completedLocalIdeal I y = Ideal.span {a})
    (p : PrimeSpectrum (completedLocalRing I y))
    (hp : adicClosedFibreThrough I y p = {completedMaximalIdeal I y}) :
    ringKrullDim (completedLocalRing I y ⧸ p.asIdeal) ≤ 1 := by
  have hJ : IdealSheafData.stalk I y ≤ maximalIdeal (X.presheaf.stalk y) :=
    le_maximalIdeal fun h => (IdealSheafData.stalk_eq_top_iff_notMem_support I y).mp h hy
  have : IsLocalRing (completedLocalRing I y) :=
    Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ hJ
  have hmax : completedMaximalIdeal I y = maximalIdeal (completedLocalRing I y) :=
    IsLocalRing.eq_maximalIdeal
      (AdicCompletion.isMaximal_map_of_le _ _ hJ (Ideal.fg_of_isNoetherianRing _))
  have hmem : completedMaximalIdeal I y ∈ adicClosedFibreThrough I y p := by
    rw [hp]; rfl
  refine ringKrullDim_quotient_le_one_of_forall_prime_eq p.asIdeal (a := a) ?_ ?_
  · rw [← hmax]; exact hmem.2.2 (ha ▸ Ideal.mem_span_singleton_self a)
  · intro Q hQ hpQ haQ
    have hQmem : Q ∈ adicClosedFibreThrough I y p :=
      ⟨hQ, hpQ, by rw [ha, Ideal.span_le, Set.singleton_subset_iff]; exact haQ⟩
    rw [hp] at hQmem
    exact hQmem.trans hmax

/-- If the ideal of `I` on an affine open `U ∋ y` is principal, then so is the completed ideal
`𝓘𝒪_{X,y}^∧`. -/
theorem exists_completedLocalIdeal_eq_span_singleton {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (y : X) (U : X.affineOpens) (hyU : y ∈ U.1) {b : Γ(X, U.1)}
    (hb : I.ideal U = Ideal.span {b}) :
    ∃ a : completedLocalRing I y, completedLocalIdeal I y = Ideal.span {a} := by
  refine ⟨algebraMap (X.presheaf.stalk y) (completedLocalRing I y)
    ((X.presheaf.germ U.1 y hyU).hom b), ?_⟩
  have h1 : IdealSheafData.stalk I y = Ideal.span {(X.presheaf.germ U.1 y hyU).hom b} := by
    rw [IdealSheafData.stalk_eq_map_germ I y U hyU, hb, Ideal.map_span, Set.image_singleton]
  rw [completedLocalIdeal,
    congrArg (Ideal.map (algebraMap (X.presheaf.stalk y) (completedLocalRing I y))) h1,
    Ideal.map_span, Set.image_singleton]

/-! ### The arithmetic of the criterion -/

/-- The criterion of Stacks 0EL5 in the extended integers, read back in `WithBot ℕ∞`. -/
theorem two_lt_add_of_two_lt_enatToEInt_add {δ : ℕ∞} {D c : WithBot ℕ∞}
    (h : (2 : EInt) < enatToEInt δ + krullDimToEInt D + krullDimToEInt c) :
    ((2 : ℕ) : WithBot ℕ∞) < (δ : WithBot ℕ∞) + D + c := by
  by_contra hle
  have hm := krullDimToEInt_mono (not_lt.mp hle)
  rw [krullDimToEInt_add, krullDimToEInt_add, krullDimToEInt_coe] at hm
  exact absurd (h.trans_le hm) (lt_irrefl _)

/-! ### Dimensions of closures of points -/

/-- The dimension of the closure of a point does not increase along a specialization. -/
theorem dimClosureAt_le_of_specializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    dimClosureAt X y ≤ dimClosureAt X x :=
  (Topology.IsEmbedding.inclusion
    (specializes_iff_closure_subset.mp h)).isInducing.topologicalKrullDim_le

/-- On a scheme locally of finite type over a field, an immediate specialization `x ⤳ x'`
raises the dimension of the closure by one: `dim({x}‾) = dim({x'}‾) + 1`. -/
theorem dimClosureAt_eq_add_one_of_isImmediateSpecialization (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {x x' : X}
    (h : IsImmediateSpecialization x x') :
    dimClosureAt X x = dimClosureAt X x' + 1 := by
  have ht := trdeg_residueField_eq_add_one_of_isImmediateSpecialization k X f h
  rw [dimClosureAt, dimClosureAt, topologicalKrullDim_closure_singleton_eq_trdeg k X f x,
    topologicalKrullDim_closure_singleton_eq_trdeg k X f x', ht, map_add, map_one]
  rfl

/-! ### The zero scheme of a section of an ample invertible module -/

section ZeroScheme

variable {k : Type u} [Field k] {P : Scheme.{u}} (fP : P ⟶ Spec (.of k)) [IsProper fP]
  (L : P.Modules) [Stacks.Ample.IsInvertibleModule P L] (hL : Stacks.Ample.IsAmple P L)
  (s : Γ(L, ⊤))

include fP hL in
/-- The zero scheme of a section of an ample invertible module on a proper scheme is locally
principal: every point has an affine open neighbourhood on which its ideal is generated by one
element. -/
theorem exists_affineOpen_zeroScheme_ideal_eq_span_singleton (x : P) :
    ∃ U : P.affineOpens, x ∈ U.1 ∧
      ∃ b : Γ(P, U.1), (zeroScheme P L s).ideal U = Ideal.span {b} := by
  have : IsIso (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL) :=
    Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper L hL fP
  obtain ⟨_, ⟨ch, rfl⟩, hx, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp (Stacks.LefschetzCone.isBasis_consecutiveChart L hL))
      (show x ∈ (⊤ : P.Opens) from trivial)
  exact ⟨ch.affineOpen hL, hx, _, Stacks.LefschetzCone.zeroScheme_ideal_consecutiveChart L hL s ch⟩

include fP hL in
/-- **Hypothesis (a) of Stacks 0EJF with `d = 1` for the zero scheme**: every point has an affine
open neighbourhood on which the ideal of the zero scheme has cohomological dimension at most
one. -/
theorem exists_affineOpen_cohomologicalDimension_zeroScheme_le_one [IsLocallyNoetherian P]
    (x : P) : ∃ U : P.affineOpens, x ∈ U.1 ∧
      letI : IsNoetherianRing Γ(P, U.1) := IsLocallyNoetherian.component_noetherian U
      Stacks.LocalCohomology.cohomologicalDimension Γ(P, U.1) ((zeroScheme P L s).ideal U)
        (Ideal.fg_of_isNoetherianRing _) ≤ ((1 : ℕ) : ℤ) := by
  obtain ⟨U, hx, b, hb⟩ := exists_affineOpen_zeroScheme_ideal_eq_span_singleton fP L hL s x
  refine ⟨U, hx, ?_⟩
  let : IsNoetherianRing Γ(P, U.1) := IsLocallyNoetherian.component_noetherian U
  exact Stacks.LocalCohomology.cohomologicalDimension_le_card_generators Γ(P, U.1) _ _ ![b]
    (by rw [hb, Matrix.range_cons, Matrix.range_empty, Set.union_empty])

include fP hL in
/-- At every point the completed ideal of the zero scheme is principal. -/
theorem exists_completedLocalIdeal_zeroScheme_eq_span_singleton [IsLocallyNoetherian P] (y : P) :
    ∃ a : completedLocalRing (zeroScheme P L s) y,
      completedLocalIdeal (zeroScheme P L s) y = Ideal.span {a} := by
  obtain ⟨U, hx, b, hb⟩ := exists_affineOpen_zeroScheme_ideal_eq_span_singleton fP L hL s y
  exact exists_completedLocalIdeal_eq_span_singleton _ y U hx hb

/-- The points of the zero scheme whose closure has dimension at most `e`; the sets `T` and `T'`
are the cases `e = 1` and `e = 0`. -/
abbrev zeroSchemeClosureDimLE (e : ℕ) : Set P :=
  {q | q ∈ (zeroScheme P L s).support ∧ dimClosureAt P q ≤ (e : WithBot ℕ∞)}

omit [IsProper fP] in
/-- The sets `T`, `T'` are stable under specialization. -/
theorem stableUnderSpecialization_zeroSchemeClosureDimLE (e : ℕ) :
    StableUnderSpecialization (zeroSchemeClosureDimLE L s e) := by
  rintro x y hxy ⟨hx, hdim⟩
  exact ⟨hxy.mem_closed (zeroScheme P L s).support.isClosed hx,
    (dimClosureAt_le_of_specializes hxy).trans hdim⟩

omit [IsProper fP] in
/-- The sets `T`, `T'` lie in the zero scheme. -/
theorem zeroSchemeClosureDimLE_subset_support (e : ℕ) :
    zeroSchemeClosureDimLE L s e ⊆ (zeroScheme P L s).support := fun _ h => h.1

omit [IsProper fP] in
/-- `T' ⊆ T`. -/
theorem zeroSchemeClosureDimLE_mono {e e' : ℕ} (h : e ≤ e') :
    zeroSchemeClosureDimLE L s e ⊆ zeroSchemeClosureDimLE L s e' :=
  fun _ hx => ⟨hx.1, hx.2.trans (by exact_mod_cast h)⟩

include fP in
/-- **Hypothesis (e) of Stacks 0EJF for `T`, `T'`**: a point of the zero scheme specializing
immediately to a closed point of the zero scheme has closure of dimension one. -/
theorem mem_zeroSchemeClosureDimLE_one_of_isImmediateSpecialization (x x' : P)
    (hx : x ∈ (zeroScheme P L s).support) (hxx' : IsImmediateSpecialization x x')
    (hx' : x' ∈ zeroSchemeClosureDimLE L s 0) : x ∈ zeroSchemeClosureDimLE L s 1 := by
  refine ⟨hx, ?_⟩
  rw [dimClosureAt_eq_add_one_of_isImmediateSpecialization k fP hxx']
  calc dimClosureAt P x' + 1 ≤ ((0 : ℕ) : WithBot ℕ∞) + 1 := add_le_add_left hx'.2 1
    _ = ((1 : ℕ) : WithBot ℕ∞) := by norm_num

variable [IsLocallyNoetherian P] (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme P L s))
  (hdepth : ∀ q ∈ (zeroScheme P L s).support,
    ∀ p : PrimeSpectrum (completedLocalRing (zeroScheme P L s) q),
      ¬ completedLocalIdeal (zeroScheme P L s) q ≤ p.asIdeal →
      (2 : EInt) < enatToEInt (completedStalkDepth (zeroScheme P L s) F q p) +
        krullDimToEInt (ringKrullDim (completedLocalRing (zeroScheme P L s) q ⧸ p.asIdeal)) +
        krullDimToEInt (dimClosureAt P q))

omit [IsProper fP] [IsLocallyNoetherian P] in
/-- A prime `𝔭 ≠ 𝔪^∧` whose closed fibre is `{𝔪^∧}` does not contain the completed ideal. -/
theorem not_completedLocalIdeal_le_of_adicClosedFibreThrough_eq (q : P)
    (p : PrimeSpectrum (completedLocalRing (zeroScheme P L s) q))
    (hne : p.asIdeal ≠ completedMaximalIdeal (zeroScheme P L s) q)
    (hfib : adicClosedFibreThrough (zeroScheme P L s) q p =
      {completedMaximalIdeal (zeroScheme P L s) q}) :
    ¬ completedLocalIdeal (zeroScheme P L s) q ≤ p.asIdeal := by
  intro hle
  have hmem : p.asIdeal ∈ adicClosedFibreThrough (zeroScheme P L s) q p :=
    ⟨p.2, le_rfl, hle⟩
  rw [hfib] at hmem
  exact hne hmem

/-- The criterion of Stacks 0EL5 with `dim(𝒪^∧/𝔭)` replaced by its bound `1`, for a prime
`𝔭 ≠ 𝔪^∧` whose closed fibre is `{𝔪^∧}`. -/
private theorem two_lt_depth_add_one_add_dimClosureAt {y : P}
    (hy : y ∈ (zeroScheme P L s).support)
    (p : PrimeSpectrum (completedLocalRing (zeroScheme P L s) y))
    (hfib : adicClosedFibreThrough (zeroScheme P L s) y p =
      {completedMaximalIdeal (zeroScheme P L s) y}) {a : completedLocalRing (zeroScheme P L s) y}
    (ha : completedLocalIdeal (zeroScheme P L s) y = Ideal.span {a})
    (hq : (2 : EInt) < enatToEInt (completedStalkDepth (zeroScheme P L s) F y p) +
      krullDimToEInt (ringKrullDim (completedLocalRing (zeroScheme P L s) y ⧸ p.asIdeal)) +
      krullDimToEInt (dimClosureAt P y)) :
    ((2 : ℕ) : WithBot ℕ∞) <
      (completedStalkDepth (zeroScheme P L s) F y p : WithBot ℕ∞) + 1 + dimClosureAt P y :=
  (two_lt_add_of_two_lt_enatToEInt_add hq).trans_le
    (add_le_add_left (add_le_add_right
      (ringKrullDim_quotient_le_one_of_adicClosedFibreThrough_eq _ hy ha p hfib) _) _)

include fP hL hdepth in
/-- **Hypothesis (b) of Stacks 0EJF for `T`.** At a point of `T` and a prime `𝔭 ≠ 𝔪^∧` whose closed
fibre is `{𝔪^∧}`, the completed stalk has positive depth. -/
theorem zeroScheme_hypothesis_b :
    ∀ y ∈ zeroSchemeClosureDimLE L s 1,
      ∀ p : PrimeSpectrum (completedLocalRing (zeroScheme P L s) y),
      p.asIdeal ≠ completedMaximalIdeal (zeroScheme P L s) y →
      adicClosedFibreThrough (zeroScheme P L s) y p =
        {completedMaximalIdeal (zeroScheme P L s) y} →
      0 < completedStalkDepth (zeroScheme P L s) F y p := by
  intro y hy p hne hfib
  obtain ⟨a, ha⟩ := exists_completedLocalIdeal_zeroScheme_eq_span_singleton fP L hL s y
  have h := two_lt_depth_add_one_add_dimClosureAt L s F hy.1 p hfib ha (hdepth y hy.1 p
    (not_completedLocalIdeal_le_of_adicClosedFibreThrough_eq L s y p hne hfib))
  rw [pos_iff_ne_zero]
  rintro h0
  rw [h0] at h
  have hle : dimClosureAt P y ≤ 1 := by simpa using hy.2
  exact absurd (h.trans_le (add_le_add_right hle (((0 : ℕ∞) : WithBot ℕ∞) + 1))) (by norm_num)

include fP hL hdepth in
/-- **Hypothesis (d) of Stacks 0EJF for `T'`.** At a closed point of the zero scheme and a prime
`𝔭 ≠ 𝔪^∧` whose closed fibre is `{𝔪^∧}`, the completed stalk has depth at least two. -/
theorem zeroScheme_hypothesis_d :
    ∀ y ∈ zeroSchemeClosureDimLE L s 0,
      ∀ p : PrimeSpectrum (completedLocalRing (zeroScheme P L s) y),
      p.asIdeal ≠ completedMaximalIdeal (zeroScheme P L s) y →
      adicClosedFibreThrough (zeroScheme P L s) y p =
        {completedMaximalIdeal (zeroScheme P L s) y} →
      1 < completedStalkDepth (zeroScheme P L s) F y p := by
  intro y hy p hne hfib
  obtain ⟨a, ha⟩ := exists_completedLocalIdeal_zeroScheme_eq_span_singleton fP L hL s y
  have h := two_lt_depth_add_one_add_dimClosureAt L s F hy.1 p hfib ha (hdepth y hy.1 p
    (not_completedLocalIdeal_le_of_adicClosedFibreThrough_eq L s y p hne hfib))
  have h2 := h.trans_le (add_le_add_right (show dimClosureAt P y ≤ 0 by simpa using hy.2) _)
  rw [add_zero, show ((2 : ℕ) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) + 1 by norm_num,
    ← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_lt_coe] at h2
  exact (ENat.add_lt_add_iff_right ENat.one_ne_top).mp h2

include hdepth in
omit [IsProper fP] [IsLocallyNoetherian P] in
/-- **Hypothesis (c) of Stacks 0EJF for `T'` with `d = 1`.** At a closed point of the zero scheme
and a prime `𝔭` off the completed ideal, `depth((𝓕_q^∧)_𝔭) + dim(𝒪^∧/𝔭) > 2`. -/
theorem zeroScheme_hypothesis_c :
    ∀ y ∈ zeroSchemeClosureDimLE L s 0,
      ∀ p : PrimeSpectrum (completedLocalRing (zeroScheme P L s) y),
      ¬ completedLocalIdeal (zeroScheme P L s) y ≤ p.asIdeal →
      adicClosedFibreThrough (zeroScheme P L s) y p ≠
        {completedMaximalIdeal (zeroScheme P L s) y} →
      1 ≤ completedStalkDepth (zeroScheme P L s) F y p ∨
        enatToEInt (completedStalkDepth (zeroScheme P L s) F y p) +
            krullDimToEInt (ringKrullDim (completedLocalRing (zeroScheme P L s) y ⧸ p.asIdeal)) >
          ((1 + ((1 : ℕ) : ℤ) : ℤ) : EInt) := by
  intro y hy p hp _
  right
  have h := two_lt_add_of_two_lt_enatToEInt_add (hdepth y hy.1 p hp)
  have hle : ((completedStalkDepth (zeroScheme P L s) F y p : WithBot ℕ∞) +
      ringKrullDim (completedLocalRing (zeroScheme P L s) y ⧸ p.asIdeal) +
      dimClosureAt P y) ≤ (completedStalkDepth (zeroScheme P L s) F y p : WithBot ℕ∞) +
      ringKrullDim (completedLocalRing (zeroScheme P L s) y ⧸ p.asIdeal) + 0 :=
    add_le_add_right (show dimClosureAt P y ≤ 0 by simpa using hy.2) _
  have h2 := two_lt_enatToEInt_add_krullDimToEInt_add (h.trans_le hle)
  rwa [show krullDimToEInt (0 : WithBot ℕ∞) = 0 from rfl, add_zero] at h2

end ZeroScheme

end Stacks.Algebraization

end
