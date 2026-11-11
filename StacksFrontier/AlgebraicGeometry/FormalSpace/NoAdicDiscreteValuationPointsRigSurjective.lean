module

public import Mathlib.Algebra.MonoidAlgebra.Ideal
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoAdicDiscreteValuationPoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFromRepresentable
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Every morphism into `Spf (⋃_{n ≥ 1} k[t^{1/n}])^∧` is rig-surjective

Let `k` be a field and `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` the `t`-adic completion of the ring of
polynomials in the fractional powers of `t`. **Stacks 0AQZ** observes that there are no adic
morphisms `Spf R ⟶ Spf A` with `R` a complete discrete valuation ring, so that every morphism
`X ⟶ Spf A` is rig-surjective in the sense of Stacks 0AQQ, although `A` is a domain in which `t`
is nonzero.

A morphism `Spf R ⟶ Spf A` of formal spectra is `Spf` of a continuous ring map `φ : A → R`
(Stacks 0AN0); if it is representable by algebraic spaces — which is what adic means, Stacks
0AQ3 — then `φ` is taut (Stacks 0AN5), hence adic as a ring map since `A` has the finitely
generated ideal of definition `(t)` (Stacks 0APU). No ring map `A → R` is adic
(`AlgebraicGeometry.FormalSpace.FractionalPowers.not_isAdic_toDiscreteValuationRing`), so there
is no such morphism, and the lifting condition of Stacks 0AQQ holds vacuously for every morphism
with target `Spf A`.

## Main results

* `AlgebraicGeometry.FormalSpace.FractionalPowers.isDomain_completion`: `A` is a domain.
* `AlgebraicGeometry.FormalSpace.FractionalPowers.isAdicComplete_completion`: `A` is
  `t`-adically complete.
* `AlgebraicGeometry.FormalSpace.FractionalPowers.not_isRepresentable_formalSpectrum`: no
  morphism `Spf R ⟶ Spf A` from the formal spectrum of a complete discrete valuation ring is
  adic.
* `AlgebraicGeometry.FormalSpace.FractionalPowers.isRigSurjective_toFormalSpectrum`: every
  morphism `X ⟶ Spf A` is rig-surjective.
* `AlgebraicGeometry.FormalSpace.FractionalPowers.noAdicPoints_isRigSurjective_isDomain`:
  **Stacks 0AQZ**, the conjunction of the two results above with the facts that `A` is a domain
  and that `t ≠ 0` in `A`.

`A` is a domain because an element of `A` is determined by its images modulo the ideals `(t^n)`,
and modulo `(t^{m + m'})` the lowest exponents of two elements nonzero modulo `(t^m)` and
`(t^{m'})` add up to an exponent below `m + m'` carrying the nonzero product of the two lowest
coefficients.

## Implementation notes

The topologies are parameters fixed by hypotheses naming the ideals that define them: the
`t`-adic topology on `A` and the maximal-adic topology on `R`. That these are topological ring
topologies, linear, and weakly admissible is derived, using that `A` is `t`-adically complete
and `R` is complete. Adicness of a morphism of formal algebraic spaces is representability by
algebraic spaces, as in `AlgebraicGeometry.FormalSpace.IsRigSurjective`.

## References

* [Stacks Project, Tag 0AQZ](https://stacks.math.columbia.edu/tag/0AQZ)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace.FractionalPowers

universe u

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An element of `⋃_{n ≥ 1} k[t^{1/n}]` lies in the ideal `(t^n)` exactly when every exponent
occurring in it is at least `n`. -/
theorem mem_span_generator_pow_smul_top_iff {n : ℕ} {r : AddMonoidAlgebra k ℚ≥0} :
    r ∈ (Ideal.span {generator k} ^ n • ⊤ : Ideal (AddMonoidAlgebra k ℚ≥0)) ↔
      ∀ q ∈ r.coeff.support, (n : ℚ≥0) ≤ q := by
  have hgen : generator k ^ n = AddMonoidAlgebra.of' k ℚ≥0 (n : ℚ≥0) := by
    rw [generator, AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, mul_one]
    rfl
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, hgen, ← Set.image_singleton,
    AddMonoidAlgebra.mem_ideal_span_of'_image]
  simp only [Set.mem_singleton_iff, exists_eq_left]
  refine forall₂_congr fun q _ => ?_
  rw [le_iff_exists_add]
  exact ⟨fun ⟨d, hd⟩ => ⟨d, hd.trans (add_comm _ _)⟩,
    fun ⟨d, hd⟩ => ⟨d, hd.trans (add_comm _ _)⟩⟩

/-- If the image at level `j ≤ N` of an element of `A` whose level `N` image is represented by
`r` is nonzero, then some exponent occurring in `r` is less than `j`. -/
private theorem exists_lt_of_val_ne_zero {z : Completion k} {N j : ℕ} (hj : j ≤ N)
    {r : AddMonoidAlgebra k ℚ≥0} (hr : Ideal.Quotient.mk _ r = z.val N) (hz : z.val j ≠ 0) :
    ∃ q ∈ r.coeff.support, q < (j : ℚ≥0) := by
  rw [← AdicCompletion.transitionMap_comp_eval_apply _ _ hj, ← hr,
    AdicCompletion.transitionMap_ideal_mk, Ne, Ideal.Quotient.eq_zero_iff_mem,
    mem_span_generator_pow_smul_top_iff] at hz
  push Not at hz
  exact hz

/-- The product of two nonzero elements of `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` is nonzero: if the
images of `x` and `y` modulo `t^m` and `t^{m'}` are nonzero, then the lowest exponents `α < m`
and `β < m'` of representatives modulo `t^{m + m'}` give the exponent `α + β < m + m'` of the
product, whose coefficient is the nonzero product of the two lowest coefficients. -/
theorem completion_mul_ne_zero {x y : Completion k} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by
  classical
  have hval : ∀ z : Completion k, z ≠ 0 → ∃ m, z.val m ≠ 0 := fun z hz => by
    by_contra h
    push Not at h
    exact hz (AdicCompletion.ext h)
  obtain ⟨m, hm⟩ := hval x hx
  obtain ⟨m', hm'⟩ := hval y hy
  obtain ⟨rx, hrx⟩ := Ideal.Quotient.mk_surjective (x.val (m + m'))
  obtain ⟨ry, hry⟩ := Ideal.Quotient.mk_surjective (y.val (m + m'))
  obtain ⟨q, hq, hqm⟩ := exists_lt_of_val_ne_zero k (Nat.le_add_right m m') hrx hm
  obtain ⟨q', hq', hqm'⟩ := exists_lt_of_val_ne_zero k (Nat.le_add_left m' m) hry hm'
  set α := rx.coeff.support.min' ⟨q, hq⟩
  set β := ry.coeff.support.min' ⟨q', hq'⟩
  have hα : α ∈ rx.coeff.support := Finset.min'_mem _ _
  have hβ : β ∈ ry.coeff.support := Finset.min'_mem _ _
  have huniq : UniqueAdd rx.coeff.support ry.coeff.support α β := by
    intro a b ha hb hab
    have h1 : α ≤ a := Finset.min'_le _ _ ha
    have h2 : β ≤ b := Finset.min'_le _ _ hb
    have h3 : a = α := by
      by_contra hne
      exact (add_lt_add_of_lt_of_le (lt_of_le_of_ne h1 (Ne.symm hne)) h2).ne' hab
    subst h3
    exact ⟨rfl, add_left_cancel hab⟩
  have hcoeff : (rx * ry).coeff (α + β) ≠ 0 := by
    rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp hα) (Finsupp.mem_support_iff.mp hβ)
  have hlt : α + β < ((m + m' : ℕ) : ℚ≥0) := by
    rw [Nat.cast_add]
    exact add_lt_add ((Finset.min'_le _ _ hq).trans_lt hqm)
      ((Finset.min'_le _ _ hq').trans_lt hqm')
  intro h
  have h0 : (x * y).val (m + m') = 0 := by rw [h]; rfl
  rw [AdicCompletion.val_mul, ← hrx, ← hry, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    mem_span_generator_pow_smul_top_iff] at h0
  exact (h0 _ (Finsupp.mem_support_iff.mpr hcoeff)).not_gt hlt

/-- The ring `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` is a domain. -/
theorem isDomain_completion : IsDomain (Completion k) :=
  have : Nontrivial (Completion k) := ⟨⟨_, _, completionGenerator_ne_zero k⟩⟩
  have : NoZeroDivisors (Completion k) := ⟨fun {_ _} h => by
    by_contra hc
    push Not at hc
    exact completion_mul_ne_zero k hc.1 hc.2 h⟩
  NoZeroDivisors.to_isDomain _

instance : IsDomain (Completion k) := isDomain_completion k

/-- The ring `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` is `t`-adically complete. -/
theorem isAdicComplete_completion :
    IsAdicComplete (Ideal.span {completionGenerator k}) (Completion k) := by
  have h := (IsAdicComplete.map_algebraMap_iff (S := Completion k) (Ideal.span {generator k})
    (Completion k)).mpr (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _))
  rw [Ideal.map_span, Set.image_singleton] at h
  exact h

/-- A topology on a commutative ring which is the adic topology of an ideal makes it a linearly
topologized topological ring. -/
private theorem isTopologicalRing_isLinearTopology_of_isAdic {R : Type*} [CommRing R]
    [TopologicalSpace R] {I : Ideal R} (hI : _root_.IsAdic I) :
    IsTopologicalRing R ∧ IsLinearTopology R R := by
  rw [hI]
  exact ⟨(Ideal.nonarchimedean I).toIsTopologicalRing, Ideal.isLinearTopology I⟩

/-- There is no adic morphism `Spf R ⟶ Spf A`, for `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` carrying its
`t`-adic topology and `R` a complete discrete valuation ring carrying its maximal-adic topology:
no morphism of formal spectra `Spf R ⟶ Spf A` over `S` is representable by algebraic spaces. -/
theorem not_isRepresentable_formalSpectrum [TopologicalSpace (Completion k)]
    (hA : _root_.IsAdic (Ideal.span {completionGenerator k}))
    (D : QuotientSystem B S hS (Completion k)) (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [TopologicalSpace R]
    (hR : _root_.IsAdic (IsLocalRing.maximalIdeal R))
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (E : QuotientSystem B S hS R)
    (p : formalSpectrum E ⟶ formalSpectrum D) :
    ¬ Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom := by
  intro hrep
  obtain ⟨_, _⟩ := isTopologicalRing_isLinearTopology_of_isAdic hA
  obtain ⟨_, _⟩ := isTopologicalRing_isLinearTopology_of_isAdic hR
  have hAw : TopologicalRing.IsWeaklyAdmissible (Completion k) :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hA (isAdicComplete_completion k)
  have hRw : TopologicalRing.IsWeaklyAdmissible R :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hR inferInstance
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAw hRw p
  rw [← hg] at hrep
  have htaut := isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap B S hS hAw hRw D E
    g hrep
  obtain ⟨-, hcomplete, hT2⟩ := hRw
  exact not_isAdic_toDiscreteValuationRing k hA R hR g.toRingHom
    (RingHom.isAdic_of_isTaut g.toRingHom htaut
      ⟨_, Submodule.fg_span_singleton _, hA⟩)

/-- Every morphism `X ⟶ Spf A`, for `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` carrying its `t`-adic
topology, is rig-surjective: there is no adic morphism `Spf R ⟶ Spf A` out of the formal
spectrum of a complete discrete valuation ring to lift. -/
theorem isRigSurjective_toFormalSpectrum [TopologicalSpace (Completion k)]
    (hA : _root_.IsAdic (Ideal.span {completionGenerator k}))
    (D : QuotientSystem B S hS (Completion k)) {X : FppfSheaf B S hS}
    (f : X ⟶ formalSpectrum D) : IsRigSurjective B S hS f := by
  intro R _ _ _ _ _ _ hR hcomplete _ E p hp
  exact absurd hp (not_isRepresentable_formalSpectrum k B S hS hA D R hR E p)

/-- **Stacks 0AQZ.** Let `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` be the `t`-adic completion of the ring
of polynomials in the fractional powers of `t` over a field `k`, carrying its `t`-adic topology.
There are no adic morphisms `Spf R ⟶ Spf A` with `R` a complete discrete valuation ring; thus
every morphism `X ⟶ Spf A` is rig-surjective; and yet `A` is a domain and `t ∈ A` is not zero. -/
@[stacks 0AQZ]
theorem noAdicPoints_isRigSurjective_isDomain [TopologicalSpace (Completion k)]
    (hA : _root_.IsAdic (Ideal.span {completionGenerator k}))
    (D : QuotientSystem B S hS (Completion k)) :
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R],
      _root_.IsAdic (IsLocalRing.maximalIdeal R) →
        IsAdicComplete (IsLocalRing.maximalIdeal R) R →
          ∀ (E : QuotientSystem B S hS R) (p : formalSpectrum E ⟶ formalSpectrum D),
            ¬ Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom) ∧
      (∀ {X : FppfSheaf B S hS} (f : X ⟶ formalSpectrum D), IsRigSurjective B S hS f) ∧
      IsDomain (Completion k) ∧ completionGenerator k ≠ 0 :=
  ⟨fun R _ _ _ _ hR _ E p => not_isRepresentable_formalSpectrum k B S hS hA D R hR E p,
    fun f => isRigSurjective_toFormalSpectrum k B S hS hA D f, isDomain_completion k,
    completionGenerator_ne_zero k⟩

end AlgebraicGeometry.FormalSpace.FractionalPowers

end
