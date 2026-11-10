module

public import StacksFrontier.RingTheory.DimensionFormula.OneGeneratorStep
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
import StacksCore.LinearAlgebra.Matrix.CommSemiring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension formula, and quasi-finiteness in codimension one

Let `R ⊆ S` be an extension of domains with `R` Noetherian and `S` of finite type over `R`, let
`p` be a prime of `R` and `q` a prime of `S` lying over `p`, that is, `p = q ∩ R`. The dimension
formula (Stacks 02IJ) compares the height of `q` with the height of `p`, correcting by the
transcendence degrees of `S` over `R` and of the residue field extension `κ(q)/κ(p)`:

* `height q + trdeg_{κ(p)} κ(q) ≤ height p + trdeg_R S`, and
* if `R` is in addition universally catenary, this is an equality.

The two extremes of the inequality are the two ways a fibre can be larger than expected: for
`R = k[x] ⊆ S = k[x, y]` the prime `q = (x, y)` has `height q = 2 = height p + trdeg_R S` with
`trdeg_{κ(p)} κ(q) = 0`, while `q = (x)S` has `height q = 1` and `trdeg_{κ(p)} κ(q) = 1`.

Let `A ⊆ B` be an extension of domains with `A` Noetherian, let `B` be of finite type over `A`,
and assume `B` is algebraic over `A`; for `B` of finite type over `A` the latter is exactly the
condition that the induced extension of fraction fields `Frac(A) ⊆ Frac(B)` be finite, i.e. that
`A → B` be *generically finite*. Stacks 02MA then says that over a prime `p` of `A` of height
one there are at most finitely many primes of `B`, and every one of them has height one; it is
proved in `StacksFrontier.RingTheory.Ideal.Over.HeightOne`, which this file imports.

Geometrically: a dominant generically finite morphism of finite type between integral schemes,
with Noetherian target, is quasi-finite in codimension one, and codimension one is preserved. The
two failure modes it excludes are both codimension two phenomena on the target: over the height
two prime `(x, y)` the blowup chart `k[x, y] ⊆ k[x, y/x]` has a whole affine line, one chart of
the exceptional `ℙ¹`; and a fibre of positive dimension, such as the one of `k[x] ⊆ k[x, y]` over
`(x)`, occurs only when the extension is not generically finite.

The conclusion is a bound above only: the fibre over `p` may well be empty, as it is for
`ℤ ⊆ ℤ[1/2]` over `p = (2)`, since `B` is not assumed integral over `A`.

The topological and residue-field preliminaries, `Ideal.ResidueField.algebraOfLiesOver`,
`zeroLocusIsoIic` and the catenary one-generator step are in
`StacksFrontier.RingTheory.DimensionFormula.OneGeneratorStep`.

## Main results

* `height_add_trdeg_residue_le`: the dimension formula as an inequality, for any finite-type
  extension of Noetherian domains.
* `height_add_trdeg_residue_ge`: the reverse inequality, for `R` universally catenary.
* `height_add_trdeg_residue_eq`: the dimension formula as an equality, for `R` universally
  catenary.
Stacks 02MA — finiteness of the fibre over a height one prime, and preservation of height one —
is `Ideal.primesOver_finite_and_forall_height_eq_one` in
`StacksFrontier.RingTheory.Ideal.Over.HeightOne`, the module that owns the `Ideal.primesOver`
vocabulary. The discussion of 02MA below applies to it.

## Implementation notes

Heights are `Ideal.height`, the supremum of the lengths of strictly increasing chains of primes
ending at the given ideal; they live in `ℕ∞` and are not assumed finite. Transcendence degrees
are `Algebra.trdeg`, the transcendence degree of `Frac B` over the image of `Frac A`, valued in
`Cardinal`; the ones occurring here are finite under the finite-type hypothesis, and are moved
into `ℕ∞` by `Cardinal.toNat`.

The source states the dimension formula subtractively, as
`height q ≤ height p + trdeg_R S - trdeg_{κ(p)} κ(q)`. The additive form used here moves the
subtracted term to the left, which avoids truncated subtraction in `ℕ∞`, where `height p` and
`height q` are not assumed finite; the two forms agree because the subtracted term is finite.

The rings may lie in independent universes. Residue-field isomorphisms compare cardinal
transcendence degrees after `Cardinal.lift`; applying `Cardinal.toNat` removes these lifts
in the dimension formula.

The residue field of a prime `I` is `Ideal.ResidueField I`, and the residue field map
`κ(p) →+* κ(q)` is `Ideal.ResidueField.map p q (algebraMap R S) Ideal.LiesOver.over`. The
`κ(p)`-algebra structure it defines on `κ(q)` is not an instance, since it depends on the
`LiesOver` witness; every statement about the residue field extension therefore opens with
`letI := Ideal.ResidueField.algebraOfLiesOver p q`.

The proof of the dimension formula goes by induction on a finite generating set of `S` over `R`,
through the one-generator extensions `R[x]` and `R[x]/n` with `n` of height one meeting `R` in
`(0)`; going down is not available, since `Algebra.HasGoingDown R S` fails already for
`k[x, xy] ⊆ k[x, y]`.

Hypothesis (2) of the source, that the induced extension of fraction fields be finite, is stated
as `Algebra.IsAlgebraic A B`. The two agree under hypotheses (1) and (4): writing
`K = Frac(A) ⊆ L = Frac(B)`, an element of `B` algebraic over `A` is algebraic over `K`, so if
`B = A[b₁, …, b_n]` is algebraic over `A` then `L = K(b₁, …, b_n)` is finite over `K`; conversely
`L/K` finite makes every element of `B ⊆ L` algebraic over `K`, hence over `A` after clearing
denominators. `IsFractionRing.isAlgebraic_iff'` and `IsFractionRing.isAlgebraic_iff` are the
transfers, and `trdeg_eq_zero_iff` turns this hypothesis into the vanishing of `Algebra.trdeg A B`
that the dimension formula, Stacks 02IJ, consumes in the proof. The gain over the literal form is
that no fraction fields, and hence no auxiliary types and scalar towers, appear in the signature;
the price is that the equivalence above is a step of the proof rather than of the statement.

The inclusion `A ⊆ B` is `FaithfulSMul A B`, injectivity of `algebraMap A B`
(`FaithfulSMul.algebraMap_injective`), which is Mathlib's spelling of a ring extension.
`IsDomain A` is not assumed: it follows from `IsDomain B` by
`Function.Injective.isDomain (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)`, so
hypothesis (1) is carried in full by `IsDomain B` together with `FaithfulSMul A B`.

The primes of `B` lying over `p` are `Ideal.primesOver p B`, whose membership unfolds to
`q.IsPrime` together with `Ideal.LiesOver q p`, i.e. `p = q.comap (algebraMap A B)`: the source's
`p = q ∩ A` for the given map `A → B`. Heights are `Ideal.height`, valued in `ℕ∞`; on a prime `q`
it is the supremum of the lengths of strictly descending chains of primes of `B` ending at `q`,
`PrimeSpectrum.height_eq_orderHeight` reading `q.height = Order.height (⟨q, _⟩ : PrimeSpectrum B)`,
so the conclusion `q.height = 1` says `dim B_q = 1`. No finiteness of any height is assumed, and
the hypothesis `p.height = 1` is an equality in `ℕ∞`.

Only the source's two assertions are stated. The proof passes through the stronger local fact that
`κ(p) ⊆ κ(q)` is finite for `q` over `p`, that is, that `A → B` is quasi-finite at each such `q`
(`Algebra.QuasiFiniteAt`); that refinement belongs to a lemma of its own, not to this tag.

None of the hypotheses of Stacks 02MA can be dropped. `p.height = 1` is needed: for
`A = k[x, y] ⊆ B = k[x, y/x]` and `p = (x, y)` of height two, every `(x, f(y/x))` with `f`
irreducible lies over `p`, so the fibre is infinite. `Algebra.IsAlgebraic A B` is needed: for
`A = k[x] ⊆ B = k[x, y]` and `p = (x)` of height one the primes `(x, f(y))` lie over `p`, and
they are infinite in number and of height two. `FaithfulSMul A B` is needed: for `A = ℤ`,
`B = 𝔽₅` and `p = (5)` the only prime over `p` is `(0)`, of height zero. `IsDomain B` is needed:
for `A = ℤ ⊆ B = ℤ × 𝔽₅` and `p = (5)` the prime `ℤ × 0` lies over `p` and is a minimal prime of
`B`. `Algebra.FiniteType A B` is needed: for `A = ℤ` and `B` the ring of all algebraic integers,
`(5)` has infinitely many primes above it, one over each prime above `5` in each layer of a tower
of number fields in which that number grows without bound. `IsNoetherianRing A` enters twice,
through the dimension formula and through the Noetherianity of the fibre `B ⊗_A κ(p)`, whose
spectrum is finite because it is a Noetherian space all of whose points are closed. A
non-degenerate instance: for `A = ℤ ⊆ B = ℤ[i]` and `p = (5) = (2 + i)(2 - i)` there are exactly
two primes over `p`, both of height one.

## References

* [StackProject 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
* [StackProject 02MA](https://stacks.math.columbia.edu/tag/02MA)

## Tags

height one prime, generically finite, quasi-finite, lying over
-/

@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
/-- If the subalgebra `B` generated over `R` by a finite set `T ⊆ S` is trivial, then `R ≃ₐ[R] ↥B`
and the contraction `q ∩ B` transports back to `p`: its height is `p.height`, and both the
transcendence degree of `B` over `R` and that of `κ(q ∩ B)` over `κ(p)` vanish. -/
private theorem adjoin_eq_bot_transport [IsDomain R] [IsDomain S]
    (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] [q.LiesOver p] (T : Finset S)
    (hbot : Algebra.adjoin R (↑T : Set S) = ⊥) :
    letI := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥(Algebra.adjoin R (↑T : Set S)))
    (q.under ↥(Algebra.adjoin R (↑T : Set S))).height = p.height
      ∧ Algebra.trdeg R (↥(Algebra.adjoin R (↑T : Set S))) = 0
      ∧ (Cardinal.toNat (Algebra.trdeg p.ResidueField
          (q.under ↥(Algebra.adjoin R (↑T : Set S))).ResidueField) : ℕ∞) = 0 := by
  let := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥(Algebra.adjoin R (↑T : Set S)))
  let e₀ : R ≃ₐ[R] ↥(Algebra.adjoin R (↑T : Set S)) :=
    ((Subalgebra.equivOfEq _ _ hbot).trans (Algebra.botEquivOfInjective hinj)).symm
  have he₀map : (e₀ : R →+* ↥(Algebra.adjoin R (↑T : Set S)))
      = algebraMap R ↥(Algebra.adjoin R (↑T : Set S)) := by
    ext r; simp [e₀]; rfl
  have hcomap0 : Ideal.comap (e₀ : R →+* ↥(Algebra.adjoin R (↑T : Set S)))
      (q.under ↥(Algebra.adjoin R (↑T : Set S))) = p := by
    rw [he₀map, ← Ideal.under_def]
    exact (Ideal.LiesOver.over (p := p) (P := q.under ↥(Algebra.adjoin R (↑T : Set S)))).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcomap0]
    exact (height_comap_ringEquiv (e₀ : R ≃+* ↥(Algebra.adjoin R (↑T : Set S)))
      (q.under ↥(Algebra.adjoin R (↑T : Set S)))).symm
  · have h := e₀.lift_trdeg_eq
    simpa only [trdeg_eq_zero (R := R) (A := R), Cardinal.lift_zero,
      Cardinal.lift_eq_zero] using h.symm
  · have hsurj : Function.Surjective
        (algebraMap p.ResidueField
          (q.under ↥(Algebra.adjoin R (↑T : Set S))).ResidueField) := by
      change Function.Surjective
        (Ideal.ResidueField.map p (q.under ↥(Algebra.adjoin R (↑T : Set S)))
          (algebraMap R ↥(Algebra.adjoin R (↑T : Set S))) Ideal.LiesOver.over)
      apply residueField_map_surjective
      rw [← he₀map]; exact e₀.surjective
    have : Algebra.IsAlgebraic p.ResidueField
        (q.under ↥(Algebra.adjoin R (↑T : Set S))).ResidueField := by
      have : Algebra.IsIntegral p.ResidueField
          (q.under ↥(Algebra.adjoin R (↑T : Set S))).ResidueField := by
        constructor
        intro x
        obtain ⟨k, rfl⟩ := hsurj x
        exact ⟨Polynomial.X - Polynomial.C k, by simp [Polynomial.monic_X_sub_C], by simp⟩
      exact Algebra.IsIntegral.isAlgebraic
    rw [trdeg_eq_zero]; simp

/-- For subalgebras `BT ≤ B'` of `S`, the `ℕ∞`-valued transcendence degrees add along the tower
`R → ↥BT → ↥B'`, and — given that the top step of the residue tower is finite — along
`κ(p) → κ(q ∩ BT) → κ(q ∩ B')` as well. -/
private theorem trdeg_toNat_step_add [IsNoetherianRing R] [IsDomain R] [IsDomain S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (BT B' : Subalgebra R S) [Algebra ↥BT ↥B'] [IsScalarTower R ↥BT ↥B']
    [IsScalarTower ↥BT ↥B' S] [FaithfulSMul R ↥BT] [FaithfulSMul ↥BT ↥B']
    [Algebra.FiniteType R ↥BT] [Algebra.FiniteType ↥BT ↥B']
    (hfin : letI := Ideal.ResidueField.algebraOfLiesOver (q.under ↥BT) (q.under ↥B')
      Algebra.trdeg (q.under ↥BT).ResidueField (q.under ↥B').ResidueField < Cardinal.aleph0) :
    letI := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥BT)
    letI := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥B')
    letI := Ideal.ResidueField.algebraOfLiesOver (q.under ↥BT) (q.under ↥B')
    ((Cardinal.toNat (Algebra.trdeg R ↥B') : ℕ∞)
        = (Cardinal.toNat (Algebra.trdeg R ↥BT) : ℕ∞)
          + (Cardinal.toNat (Algebra.trdeg ↥BT ↥B') : ℕ∞))
      ∧ ((Cardinal.toNat (Algebra.trdeg p.ResidueField (q.under ↥B').ResidueField) : ℕ∞)
        = (Cardinal.toNat (Algebra.trdeg p.ResidueField (q.under ↥BT).ResidueField) : ℕ∞)
          + (Cardinal.toNat (Algebra.trdeg (q.under ↥BT).ResidueField
              (q.under ↥B').ResidueField) : ℕ∞)) := by
  let := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥BT)
  let := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥B')
  let := Ideal.ResidueField.algebraOfLiesOver (q.under ↥BT) (q.under ↥B')
  constructor
  · have hadd := trdeg_add_eq R (↥BT) (A := ↥B')
    have hfin1 : Algebra.trdeg R (↥BT) < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
    have hfin2 : Algebra.trdeg (↥BT) (↥B') < Cardinal.aleph0 :=
      trdeg_lt_aleph0_of_finiteType
    rw [← hadd, Cardinal.toNat_add hfin1 hfin2]
    push_cast; ring
  · have restow : IsScalarTower p.ResidueField (q.under ↥BT).ResidueField
        (q.under ↥B').ResidueField := by
      apply IsScalarTower.of_algebraMap_eq'
      change (Ideal.ResidueField.map p (q.under ↥B') (algebraMap R (↥B')) Ideal.LiesOver.over)
          = (Ideal.ResidueField.map (q.under ↥BT) (q.under ↥B') (algebraMap (↥BT) (↥B'))
              Ideal.LiesOver.over).comp
            (Ideal.ResidueField.map p (q.under ↥BT) (algebraMap R (↥BT)) Ideal.LiesOver.over)
      have hcomp_eq : (algebraMap (↥BT) (↥B')).comp (algebraMap R (↥BT))
          = algebraMap R (↥B') := (IsScalarTower.algebraMap_eq R (↥BT) (↥B')).symm
      have hcomp := residueField_map_comp p (q.under ↥BT) (q.under ↥B')
        (algebraMap R (↥BT)) (algebraMap (↥BT) (↥B'))
        Ideal.LiesOver.over Ideal.LiesOver.over (by rw [hcomp_eq]; exact Ideal.LiesOver.over)
      have hmapeq := residueField_map_congr p (q.under ↥B')
        ((algebraMap (↥BT) (↥B')).comp (algebraMap R (↥BT))) (algebraMap R (↥B')) hcomp_eq
        (by rw [hcomp_eq]; exact Ideal.LiesOver.over) Ideal.LiesOver.over
      rw [hcomp, ← hmapeq]
    have : FaithfulSMul p.ResidueField (q.under ↥BT).ResidueField := by
      rw [faithfulSMul_iff_algebraMap_injective]
      exact (algebraMap p.ResidueField (q.under ↥BT).ResidueField).injective
    have : FaithfulSMul (q.under ↥BT).ResidueField (q.under ↥B').ResidueField := by
      rw [faithfulSMul_iff_algebraMap_injective]
      exact (algebraMap (q.under ↥BT).ResidueField (q.under ↥B').ResidueField).injective
    have hfin1 : Algebra.trdeg p.ResidueField (q.under ↥BT).ResidueField < Cardinal.aleph0 :=
      resfield_trdeg_lt_aleph0_general p (q.under ↥BT)
    have hadd := trdeg_add_eq p.ResidueField (q.under ↥BT).ResidueField
      (A := (q.under ↥B').ResidueField)
    rw [← hadd, Cardinal.toNat_add hfin1 hfin]
    push_cast; ring

/-- If a finite set `G` generates `S` as an `R`-algebra, then `↥(R[G]) ≃ₐ[R] S` and the
contraction `q ∩ R[G]` has the height of `q`, the same transcendence degree over `R` as `S`,
and a residue field of the same transcendence degree over `κ(p)` as `κ(q)`. -/
private theorem adjoin_eq_top_transport [IsDomain S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] (G : Finset S)
    (hG : Algebra.adjoin R (↑G : Set S) = ⊤) :
    letI := Ideal.ResidueField.algebraOfLiesOver p q
    letI := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥(Algebra.adjoin R (↑G : Set S)))
    (q.under ↥(Algebra.adjoin R (↑G : Set S))).height = q.height
      ∧ Algebra.trdeg R (↥(Algebra.adjoin R (↑G : Set S))) = Algebra.trdeg R S
      ∧ Algebra.trdeg p.ResidueField (q.under ↥(Algebra.adjoin R (↑G : Set S))).ResidueField
          = Algebra.trdeg p.ResidueField q.ResidueField := by
  let := Ideal.ResidueField.algebraOfLiesOver p q
  let := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥(Algebra.adjoin R (↑G : Set S)))
  let e : ↥(Algebra.adjoin R (↑G : Set S)) ≃ₐ[R] S :=
    (Subalgebra.equivOfEq _ _ hG).trans Subalgebra.topEquiv
  have hcomapeq : Ideal.comap (e : ↥(Algebra.adjoin R (↑G : Set S)) →+* S) q
      = q.under ↥(Algebra.adjoin R (↑G : Set S)) := rfl
  have hqBLO : (Ideal.comap (e : ↥(Algebra.adjoin R (↑G : Set S)) →+* S) q).LiesOver p :=
    Ideal.LiesOver.of_eq_comap p e rfl
  refine ⟨?_, AlgEquiv.trdeg_eq e, resfield_trdeg_algEquiv_eq e p q⟩
  rw [← hcomapeq]
  exact height_comap_ringEquiv (e : ↥(Algebra.adjoin R (↑G : Set S)) ≃+* S) q

/-- For `BT ≤ B'` subalgebras of `S` with `↥B'` an `↥BT`-algebra through the inclusion, the triples
`↥BT, ↥B', S` and `R, ↥BT, ↥B'` are scalar towers, and — when `R → S` is injective — both
structure maps `R → ↥BT` and `↥BT → ↥B'` are faithful. -/
private theorem inclusion_towers (hinj : Function.Injective (algebraMap R S))
    {BT B' : Subalgebra R S} (hle : BT ≤ B') :
    letI : Algebra ↥BT ↥B' := (Subalgebra.inclusion hle).toAlgebra
    IsScalarTower ↥BT ↥B' S ∧ IsScalarTower R ↥BT ↥B'
      ∧ FaithfulSMul R ↥BT ∧ FaithfulSMul ↥BT ↥B' := by
  let : Algebra (↥BT) (↥B') := (Subalgebra.inclusion hle).toAlgebra
  have hincleq : (algebraMap (↥BT) (↥B') : ↥BT →+* ↥B')
      = (Subalgebra.inclusion hle : ↥BT →+* ↥B') := rfl
  refine ⟨IsScalarTower.of_algebraMap_eq (fun _ => rfl), ?_, ?_, ?_⟩
  · apply IsScalarTower.of_algebraMap_eq
    intro r; rw [hincleq]; apply Subtype.ext; simp [Subalgebra.inclusion]
  · rw [faithfulSMul_iff_algebraMap_injective]
    refine Function.Injective.of_comp (f := algebraMap (↥BT) S) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact hinj
  · rw [faithfulSMul_iff_algebraMap_injective, hincleq]
    exact Subalgebra.inclusion_injective hle

/-- For `a : S` and `T : Finset S`, the subalgebra `R[insert a T]` of `S` is generated by the
single element `a` over the subalgebra `R[T]`. -/
private theorem adjoin_insert_isOneGenerator [DecidableEq S] (a : S) (T : Finset S)
    [Algebra ↥(Algebra.adjoin R (↑T : Set S)) ↥(Algebra.adjoin R (↑(insert a T) : Set S))]
    [IsScalarTower ↥(Algebra.adjoin R (↑T : Set S))
      ↥(Algebra.adjoin R (↑(insert a T) : Set S)) S] :
    ∃ x : ↥(Algebra.adjoin R (↑(insert a T) : Set S)),
      Algebra.adjoin ↥(Algebra.adjoin R (↑T : Set S)) {x} = ⊤ := by
  have haB' : a ∈ Algebra.adjoin R (↑(insert a T) : Set S) := by
    apply Algebra.subset_adjoin; simp
  refine ⟨⟨a, haB'⟩, ?_⟩
  have hB'eq : Algebra.adjoin R (↑(insert a T) : Set S)
      = Subalgebra.restrictScalars R
        (Algebra.adjoin ↥(Algebra.adjoin R (↑T : Set S)) ({a} : Set S)) := by
    have hu : (↑(insert a T) : Set S) = (↑T : Set S) ∪ {a} := by
      rw [Finset.coe_insert]; ext z; simp
    rw [hu, Algebra.adjoin_union_eq_adjoin_adjoin]
  have hmem : ∀ x : S, x ∈ Algebra.adjoin R (↑(insert a T) : Set S)
      ↔ x ∈ Algebra.adjoin ↥(Algebra.adjoin R (↑T : Set S)) ({a} : Set S) := by
    intro x; rw [hB'eq]; rfl
  let j : ↥(Algebra.adjoin R (↑(insert a T) : Set S))
      →ₐ[↥(Algebra.adjoin R (↑T : Set S))] S :=
    IsScalarTower.toAlgHom ↥(Algebra.adjoin R (↑T : Set S))
      ↥(Algebra.adjoin R (↑(insert a T) : Set S)) S
  have hjinj : Function.Injective j := Subtype.val_injective
  apply Subalgebra.map_injective hjinj
  rw [AlgHom.map_adjoin]
  have himg : (j : ↥(Algebra.adjoin R (↑(insert a T) : Set S)) → S)
      '' {(⟨a, haB'⟩ : ↥(Algebra.adjoin R (↑(insert a T) : Set S)))} = {a} := by
    simp [j, IsScalarTower.toAlgHom]
  rw [himg, Algebra.map_top]
  ext x
  rw [AlgHom.mem_range]
  exact ⟨fun hx => ⟨⟨x, (hmem _).mpr hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact (hmem _).mp y.property⟩

/-- For `a : S` and `T : Finset S`, the subalgebra `R[insert a T]` of `S` is generated by the
single element `a` over the subalgebra `R[T]`. -/
alias adjoin_insert_isOneGenerator' := adjoin_insert_isOneGenerator

/-- The dimension formula for an arbitrary finite-type extension `R ⊆ S`, given the one-generator
case as the hypothesis `hstep`, in the form
`r (p.height + trdeg_R S) (q.height + trdeg_{κ(p)} κ(q))`: at `r = (· ≤ ·)` this is the catenary
half of the formula and at `r = (· ≥ ·)` the unconditional one. Induction on a finite generating
set `G` of `S` runs through the subalgebras `R[T]`, `T ⊆ G`, each step adding one generator; the
contraction `q ∩ R[T]` lies over `p`, the heights telescope, and the transcendence degrees add
along the towers `R → R[T] → R[T ∪ {a}]` and `κ(p) → κ(q ∩ R[T]) → κ(q ∩ R[T ∪ {a}])`. The
predicate `good` carries whatever the one-generator step assumes of the base ring — universal
catenarity in the `≤` direction, nothing in the `≥` one — and `hgood` supplies it for the
intermediate rings `R[T]`. -/
private theorem dim_formula_generator_induction (r : ℕ∞ → ℕ∞ → Prop)
    (hrefl : ∀ x : ℕ∞, r x x) (htrans : ∀ x y z : ℕ∞, r x y → r y z → r x z)
    (hadd : ∀ x y c : ℕ∞, r x y → r (x + c) (y + c))
    (good : (A : Type v) → [CommRing A] → Prop)
    (hstep : ∀ (A A' : Type v) [CommRing A] [CommRing A'] [Algebra A A']
        [IsNoetherianRing A] [Algebra.FiniteType A A'] [IsDomain A] [IsDomain A'],
        Function.Injective (algebraMap A A') → good A →
        (∃ x : A', Algebra.adjoin A {x} = ⊤) →
        ∀ (P : Ideal A) (Q : Ideal A') [P.IsPrime] [Q.IsPrime] [Q.LiesOver P],
          letI := Ideal.ResidueField.algebraOfLiesOver P Q
          r (P.height + (Cardinal.toNat (Algebra.trdeg A A') : ℕ∞))
            (Q.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞)))
    [IsNoetherianRing R] [Algebra.FiniteType R S] [IsDomain R] [IsDomain S]
    (hinj : Function.Injective (algebraMap R S))
    (hgood : ∀ T : Finset S, good ↥(Algebra.adjoin R (↑T : Set S)))
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI := Ideal.ResidueField.algebraOfLiesOver p q
    r (p.height + (Cardinal.toNat (Algebra.trdeg R S) : ℕ∞))
      (q.height + (Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) : ℕ∞)) := by
  classical
  let := Ideal.ResidueField.algebraOfLiesOver p q
  have tele : ∀ a₀ Ai Ai1 Di di Ti ti : ℕ∞, r (a₀ + Di) (Ai + Ti) → r (Ai + di) (Ai1 + ti) →
      r (a₀ + (Di + di)) (Ai1 + (Ti + ti)) := by
    intro a₀ Ai Ai1 Di di Ti ti ih step
    have h₁ : r (a₀ + Di + di) (Ai + di + Ti) := by
      rw [show Ai + di + Ti = Ai + Ti + di from by ring]; exact hadd _ _ _ ih
    rw [show a₀ + (Di + di) = a₀ + Di + di from by ring,
      show Ai1 + (Ti + ti) = Ai1 + ti + Ti from by ring]
    exact htrans _ _ _ h₁ (hadd _ _ _ step)
  have main : ∀ T : Finset S,
      letI := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥(Algebra.adjoin R (↑T : Set S)))
      r (p.height + (Cardinal.toNat (Algebra.trdeg R ↥(Algebra.adjoin R (↑T : Set S))) : ℕ∞))
        ((q.under ↥(Algebra.adjoin R (↑T : Set S))).height
          + (Cardinal.toNat (Algebra.trdeg p.ResidueField
              (q.under ↥(Algebra.adjoin R (↑T : Set S))).ResidueField) : ℕ∞)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      obtain ⟨hheight0, htrdeg0, hres0⟩ :=
        adjoin_eq_bot_transport hinj p q (∅ : Finset S) (by simp)
      rw [htrdeg0, hheight0, hres0]
      simpa using hrefl p.height
    | insert a T ha ih =>
      set BT := Algebra.adjoin R (↑T : Set S) with hBTdef
      set B' := Algebra.adjoin R (↑(insert a T) : Set S) with hB'def
      have hle : BT ≤ B' := Algebra.adjoin_mono (Finset.coe_subset.mpr (Finset.subset_insert a T))
      let : Algebra (↥BT) (↥B') := (Subalgebra.inclusion hle).toAlgebra
      obtain ⟨htowS, towR, hfRBT, hfBTB'⟩ := inclusion_towers hinj hle
      have hBTft : Algebra.FiniteType R (↥BT) :=
        (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T)
      have hB'ft : Algebra.FiniteType R (↥B') :=
        (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset (insert a T))
      have : IsNoetherianRing (↥BT) := Algebra.FiniteType.isNoetherianRing R _
      have : IsNoetherianRing (↥B') := Algebra.FiniteType.isNoetherianRing R _
      have hgen' : (∃ x : ↥B', Algebra.adjoin (↥BT) {x} = ⊤) :=
        adjoin_insert_isOneGenerator a T
      have hB'ftBT : Algebra.FiniteType (↥BT) (↥B') := by
        obtain ⟨x, hx⟩ := hgen'
        constructor
        rw [← hx]
        exact ⟨{x}, by rw [Finset.coe_singleton]⟩
      have hstepres := hstep (↥BT) (↥B') (Subalgebra.inclusion_injective hle) (hgood T) hgen'
        (q.under ↥BT) (q.under ↥B')
      let := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥BT)
      let := Ideal.ResidueField.algebraOfLiesOver p (q.under ↥B')
      let := Ideal.ResidueField.algebraOfLiesOver (q.under ↥BT) (q.under ↥B')
      obtain ⟨htrdegRadd, htrdegResadd⟩ := trdeg_toNat_step_add p q BT B'
        (resfield_trdeg_lt_aleph0_general (q.under ↥BT) (q.under ↥B'))
      rw [htrdegRadd, htrdegResadd]
      exact tele p.height (q.under ↥BT).height (q.under ↥B').height
        (Cardinal.toNat (Algebra.trdeg R (↥BT)) : ℕ∞)
        (Cardinal.toNat (Algebra.trdeg (↥BT) (↥B')) : ℕ∞)
        (Cardinal.toNat (Algebra.trdeg p.ResidueField (q.under ↥BT).ResidueField) : ℕ∞)
        (Cardinal.toNat (Algebra.trdeg (q.under ↥BT).ResidueField (q.under ↥B').ResidueField) : ℕ∞)
        ih hstepres
  obtain ⟨G, hG⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  have hmainG := main G
  obtain ⟨hheight, htrdegA, htresB⟩ := adjoin_eq_top_transport p q G hG
  rwa [htrdegA, hheight, htresB] at hmainG

/-- **Stacks 02IJ**, reverse inequality. For `R` Noetherian and universally catenary, `S` a
finite-type domain extension of the domain `R`, and `q` a prime of `S` lying over `p`,
`p.height + trdeg_R S ≤ q.height + trdeg_{κ(p)} κ(q)`. This is the catenary half of the
dimension formula; together with `height_add_trdeg_residue_le` it gives the equality
`height_add_trdeg_residue_eq`. -/
@[ega "IV 13.3.4" "Inequality dim O_{Y_j",
  ega "IV 5.5.6" "partial",
  ega "IV 5.5.7" "(ii)",
  ega "IV 5.5.8" "partial",
  ega "IV 5.6.5" "partial"]
theorem height_add_trdeg_residue_ge
    [IsNoetherianRing R] [Algebra.FiniteType R S] [IsDomain R] [IsDomain S]
    (hinj : Function.Injective (algebraMap R S)) (hcat : IsUniversallyCatenary R)
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI := Ideal.ResidueField.algebraOfLiesOver p q
    p.height + (Cardinal.toNat (Algebra.trdeg R S) : ℕ∞)
      ≤ q.height + (Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) : ℕ∞) := by
  have bcat : ∀ T : Finset S, IsUniversallyCatenary ↥(Algebra.adjoin R (↑T : Set S)) := fun T =>
    have := (Subalgebra.fg_iff_finiteType (Algebra.adjoin R (↑T : Set S))).mp
      (Subalgebra.fg_adjoin_finset T)
    hcat.trans
  exact dim_formula_generator_induction (· ≤ ·) (fun _ => le_rfl) (fun _ _ _ => le_trans)
    (fun _ _ _ h => add_le_add h le_rfl) IsUniversallyCatenary
    (fun A A' _ _ _ _ _ _ _ hinj' hcat' hgen' P Q _ _ _ =>
      single_generator_step hinj' hcat' hgen' P Q)
    hinj bcat p q

/-- For primes `n ≤ Q̃` of a commutative ring, with `Q` the image of `Q̃` in the quotient by `n`,
`Q.height + n.height ≤ Q̃.height`: a chain below `Q` lifts to a chain below `Q̃` of primes
containing `n`, and prepending a chain below `n` concatenates the two lengths. -/
@[ega "0 16.1.4" "special case"]
theorem height_map_quotient_add_height_le
    {B : Type u} [CommRing B] (n : Ideal B) [n.IsPrime] (Qt : Ideal B) [Qt.IsPrime]
    (hnle : n ≤ Qt) :
    (Ideal.map (Ideal.Quotient.mk n) Qt).height + n.height ≤ Qt.height := by
  have hFp : (Ideal.map (Ideal.Quotient.mk n) Qt).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hnle
  set F := Ideal.map (Ideal.Quotient.mk n) Qt with hF
  rw [PrimeSpectrum.height_eq_orderHeight ⟨F, hFp⟩,
    PrimeSpectrum.height_eq_orderHeight ⟨n, inferInstance⟩,
    PrimeSpectrum.height_eq_orderHeight ⟨Qt, inferInstance⟩]
  change Order.height (⟨F, hFp⟩ : PrimeSpectrum (B ⧸ n))
      + Order.height (⟨n, inferInstance⟩ : PrimeSpectrum B)
      ≤ Order.height (⟨Qt, inferInstance⟩ : PrimeSpectrum B)
  set Qpt : PrimeSpectrum B := ⟨Qt, inferInstance⟩ with hQpt
  set npt : PrimeSpectrum B := ⟨n, inferInstance⟩ with hnpt
  set Fpt : PrimeSpectrum (B ⧸ n) := ⟨F, hFp⟩ with hFpt
  set g := Ideal.primeSpectrumQuotientOrderIsoZeroLocus n with hg
  set φ : PrimeSpectrum (B ⧸ n) → PrimeSpectrum B := fun x => (g x : PrimeSpectrum B) with hφ
  have hφmono : StrictMono φ := fun a b hab => g.lt_iff_lt.mpr hab
  have hφF : φ Fpt = Qpt := by
    refine PrimeSpectrum.ext ?_
    change (Ideal.comap (Ideal.Quotient.mk n) F) = Qt
    rw [hF, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hnle]
  have : Nonempty (LTSeries (PrimeSpectrum (B ⧸ n))) := ⟨RelSeries.singleton _ Fpt⟩
  have : Nonempty (LTSeries (PrimeSpectrum B)) := ⟨RelSeries.singleton _ npt⟩
  have mapchain : ∀ (p : LTSeries (PrimeSpectrum (B ⧸ n))), RelSeries.last p = Fpt →
      ∃ p' : LTSeries (PrimeSpectrum B), p'.last = Qpt ∧ p'.length = p.length ∧ npt ≤ p'.head := by
    intro p hpF
    refine ⟨p.map φ hφmono, ?_, by rw [LTSeries.map_length], ?_⟩
    · rw [LTSeries.last_map, hpF, hφF]
    · rw [LTSeries.head_map]
      change npt ≤ ((g p.head : PrimeSpectrum B))
      have hmem := (g p.head).property
      rw [PrimeSpectrum.mem_zeroLocus] at hmem
      exact hmem
  have hcbound : ∀ (c : LTSeries (PrimeSpectrum B)), RelSeries.last c = npt →
      (c.length : ℕ∞) ≤ Order.height Qpt := by
    intro c hc
    have h1 : (c.length : ℕ∞) ≤ Order.height c.last := Order.length_le_height_last
    rw [hc] at h1
    exact h1.trans (Order.height_mono (by exact hnle))
  have hpbound : ∀ (p : LTSeries (PrimeSpectrum (B ⧸ n))), RelSeries.last p = Fpt →
      (p.length : ℕ∞) ≤ Order.height Qpt := by
    intro p hpF
    obtain ⟨p', hl, hlen, _⟩ := mapchain p hpF
    rw [← hlen, ← hl]
    exact Order.length_le_height_last
  rw [Order.height_eq_iSup_last_eq Fpt, Order.height_eq_iSup_last_eq npt]
  apply ENat.iSup_add_iSup_le
  intro p c
  rcases Classical.em (RelSeries.last p = Fpt) with hpF | hpF
  · rcases Classical.em (RelSeries.last c = npt) with hcn | hcn
    · rw [ciSup_pos hpF, ciSup_pos hcn]
      obtain ⟨p', hp'last, hp'len, hp'head⟩ := mapchain p hpF
      by_cases heq : c.last = p'.head
      · have hslen := RelSeries.smash_length c p' heq
        have hle := Order.length_le_height_last (p := c.smash p' heq)
        rw [RelSeries.last_smash, hp'last] at hle
        calc (p.length : ℕ∞) + (c.length : ℕ∞)
            = (((c.smash p' heq).length : ℕ) : ℕ∞) := by rw [hslen, hp'len]; push_cast; ring
          _ ≤ Order.height Qpt := hle
      · have hlt : c.last < p'.head := lt_of_le_of_ne (hcn ▸ hp'head) heq
        have hslen := RelSeries.append_length c p' hlt
        have hle := Order.length_le_height_last (p := c.append p' hlt)
        rw [RelSeries.last_append, hp'last] at hle
        calc (p.length : ℕ∞) + (c.length : ℕ∞)
            ≤ (((c.append p' hlt).length : ℕ) : ℕ∞) := by
              rw [hslen, hp'len]; exact_mod_cast by omega
          _ ≤ Order.height Qpt := hle
    · rw [ciSup_pos hpF, (iSup_neg hcn : (⨆ (_ : RelSeries.last c = npt), (c.length:ℕ∞)) = ⊥)]
      simpa using hpbound p hpF
  · rw [(iSup_neg hpF : (⨆ (_ : RelSeries.last p = Fpt), (p.length:ℕ∞)) = ⊥)]
    rcases Classical.em (RelSeries.last c = npt) with hcn | hcn
    · rw [ciSup_pos hcn]; simpa using hcbound c hcn
    · rw [(iSup_neg hcn : (⨆ (_ : RelSeries.last c = npt), (c.length:ℕ∞)) = ⊥)]; simp

/-- For `Ft` a prime of `D[X]`, `D` a domain, contracting to `(0)` in `D`, one has
`Ft.height + trdeg_D (D[X] ⧸ Ft) ≤ 1`, with equality: either `Ft = (0)`, of height zero with
quotient `D[X]` of transcendence degree one, or `Ft` has height one and algebraic quotient. -/
@[ega "IV 5.5.6" "partial"]
theorem affine_line_height_add_trdeg_le {D : Type u} [CommRing D] [IsDomain D]
    (Ft : Ideal (Polynomial D)) [Ft.IsPrime]
    (hcap : Ideal.comap (algebraMap D (Polynomial D)) Ft = ⊥) :
    Ft.height + (Cardinal.toNat (Algebra.trdeg D (Polynomial D ⧸ Ft)) : ℕ∞) ≤ 1 := by
  by_cases hbot : Ft = ⊥
  · subst hbot
    rw [Ideal.height_bot, zero_add]
    have hq : Algebra.trdeg D (Polynomial D ⧸ (⊥ : Ideal (Polynomial D)))
        = Algebra.trdeg D (Polynomial D) :=
      AlgEquiv.trdeg_eq
        ((Ideal.quotientEquivAlgOfEq D (rfl : (⊥ : Ideal (Polynomial D)) = ⊥)).trans
          (AlgEquiv.quotientBot D (Polynomial D)))
    rw [hq, Polynomial.trdeg_of_isDomain]
    simp
  · have h1 : Ft.height = 1 := height_one_of_comap_bot Ft hbot hcap
    have h0 : Algebra.trdeg D (Polynomial D ⧸ Ft) = 0 := trdeg_alg_quot_eq_zero Ft h1
    rw [h1, h0]; simp

/-- Transporting the fibre prime `F` of `A[X] ⧸ P·A[X]` across a polynomial-quotient isomorphism
`e : (A ⧸ P)[X] ≃+* A[X] ⧸ P·A[X]` compatible with the constants (`hekey`) identifies the
transcendence degrees over `A ⧸ P`,
`trdeg_{A ⧸ P} (A[X] ⧸ Q) = trdeg_{A ⧸ P} ((A ⧸ P)[X] ⧸ comap e F)`: the third isomorphism
theorem turns `(A ⧸ P)[X] ⧸ comap e F` into `A[X] ⧸ Q` as an `A ⧸ P`-algebra. -/
theorem polyquot_trdeg_eq {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) (Q : Ideal (Polynomial A)) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P]
    (hPtilde_le : Ideal.map (algebraMap A (Polynomial A)) P ≤ Q)
    (F : Ideal (Polynomial A ⧸ Ideal.map (algebraMap A (Polynomial A)) P))
    (hF : F = Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial A)) P)) Q)
    (e : Polynomial (A ⧸ P) ≃+* (Polynomial A ⧸ Ideal.map (algebraMap A (Polynomial A)) P))
    (hekey : ∀ a : A, (e : Polynomial (A ⧸ P) →+* _) (Polynomial.C ((Ideal.Quotient.mk P) a))
      = (Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial A)) P)) (Polynomial.C a)) :
    Algebra.trdeg (A ⧸ P) (Polynomial A ⧸ Q)
      = Algebra.trdeg (A ⧸ P) (Polynomial (A ⧸ P) ⧸ Ideal.comap (e : Polynomial (A ⧸ P) →+* _)
          F) := by
  have hFeq : F = Ideal.map (e : Polynomial (A ⧸ P) →+* _) (Ideal.comap (e : Polynomial (A ⧸ P) →+*
      _) F) :=
    (Ideal.map_comap_of_surjective _ (EquivLike.surjective e) F).symm
  have hφval : ∀ a : A,
      ((Ideal.quotientEquiv _ F e hFeq).trans
          ((Ideal.quotEquivOfEq hF).trans (DoubleQuot.quotQuotEquivQuotOfLE hPtilde_le)))
        ((Ideal.Quotient.mk (Ideal.comap (e : Polynomial (A ⧸ P) →+* _) F)) (Polynomial.C
            ((Ideal.Quotient.mk P) a)))
      = (Ideal.Quotient.mk Q) (Polynomial.C a) := by
    intro a
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
      Ideal.quotEquivOfEq_mk]
    rw [show (e (Polynomial.C ((Ideal.Quotient.mk P) a)))
          = (e : Polynomial (A ⧸ P) →+* _) (Polynomial.C ((Ideal.Quotient.mk P) a)) from rfl, hekey
              a]
    rw [show (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial
        A)) P)) Q))
            ((Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial A)) P)) (Polynomial.C a))
          = DoubleQuot.quotQuotMk (Ideal.map (algebraMap A (Polynomial A)) P) Q (Polynomial.C a)
        from rfl,
      DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk]
  let φalg : (Polynomial (A ⧸ P) ⧸ Ideal.comap (e : Polynomial (A ⧸ P) →+* _) F) ≃ₐ[A ⧸ P]
      (Polynomial A ⧸ Q) :=
    AlgEquiv.ofRingEquiv
      (f := (Ideal.quotientEquiv _ F e hFeq).trans
          ((Ideal.quotEquivOfEq hF).trans (DoubleQuot.quotQuotEquivQuotOfLE hPtilde_le)))
      (fun x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact hφval a)
  exact (AlgEquiv.trdeg_eq φalg).symm

/-- The reverse dimension-formula inequality for the polynomial extension `A ⊆ A[X]`:
`Q.height + trdeg_{κ(P)} κ(Q) ≤ P.height + trdeg_A A[X]`. Flatness of `A ⊆ A[X]` splits the
height of `Q` as `P.height + F.height` for `F` the fibre prime, and the affine-line formula
bounds `F.height + trdeg_{κ(P)} κ(Q)` by `1 = trdeg_A A[X]`. -/
private theorem single_generator_step_poly_le {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsDomain A]
    (P : Ideal A) (Q : Ideal (Polynomial A)) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    Q.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞)
      ≤ P.height + (Cardinal.toNat (Algebra.trdeg A (Polynomial A)) : ℕ∞) := by
  rw [Polynomial.trdeg_of_isDomain, map_one, Nat.cast_one]
  let := Ideal.ResidueField.algebraOfLiesOver P Q
  set F : Ideal (Polynomial A ⧸ Ideal.map (algebraMap A (Polynomial A)) P) :=
    Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial A)) P)) Q with hF
  have hQh : Q.height = P.height + F.height :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P Q
  set t : ℕ∞ := (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) with ht
  rw [hQh, add_assoc]
  gcongr P.height + ?_
  have hPtilde_le : Ideal.map (algebraMap A (Polynomial A)) P ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over (p := P) (P := Q))
  have hdomB : IsDomain (Polynomial A ⧸ Ideal.map (algebraMap A (Polynomial A)) P) := by
    rw [Polynomial.algebraMap_eq]
    exact Ideal.isDomain_map_C_quotient inferInstance
  have hFprime : F.IsPrime := by
    rw [hF]
    exact Ideal.isPrime_map_quotientMk_of_isPrime hPtilde_le
  have hmapeq : Ideal.map (algebraMap A (Polynomial A)) P = Ideal.map Polynomial.C P := by
    rw [Polynomial.algebraMap_eq]
  set e : Polynomial (A ⧸ P) ≃+* (Polynomial A ⧸ Ideal.map (algebraMap A (Polynomial A)) P) :=
    (Ideal.polynomialQuotientEquivQuotientPolynomial P).trans
      (Ideal.quotientEquiv (Ideal.map Polynomial.C P)
        (Ideal.map (algebraMap A (Polynomial A)) P) (RingEquiv.refl _) (by
          rw [RingEquiv.toRingHom_refl, Ideal.map_id]; exact hmapeq.symm)) with he
  set Ft : Ideal (Polynomial (A ⧸ P)) := Ideal.comap (e : Polynomial (A ⧸ P) →+* _) F with hFt
  have hFtprime : Ft.IsPrime := Ideal.comap_isPrime _ _
  have hekey : ∀ a : A, (e : Polynomial (A ⧸ P) →+* _) (Polynomial.C ((Ideal.Quotient.mk P) a))
      = (Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial A)) P)) (Polynomial.C a) := by
    intro a
    have hee : (e : Polynomial (A ⧸ P) →+* _) (Polynomial.C ((Ideal.Quotient.mk P) a))
        = e (Polynomial.C ((Ideal.Quotient.mk P) a)) := rfl
    rw [hee, he, RingEquiv.trans_apply, ← Polynomial.map_C (Ideal.Quotient.mk P),
        Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk,
        Ideal.quotientEquiv_mk]
    rfl
  have hcap : Ideal.comap (algebraMap (A ⧸ P) (Polynomial (A ⧸ P))) Ft = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_comap] at hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hxC : (e : Polynomial (A ⧸ P) →+* _) (Polynomial.C ((Ideal.Quotient.mk P) a)) ∈ F := by
      have h1 : (algebraMap (A ⧸ P) (Polynomial (A ⧸ P))) ((Ideal.Quotient.mk P) a)
          = Polynomial.C ((Ideal.Quotient.mk P) a) := by rw [Polynomial.algebraMap_eq]
      rwa [hFt, Ideal.mem_comap, h1] at hx
    rw [hekey a, hF, Ideal.mem_quotient_iff_mem hPtilde_le] at hxC
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    have ha : a ∈ Ideal.comap (algebraMap A (Polynomial A)) Q := by
      rw [Ideal.mem_comap, Polynomial.algebraMap_eq]; exact hxC
    have hover : P = Ideal.comap (algebraMap A (Polynomial A)) Q := by
      have hov := Ideal.LiesOver.over (p := P) (P := Q)
      rwa [Ideal.under_def] at hov
    rw [hover]; exact ha
  have hheight : F.height = Ft.height := (height_comap_ringEquiv e F).symm
  have htrdeg : t = (Cardinal.toNat (Algebra.trdeg (A ⧸ P) (Polynomial (A ⧸ P) ⧸ Ft)) : ℕ∞) := by
    rw [ht, resfield_trdeg_eq_quot_trdeg P Q, hFt, polyquot_trdeg_eq P Q hPtilde_le F hF e hekey]
  rw [hheight, htrdeg]
  exact affine_line_height_add_trdeg_le Ft hcap

-- the `simp` below needs to unfold the `Localization.AtPrime` residue-field
-- abbreviations the statement is phrased at.
set_option backward.isDefEq.respectTransparency false in
/-- The reverse dimension-formula inequality for `A ⊆ A[X] ⧸ n` with `n` a height-one prime of
`A[X]` meeting `A` in `(0)`: `Q.height + trdeg_{κ(P)} κ(Q) ≤ P.height + trdeg_A (A[X] ⧸ n)`.
Unlike the forward direction it needs no catenarity hypothesis, since only the unconditional
inequality `Q.height + n.height ≤ (comap (mk n) Q).height` is used. -/
private theorem single_generator_step_alg_le {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsDomain A]
    (n : Ideal (Polynomial A)) [n.IsPrime] (hn1 : n.height = 1)
    (P : Ideal A) (Q : Ideal ((Polynomial A) ⧸ n))
    [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    Q.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞)
      ≤ P.height + (Cardinal.toNat (Algebra.trdeg A ((Polynomial A) ⧸ n)) : ℕ∞) := by
  let := Ideal.ResidueField.algebraOfLiesOver P Q
  have hQtLO : (Ideal.comap (Ideal.Quotient.mk n) Q).LiesOver P := by
    constructor
    have h := Ideal.LiesOver.over (p := P) (P := Q)
    rw [h, Ideal.under_def, Ideal.under_def, Ideal.comap_comap]; rfl
  have htreq := resfield_trdeg_comap_eq (A := A) (Ideal.Quotient.mk n)
    Ideal.Quotient.mk_surjective rfl P Q
  set Qt : Ideal (Polynomial A) := Ideal.comap (Ideal.Quotient.mk n) Q with hQt
  have hnle : n ≤ Qt := by
    intro x hx
    rw [hQt, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Q.zero_mem
  have hmapQt : Ideal.map (Ideal.Quotient.mk n) Qt = Q := by
    rw [hQt, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hadd := height_map_quotient_add_height_le n Qt hnle
  rw [hmapQt, hn1] at hadd
  have htr0 : Algebra.trdeg A ((Polynomial A) ⧸ n) = 0 := trdeg_alg_quot_eq_zero n hn1
  rw [htr0, map_zero, Nat.cast_zero, add_zero]
  have hpoly := single_generator_step_poly_le P Qt
  rw [Polynomial.trdeg_of_isDomain, map_one, htreq, Nat.cast_one] at hpoly
  refine (WithTop.add_le_add_iff_right (z := (1 : ℕ∞)) (by simp)).mp ?_
  calc Q.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) + 1
      = (Q.height + 1) + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) := by
        abel
    _ ≤ Qt.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) := by
        gcongr
    _ ≤ P.height + 1 := hpoly

/-- The reverse dimension-formula inequality for a one-generator extension `A ⊆ A'` of domains
with `A` Noetherian: `Q.height + trdeg_{κ(P)} κ(Q) ≤ P.height + trdeg_A A'`. No catenarity
hypothesis is needed. -/
private theorem single_generator_step_le
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [Algebra A A']
    [IsNoetherianRing A] [Algebra.FiniteType A A'] [IsDomain A] [IsDomain A']
    (hinj : Function.Injective (algebraMap A A'))
    (hgen : ∃ x : A', Algebra.adjoin A {x} = ⊤)
    (P : Ideal A) (Q : Ideal A') [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    Q.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞)
      ≤ P.height + (Cardinal.toNat (Algebra.trdeg A A') : ℕ∞) := by
  obtain ⟨x, htop⟩ := hgen
  have hsurj : Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] A') := by
    rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  set n : Ideal (Polynomial A) :=
    RingHom.ker (Polynomial.aeval x : Polynomial A →ₐ[A] A').toRingHom with hn
  let e : (Polynomial A ⧸ n) ≃ₐ[A] A' := Ideal.quotientKerAlgEquivOfSurjective hsurj
  have hnp : n.IsPrime := RingHom.ker_isPrime _
  have hncap : Ideal.comap (algebraMap A (Polynomial A)) n = ⊥ := by
    rw [hn]; ext a
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    constructor
    · intro h
      have hcc : (Polynomial.aeval x : Polynomial A →ₐ[A] A').toRingHom
            (algebraMap A (Polynomial A) a) = algebraMap A A' a := by
        rw [Polynomial.algebraMap_eq]; simp [Polynomial.aeval_C]
      rw [hcc] at h
      exact hinj (by rw [h, map_zero])
    · rintro rfl; simp
  set Q'' : Ideal (Polynomial A ⧸ n) := Ideal.comap (e : (Polynomial A ⧸ n) →+* A') Q with hQ''
  have hQ''p : Q''.IsPrime := Ideal.comap_isPrime (e : (Polynomial A ⧸ n) →+* A') Q
  have hcompmap : (e : (Polynomial A ⧸ n) →+* A').comp (algebraMap A (Polynomial A ⧸ n))
      = algebraMap A A' := by ext a; exact e.commutes a
  have hQ''LO : Q''.LiesOver P := Ideal.LiesOver.of_eq_comap P e rfl
  have hheight : Q.height = Q''.height :=
    (height_comap_ringEquiv (e : (Polynomial A ⧸ n) ≃+* A') Q).symm
  let := Ideal.ResidueField.algebraOfLiesOver P Q
  let := Ideal.ResidueField.algebraOfLiesOver P Q''
  have htrdegA : Cardinal.toNat (Algebra.trdeg A A') =
      Cardinal.toNat (Algebra.trdeg A (Polynomial A ⧸ n)) := by
    simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat e.lift_trdeg_eq.symm
  have htres := congrArg Cardinal.toNat
    (resfield_lift_trdeg_comap_eq (e : (Polynomial A ⧸ n) →+* A')
      e.surjective hcompmap P Q)
  simp only [Cardinal.toNat_lift] at htres
  rw [htrdegA, hheight, ← htres]
  by_cases hnbot : n = ⊥
  · let e3 : Polynomial A ≃ₐ[A] (Polynomial A ⧸ n) :=
      (AlgEquiv.quotientBot A (Polynomial A)).symm.trans (Ideal.quotientEquivAlgOfEq A hnbot).symm
    set Q''' : Ideal (Polynomial A) :=
      Ideal.comap (e3 : Polynomial A →+* (Polynomial A ⧸ n)) Q'' with hQ'''
    have hQ'''p : Q'''.IsPrime :=
      Ideal.comap_isPrime (e3 : Polynomial A →+* (Polynomial A ⧸ n)) Q''
    have hQ'''LO : Q'''.LiesOver P := Ideal.LiesOver.of_eq_comap P e3 rfl
    have hheight3 : Q''.height = Q'''.height :=
      (height_comap_ringEquiv (e3 : Polynomial A ≃+* (Polynomial A ⧸ n)) Q'').symm
    have htrdegA3 : Algebra.trdeg A (Polynomial A ⧸ n) = Algebra.trdeg A (Polynomial A) :=
      (AlgEquiv.trdeg_eq e3).symm
    have htres3 := resfield_trdeg_algEquiv_eq e3 P Q''
    rw [htrdegA3, hheight3, ← htres3]
    exact single_generator_step_poly_le P Q'''
  · have hn1 : n.height = 1 := height_one_of_comap_bot n hnbot hncap
    exact single_generator_step_alg_le n hn1 P Q''

/-- **Stacks 02IJ**.
For `R` Noetherian, `S` a finite-type domain extension of the domain `R`, and `q` a prime of `S`
lying over `p`, `q.height + trdeg_{κ(p)} κ(q) ≤ p.height + trdeg_R S`. -/
@[stacks 02IJ,
  ega "IV 13.3.4" "partial",
  ega "IV 5.5.6" "partial",
  ega "IV 5.5.7" "more general",
  ega "IV 5.5.8" "more general",
  ega "IV 5.6.5" "special case"]
theorem height_add_trdeg_residue_le
    [IsNoetherianRing R] [Algebra.FiniteType R S] [IsDomain R] [IsDomain S]
    (hinj : Function.Injective (algebraMap R S))
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI := Ideal.ResidueField.algebraOfLiesOver p q
    q.height + (Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) : ℕ∞)
      ≤ p.height + (Cardinal.toNat (Algebra.trdeg R S) : ℕ∞) :=
  dim_formula_generator_induction (· ≥ ·) (fun _ => le_rfl)
    (fun _ _ _ h₁ h₂ => le_trans h₂ h₁) (fun _ _ _ h => add_le_add h le_rfl) (fun _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ hinj' _ hgen' P Q _ _ _ => single_generator_step_le hinj' hgen' P Q)
    hinj (fun _ => trivial) p q

/-- **Stacks 02IJ**.
If in addition `R` is universally catenary, the dimension formula is an equality:
`q.height + trdeg_{κ(p)} κ(q) = p.height + trdeg_R S`. -/
@[stacks 02IJ,
  ega "IV 13.3.4" "special case",
  ega "IV 5.5.6" "special case",
  ega "IV 5.5.7" "special case",
  ega "IV 5.6.5" "partial"]
theorem height_add_trdeg_residue_eq
    [IsNoetherianRing R] [Algebra.FiniteType R S] [IsDomain R] [IsDomain S]
    (hinj : Function.Injective (algebraMap R S)) (hcat : IsUniversallyCatenary R)
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI := Ideal.ResidueField.algebraOfLiesOver p q
    q.height + (Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) : ℕ∞)
      = p.height + (Cardinal.toNat (Algebra.trdeg R S) : ℕ∞) := by
  let := Ideal.ResidueField.algebraOfLiesOver p q
  exact le_antisymm
    (height_add_trdeg_residue_le hinj p q)
    (height_add_trdeg_residue_ge hinj hcat p q)

end
