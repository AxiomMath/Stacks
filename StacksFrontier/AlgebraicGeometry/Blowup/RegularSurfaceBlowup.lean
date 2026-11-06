module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.RingTheory.Koszul.Blowup
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# The blowup of a regular local surface at its closed point

Let `(A, 𝔪, κ)` be a regular local ring of dimension two and let `X → Spec A` be the blowup of
`Spec A` in its closed point. Then `X` is an irreducible regular scheme.

Irreducibility is integrality of the blowup of an integral scheme in a nonzero ideal, a regular
local ring being a domain. Regularity is checked on the standard affine charts: `𝔪` is generated
by two elements `x, y`, which form a regular sequence, so the two charts `Spec A[𝔪/x]` and
`Spec A[𝔪/y]` already cover `X`, and it suffices to see that `A[𝔪/x]` is a regular ring. The
regular sequence presents that chart as `A[T]/(xT - y)`, whence `A[𝔪/x]/x A[𝔪/x] ≅ κ[T]`: at a
prime of the chart containing `x` the chart is therefore the quotient of a regular local ring by
a nonzerodivisor, and at a prime not containing `x` the chart is a localization of `A` itself,
`x` being invertible there.

## Main results

* `AlgebraicGeometry.irreducibleSpace_blowUp_maximalIdeal`: the blowup is irreducible.
* `AlgebraicGeometry.isRegular_blowUp_maximalIdeal`: the blowup is regular.

## Implementation notes

The centre is the ideal sheaf generated over the whole space by the image of the maximal ideal
under the canonical identification `Γ(Spec A, ⊤) ≅ A`, which is the spelling the library already
uses for this blowup. Two dimensions are what makes the maximal ideal nonzero; over a field the
blowup in the zero ideal is empty.

Regularity of a scheme is `AlgebraicGeometry.IsRegular`, the existence at every point of an
affine open neighbourhood with regular ring of sections (Stacks tag 02IS). Since Mathlib's
`IsRegularRing` contains the Noetherian condition, no separate local Noetherian hypothesis
appears, and the charts give the required neighbourhoods directly: a chart is an open immersion,
so the ring of sections of its image is the affine blowup algebra. The charts are
`AlgebraicGeometry.blowupChartι`, attached to the two generators of the maximal ideal, and they
cover the blowup by `AlgebraicGeometry.exists_mem_range_blowupChartι`.

The regularity of the chart is deduced from `Stacks.Blowup.isRegularRing_of_quotient_away`, which
isolates the shape of the argument: a Noetherian domain `B` containing a regular ring `R`, in
which every element becomes a multiple of an element of `R` after multiplying by a power of
`x ∈ R`, is regular as soon as `B / xB` is regular.

The presentation of the affine blowup algebra of a regular sequence as a polynomial algebra
modulo the relations `x Tᵢ - yᵢ` is
`Koszul.exists_affineBlowup_algEquiv_mvPolynomial_quotient_of_isH1Regular`, and the passage from
a regular local ring to a regular sequence generating its maximal ideal is Stacks tag 00NQ. The
statement that a regular local ring is a regular ring, used at the primes of the chart where `x`
is invertible, is the third item of `IsLocalRing.isRegularRing_tfae`.

## References

* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite IsLocalRing

universe u

namespace Stacks.Blowup

/-! ### Polynomial rings over a residue field -/

/-- Reducing the coefficients of a polynomial modulo an ideal kills exactly the polynomials all
of whose coefficients lie in that ideal. -/
private lemma ker_mvPolynomialMap {R : Type u} [CommRing R] (I : Ideal R) (ι : Type*) :
    RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) :
        MvPolynomial ι R →+* MvPolynomial ι (R ⧸ I)) =
      Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R) I := by
  ext p
  simp only [RingHom.mem_ker, MvPolynomial.mem_map_C_iff, MvPolynomial.ext_iff,
    MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The fibre of a polynomial ring over a maximal ideal of the coefficient ring is a polynomial
ring over a field, hence a regular ring. -/
private lemma isRegularRing_quotient_map_C {R : Type u} [CommRing R] (I : Ideal R) [I.IsMaximal]
    (ι : Type*) [Finite ι] :
    IsRegularRing (MvPolynomial ι R ⧸ Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R) I) := by
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  have e := RingHom.quotientKerEquivOfSurjective
    (f := (MvPolynomial.map (Ideal.Quotient.mk I) :
      MvPolynomial ι R →+* MvPolynomial ι (R ⧸ I)))
    (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  exact IsRegularRing.of_ringEquiv
    ((Ideal.quotEquivOfEq (ker_mvPolynomialMap I ι).symm).trans e).symm

/-! ### Localizing a quotient -/

/-- Let `J ⊆ q` be ideals of `B` with `q` prime. The quotient of a localization of `B` at `q` by
the ideal generated by `J` is a localization of `B ⧸ J` at the prime `q / J`; hence it is a
regular local ring as soon as `B ⧸ J` is a regular ring. -/
private lemma isRegularLocalRing_quotient_map {B : Type u} [CommRing B] (J : Ideal B)
    (q : Ideal B) [q.IsPrime] (hJq : J ≤ q) [IsRegularRing (B ⧸ J)]
    (S : Type u) [CommRing S] [Algebra B S] [IsLocalization.AtPrime S q] :
    IsRegularLocalRing (S ⧸ Ideal.map (algebraMap B S) J) := by
  have : (Ideal.map (Ideal.Quotient.mk J) q).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hJq
  have hcomap : Ideal.comap (Ideal.Quotient.mk J) (Ideal.map (Ideal.Quotient.mk J) q) = q :=
    Ideal.comap_map_mk hJq
  have hT : Submonoid.map (Ideal.Quotient.mk J) q.primeCompl =
      (Ideal.map (Ideal.Quotient.mk J) q).primeCompl := by
    ext d
    simp only [Submonoid.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩ hd
      exact hb (hcomap.le hd)
    · intro hd
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
      exact ⟨b, fun hb => hd (Ideal.mem_map_of_mem _ hb), rfl⟩
  have hle : q.primeCompl ≤
      Submonoid.comap (Ideal.Quotient.mk J) (Ideal.map (Ideal.Quotient.mk J) q).primeCompl := by
    intro s hs hmem
    exact hs (hcomap.le hmem)
  let ψ : S →+* Localization.AtPrime (Ideal.map (Ideal.Quotient.mk J) q) :=
    IsLocalization.map (M := q.primeCompl) (S := S)
      (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk J) q)) (Ideal.Quotient.mk J) hle
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨d, u⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Ideal.map (Ideal.Quotient.mk J) q).primeCompl z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
    have hcq : c ∈ q.primeCompl := fun hcq' => u.2 (hc ▸ Ideal.mem_map_of_mem _ hcq')
    refine ⟨IsLocalization.mk' (M := q.primeCompl) S b ⟨c, hcq⟩, ?_⟩
    rw [IsLocalization.map_mk']
    exact IsLocalization.mk'_eq_of_eq' (by simp [hc])
  have hker : RingHom.ker ψ = Ideal.map (algebraMap B S) J :=
    (IsLocalization.ker_map (M := q.primeCompl) (S := S)
      (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk J) q)) (Ideal.Quotient.mk J) hT).trans
      (by rw [Ideal.mk_ker])
  have : IsRegularLocalRing (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk J) q)) :=
    IsRegularRing.isRegularLocalRing_localization _
  exact IsRegularLocalRing.of_ringEquiv
    ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).symm

/-! ### A criterion for regularity of a ring -/

/-- **A regularity criterion for an algebra obtained by inverting one element partially.** Let
`R` be a regular ring, let `B` be a Noetherian domain containing `R`, and let `x ∈ R` be nonzero
and such that every element of `B` becomes the image of an element of `R` after multiplication
by a power of `x`. If `B / xB` is a regular ring, then so is `B`.

At a prime of `B` containing `x` the local ring is the quotient of a regular local ring of
`B / xB` by the nonzerodivisor `x`, so Stacks tag 00NU applies; at a prime not containing `x`
the local ring is a localization of `R`. -/
theorem isRegularRing_of_quotient_away {R : Type u} [CommRing R] [IsRegularRing R]
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) (x : R) (hx : x ≠ 0)
    (hfrac : ∀ b : B, ∃ (n : ℕ) (a : R), b * algebraMap R B x ^ n = algebraMap R B a)
    [IsRegularRing (B ⧸ Ideal.span ({algebraMap R B x} : Set B))] :
    IsRegularRing B := by
  rw [isRegularRing_iff]
  intro q hq
  have hqnzd : q.primeCompl ≤ nonZeroDivisors B :=
    fun s hs => mem_nonZeroDivisors_of_ne_zero fun h => hs (h ▸ q.zero_mem)
  have : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime q) hqnzd
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  by_cases hmem : algebraMap R B x ∈ q
  · -- `x` vanishes at `q`: cut by the local equation of the exceptional divisor.
    have hJq : Ideal.span ({algebraMap R B x} : Set B) ≤ q := by
      rwa [Ideal.span_le, Set.singleton_subset_iff]
    have h := isRegularLocalRing_quotient_map
      (Ideal.span ({algebraMap R B x} : Set B)) q hJq (Localization.AtPrime q)
    rw [Ideal.map_span, Set.image_singleton] at h
    refine isRegularLocalRing_of_nonZeroDivisor (Localization.AtPrime q)
      (algebraMap B (Localization.AtPrime q) (algebraMap R B x)) ?_ h
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hx (hinj ?_)
    rw [map_zero]
    exact IsLocalization.injective (Localization.AtPrime q) hqnzd (by simpa using h0)
  · -- `x` is invertible at `q`: the local ring is a localization of `R`.
    let : Algebra R (Localization.AtPrime q) :=
      ((algebraMap B (Localization.AtPrime q)).comp (algebraMap R B)).toAlgebra
    have halg : ∀ r : R, algebraMap R (Localization.AtPrime q) r =
        algebraMap B (Localization.AtPrime q) (algebraMap R B r) := fun _ => rfl
    have : (Ideal.comap (algebraMap R B) q).IsPrime := Ideal.comap_isPrime _ _
    have hxp : x ∈ (Ideal.comap (algebraMap R B) q).primeCompl := hmem
    have : IsLocalization.AtPrime (Localization.AtPrime q)
        (Ideal.comap (algebraMap R B) q) := by
      refine ⟨⟨fun s => ?_, fun z => ?_, fun {r r'} h => ⟨1, ?_⟩⟩⟩
      · rw [halg]
        exact IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q)
          ⟨algebraMap R B (s : R), fun hs => s.2 hs⟩
      · obtain ⟨⟨b, u⟩, hbu⟩ := IsLocalization.surj q.primeCompl z
        obtain ⟨n, a, hb⟩ := hfrac b
        obtain ⟨k, c, hc⟩ := hfrac (u : B)
        have hcp : c ∈ (Ideal.comap (algebraMap R B) q).primeCompl := by
          intro hcq
          have hcq' : algebraMap R B c ∈ q := hcq
          rw [← hc] at hcq'
          rcases hq.mem_or_mem hcq' with h' | h'
          · exact u.2 h'
          · exact hmem (hq.mem_of_pow_mem _ h')
        refine ⟨⟨a * x ^ k, ⟨c * x ^ n, mul_mem hcp (pow_mem hxp n)⟩⟩, ?_⟩
        have hXu : algebraMap R B (c * x ^ n) = (u : B) * algebraMap R B x ^ (k + n) := by
          rw [map_mul, map_pow, ← hc, pow_add]
          ring
        have hXb : algebraMap R B (a * x ^ k) = b * algebraMap R B x ^ (n + k) := by
          rw [map_mul, map_pow, ← hb, pow_add]
          ring
        show z * algebraMap R (Localization.AtPrime q) (c * x ^ n) =
          algebraMap R (Localization.AtPrime q) (a * x ^ k)
        rw [halg, halg, hXu, hXb, map_mul, map_mul, map_pow, map_pow, ← hbu]
        ring
      · rw [hinj (IsLocalization.injective (Localization.AtPrime q) hqnzd h)]
    exact IsRegularRing.isRegularLocalRing_of_isLocalization
      (Ideal.comap (algebraMap R B) q) (Localization.AtPrime q)

/-! ### The affine blowup charts of a regular local surface -/

/-- The two models of the affine blowup algebra inside the localization away from the denominator
are the same subalgebra. -/
private lemma affineBlowupAlgebra_eq_away {R : Type u} [CommRing R] (I : Ideal R) (a : R) :
    affineBlowupAlgebra I a (Localization.Away a) = affineBlowupAlgebraAway I a := by
  unfold affineBlowupAlgebra affineBlowupAlgebraAway
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  all_goals
    rintro ⟨g, hg, rfl⟩
    refine ⟨g, hg, ?_⟩
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    simp [IsLocalization.Away.invSelf, mul_comm]

/-- The range of a two-element family. -/
private lemma range_pair {R : Type u} (x y : R) :
    Set.range (Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) = {x, y} := by
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.cases (Or.inl rfl) (fun _ => Or.inr rfl) i
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The maximal ideal of a two-dimensional regular local ring needs exactly two generators. -/
private lemma spanFinrank_maximalIdeal_eq_two {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) : (maximalIdeal R).spanFinrank = 2 := by
  have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hdim] at h
  exact_mod_cast h

section Chart

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (x y : R)

/-- The affine blowup algebra of the maximal ideal is a domain, the ambient localization away
from a nonzero element of a regular local ring being one. -/
private lemma isDomain_affineBlowupAlgebraAway (hx : x ≠ 0) :
    IsDomain (affineBlowupAlgebraAway (maximalIdeal R) x) := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have : IsDomain (Localization.Away x) := IsLocalization.isDomain_of_le_nonZeroDivisors
    (Localization.Away x) (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  infer_instance

/-- The ring of the affine blowup chart sits inside the localization away from the denominator,
so the structure map into it is injective. -/
private lemma injective_algebraMap_affineBlowupAlgebraAway (hx : x ≠ 0) :
    Function.Injective (algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x)) := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  intro r r' h
  exact IsLocalization.injective (Localization.Away x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx) (congrArg Subtype.val h)

/-- Every element of the affine blowup chart becomes the image of an element of the base after
multiplication by a power of the denominator. -/
private lemma exists_mul_pow_eq_algebraMap (hx : x ∈ maximalIdeal R) :
    ∀ b : affineBlowupAlgebraAway (maximalIdeal R) x, ∃ (n : ℕ) (a : R),
      b * algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x ^ n =
        algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) a := by
  have hinv : IsLocalization.Away.invSelf x * algebraMap R (Localization.Away x) x = 1 :=
    (mul_comm _ _).trans (IsLocalization.Away.mul_invSelf x)
  intro b
  obtain ⟨n, a, -, hb⟩ := (mem_affineBlowup_iff (maximalIdeal R) x hx).mp b.2
  refine ⟨n, a, Subtype.ext ?_⟩
  have hcoe : ((b * algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x ^ n :
        affineBlowupAlgebraAway (maximalIdeal R) x) : Localization.Away x) =
      (b : Localization.Away x) * algebraMap R (Localization.Away x) x ^ n := by
    push_cast
    rfl
  rw [hcoe, hb]
  calc IsLocalization.Away.invSelf x ^ n * algebraMap R (Localization.Away x) a *
        algebraMap R (Localization.Away x) x ^ n
      = (IsLocalization.Away.invSelf x * algebraMap R (Localization.Away x) x) ^ n *
          algebraMap R (Localization.Away x) a := by
        rw [mul_pow]
        ring
    _ = algebraMap R (Localization.Away x) a := by rw [hinv, one_pow, one_mul]

omit [IsRegularLocalRing R] in
/-- A regular sequence of two elements is `H₁`-regular as a family. -/
private lemma isH1Regular_pair (hreg : RingTheory.Sequence.IsRegular R [x, y]) :
    Koszul.IsH1Regular (Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) := by
  have hlist : List.ofFn (Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) = [x, y] := by
    simp [List.ofFn_succ]
  exact ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := R)).2.2
    (by rwa [hlist])).isH1Regular

omit [IsRegularLocalRing R] in
/-- The presentation of the affine blowup algebra of a two-element regular sequence. -/
private lemma exists_chart_algEquiv_raw (hreg : RingTheory.Sequence.IsRegular R [x, y]) :
    Nonempty (affineBlowupAlgebraAway
        (Ideal.span (Set.range (Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R)))
        ((Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) 0) ≃ₐ[R]
      MvPolynomial (Fin 1) R ⧸ Ideal.span (Set.range fun i : Fin 1 ↦
        MvPolynomial.C ((Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) 0) * MvPolynomial.X i -
          MvPolynomial.C ((Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) i.succ))) :=
  Koszul.exists_affineBlowup_algEquiv_mvPolynomial_quotient_of_isH1Regular _
    (isH1Regular_pair x y hreg)

omit [IsRegularLocalRing R] in
/-- The relation ideal of the presentation is principal. -/
private lemma chart_relation_ideal_eq :
    Ideal.span (Set.range fun i : Fin 1 ↦
        MvPolynomial.C ((Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) 0) * MvPolynomial.X i -
          MvPolynomial.C ((Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) i.succ)) =
      Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y} := by
  congr 1
  exact Set.range_unique

/-- The presentation of the affine blowup chart attached to the first member of a regular
sequence generating the maximal ideal. -/
private lemma exists_chart_algEquiv (hreg : RingTheory.Sequence.IsRegular R [x, y])
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    Nonempty (affineBlowupAlgebraAway (maximalIdeal R) x ≃ₐ[R]
      MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) := by
  obtain ⟨e⟩ := exists_chart_algEquiv_raw x y hreg
  rw [range_pair, hxy, chart_relation_ideal_eq] at e
  exact ⟨e⟩

/-- Modulo the denominator, the presented chart is a polynomial ring over the residue field, so
it is a regular ring. -/
private lemma isRegularRing_quotient_presented
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    IsRegularRing ((MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) ⧸
      Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x}) := by
  have : (maximalIdeal R).IsMaximal := maximalIdeal.isMaximal R
  have hsup : Ideal.span ({MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y} :
        Set (MvPolynomial (Fin 1) R)) ⊔
      Ideal.span {(MvPolynomial.C x : MvPolynomial (Fin 1) R)} =
      Ideal.map (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R) (maximalIdeal R) := by
    rw [← hxy, Ideal.map_span, ← Ideal.span_union]
    rw [Set.image_pair]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro p (rfl | rfl)
      · exact Ideal.mem_span_pair.mpr ⟨MvPolynomial.X 0, -1, by ring⟩
      · exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
    · rintro p (rfl | rfl)
      · exact Ideal.subset_span (Or.inr (Set.mem_singleton _))
      · exact Ideal.mem_span_pair.mpr ⟨-1, MvPolynomial.X 0, by ring⟩
  have hid : Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
        Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x} =
      Ideal.map (Ideal.Quotient.mk (Ideal.span
          {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}))
        (Ideal.span {(MvPolynomial.C x : MvPolynomial (Fin 1) R)}) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [hid]
  have := isRegularRing_quotient_map_C (R := R) (maximalIdeal R) (Fin 1)
  exact IsRegularRing.of_ringEquiv
    ((Ideal.quotEquivOfEq hsup.symm).trans
      (DoubleQuot.quotQuotEquivQuotSup
        (Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y})
        (Ideal.span {(MvPolynomial.C x : MvPolynomial (Fin 1) R)})).symm)

/-- **The affine blowup chart of a two-dimensional regular local ring at a minimal generator of
its maximal ideal is a regular ring.** -/
private theorem isRegularRing_affineBlowupAlgebraAway (hdim : ringKrullDim R = 2)
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    IsRegularRing (affineBlowupAlgebraAway (maximalIdeal R) x) := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hregR : IsRegularRing R := ((IsLocalRing.isRegularRing_tfae (R := R)).out 1 3).mp ‹_›
  have hxm : x ∈ maximalIdeal R := hxy ▸ Ideal.subset_span (Set.mem_insert _ _)
  -- The maximal ideal needs two generators, so `x, y` is a regular sequence.
  have hsf := spanFinrank_maximalIdeal_eq_two hdim
  have hofList : Ideal.ofList [x, y] = maximalIdeal R := by
    rw [← hxy, Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil]
    simp [Ideal.span_insert]
  have hreg : RingTheory.Sequence.IsRegular R [x, y] :=
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      R).1 [x, y] hofList (by simp [hsf])).1
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
    exact one_ne_zero (hreg.1 (show (0 : R) • (1 : R) = (0 : R) • (0 : R) by simp))
  have : IsDomain (affineBlowupAlgebraAway (maximalIdeal R) x) :=
    isDomain_affineBlowupAlgebraAway x hxne
  obtain ⟨e⟩ := exists_chart_algEquiv x y hreg hxy
  have : IsNoetherianRing (affineBlowupAlgebraAway (maximalIdeal R) x) :=
    isNoetherianRing_of_ringEquiv _ e.toRingEquiv.symm
  have : IsRegularRing (affineBlowupAlgebraAway (maximalIdeal R) x ⧸
      Ideal.span ({algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x} :
        Set (affineBlowupAlgebraAway (maximalIdeal R) x))) := by
    have hcomm : (e.toRingEquiv : affineBlowupAlgebraAway (maximalIdeal R) x →+* _)
          (algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x) =
        algebraMap R (MvPolynomial (Fin 1) R ⧸
          Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x :=
      e.commutes x
    have hmap : Ideal.span {algebraMap R (MvPolynomial (Fin 1) R ⧸
          Ideal.span {MvPolynomial.C x * MvPolynomial.X (0 : Fin 1) - MvPolynomial.C y}) x} =
        Ideal.map (e.toRingEquiv : affineBlowupAlgebraAway (maximalIdeal R) x →+* _)
          (Ideal.span ({algebraMap R (affineBlowupAlgebraAway (maximalIdeal R) x) x} :
            Set (affineBlowupAlgebraAway (maximalIdeal R) x))) := by
      rw [Ideal.map_span, Set.image_singleton, hcomm]
    have := isRegularRing_quotient_presented x y hxy
    exact IsRegularRing.of_ringEquiv
      (Ideal.quotientEquiv _ _ e.toRingEquiv hmap).symm
  exact isRegularRing_of_quotient_away
    (injective_algebraMap_affineBlowupAlgebraAway x hxne) x hxne
    (exists_mul_pow_eq_algebraMap x hxm)

/-- The affine blowup chart in the form in which `AlgebraicGeometry.blowupChartι` presents it. -/
private theorem isRegularRing_affineBlowupAlgebra (hdim : ringKrullDim R = 2)
    (hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R) :
    IsRegularRing (affineBlowupAlgebra (maximalIdeal R) x (Localization.Away x)) := by
  have := isRegularRing_affineBlowupAlgebraAway x y hdim hxy
  exact IsRegularRing.of_ringEquiv
    (Subalgebra.equivOfEq _ _ (affineBlowupAlgebra_eq_away (maximalIdeal R) x)).symm.toRingEquiv

end Chart

/-! ### The charts of the blowup -/

/-- The ring of sections of the image of an affine blowup chart is the affine blowup algebra. -/
private lemma isRegularRing_sections_chart {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : I.ideal U)
    (h : IsRegularRing (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
      (Localization.Away (a : X.presheaf.obj (op U.1))))) :
    IsRegularRing Γ(blowUp I, blowupChartι I U a ''ᵁ ⊤) := by
  have := h
  have : IsRegularRing Γ(Spec (CommRingCat.of
      (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
        (Localization.Away (a : X.presheaf.obj (op U.1))))), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm
  exact IsRegularRing.of_ringEquiv
    ((blowupChartι I U a).appIso ⊤).commRingCatIsoToRingEquiv.symm

/-- **A blowup is regular as soon as the charts attached to a generating family of the centre
over one affine open covering the base are regular rings.** -/
private theorem isRegular_blowUp_of_charts {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (hUtop : ∀ z : X, z ∈ U.1) {ι : Type*}
    (f : ι → X.presheaf.obj (op U.1)) (hg : ∀ j, f j ∈ I.ideal U)
    (hspan : (I.ideal U : Ideal (X.presheaf.obj (op U.1))) ≤ Ideal.span (Set.range f))
    (hchart : ∀ j, IsRegularRing (affineBlowupAlgebra (I.ideal U) (f j)
      (Localization.Away (f j)))) :
    IsRegular (blowUp I) := by
  intro ξ
  obtain ⟨j, w, hw⟩ := exists_mem_range_blowupChartι I U f hg hspan ξ (hUtop _)
  exact ⟨⟨blowupChartι I U ⟨f j, hg j⟩ ''ᵁ ⊤,
    (isAffineOpen_top _).image_of_isOpenImmersion _⟩, ⟨w, trivial, hw⟩,
    isRegularRing_sections_chart I U ⟨f j, hg j⟩ (hchart j)⟩

/-- The centre of the blowup of a two-dimensional regular local ring at its closed point is a
nonzero ideal sheaf. -/
private lemma center_ne_bot (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) :
    Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A)) ≠ ⊥ := by
  have hmax : maximalIdeal A ≠ ⊥ := fun hm => by
    have := hdim.symm.trans (ringKrullDim_eq_zero_of_isField
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm))
    norm_num at this
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := fun r r' h => by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom h
  intro h
  have htop := congrArg
    (fun J : (Spec (CommRingCat.of A)).IdealSheafData =>
      J.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩) h
  have hbot : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A) = ⊥ := by
    simpa [Scheme.IdealSheafData.ofIdealTop_ideal] using htop
  exact hmax ((Ideal.map_eq_bot_iff_of_injective hinj).mp hbot)

end Stacks.Blowup

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0AGR.** The blowup of a two-dimensional regular local ring at its
closed point is irreducible. -/
@[stacks 0AGR "irreducibility"]
public theorem irreducibleSpace_blowUp_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    IrreducibleSpace (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A)))) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsIntegral (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A)))) :=
    isIntegral_blowUp _ (Stacks.Blowup.center_ne_bot A hdim)
  infer_instance

/-- **Stacks Project, Tag 0AGR.** The blowup of a two-dimensional regular local ring at its
closed point is a regular scheme. -/
@[stacks 0AGR "regularity"]
public theorem isRegular_blowUp_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) :
    IsRegular (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A)))) := by
  classical
  let U : (Spec (CommRingCat.of A)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩
  let R := (Spec (CommRingCat.of A)).presheaf.obj (op U.1)
  let I : (Spec (CommRingCat.of A)).IdealSheafData := Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A))
  let φ : A ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  have hφ : (φ : A →+* R) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    RingHom.ext fun _ => rfl
  have : IsRegularLocalRing R := IsRegularLocalRing.of_ringEquiv φ
  have hdimR : ringKrullDim R = 2 := (ringKrullDim_eq_of_ringEquiv φ).symm.trans hdim
  have hIU : I.ideal U = maximalIdeal R := by
    have h1 : I.ideal U =
        Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A) := by
      simp [I, U]
    rw [h1, ← hφ]
    exact map_ringEquiv_maximalIdeal φ
  -- Two generators of the maximal ideal.
  obtain ⟨s, hscard, hsspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal R).fg_of_isNoetherianRing
  have hsf := Stacks.Blowup.spanFinrank_maximalIdeal_eq_two hdimR
  rw [hsf] at hscard
  obtain ⟨x, y, -, rfl⟩ := Finset.card_eq_two.mp hscard
  have hxy : Ideal.span ({x, y} : Set R) = maximalIdeal R := by simpa using hsspan
  have hfspan : Ideal.span (Set.range (Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R)) =
      maximalIdeal R := by
    rwa [Stacks.Blowup.range_pair]
  have hg : ∀ j, (Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) j ∈ I.ideal U := fun j => by
    rw [hIU, ← hfspan]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hchart : ∀ j : Fin 2, IsRegularRing
      (affineBlowupAlgebra (I.ideal U) ((Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) j)
        (Localization.Away ((Fin.cases x (fun _ : Fin 1 => y) : Fin 2 → R) j))) := by
    have h0 : IsRegularRing (affineBlowupAlgebra (I.ideal U) x (Localization.Away x)) := by
      rw [hIU]
      exact Stacks.Blowup.isRegularRing_affineBlowupAlgebra x y hdimR hxy
    have h1 : IsRegularRing (affineBlowupAlgebra (I.ideal U) y (Localization.Away y)) := by
      rw [hIU]
      exact Stacks.Blowup.isRegularRing_affineBlowupAlgebra y x hdimR
        (by rwa [Set.pair_comm])
    intro j
    exact Fin.cases h0 (fun _ => h1) j
  exact Stacks.Blowup.isRegular_blowUp_of_charts I U (fun _ => trivial) _ hg
    (by rw [hIU, hfspan]) hchart

end AlgebraicGeometry

end
