module

public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IsolatedPrime

/-!
# Cohomological dimension bounds a height in the quotient by a prime

Let `A` be a Noetherian universally catenary ring and `I ⊆ A` an ideal. Let `𝔭 ⋖ 𝔮` be a
covering pair of primes of `A`, let `𝔶` be a prime with `𝔭 ⊆ 𝔶`, let `𝔷` be a prime with
`𝔶 ⊊ 𝔷`, and let `𝔷` be minimal over `𝔮 + I`. Then

`height(𝔶(A/𝔭)) ≤ cd(A, I)`.

This is the dimension bookkeeping that the proof of [Stacks, Tag 0EJ8] runs on the four primes
it produces: the point `𝔶` it hands to the next step must be no deeper, inside the closed
subscheme cut out by `𝔭`, than the cohomological dimension allows.

## Main results

* `Stacks.Algebraization.quotient_height_le_cohomologicalDimension` — the height bound above.

## Implementation notes

The bound is proved in the local ring `R = (A/𝔭)_𝔷`, which `𝔭 ⋖ 𝔮` and the minimality of `𝔷`
turn into exactly the situation of [Stacks, Tag 0DXF]:

* the image `𝔮R` of `𝔮` has height one, because `𝔭 ⋖ 𝔮` and the zero ideal of `R` is the image
  of `𝔭`;
* `V(𝔮R) ∩ V(IR)` is the closed point, because `𝔷` is a *minimal* prime over `𝔮 + I` and every
  prime of `R` lies under `𝔷`;
* the image `𝔶R` of `𝔶` is strictly below the maximal ideal, because `𝔶 ⊊ 𝔷`.

The private helper `Stacks.Algebraization.height_le_cohomologicalDimension_of_height_one` is
that configuration in the abstract: [Stacks, Tag 0DXF] bounds `dim(R/𝔮R)` by `cd(R, IR)`, and
universal catenarity ([Stacks, Tag 02IH]) splits the height of the maximal ideal of `R` as
`height(𝔮R) + dim(R/𝔮R) = 1 + dim(R/𝔮R)` through `catenary_height_add`, so a prime strictly
below the maximal ideal has height at most `dim(R/𝔮R)`. Passing from `cd(R, IR)` back to
`cd(A, I)` is [Stacks, Tag 0DXA].

The hypothesis `Ring.IsUniversallyCatenary A` is the ring-theoretic predicate of
[Stacks, Tag 00NL]; `catenary_height_add` takes the topological spelling, and the two are
identified by `Ring.isUniversallyCatenary_iff_isUniversallyCatenary`. It is transported to `R`
by `Ring.IsUniversallyCatenary.of_surjective` and `Ring.IsUniversallyCatenary.localization`,
rather than by a catenarity statement about the space `Spec(R)`.

## References

* [Stacks Project, Tag 0EJ8](https://stacks.math.columbia.edu/tag/0EJ8)
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
* [Stacks Project, Tag 02IH](https://stacks.math.columbia.edu/tag/02IH)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Algebraization

/-- In a Noetherian universally catenary local domain `R`, if `P` is a prime of height one whose
zero locus meets `V(I)` only in the closed point, then every prime `Q` strictly below the maximal
ideal satisfies `height(Q) ≤ cd(R, I)`.

Indeed `dim(R/P) ≤ cd(R, I)` by [Stacks, Tag 0DXF], and additivity of heights along `P ⊆ 𝔪`
gives `height(𝔪) = 1 + dim(R/P)`, while `height(Q) + 1 ≤ height(𝔪)`. -/
private lemma height_le_cohomologicalDimension_of_height_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsUniversallyCatenary R) (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : P.height = 1)
    (hinter : PrimeSpectrum.zeroLocus (P : Set R) ∩ PrimeSpectrum.zeroLocus (I : Set R) =
      {IsLocalRing.closedPoint R})
    (hQ : Q < IsLocalRing.maximalIdeal R) :
    (Q.height.toNat : ℤ) ≤
      Stacks.LocalCohomology.cohomologicalDimension R I I.fg_of_isNoetherianRing := by
  have : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hadd := catenary_height_add
    (Ring.isUniversallyCatenary_iff_isUniversallyCatenary.mp hcat) P
    (IsLocalRing.maximalIdeal R) (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top')
  rw [hP, IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective] at hadd
  have hmne : (IsLocalRing.maximalIdeal (R ⧸ P)).height ≠ ⊤ :=
    Ideal.height_ne_top (IsLocalRing.maximalIdeal.isMaximal (R ⧸ P)).ne_top
  have hdim := Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension' R P I
    I.fg_of_isNoetherianRing hinter (IsLocalRing.maximalIdeal (R ⧸ P)).height.toNat
    (by rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
        exact_mod_cast (ENat.natCast_toNat hmne).symm)
  have hle := Ideal.height_add_one_le_of_lt_of_isPrime hQ
  rw [hadd, add_comm (1 : ℕ∞)] at hle
  have hle' : Q.height ≤ (IsLocalRing.maximalIdeal (R ⧸ P)).height :=
    (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hle
  exact (Int.ofNat_le.mpr (ENat.toNat_le_toNat hle' hmne)).trans hdim

/-- **The cohomological dimension bounds the height of `𝔶` in `A/𝔭`.** Let `A` be a Noetherian
universally catenary ring, `I ⊆ A` an ideal, `𝔭 ⋖ 𝔮` a covering pair of primes, `𝔭 ⊆ 𝔶` and
`𝔶 ⊊ 𝔷` with `𝔷` minimal over `𝔮 + I`. Then `height(𝔶(A/𝔭)) ≤ cd(A, I)`.

This is the height bookkeeping of the proof of [Stacks, Tag 0EJ8]: the configuration becomes the
isolated-prime situation of [Stacks, Tag 0DXF] after passing to the local ring `(A/𝔭)_𝔷`. -/
public theorem quotient_height_le_cohomologicalDimension
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hcat : Ring.IsUniversallyCatenary A) (I : Ideal A)
    (p q y z : PrimeSpectrum A) (hpq : p ⋖ q) (hpy : p ≤ y) (hyz : y < z)
    (hzmin : z.asIdeal ∈ (q.asIdeal ⊔ I).minimalPrimes) :
    ((y.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height.toNat : ℤ) ≤
      Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing := by
  classical
  let B := A ⧸ p.asIdeal
  let eQ := p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  have hqz : q ≤ z := le_sup_left.trans hzmin.1.2
  have hpz : p ≤ z := hpq.le.trans hqz
  let zB : PrimeSpectrum B := eQ.symm ⟨z, hpz⟩
  let qB : PrimeSpectrum B := eQ.symm ⟨q, hpq.le⟩
  let yB : PrimeSpectrum B := eQ.symm ⟨y, hpy⟩
  let R := Localization.AtPrime zB.asIdeal
  let eL := IsLocalization.AtPrime.primeSpectrumOrderIso R zB.asIdeal
  have hqBz : qB ≤ zB := eQ.symm.monotone hqz
  have hyBz : yB < zB := eQ.symm.strictMono hyz
  let qR : PrimeSpectrum R := eL.symm ⟨qB, hqBz⟩
  let yR : PrimeSpectrum R := eL.symm ⟨yB, hyBz.le⟩
  let g : A →+* R := (algebraMap B R).comp (Ideal.Quotient.mk p.asIdeal)
  let f : PrimeSpectrum R → PrimeSpectrum A := PrimeSpectrum.comap g
  have hfinj : Function.Injective f := by
    intro a b h
    apply eL.injective
    apply Subtype.ext
    apply eQ.injective
    apply Subtype.ext
    exact h
  have hfq : f qR = q := by
    change (eQ (eL qR).val).val = q
    rw [eL.apply_symm_apply]
    exact congrArg Subtype.val (eQ.apply_symm_apply _)
  have hfy : f yR = y := by
    change (eQ (eL yR).val).val = y
    rw [eL.apply_symm_apply]
    exact congrArg Subtype.val (eQ.apply_symm_apply _)
  have hfz (a : PrimeSpectrum R) : f a ≤ z := by
    have h := eQ.monotone (eL a).property
    change (eQ (eL a).val).val ≤ (eQ zB).val at h
    change (eQ (eL a).val).val ≤ z
    simpa only [zB, eQ.apply_symm_apply] using h
  have hfm : f (IsLocalRing.closedPoint R) = z := by
    let zR : PrimeSpectrum R := eL.symm ⟨zB, show zB.asIdeal ≤ zB.asIdeal from le_rfl⟩
    have hzR : f zR = z := by
      change (eQ (eL zR).val).val = z
      rw [eL.apply_symm_apply]
      exact congrArg Subtype.val (eQ.apply_symm_apply _)
    refine le_antisymm (hfz _) ?_
    rw [← hzR]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal zR.isPrime.ne_top)
  have hfp : f ⊥ = p := by
    apply PrimeSpectrum.ext
    change RingHom.ker g = p.asIdeal
    rw [RingHom.ker_comp_of_injective _ (IsLocalization.injective R
      zB.asIdeal.primeCompl_le_nonZeroDivisors), Ideal.mk_ker]
  have hcov : (⊥ : PrimeSpectrum R) ⋖ qR := by
    refine ⟨bot_lt_iff_ne_bot.mpr fun h =>
      hpq.ne ((hfp.symm.trans (congrArg f h.symm)).trans hfq), ?_⟩
    intro a ha haq
    have hmon : StrictMono f := fun a b hab =>
      lt_of_le_of_ne (Ideal.comap_mono hab.le) fun h => hab.ne (hfinj h)
    have h₁ := hmon ha
    have h₂ := hmon haq
    rw [hfp] at h₁
    rw [hfq] at h₂
    exact hpq.2 h₁ h₂
  have hheight : qR.asIdeal.height = 1 := by
    rw [PrimeSpectrum.height_eq_orderHeight]
    change Order.height qR = (0 : ℕ∞) + 1
    refine (Order.height_eq_coe_add_one_iff (n := 0)).mpr ⟨?_, ⟨⊥, hcov.lt, by simp⟩, ?_⟩
    · rw [← PrimeSpectrum.height_eq_orderHeight]
      exact lt_top_iff_ne_top.mpr (Ideal.height_ne_top qR.isPrime.ne_top)
    · intro a haq
      have ha : a = ⊥ := by
        by_contra ha
        exact hcov.2 (bot_lt_iff_ne_bot.mpr ha) haq
      rw [ha]
      simp
  have hImax : I.map g ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    change I ≤ (f (IsLocalRing.closedPoint R)).asIdeal
    rw [hfm]
    exact le_sup_right.trans hzmin.1.2
  have hinter : PrimeSpectrum.zeroLocus (qR.asIdeal : Set R) ∩
      PrimeSpectrum.zeroLocus (I.map g : Set R) = {IsLocalRing.closedPoint R} := by
    ext a
    constructor
    · rintro ⟨hqa, hIa⟩
      apply hfinj
      rw [hfm]
      apply PrimeSpectrum.ext
      refine le_antisymm (show (f a).asIdeal ≤ z.asIdeal from hfz a) (hzmin.2 ?_ (hfz a))
      refine ⟨(f a).isPrime, sup_le ?_ (Ideal.map_le_iff_le_comap.mp hIa)⟩
      have h := Ideal.comap_mono (f := g) hqa
      change f qR ≤ f a at h
      rwa [hfq] at h
    · rintro rfl
      exact ⟨IsLocalRing.le_maximalIdeal qR.isPrime.ne_top, hImax⟩
  have hyRlt : yR.asIdeal < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal yR.isPrime.ne_top) fun h => hyz.ne ?_
    have hyRm : yR = IsLocalRing.closedPoint R := PrimeSpectrum.ext h
    exact hfy.symm.trans ((congrArg f hyRm).trans hfm)
  have hbound := height_le_cohomologicalDimension_of_height_one
    (Ring.IsUniversallyCatenary.localization zB.asIdeal.primeCompl R
      (Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hcat))
    (I.map g) qR.asIdeal yR.asIdeal hheight hinter hyRlt
  have hhy : yR.asIdeal.height = yB.asIdeal.height := by
    have hh := IsLocalization.height_under zB.asIdeal.primeCompl yR.asIdeal
    have he : yR.asIdeal.under B = yB.asIdeal :=
      congrArg (fun a : {a : PrimeSpectrum B // a ≤ zB} => a.val.asIdeal)
        (eL.apply_symm_apply ⟨yB, hyBz.le⟩)
    rw [he] at hh
    exact hh.symm
  rw [hhy] at hbound
  exact hbound.trans (Stacks.LocalCohomology.cohomologicalDimension_map_le g I _)

end Stacks.Algebraization

end
