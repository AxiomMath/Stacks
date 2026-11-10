module

import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.Smooth.IntegralClosure

public import StacksFrontier.RingTheory.IntegrallyClosed.Polynomial
public import StacksFrontier.FieldTheory.TranscendentalSeparable
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric normality is detected by finite purely inseparable base change

Proof of `Algebra.isNormalRing_tensorProduct_tfae`: for a field `k` of exponential characteristic
`p` and a commutative `k`-algebra `A`, normality of `k' ⊗[k] A` for every field extension `k'/k`,
for every finitely generated one, for every finite purely inseparable one, and normality of the
single ring `k^{perf} ⊗[k] A` are all equivalent.

## The route

Three of the four implications are formal. Item (1) restricts to item (2) and item (2) to item (3),
a finite extension being essentially of finite type. Item (1) gives item (4) because `k^{perf}/k`
is purely inseparable, hence algebraic, hence `k`-embeddable into `AlgebraicClosure k`, so that
`k^{perf}` is `k`-isomorphic to an intermediate field of `AlgebraicClosure k` — a field in the
universe of `k`, where item (1) quantifies — and normality transports along the induced isomorphism
of base changes. Item (4) gives item (3) because a finite purely inseparable `k'/k` embeds into the
perfect field `k^{perf}` over `k`, and normality descends along the faithfully flat ring map
`k' ⊗[k] A → k^{perf} ⊗[k] A` (Lemma 033G).

The content is item (3) `⇒` item (1), and it is proved in the shape of the source's (3) `⇒` (2)
`⇒` (1) with the two steps merged, since the reduction to finitely generated subextensions is
needed for both. For a field extension `L/k` the ring `L ⊗[k] A` is the directed union of the
subrings `F ⊗[k] A` for `F/k` a finitely generated subextension — the maps `F ⊗[k] A → L ⊗[k] A`
are injective because `A` is flat over the field `k` — so by Lemma 037D it is enough to treat a
finitely generated `F/k`. Inside an algebraic closure of such an `F`, Lemma 04KM produces finite
purely inseparable extensions `k'/k` and `F'/F` with `F'/k'` separably generated; item (3) makes
`k' ⊗[k] A` normal, base change along the separably generated extension `F'/k'` makes
`F' ⊗[k'] (k' ⊗[k] A) = F' ⊗[k] A` normal, and `F ⊗[k] A` is recovered from it by descent along
the faithfully flat map `F ⊗[k] A → F' ⊗[k] A` (Lemma 033G again).

Base change along a separably generated extension `K/F` is the substance. With `s` a separating
transcendence basis it factors as `K ⊗[F(s)] (F(s) ⊗[F] T)`, and the two halves are:

* `F(s) ⊗[F] T` is a localization of the polynomial ring `T[s]`, which is normal by Lemma 00H1 in
  finitely many variables and by Lemma 037D — as the directed union of those — in general;
  localizations of normal rings are normal (Lemma 037C).
* `K/F(s)` is separable algebraic, so again by the reduction to finitely generated subextensions it
  suffices to base change along a *finite* separable extension `B/F`, and `B ⊗[F] T` is étale over
  `T`. An étale algebra over a normal ring is normal (`IsNormalRing.of_etale`, the étale case of
  Lemma 033C): it is local on the base, so one may assume `T` a normal domain `D` with fraction
  field `Q`, and then an étale `D`-algebra `S` is reduced — it embeds into `S ⊗[D] Q`, which is
  étale over the field `Q` and hence reduced — has finitely many minimal primes, its total ring of
  fractions being that finite-dimensional, so Artinian, `Q`-algebra, and is integrally closed in
  that total ring of fractions, because integral closure commutes with smooth base change
  (`TensorProduct.toIntegralClosure_bijective_of_smooth`). Lemma 030C turns those three facts into
  normality.

## Main results

* `Stacks.GeometricallyNormal.Criterion.solution`: the statement of Stacks Tag 037Z.

## Implementation notes

The basic API for the library's `IsNormalRing` that the proof needs is proved upstream, next to
the definition in `StacksFrontier.RingTheory.IntegrallyClosed.Defs`: normality transports along a
ring
isomorphism (`IsNormalRing.congr`), passes to an arbitrary localization
(`IsNormalRing.isLocalization`, which is Lemma 037C for a normal ring rather than for a normal
domain), is read off at a prime through any model of the localization (`IsNormalRing.atPrime`), and
means "normal domain" for a local ring (`IsNormalRing.of_isLocalRing`); a normal domain is a normal
ring (`IsNormalRing.of_isIntegrallyClosed`), and a normal ring is reduced
(`IsNormalRing.isReduced`).

The further facts the proof needs are established here and are not private, being of general use:
normality passes to a directed union of normal subrings (`isNormalRing_of_directedUnion`, Lemma
037D in the form used throughout), holds for a polynomial ring in an arbitrary number of variables
(`isNormalRing_mvPolynomial`, Lemma 00H1 with the number of variables no longer finite), ascends to
an étale algebra over a normal ring (`IsNormalRing.of_etale`), and for a base change `L ⊗[k] A`
along a field extension is detected on the finitely generated subextensions
(`isNormalRing_tensorProduct_of_forall_fg_intermediateField`).

`IsNormalRing.of_isLocalRing` is what makes the localization arguments compose: to prove that
`Localization.AtPrime 𝔮` is a normal domain it is enough to exhibit it as a localization of a
normal ring, since a local normal ring is a normal domain.

## References

* [Stacks 037Z](https://stacks.math.columbia.edu/tag/037Z). The ingredients are Lemmas 033G, 037D,
  04KM, 00H1, 037C and 030C; the source's Lemmas 037X and 033C are replaced by the separating
  transcendence basis of Lemma 04KM and the étale case described above.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-- A directed union of normal subrings is a normal ring. -/
theorem isNormalRing_of_directedUnion {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] (S : ι → Subring R) (hmono : Monotone S)
    (hcover : ∀ x : R, ∃ i, x ∈ S i) (hnormal : ∀ i, IsNormalRing (S i)) : IsNormalRing R := by
  set G : ι → Type _ := fun i => ↥(S i)
  set φ : (i j : ι) → i ≤ j → G i →+* G j := fun i j h => Subring.inclusion (hmono h)
  have hdir : DirectedSystem G (fun i j h => (φ i j h : G i → G j)) :=
    ⟨fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  have Hg : ∀ (i j : ι) (hij : i ≤ j) (x : G i), (S j).subtype (φ i j hij x) =
      (S i).subtype x := fun _ _ _ _ => rfl
  have hbij : Function.Bijective (Ring.DirectLimit.lift G
      (fun i j h => (φ i j h : G i → G j)) R (fun i => (S i).subtype) Hg) := by
    refine ⟨Ring.DirectLimit.lift_injective R _ Hg fun i => Subtype.val_injective, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨Ring.DirectLimit.of G _ i ⟨x, hi⟩, by rw [Ring.DirectLimit.lift_of]; rfl⟩
  exact IsNormalRing.congr (RingEquiv.ofBijective _ hbij)
    (directLimit_isNormalRing G φ hdir hnormal)

/-- A polynomial ring in finitely many variables `Fin n` over a normal ring is normal. -/
private theorem isNormalRing_mvPolynomial_fin {R : Type*} [CommRing R] (h : IsNormalRing R) :
    ∀ n : ℕ, IsNormalRing (MvPolynomial (Fin n) R)
  | 0 => IsNormalRing.congr (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv h
  | n + 1 => IsNormalRing.congr (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv
      (polynomial_ring_normal _ (isNormalRing_mvPolynomial_fin h n))

/-- A polynomial ring in finitely many variables over a normal ring is normal. -/
private theorem isNormalRing_mvPolynomial_fintype (τ : Type*) [Finite τ] {R : Type*} [CommRing R]
    (h : IsNormalRing R) : IsNormalRing (MvPolynomial τ R) := by
  let _ := Fintype.ofFinite τ
  exact IsNormalRing.congr (MvPolynomial.renameEquiv R (Fintype.equivFin τ)).symm.toRingEquiv
    (isNormalRing_mvPolynomial_fin h _)

/-- A polynomial ring in an arbitrary number of variables over a normal ring is normal. -/
theorem isNormalRing_mvPolynomial (σ : Type*) {R : Type*} [CommRing R] (h : IsNormalRing R) :
    IsNormalRing (MvPolynomial σ R) := by
  refine isNormalRing_of_directedUnion
    (fun t : Finset σ => (MvPolynomial.supported R (t : Set σ)).toSubring) ?_ ?_ ?_
  · exact fun s t hst _ hx => MvPolynomial.supported_mono (by exact_mod_cast hst) hx
  · exact fun p => ⟨p.vars, MvPolynomial.mem_supported.mpr (by simp)⟩
  · exact fun t => IsNormalRing.congr
      (MvPolynomial.supportedEquivMvPolynomial (R := R) (t : Set σ)).symm.toRingEquiv
      (isNormalRing_mvPolynomial_fintype _ h)

/-! ### Étale algebras over normal rings -/

/-- If `D` is integrally closed in `Q`, then every element of `S ⊗[D] integralClosure D Q` has
image in `S ⊗[D] Q` of the form `algebraMap S (S ⊗[D] Q) y`: on a pure tensor `s ⊗ₜ c` the
second factor is `algebraMap D Q d`, and `s ⊗ₜ algebraMap D Q d = (d • s) ⊗ₜ 1`. -/
theorem TensorProduct.exists_algebraMap_eq_toIntegralClosure {D Q S : Type*} [CommRing D]
    [CommRing Q] [Algebra D Q] [CommRing S] [Algebra D S] (h : integralClosure D Q = ⊥)
    (z : S ⊗[D] (integralClosure D Q)) :
    ∃ y : S,
      algebraMap S (S ⊗[D] Q) y = (TensorProduct.toIntegralClosure D S Q z : S ⊗[D] Q) := by
  induction z with
  | tmul s c =>
      obtain ⟨d, hd⟩ : ∃ d : D, algebraMap D Q d = (c : Q) := by
        have hc : (c : Q) ∈ (⊥ : Subalgebra D Q) := h ▸ c.2
        simpa [Algebra.mem_bot] using hc
      refine ⟨d • s, ?_⟩
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      simp [TensorProduct.toIntegralClosure, ← hd, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul']
  | add z w hz hw =>
      obtain ⟨y, hy⟩ := hz
      obtain ⟨y', hy'⟩ := hw
      exact ⟨y + y', by rw [map_add, hy, hy', map_add, Subalgebra.coe_add]⟩

/-- A ring with finitely many minimal primes, whose total ring of fractions is a base change
`S ⊗[D] Frac D`: the minimal primes of `S` avoid the nonzerodivisors, so they are among the
primes of the total ring of fractions, of which there are finitely many when it is Artinian. -/
private theorem finite_minimalPrimes_of_isArtinianRing {D S : Type*} [CommRing D] [IsDomain D]
    [CommRing S] [IsReduced S] [Algebra D S] [IsArtinianRing (S ⊗[D] FractionRing D)]
    [IsFractionRing S (S ⊗[D] FractionRing D)] : (minimalPrimes S).Finite := by
  have hdisj : ∀ p ∈ minimalPrimes S,
      Disjoint (nonZeroDivisors S : Set S) (p : Set S) := by
    intro p hp
    rw [Set.disjoint_right]
    intro x hx hx'
    obtain ⟨y, hy0, hxy⟩ :=
      mem_zeroDivisorSet.mp (mem_minimalPrime_imp_zeroDivisor S p hp x hx)
    exact hy0 (mem_nonZeroDivisors_iff_right.mp hx' y (by rw [mul_comm]; exact hxy))
  have : Finite (minimalPrimes S) := by
    refine Finite.of_injective (fun p : minimalPrimes S ↦ (⟨_, ((IsLocalization.orderIsoOfPrime
      (nonZeroDivisors S) (S ⊗[D] FractionRing D)).symm ⟨p.1, p.2.1.1, hdisj p.1 p.2⟩).2⟩ :
        PrimeSpectrum (S ⊗[D] FractionRing D))) fun p q hpq ↦ ?_
    have h := (IsLocalization.orderIsoOfPrime (nonZeroDivisors S)
      (S ⊗[D] FractionRing D)).symm.injective (Subtype.ext (congrArg PrimeSpectrum.asIdeal hpq))
    rw [Subtype.mk.injEq] at h
    exact Subtype.ext h
  exact Set.toFinite _

/-- **An étale algebra over a normal domain is a normal ring.** It is reduced, embedding into the
étale, hence reduced, algebra `S ⊗[D] Frac D` over the field `Frac D`; that algebra is finite over
`Frac D`, hence Artinian, so it is the total ring of fractions of `S` and `S` has finitely many
minimal primes; and `S` is integrally closed in it, since integral closure commutes with smooth
base change (`TensorProduct.toIntegralClosure_bijective_of_smooth`). Lemma 030C turns those three
facts into normality. -/
@[ega "IV 7.5.3" "(vi), special case"]
theorem IsNormalRing.of_etale_of_isDomain (D S : Type*) [CommRing D] [IsDomain D]
    [IsIntegrallyClosed D] [CommRing S] [Algebra D S] [Algebra.Etale D S] : IsNormalRing S := by
  have hredA : IsReduced (FractionRing D ⊗[D] S) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing D) _
  have : Module.Finite (FractionRing D) (FractionRing D ⊗[D] S) :=
    Algebra.FormallyUnramified.finite_of_free (FractionRing D) _
  have : IsArtinianRing (FractionRing D ⊗[D] S) := IsArtinianRing.of_finite (FractionRing D) _
  let e : (S ⊗[D] FractionRing D) ≃+* (FractionRing D ⊗[D] S) :=
    (Algebra.TensorProduct.comm D S (FractionRing D)).toRingEquiv
  have : IsArtinianRing (S ⊗[D] FractionRing D) := e.symm.isArtinianRing
  have hM : Algebra.algebraMapSubmonoid S (nonZeroDivisors D) ≤ nonZeroDivisors S := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    rw [mul_comm, ← Algebra.smul_def] at hy
    exact (smul_eq_zero.mp hy).resolve_left (mem_nonZeroDivisors_iff_ne_zero.mp hd)
  have hinj : Function.Injective (algebraMap S (S ⊗[D] FractionRing D)) :=
    IsLocalization.injective _ hM
  have : IsReduced S :=
    isReduced_of_injective (e.toRingHom.comp (algebraMap S (S ⊗[D] FractionRing D)))
      fun a b h ↦ hinj (e.injective h)
  have : IsFractionRing S (S ⊗[D] FractionRing D) := by
    refine IsLocalization.of_le _ _ hM fun r hr ↦ ?_
    have h1 := IsLocalization.map_nonZeroDivisors_le
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors D))
      (S := S ⊗[D] FractionRing D) (Submonoid.mem_map_of_mem _ hr)
    exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors h1
  have hbot : integralClosure D (FractionRing D) = ⊥ :=
    IsIntegrallyClosed.integralClosure_eq_bot D (FractionRing D)
  have hIC : IsIntegrallyClosed S := by
    rw [isIntegrallyClosed_iff_isIntegrallyClosedIn (S ⊗[D] FractionRing D)]
    refine isIntegrallyClosedIn_iff.mpr ⟨hinj, fun {x} hx ↦ ?_⟩
    obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := D) (S := S) (B := FractionRing D)).2 ⟨x, hx⟩
    obtain ⟨y, hy⟩ := TensorProduct.exists_algebraMap_eq_toIntegralClosure hbot z
    exact ⟨y, hy.trans (congrArg Subtype.val hz)⟩
  exact ((isIntegrallyClosed_tfae_of_finite_minimalPrimes
    (finite_minimalPrimes_of_isArtinianRing (D := D))).out 1 2).mpr hIC

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A localization of an `R`-algebra `S` at a prime `q` is a localization of `R_𝔭 ⊗[R] S`, for
`𝔭` the contraction of `q`; so `S_q` is a normal domain as soon as `R_𝔭 ⊗[R] S` is a normal ring.
-/
theorem IsNormalRing.of_localization_atPrime_tensorProduct {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], IsNormalRing (Localization.AtPrime p ⊗[R] S)) :
    IsNormalRing S := by
  intro q hq
  have : (q.comap (algebraMap R S)).IsPrime := hq.comap _
  set p : Ideal R := q.comap (algebraMap R S)
  have hle : Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩
    exact hr
  let A := Localization.AtPrime p ⊗[R] S
  let _ : Algebra A (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ q.primeCompl hle
  have : IsScalarTower S A (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ q.primeCompl hle
  have : IsLocalization (q.primeCompl.map (algebraMap S A)) (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ q.primeCompl hle
  exact ((H p).isLocalization (q.primeCompl.map (algebraMap S A))
    (Localization.AtPrime q)).of_isLocalRing

end

/-- **An étale algebra over a normal ring is a normal ring.** Normality is local on the base, and
over the normal domain `R_𝔭` it is `IsNormalRing.of_etale_of_isDomain`. -/
theorem IsNormalRing.of_etale {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (hR : IsNormalRing R) : IsNormalRing S :=
  of_localization_atPrime_tensorProduct fun p _ ↦
    have := (hR p).1
    have := (hR p).2
    of_etale_of_isDomain (Localization.AtPrime p) _

/-! ### Reduction to finitely generated subextensions -/

section FG

variable {k L A : Type*} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]

/-- The base change of `A` along a subextension `F` of `L/k`, mapped into `L ⊗[k] A`. -/
private noncomputable def inclIntermediateField (F : IntermediateField k L) :
    ↥F ⊗[k] A →ₐ[k] L ⊗[k] A :=
  Algebra.TensorProduct.map F.val (AlgHom.id k A)

/-- `incl` is injective, since `↥F → L` is injective and `A` is flat over the field `k`. -/
private theorem inclIntermediateField_injective (F : IntermediateField k L) :
    Function.Injective (inclIntermediateField (A := A) F) := by
  have h : ((inclIntermediateField (A := A) F).toLinearMap : ↥F ⊗[k] A →ₗ[k] L ⊗[k] A)
      = LinearMap.rTensor A F.val.toLinearMap := by
    ext x a; simp [inclIntermediateField]
  have := Module.Flat.rTensor_preserves_injective_linearMap (M := A) F.val.toLinearMap
    F.val.injective
  rwa [← h] at this

/-- The image of `↥F ⊗[k] A` in `L ⊗[k] A`, as a subring. -/
private noncomputable def inclIntermediateFieldRange (F : IntermediateField k L) :
    Subring (L ⊗[k] A) :=
  (inclIntermediateField (A := A) F).range.toSubring

/-- The images of the base changes grow with the subextension. -/
private theorem inclIntermediateFieldRange_mono {F₁ F₂ : IntermediateField k L}
    (h : F₁ ≤ F₂) :
    inclIntermediateFieldRange (A := A) F₁ ≤ inclIntermediateFieldRange (A := A) F₂ := by
  have hcomp : (inclIntermediateField (A := A) F₂).comp
      (Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id k A))
      = inclIntermediateField (A := A) F₁ := by
    ext x <;> simp [inclIntermediateField]
  have hle := AlgHom.range_comp_le_range
    (Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id k A))
    (inclIntermediateField (A := A) F₂)
  rw [hcomp] at hle
  exact fun x hx => hle hx

/-- Normality of a base change `L ⊗[k] A` along a field extension `L/k` is detected by the
finitely generated subextensions of `L/k`. -/
theorem isNormalRing_tensorProduct_of_forall_fg_intermediateField
    {k L A : Type*} [Field k]
    [Field L] [Algebra k L] [CommRing A] [Algebra k A]
    (H : ∀ F : IntermediateField k L, F.FG → IsNormalRing (↥F ⊗[k] A)) :
    IsNormalRing (L ⊗[k] A) := by
  have : Nonempty {F : IntermediateField k L // F.FG} := ⟨⟨⊥, IntermediateField.fg_bot⟩⟩
  have : IsDirectedOrder {F : IntermediateField k L // F.FG} :=
    ⟨fun i j => ⟨⟨i.1 ⊔ j.1, IntermediateField.fg_sup i.2 j.2⟩,
      Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩
  refine isNormalRing_of_directedUnion (ι := {F : IntermediateField k L // F.FG})
    (fun i => inclIntermediateFieldRange (A := A) i.1)
    (fun _ _ h => inclIntermediateFieldRange_mono h) (fun x => ?_) (fun i => ?_)
  · induction x with
    | tmul l a =>
        refine ⟨⟨IntermediateField.adjoin k {l},
          IntermediateField.fg_adjoin_of_finite (Set.finite_singleton l)⟩,
          ⟨⟨l, IntermediateField.subset_adjoin k _ rfl⟩ ⊗ₜ[k] a, ?_⟩⟩
        simp [inclIntermediateField]
    | add x y hx hy =>
        obtain ⟨i, hi⟩ := hx
        obtain ⟨j, hj⟩ := hy
        obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
        exact ⟨m, add_mem (inclIntermediateFieldRange_mono him hi)
          (inclIntermediateFieldRange_mono hjm hj)⟩
  · exact IsNormalRing.congr
      (AlgEquiv.ofInjective (inclIntermediateField (A := A) i.1)
        (inclIntermediateField_injective i.1)).toRingEquiv (H i.1 i.2)

end FG

namespace Stacks.GeometricallyNormal.Criterion


/-! ### Descent along a faithfully flat base change of fields -/

/-- Normality of a base change descends along a field extension of the extension: if
`K' ⊗[k] A` is normal and `k ⊆ K ⊆ K'`, then `K ⊗[k] A` is normal. -/
private theorem isNormalRing_tensorProduct_of_isScalarTower {k K K' A : Type*} [Field k] [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] [CommRing A]
    [Algebra k A] (h : IsNormalRing (K' ⊗[k] A)) : IsNormalRing (K ⊗[k] A) := by
  have e : K' ⊗[k] A ≃+* (K ⊗[k] A) ⊗[K] K' :=
    (Algebra.TensorProduct.cancelBaseChange k K K' K' A).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm K K' (K ⊗[k] A)).toRingEquiv
  exact isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat (IsNormalRing.congr e h)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Base change along a purely transcendental extension -/

/-- Base change of a normal ring along a purely transcendental field extension is normal. -/
private theorem isNormalRing_tensorProduct_fractionRing_mvPolynomial (k : Type*) [Field k]
    (σ : Type*) {N : Type*} [CommRing N] [Algebra k N] (h : IsNormalRing N) :
    IsNormalRing (FractionRing (MvPolynomial σ k) ⊗[k] N) := by
  have h1 : IsNormalRing (MvPolynomial σ k ⊗[k] N) :=
    IsNormalRing.congr (((Algebra.TensorProduct.comm k (MvPolynomial σ k) N).trans
      ((MvPolynomial.algebraTensorAlgEquiv k N).restrictScalars k)).symm.toRingEquiv)
      (isNormalRing_mvPolynomial σ h)
  refine IsNormalRing.congr (Algebra.TensorProduct.cancelBaseChange k (MvPolynomial σ k)
    (FractionRing (MvPolynomial σ k)) (FractionRing (MvPolynomial σ k)) N).toRingEquiv ?_
  exact h1.isLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ k ⊗[k] N)
    (nonZeroDivisors (MvPolynomial σ k))) _

/-! ### Base change along a separable, or separably generated, extension -/

/-- **Base change of a normal ring along a finite separable field extension is normal**, being
étale over it. -/
@[ega "IV 21.14.4" "special case", ega "IV 4.3.5" "special case"]
private theorem isNormalRing_tensorProduct_of_finiteDimensional {F B N : Type*} [Field F] [Field B]
    [Algebra F B] [Algebra.IsSeparable F B] [FiniteDimensional F B] [CommRing N] [Algebra F N]
    (h : IsNormalRing N) : IsNormalRing (B ⊗[F] N) := by
  have : Algebra.Etale F B :=
    ⟨Algebra.FormallyEtale.of_isSeparable F B, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  exact IsNormalRing.congr (Algebra.TensorProduct.comm F N B).toRingEquiv
    (IsNormalRing.of_etale (R := N) h)

/-- Base change of a normal ring along a separable algebraic field extension is normal: by the
reduction to finitely generated subextensions one may assume the extension finite. -/
@[ega "IV 21.14.4" "special case", ega "IV 4.3.5" "special case", ega "IV 6.7.6" "special case"]
private theorem isNormalRing_tensorProduct_of_isSeparable {F K T : Type*} [Field F] [Field K]
    [Algebra F K] [Algebra.IsSeparable F K] [CommRing T] [Algebra F T] (h : IsNormalRing T) :
    IsNormalRing (K ⊗[F] T) := by
  refine isNormalRing_tensorProduct_of_forall_fg_intermediateField fun M hM => ?_
  obtain ⟨s, rfl⟩ := hM
  have : FiniteDimensional F ↥(IntermediateField.adjoin F (s : Set K)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact isNormalRing_tensorProduct_of_finiteDimensional h

/-- **Base change of a normal ring along a separably generated field extension is normal.** With
`s` a separating transcendence basis of `K/F`, the base change factors through `F(s)`, where
`F(s) ⊗[F] T` is a localization of the polynomial ring `T[s]`, and `K/F(s)` is separable
algebraic. -/
@[ega "IV 21.14.4" "special case", ega "IV 4.3.5" "special case"]
private theorem isNormalRing_tensorProduct_of_isSeparablyGenerated (F : Type u) (K : Type v)
    [Field F] [Field K] [Algebra F K] [Algebra.IsSeparablyGenerated F K] (T : Type w) [CommRing T]
    [Algebra F T] (h : IsNormalRing T) : IsNormalRing (K ⊗[F] T) := by
  obtain ⟨s, hs, hsep⟩ :=
    Algebra.IsSeparablyGenerated.isSeparable (k := F) (K := K)
  have := hsep
  have e : FractionRing (MvPolynomial (s : Type v) F) ≃ₐ[F] IntermediateField.adjoin F s :=
    hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by rw [Subtype.range_coe]))
  have hbase : IsNormalRing (↥(IntermediateField.adjoin F s) ⊗[F] T) :=
    IsNormalRing.congr (Algebra.TensorProduct.congr e AlgEquiv.refl).toRingEquiv
      (isNormalRing_tensorProduct_fractionRing_mvPolynomial F (s : Type v) h)
  exact IsNormalRing.congr (Algebra.TensorProduct.cancelBaseChange F
      ↥(IntermediateField.adjoin F s) K K T).toRingEquiv
    (isNormalRing_tensorProduct_of_isSeparable hbase)

/-- Base change along a separably generated extension of an intermediate base field: if
`k' ⊗[k] A` is normal and `K'/k'` is separably generated, then `K' ⊗[k] A` is normal. -/
@[ega "IV 21.14.4" "special case", ega "IV 6.14.2" "special case"]
private theorem isNormalRing_tensorProduct_of_isSeparablyGenerated_of_isScalarTower
    {k k' K' A : Type*} [Field k] [Field k'] [Field K'] [CommRing A] [Algebra k A]
    [Algebra k k'] [Algebra k K'] [Algebra k' K'] [IsScalarTower k k' K']
    [Algebra.IsSeparablyGenerated k' K'] (h : IsNormalRing (k' ⊗[k] A)) :
    IsNormalRing (K' ⊗[k] A) :=
  IsNormalRing.congr (Algebra.TensorProduct.cancelBaseChange k k' K' K' A).toRingEquiv
    (isNormalRing_tensorProduct_of_isSeparablyGenerated k' K' _ h)

/-- **Item (3) ⇒ item (1) of Stacks 037Z.** If `k' ⊗[k] A` is normal for every finite purely
inseparable extension `k'/k`, then `L ⊗[k] A` is normal for every field extension `L/k`. -/
@[ega "IV 6.7.7" "(b) ⇒ (c), (b) ⇒ (d)"]
private theorem isNormalRing_tensorProduct_of_forall_finiteDimensional_isPurelyInseparable
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    (H : ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'], IsNormalRing (k' ⊗[k] A))
    (L : Type u) [Field L] [Algebra k L] : IsNormalRing (L ⊗[k] A) := by
  refine isNormalRing_tensorProduct_of_forall_fg_intermediateField fun F hF => ?_
  have : Algebra.EssFiniteType k ↥F := IntermediateField.essFiniteType_iff.2 hF
  obtain ⟨L', k₀, -, -, hfin, hpi, hsg⟩ :=
    exists_isPurelyInseparable_and_isSeparablyGenerated_of_essFiniteType k ↥F (AlgebraicClosure ↥F)
  have : FiniteDimensional k ↥k₀ := hfin
  have := hpi
  have := hsg
  have hL' : IsNormalRing (↥L' ⊗[k] A) :=
    isNormalRing_tensorProduct_of_isSeparablyGenerated_of_isScalarTower (K' := ↥L') (H ↥k₀)
  exact isNormalRing_tensorProduct_of_isScalarTower hL'

/-- **Stacks 037Z**: the four conditions of `Algebra.isNormalRing_tensorProduct_tfae` are
equivalent. The cycle proved is (1) `⇒` (2) `⇒` (3) `⇒` (1) together with (1) `⇒` (4) `⇒` (3). -/
public theorem solution
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (A : Type v) [CommRing A] [Algebra k A]
    (kperf : Type w) [Field kperf] [Algebra k kperf] [ExpChar kperf p] [PerfectRing kperf p]
    [IsPerfectClosure (algebraMap k kperf) p] :
    [∀ (k' : Type u) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
        IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'], IsNormalRing (k' ⊗[k] A),
      IsNormalRing (kperf ⊗[k] A)].TFAE := by
  have : IsPurelyInseparable k kperf := IsPRadical.isPurelyInseparable k kperf p
  have : PerfectField kperf := PerfectRing.toPerfectField kperf p
  tfae_have 1 → 2 := fun H k' _ _ _ => H k'
  tfae_have 2 → 3 := fun H k' _ _ _ _ => H k'
  tfae_have 3 → 1 := fun H k' _ _ =>
    isNormalRing_tensorProduct_of_forall_finiteDimensional_isPurelyInseparable H k'
  tfae_have 1 → 4 := by
    intro H
    let f : kperf →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
    exact IsNormalRing.congr
      (Algebra.TensorProduct.congr (AlgEquiv.ofInjectiveField f) AlgEquiv.refl).symm.toRingEquiv
      (H ↥f.fieldRange)
  tfae_have 4 → 3 := by
    intro h k' _ _ _ _
    obtain ⟨f⟩ : Nonempty (k' →ₐ[k] kperf) := inferInstance
    let _ : Algebra k' kperf := f.toRingHom.toAlgebra
    have : IsScalarTower k k' kperf :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    exact isNormalRing_tensorProduct_of_isScalarTower h
  tfae_finish

end Stacks.GeometricallyNormal.Criterion

end

/-!
# Geometric normality is detected by finite purely inseparable base change

Let `k` be a field of exponential characteristic `p` and let `A` be a commutative `k`-algebra. Call
`A` *geometrically normal over `k`* when `k' ⊗[k] A` is a normal ring — every localization at a
prime is an integrally closed integral domain, Definition 00GV — for every field extension `k'/k`.
That is a condition on all extensions of `k`, transcendental ones included, and the content of this
file is that it is already detected by the finite purely inseparable ones, indeed by the single
extension `k^{perf}/k`. The reason is that a separable extension can be built from a smooth algebra
and a localization, and normality ascends along smooth ring maps and passes to localizations, while
it descends along faithfully flat ring maps; so the only extensions that can destroy normality are
the inseparable ones, and a general extension is a directed colimit of finitely generated ones,
along which normality is preserved.

Concretely the following are equivalent: normality of `k' ⊗[k] A` for every field extension `k'/k`;
for every finitely generated field extension `k'/k`; for every finite purely inseparable extension
`k'/k`; and normality of the single ring `k^{perf} ⊗[k] A`, for a perfect closure `k^{perf}` of
`k`.

## Main results

* `Algebra.isNormalRing_tensorProduct_tfae`: the four conditions above are equivalent.

## Implementation notes

Items (1)–(4) are the source's four conditions in its order. A normal ring is the library's
`IsNormalRing` (Definition 00GV): `Localization.AtPrime 𝔭` is an integral domain and is integrally
closed, for every prime `𝔭`. Mathlib has no predicate for this (its `IsIntegrallyClosed` file
records the gap as a TODO, citing that very tag), and the `IsDomain` conjunct is genuine content,
`IsIntegrallyClosed` being `IsIntegrallyClosedIn R (FractionRing R)` with no domain hypothesis. The
predicate is cited by name rather than inlined because the lemmas the source's proof runs through
are already stated for it: normality of a directed colimit of normal rings (Lemma 037D,
`directLimit_isNormalRing`), of a finite product of normal rings (Lemma 0CYA, `isNormalRing_pi`)
and of a polynomial ring over a normal ring (Lemma 00H1, `polynomial_ring_normal`).

"Finitely generated field extension" is `Algebra.EssFiniteType k k'`, Mathlib's spelling of finite
generation for field extensions (`IntermediateField.essFiniteType_iff`), as in the statement
of Lemma 037X in the library; it is not `Algebra.FiniteType`, which for fields is the strictly
stronger condition
of being generated as a `k`-algebra, and would make item (2) miss `k(t)`.

The test field of items (1)–(3) ranges over `Type u`, the universe of `k`, and this is the source's
condition for extensions in every universe: an element of `k'' ⊗[k] A` for `k''/k` in an arbitrary
universe already lies in the image of `k₀ ⊗[k] A` for the finitely generated subextension `k₀/k`
generated by the finitely many elements of `k''` occurring in a representative, `k₀` is
`k`-isomorphic to a field in `Type u`, and `k₀ ⊗[k] A → k'' ⊗[k] A` is injective because `A` is
flat over the field `k`; normality being a condition on localizations at primes, it transfers along
the resulting isomorphisms. Quantifying over a free universe variable instead would be *weaker*,
and would make the equivalence false: for `k` a field in `Type 1` of cardinality above the
continuum no field in `Type 0` carries a `k`-algebra structure at all, so items (1)–(3) would hold
vacuously while item (4) failed. The same applies to the finite purely inseparable extensions of
item (3), each of which is `k`-isomorphic to an intermediate field of `AlgebraicClosure k`.

The perfect closure enters abstractly rather than through a chosen construction, exactly as in the
library statement of Lemma 030V: `k^{perf}` is any field `kperf` with
`IsPerfectClosure (algebraMap k kperf) p` (and `PerfectRing kperf p`), so item (4) is about every
model at once. It is inhabited — `perfectClosure k (AlgebraicClosure k)` is one, and in exponential
characteristic `p = 1`, that is in characteristic zero, `k` itself is — so nothing is assumed away,
and its universe is left free because any two perfect closures of `k` are `k`-isomorphic whatever
their universes. For `p = 1` all four items read "`A` is a normal ring", and the lemma becomes the
statement that a normal algebra over a perfect field is geometrically normal.

`A` is assumed commutative, as in the source, since `IsNormalRing` is a condition on the
localizations of a commutative ring. Base changes are written with the extension on the left,
`k' ⊗[k] A`, as in Mathlib, where the source writes `k' ⊗_k A`.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead: `Field k`, `CommRing A` and `Algebra k A` are what form the base changes
and their localizations; `p` and `ExpChar k p` are used only to say what `kperf` is, and dropping
`IsPerfectClosure (algebraMap k kperf) p` would leave item (4) a statement about an unspecified
extension, false as an equivalence since `IsNormalRing (k ⊗[k] A)` is strictly weaker than
item (1). Inside the list, `EssFiniteType k k'` and `FiniteDimensional k k'` are restrictions of a
quantifier, not decoration: they are what make items (2) and (3) weaker than item (1), which is the
whole content of the lemma, and `IsPurelyInseparable k k'` likewise — with it dropped item (3)
would be item (2) for algebraic extensions.
(2) The scalars and the base are the source's: every tensor product is over `k`, every field in
sight is an extension of `k` through its `Algebra k` structure, and normality of `k' ⊗[k] A` is
integral closedness of each localization inside its own fraction field, not of `A` inside `Q(A)`.
(3) Where the source names a canonical map the statement pins it: `k^{perf}` is pinned by
`algebraMap k kperf` being a perfect closure, not by the mere existence of a perfect field over
`k`, and the `k`-algebra structure on each test field `k'` is the one its `Algebra k` instance
names.
(4) The instantiation is not degenerate: for `k = 𝔽_p(t)` and `A = k[x]/(x^p - t)`, a field and so
a normal domain, all four items fail — `k^{perf} ⊗[k] A` has the nonzero nilpotent
`t^{1/p} ⊗ 1 - 1 ⊗ x`, so it is not even reduced — whereas for `A = k[x]` all four hold, `k'[x]`
being a normal domain for every field `k'`. So no item is vacuous or automatic, and item (1) is
strictly stronger than "`A` is a normal ring".

## References

* [Stacks 037Z](https://stacks.math.columbia.edu/tag/037Z), in the section "Geometrically normal
  algebras"; a normal ring is Definition 00GV, and the lemma is what Definition 0380 turns into the
  notion "geometrically normal". The proof runs through descent of normality along faithfully flat
  ring maps (Lemma 033G), a directed colimit of normal rings (Lemma 037D), the diagram of purely
  inseparable extensions (Lemma 030R), separable extensions as fraction fields of smooth algebras
  (Lemma 037X), ascent of normality along smooth ring maps (Lemma 033C) and normality of a
  localization (Lemma 037C).
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- **Stacks 037Z.** Let `k` be a field of exponential characteristic `p` and let `A` be a
commutative `k`-algebra. The following are equivalent:
(1) `k' ⊗[k] A` is a normal ring for every field extension `k'/k`;
(2) `k' ⊗[k] A` is a normal ring for every finitely generated field extension `k'/k`;
(3) `k' ⊗[k] A` is a normal ring for every finite purely inseparable extension `k'/k`;
(4) `k^{perf} ⊗[k] A` is a normal ring, for a perfect closure `k^{perf}` of `k`. -/
@[stacks 037Z "The source's four conditions in its order, with a normal ring spelled by the
  library's `IsNormalRing` (Definition 00GV), a finitely generated field extension by
  `Algebra.EssFiniteType`, and the perfect closure taken abstractly, as `IsPerfectClosure`."]
public theorem isNormalRing_tensorProduct_tfae
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (A : Type v) [CommRing A] [Algebra k A]
    (kperf : Type w) [Field kperf] [Algebra k kperf] [ExpChar kperf p] [PerfectRing kperf p]
    [IsPerfectClosure (algebraMap k kperf) p] :
    [∀ (k' : Type u) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [EssFiniteType k k'],
        IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'], IsNormalRing (k' ⊗[k] A),
      IsNormalRing (kperf ⊗[k] A)].TFAE :=
  Stacks.GeometricallyNormal.Criterion.solution k p A kperf

end Algebra

end
