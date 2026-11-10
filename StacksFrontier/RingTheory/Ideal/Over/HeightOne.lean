module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.KrullAkizuki
import StacksFrontier.RingTheory.Artinian.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Generically finite maps are quasi-finite in codimension one

Let `A ⊆ B` be an extension of domains with `A` Noetherian, let `B` be of finite type over `A`,
and assume `B` is algebraic over `A`; for `B` of finite type over `A` the latter is exactly the
condition that the induced extension of fraction fields `Frac(A) ⊆ Frac(B)` be finite, i.e. that
`A → B` be *generically finite*. This file states Stacks 02MA: over a prime `p` of `A` of height
one there are at most finitely many primes of `B`, and every one of them has height one.

Geometrically: a dominant generically finite morphism of finite type between integral schemes,
with Noetherian target, is quasi-finite in codimension one, and codimension one is preserved. The
two failure modes it excludes are both codimension two phenomena on the target: over the height
two prime `(x, y)` the blowup chart `k[x, y] ⊆ k[x, y/x]` has a whole affine line, one chart of
the exceptional `ℙ¹`; and a fibre of positive dimension, such as the one of `k[x] ⊆ k[x, y]` over
`(x)`, occurs only when the extension is not generically finite.

The conclusion is a bound above only: the fibre over `p` may well be empty, as it is for
`ℤ ⊆ ℤ[1/2]` over `p = (2)`, since `B` is not assumed integral over `A`.

## Main results

* `Ideal.primesOver_finite_and_forall_height_eq_one`: for `A ⊆ B` an extension of domains with `A`
  Noetherian, `B` algebraic and of finite type over `A`, and `p` a prime of `A` of height one, the
  set of primes of `B` lying over `p` is finite and each of its members has height one.

## Implementation notes

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

Faithfulness. (1) No hypothesis is dead. `p.height = 1` is live: for `A = k[x, y] ⊆ B = k[x, y/x]`
and `p = (x, y)` of height two, every `(x, f(y/x))` with `f` irreducible lies over `p`, so the
fibre is infinite. `Algebra.IsAlgebraic A B` is live: for `A = k[x] ⊆ B = k[x, y]` and `p = (x)`
of height one the primes `(x, f(y))` lie over `p`, and they are infinite in number and of height
two. `FaithfulSMul A B` is live: for `A = ℤ`, `B = 𝔽₅` and `p = (5)` the only prime over `p` is
`(0)`, of height zero. `IsDomain B` is live: for `A = ℤ ⊆ B = ℤ × 𝔽₅` and `p = (5)` the prime
`ℤ × 0` lies over `p` and is a minimal prime of `B`, so of height zero. `Algebra.FiniteType A B`
is live: for `A = ℤ` and `B` the ring of all algebraic integers, `B` is an algebraic domain
extension of `ℤ` in which `(5)` has infinitely many primes above it, one over each prime above `5`
in each layer of a tower of number fields in which that number grows without bound.
`IsNoetherianRing A` enters twice, through the dimension formula Stacks 02IJ and through the
Noetherianity of the fibre `B ⊗_A κ(p)`, whose spectrum is finite because it is a Noetherian space
all of whose points are closed; no claim is made that it cannot be removed. (2) The scalars and
the base are the source's: `p` is an ideal of `A`, the primes and their heights are computed in
`B`, and the algebra structure is the given `A → B`; no localisation, base change or fraction
field occurs in the statement. (3) The map is pinned rather than merely assumed to exist: lying
over is `comap` along `algebraMap A B`, and the conclusion pins the value `1` of each height, not
merely finiteness of it. (4) The instantiation is not degenerate: for `A = ℤ ⊆ B = ℤ[i]` and
`p = (5) = (2 + i)(2 - i)` there are exactly two primes over `p`, both of height one.

## References

* [StackProject 02MA](https://stacks.math.columbia.edu/tag/02MA)

## Tags

height one prime, generically finite, quasi-finite, lying over
-/

section

namespace Stacks.PrimesOver.CodimensionOneFibre

/-- **Krull–Akizuki, dimension half.** With `R` a Noetherian domain of Krull dimension one,
`K = Frac(R)` and `L/K` finite, every intermediate ring `R ⊆ A ⊆ L` has all its nonzero primes
maximal. -/
private theorem dimensionLEOne_of_le_range
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra R L] [IsScalarTower R K L]
    (hdim : ringKrullDim R = 1)
    (A : Subring L) [Algebra R A] [IsScalarTower R A L] :
    Ring.DimensionLEOne A := by
  refine ⟨fun {Q} hQ0 hQ => ?_⟩
  obtain ⟨x, hx0, hxQ⟩ := exists_nonzero_mem_of_ne_bot R K L A Q hQ0
  have hlen := isFiniteLength_quotient_smul R K L hdim A hx0
  set J : Ideal A := Ideal.span {algebraMap R A x}
  have hJQ : J ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hxQ
  have hartR : IsArtinian R (A ⧸ J) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  have hartA : IsArtinian A (A ⧸ J) := isArtinian_of_tower R hartR
  have : IsArtinianRing (A ⧸ J) := isArtinian_of_tower A hartA
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ Q := Ideal.mk_ker.trans_le hJQ
  have hprime : (Ideal.map (Ideal.Quotient.mk J) Q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hmax : (Ideal.map (Ideal.Quotient.mk J) Q).IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime _
  have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective (K := Ideal.map (Ideal.Quotient.mk J) Q)
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJQ] at this

/-- For an extension of domains `A ⊆ B` which is algebraic and of finite type, the induced
extension of fraction fields `Frac(A) ⊆ Frac(B)` is finite. -/
private theorem finite_of_isAlgebraic_of_finiteType
    (A : Type*) [CommRing A] [IsDomain A] (B : Type*) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.IsAlgebraic A B] [Algebra.FiniteType A B]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower A K L] :
    Module.Finite K L := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B).FG)
  -- the images of a finite generating set of `B` over `A`
  set S : Set L := algebraMap B L '' (↑s : Set B)
  have hSfin : Finite (↑S : Set L) := (s.finite_toSet.image _).to_subtype
  -- every element of the image of `B` is integral over `K`
  have hint : ∀ b : B, IsIntegral K (algebraMap B L b) := by
    intro b
    obtain ⟨P, hP0, hPb⟩ : IsAlgebraic A (algebraMap B L b) :=
      (Algebra.IsAlgebraic.isAlgebraic (R := A) b).algebraMap
    exact IsAlgebraic.isIntegral (⟨P.map (algebraMap A K),
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective A K)).mpr hP0,
      by rwa [Polynomial.aeval_map_algebraMap]⟩ : IsAlgebraic K _)
  set E : IntermediateField K L := IntermediateField.adjoin K S
  have hBE : ∀ b : B, algebraMap B L b ∈ E := by
    intro b
    have hb : b ∈ Algebra.adjoin A (↑s : Set B) := by rw [hs]; exact Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K S ⟨y, hy, rfl⟩
    | algebraMap a =>
        rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
        exact E.algebraMap_mem _
    | add y z _ _ hy hz => simpa only [map_add] using E.add_mem hy hz
    | mul y z _ _ hy hz => simpa only [map_mul] using E.mul_mem hy hz
  have hEtop : E = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨b, c, _, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    exact E.div_mem (hBE b) (hBE c)
  have hfd : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (K := K) (S := S) (fun y hy => by
      obtain ⟨b, _, rfl⟩ := hy
      exact hint b)
  rw [hEtop] at hfd
  exact Module.Finite.equiv (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv

/-- In a localization `R` of `A` and an `A`-algebra `L` over `R`, `(a / s) * s = a` in `L`. -/
private theorem algebraMap_mk'_mul_algebraMap {A : Type*} [CommRing A] {M : Submonoid A}
    (R : Type*) [CommRing R] [Algebra A R] [IsLocalization M R]
    (L : Type*) [CommRing L] [Algebra A L] [Algebra R L] [IsScalarTower A R L]
    (a : A) (s : M) :
    algebraMap R L (IsLocalization.mk' R a s) * algebraMap A L s = algebraMap A L a := by
  rw [IsScalarTower.algebraMap_apply A R L s, ← map_mul, IsLocalization.mk'_spec,
    ← IsScalarTower.algebraMap_apply]

/-- For a prime `q` lying over `p`, the image of a localization of `A` at `p` in a common
`A`-algebra `L` lies in the image of a localization of `B` at `q`. -/
private theorem range_algebraMap_le_of_liesOver
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (R : Type*) [CommRing R] [Algebra A R] [IsLocalization.AtPrime R p]
    (BQ : Type*) [CommRing BQ] [Algebra B BQ] [IsLocalization.AtPrime BQ q]
    (L : Type*) [CommRing L] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    [Algebra R L] [IsScalarTower A R L] [Algebra BQ L] [IsScalarTower B BQ L] :
    (algebraMap R L).range ≤ (algebraMap BQ L).range := by
  rintro _ ⟨r, rfl⟩
  obtain ⟨⟨a, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl r
  have hover : p = Ideal.comap (algebraMap A B) q := Ideal.LiesOver.over
  have hy : algebraMap A B s ∈ q.primeCompl := by
    intro hmem
    have h2 : s ∈ Ideal.comap (algebraMap A B) q := hmem
    rw [← hover] at h2
    exact hs h2
  refine ⟨IsLocalization.mk' BQ (algebraMap A B a) ⟨algebraMap A B s, hy⟩, ?_⟩
  symm
  -- both sides become `a / s` in `L` after multiplying by the unit `s`
  have hsu : IsUnit (algebraMap A L s) := by
    rw [IsScalarTower.algebraMap_apply A R L]
    exact (IsLocalization.map_units R (⟨s, hs⟩ : p.primeCompl)).map _
  refine hsu.mul_left_inj.mp ?_
  have h1 := algebraMap_mk'_mul_algebraMap R L a (⟨s, hs⟩ : p.primeCompl)
  have h2 := algebraMap_mk'_mul_algebraMap (A := B) BQ L (algebraMap A B a)
    (⟨algebraMap A B s, hy⟩ : q.primeCompl)
  simp only [← IsScalarTower.algebraMap_apply A B L] at h2
  rw [h1, h2]

/-- **Krull–Akizuki, dimension half, for an embedded ring.** With `R` a Noetherian domain of
Krull dimension one, `K = Frac(R)` and `L/K` finite, a ring `S` embedded in `L` whose image
contains that of `R` has all its nonzero primes maximal. -/
private theorem dimensionLEOne_of_range_le
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra R L] [IsScalarTower R K L]
    (hdim : ringKrullDim R = 1)
    (S : Type*) [CommRing S] [Algebra S L] (hinj : Function.Injective (algebraMap S L))
    (hrange : (algebraMap R L).range ≤ (algebraMap S L).range) :
    Ring.DimensionLEOne S := by
  set A' : Subring L := (algebraMap S L).range
  let _ : Algebra R A' :=
    ((algebraMap R L).codRestrict A' fun r => hrange ⟨r, rfl⟩).toAlgebra
  have _ : IsScalarTower R A' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : Ring.DimensionLEOne A' := dimensionLEOne_of_le_range R K L hdim A'
  let e : S ≃+* A' := RingEquiv.ofBijective (algebraMap S L).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap S L).rangeRestrict_surjective⟩
  exact Ring.DimensionLEOne.of_ringEquiv e

/-- A prime `q` whose localization is a domain of dimension at most one has height at most
one. -/
private theorem height_le_one_of_dimensionLEOne
    {B : Type*} [CommRing B] (q : Ideal B) [q.IsPrime]
    (BQ : Type*) [CommRing BQ] [IsDomain BQ] [Algebra B BQ] [IsLocalization.AtPrime BQ q]
    (hdim : Ring.DimensionLEOne BQ) : q.height ≤ 1 := by
  -- read off the height of `q`
  have hkd : Ring.KrullDimLE 1 BQ := Ring.KrullDimLE.mk₁ fun I hI => by
    rcases eq_or_ne I ⊥ with rfl | h
    · exact Or.inl (by rw [IsDomain.minimalPrimes_eq_singleton_bot]; rfl)
    · exact Or.inr (hdim.maximalOfPrime h hI)
  have h1 : ringKrullDim BQ ≤ 1 := Ring.krullDimLE_iff.mp hkd
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q BQ] at h1
  exact_mod_cast h1

/-- **Krull–Akizuki bound on the fibre.** Under the hypotheses of Stacks 02MA, a prime of `B`
lying over the height one prime `p` has height at most one. -/
@[ega "IV 5.6.11" "partial"]
private theorem height_le_one_of_liesOver
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [Algebra.IsAlgebraic A B] [Algebra.FiniteType A B] (hp : p.height = 1)
    (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    q.height ≤ 1 := by
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : IsDomain A := Function.Injective.isDomain (algebraMap A B) hinj
  set K := FractionRing A
  set L := FractionRing B
  -- `A → L` and `K → L`
  have hinjAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A B L]
    exact (IsFractionRing.injective B L).comp hinj
  let algKL : Algebra K L := (IsFractionRing.lift (A := A) (K := K) hinjAL).toAlgebra
  have towAKL : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinjAL x).symm
  have hfinKL : Module.Finite K L := finite_of_isAlgebraic_of_finiteType A B K L
  -- the local rings
  set R := Localization.AtPrime p
  set BQ := Localization.AtPrime q
  have hunitsK : ∀ y : p.primeCompl, IsUnit (algebraMap A K (y : A)) := fun y =>
    IsLocalization.map_units K (⟨y, p.primeCompl_le_nonZeroDivisors y.2⟩ : nonZeroDivisors A)
  let algRK : Algebra R K := (IsLocalization.lift (M := p.primeCompl) hunitsK).toAlgebra
  have towARK : IsScalarTower A R K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunitsK x).symm
  have hfrRK : IsFractionRing R K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl R K
  have hunitsL : ∀ y : q.primeCompl, IsUnit (algebraMap B L (y : B)) := fun y =>
    IsLocalization.map_units L (⟨y, q.primeCompl_le_nonZeroDivisors y.2⟩ : nonZeroDivisors B)
  let algBQL : Algebra BQ L := (IsLocalization.lift (M := q.primeCompl) hunitsL).toAlgebra
  have towBBQL : IsScalarTower B BQ L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunitsL x).symm
  have hfrBQL : IsFractionRing BQ L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl BQ L
  -- `A_p → L`, and its image lands in the image of `B_q`
  have hunitsAL : ∀ y : p.primeCompl, IsUnit (algebraMap A L (y : A)) := by
    intro y
    have h := (hunitsK y).map (algebraMap K L)
    rwa [← IsScalarTower.algebraMap_apply A K L] at h
  let algRL : Algebra R L := (IsLocalization.lift (M := p.primeCompl) hunitsAL).toAlgebra
  have towARL : IsScalarTower A R L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunitsAL x).symm
  have towRKL : IsScalarTower R K L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine IsLocalization.ringHom_ext p.primeCompl ?_
    ext a
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A R L,
      ← IsScalarTower.algebraMap_apply A R K, ← IsScalarTower.algebraMap_apply A K L]
  -- Krull–Akizuki
  have hdimR : ringKrullDim R = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p R, hp]
    rfl
  have hinjBQ : Function.Injective (algebraMap BQ L) := IsFractionRing.injective BQ L
  have : IsDomain BQ := Function.Injective.isDomain (algebraMap BQ L) hinjBQ
  exact height_le_one_of_dimensionLEOne q BQ (dimensionLEOne_of_range_le R K L hdimR BQ hinjBQ
    (range_algebraMap_le_of_liesOver p q R BQ L))

end Stacks.PrimesOver.CodimensionOneFibre


@[expose] public section

open Stacks.PrimesOver.CodimensionOneFibre in
/-- **Generically finite maps are quasi-finite in codimension one.**
Let `A ⊆ B` be an extension of domains with `A` Noetherian, `B` algebraic and of finite type over
`A`, and let `p` be a prime of `A` of height one. Then only finitely many primes of `B` lie over
`p`, and each of them has height one. Algebraicity of `B` over `A` is, under the finite type
hypothesis, finiteness of the induced extension of fraction fields. -/
@[stacks 02MA "Finiteness of the induced extension of fraction fields is stated as
`Algebra.IsAlgebraic A B`, to which it is equivalent for `B` of finite type over `A`; see the
module docstring."]
public theorem Ideal.primesOver_finite_and_forall_height_eq_one {A : Type*} [CommRing A]
    [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] (B : Type*) [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsAlgebraic A B] [Algebra.FiniteType A B]
    (hp : p.height = 1) :
    (p.primesOver B).Finite ∧ ∀ q ∈ p.primesOver B, q.height = 1 := by
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : IsDomain A := Function.Injective.isDomain (algebraMap A B) hinj
  have hBnoeth : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have one_le_height : ∀ I : Ideal B, I ≠ ⊥ → 1 ≤ I.height := fun I hI =>
    Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hI)
  have hcomap : Ideal.comap (algebraMap A B) (⊥ : Ideal B) = ⊥ :=
    Ideal.comap_bot_of_injective (algebraMap A B) hinj
  have hp0 : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp
  -- every prime over `p` has height one
  have key : ∀ q ∈ p.primesOver B, q.height = 1 := by
    rintro q ⟨_, _⟩
    have hqbot : q ≠ ⊥ := by
      intro h
      refine hp0 ?_
      rw [Ideal.LiesOver.over (A := A) (p := p) (P := q), Ideal.under_def, h, hcomap]
    exact le_antisymm (height_le_one_of_liesOver p B hp q) (one_le_height q hqbot)
  refine ⟨?_, key⟩
  -- finiteness: a prime over `p` of height one is a minimal prime of `pB`
  have hpBne : Ideal.map (algebraMap A B) p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr hp0
  refine Set.Finite.subset
    (Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.map (algebraMap A B) p)) ?_
  rintro q ⟨hq1, hq2⟩
  have hh := key q ⟨hq1, hq2⟩
  have : q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by simp [hh]))
  exact Ideal.mem_minimalPrimes_of_height_le
    (Ideal.map_le_iff_le_comap.mpr (Ideal.LiesOver.over (A := A) (p := p) (P := q)).le)
    (hh.trans_le (one_le_height _ hpBne))
end


end

/-!
# Primes over a maximal ideal of a one-dimensional Noetherian domain

Proof of Stacks 031F. Let `R` be a Noetherian domain of Krull dimension at most one with
fraction field `K`, let `L/K` be a finite extension, and let `S` be a domain with fraction
field `L` which is an `R`-algebra compatibly with `K ⊆ L`. For a maximal ideal `m` of `R` the
fibre ring `S/mS` is a finite-dimensional `κ(m)`-vector space; consequently every prime of `S`
lying over `m` is maximal, there are finitely many of them, and each residue field extension
`κ(n)/κ(m)` is finite.

The mechanism is the finite length of `S/xS` for a nonzero `x ∈ m`: as an `R`-module `S` is a
submodule of the finite-dimensional `K`-vector space `L`, so the length bound of Stacks 00PE
applies; `S/mS` is a quotient of `S/xS`, hence a finite `R`-module, hence a finite module over
the field `κ(m)`. A finite-dimensional algebra over a field is Artinian (Stacks 00J6), and an
Artinian domain is a field, which turns the finiteness of `κ(n)/κ(m)` into the maximality of `n`;
the finiteness of the fibre is the finiteness of `Spec` of an Artinian ring.

## Main results

* `Stacks.PrimesOver.KrullAkizuki.solution`: the statement of Stacks 031F.

## Implementation notes

The whole content is the fibre lemma `module_finite_quotient_map`: if `m` is a maximal ideal of
`R` and the `R`-algebra `S` embeds `R`-linearly in a finite-dimensional `K`-vector space `V`, then
`S/mS` is a finite `R`-module. It is stated for an arbitrary `V` and an arbitrary injective
`R`-linear `S → V` rather than for `S ⊆ L`, since neither the multiplication on `V` nor the fact
that the embedding is a ring map plays any role; `solution` instantiates `V := L` and the
embedding by `IsScalarTower.toAlgHom R S L`, which is injective because `IsFractionRing S L`.
This is the source's "apply 00PE to `S ⊆ L ≅ K^{⊕n}`", with no choice of a `K`-basis of `L`
and no localization of `R` intervening: the length bound is already over `R`, and it needs only
`Ring.KrullDimLE 1 R` rather than `dim R = 1`.

That lemma splits into the two cases the weakened dimension hypothesis creates. For `m ≠ ⊥` it is
`module_finite_quotient_span_singleton`, the application of the length bound in the uniform form
`length_quotient_smul_le_finrank_mul` (Stacks 00PE/00PF, in
`StacksFrontier.RingTheory.KrullAkizuki`),
which bounds `length_R (M/xM) ≤ finrank K V · length_R (R/xR)` for an `R`-submodule `M` of `V`;
finite length gives Noetherian, hence finite. For `m = ⊥` the ring `R` is a field, there is no
nonzero `x ∈ m` to run the length argument with, and `S` itself is finite over `R` because
`R → K` is then onto: this is `module_finite_of_isField`. Both cases end in the same step, a
further quotient of a finite quotient — `module_finite_quotient_of_le`, which is also what
produces the finiteness of `κ(n) = S/n` over `R` from that of `S/mS`.

The source passes from `length_R (S/mS) < ∞` to `dim_{κ(m)} S/mS < ∞` by Stacks 00IY. Here the
finiteness is produced as `Module.Finite R (S/mS)` in the first place, and the descent of the base
along `R → κ(m)` is `Module.Finite.of_restrictScalars_finite`, which is the direction of 00IY(2)
that the argument uses. The structural input on Artinian rings that the source takes from
Stacks 00JB is used twice, in Mathlib's form: `IsArtinianRing.isField_of_isDomain` at `S/n`, which
makes the maximality of `n` a consequence of the finiteness of `κ(n)/κ(m)` rather than a separate
argument, and the instance `Finite (PrimeSpectrum _)` at `S/mS`. So this statement is proved without
depending on 00JB's statement.

## References

* [StacksProject 031F](https://stacks.math.columbia.edu/tag/031F)
-/

namespace Stacks.PrimesOver.KrullAkizuki

open Pointwise

/-- A further quotient of a quotient that is finite over the base is finite over the base. -/
private lemma module_finite_quotient_of_le {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} (h : I ≤ J) [Module.Finite R (S ⧸ I)] : Module.Finite R (S ⧸ J) :=
  Module.Finite.of_surjective (Ideal.Quotient.factorₐ R h).toLinearMap
    (Ideal.Quotient.factor_surjective h)

/-- If `R` is a field with fraction field `K`, then an `R`-module which embeds `R`-linearly in a
finite-dimensional `K`-vector space is a finite `R`-module.

This is the degenerate case `m = ⊥` of Stacks 031F: a Noetherian domain of Krull dimension at
most one may be a field, and then the length argument has no nonzero `x ∈ m` to run with. -/
private lemma module_finite_of_isField (R K V N : Type*) [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup N] [Module R N] (hR : IsField R)
    (f : N →ₗ[R] V) (hf : Function.Injective f) : Module.Finite R N := by
  let _ : Field R := hR.toField
  -- `R → K` is onto, since every nonzero element of `R` is already invertible.
  have : Module.Finite R K := Module.Finite.of_surjective (Algebra.linearMap R K)
    (IsField.localization_map_bijective zero_notMem_nonZeroDivisors hR).surjective
  have : Module.Finite R V := Module.Finite.trans K V
  exact Module.Finite.equiv (LinearEquiv.ofInjective f hf).symm

/-- **Stacks 00PE, applied to an embedding of `S` in a finite-dimensional `K`-vector space.** If
`R` is a Noetherian domain of Krull dimension at most one with fraction field `K`, and the
`R`-algebra `S` embeds `R`-linearly in a finite-dimensional `K`-vector space `V`, then `S/xS` is
a finite `R`-module for every nonzero `x : R`. -/
private lemma module_finite_quotient_span_singleton (R S K V : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (f : S →ₗ[R] V) (hf : Function.Injective f) {x : R} (hx : x ≠ 0) :
    Module.Finite R (S ⧸ Ideal.span {algebraMap R S x}) := by
  -- The length bound `length_R (M/xM) ≤ finrank K V · length_R (R/xR)` for `M = range f`, whose
  -- right-hand side is finite because `x` is a nonzerodivisor.
  have hlen : IsFiniteLength R (QuotSMulTop x (LinearMap.range f)) := by
    rw [← Module.length_ne_top_iff]
    refine ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top _) ?_)
      (length_quotient_smul_le_finrank_mul R K (LinearMap.range f) hx)
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero hx))
  have : IsNoetherian R (QuotSMulTop x S) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      ((QuotSMulTop.congr x (LinearEquiv.ofInjective f hf).symm).isFiniteLength hlen)).1
  have : Module.Finite R (QuotSMulTop x S) := ⟨IsNoetherian.noetherian ⊤⟩
  -- As an `R`-submodule of `S`, the ideal `xS` is `x • ⊤`.
  have hxS : (x • ⊤ : Submodule R S)
      = Submodule.restrictScalars R (Ideal.span {algebraMap R S x}) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map, Ideal.map_span,
      Set.image_singleton]
  exact Module.Finite.equiv ((Submodule.quotEquivOfEq _ _ hxS).trans
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R S x})))

/-- **The fibre of Stacks 031F.** If `R` is a Noetherian domain of Krull dimension at most one
with fraction field `K`, the `R`-algebra `S` embeds `R`-linearly in a finite-dimensional
`K`-vector space `V`, and `m` is a maximal ideal of `R`, then the fibre ring `S/mS` is a finite
`R`-module.

For `m ≠ ⊥` this is the length bound applied to a nonzero `x ∈ m`, since `S/mS` is a quotient of
`S/xS`; for `m = ⊥` the ring `R` is a field and already `S` is finite over `R`. -/
private lemma module_finite_quotient_map (R S K V : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (f : S →ₗ[R] V) (hf : Function.Injective f) (m : Ideal R) [m.IsMaximal] :
    Module.Finite R (S ⧸ m.map (algebraMap R S)) := by
  rcases eq_or_ne m ⊥ with rfl | hm
  · have := module_finite_of_isField R K V S (Ring.isField_iff_maximal_bot.mpr ‹_›) f hf
    exact Module.Finite.quotient R _
  · obtain ⟨x, hxm, hx⟩ := (Submodule.ne_bot_iff m).mp hm
    have := module_finite_quotient_span_singleton R S K V f hf hx
    exact module_finite_quotient_of_le
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hxm))

/-- If the fibre ring `S/J` has finitely many primes and every prime of `S` lying over `m`
contains `J`, then only finitely many primes of `S` lie over `m`: such a prime is the contraction
of its image in `S/J`. -/
private lemma finite_primesOver_of_le {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) (J : Ideal S) [Finite (PrimeSpectrum (S ⧸ J))]
    (hJ : ∀ n ∈ m.primesOver S, J ≤ n) : (m.primesOver S).Finite := by
  refine Set.Finite.subset (Set.finite_range fun p : PrimeSpectrum (S ⧸ J) =>
    p.asIdeal.comap (Ideal.Quotient.mk J)) fun n hn => ?_
  have := hn.1
  exact ⟨⟨n.map (Ideal.Quotient.mk J), Ideal.isPrime_map_quotientMk_of_isPrime (hJ n hn)⟩,
    Ideal.comap_map_mk (hJ n hn)⟩

/-- For a maximal ideal `m` of a Noetherian domain `R` of dimension at most one, every prime of `S`
over `m` is maximal, only finitely many primes of `S` lie over `m`, each quotient `S/n` by such a
prime is finite over `R/m`, and so is `S/mS`. -/
public theorem solution
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L]
    [IsScalarTower R S L] (m : Ideal R) [m.IsMaximal] :
    (∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], n.IsMaximal) ∧
      (m.primesOver S).Finite ∧
      (∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], Module.Finite (R ⧸ m) (S ⧸ n)) ∧
      Module.Finite (R ⧸ m) (S ⧸ m.map (algebraMap R S)) := by
  -- Every prime of `S` lying over `m` contains `mS`.
  have hle : ∀ n : Ideal S, n.LiesOver m → m.map (algebraMap R S) ≤ n := fun n hn =>
    Ideal.map_le_iff_le_comap.mpr hn.over.le
  have hfibre : Module.Finite R (S ⧸ m.map (algebraMap R S)) :=
    module_finite_quotient_map R S K L (IsScalarTower.toAlgHom R S L).toLinearMap
      (IsFractionRing.injective S L) m
  -- `S/mS` and each `S/n` are finite-dimensional `κ(m)`-algebras, hence Artinian rings.
  let _ : Field (R ⧸ m) := Ideal.Quotient.field m
  have hres : ∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], Module.Finite (R ⧸ m) (S ⧸ n) := by
    intro n _ hn
    have := module_finite_quotient_of_le (R := R) (hle n hn)
    exact Module.Finite.of_restrictScalars_finite R (R ⧸ m) (S ⧸ n)
  have hfin : Module.Finite (R ⧸ m) (S ⧸ m.map (algebraMap R S)) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ m) _
  have : IsArtinianRing (S ⧸ m.map (algebraMap R S)) :=
    finite_dimensional_algebra_is_artinian (R ⧸ m) _
  refine ⟨fun n _ _ => ?_, finite_primesOver_of_le m _ fun n hn => hle n hn.2, hres, hfin⟩
  -- `S/n` is an Artinian domain, hence a field.
  have := hres n
  have : IsArtinianRing (S ⧸ n) := finite_dimensional_algebra_is_artinian (R ⧸ m) _
  exact Ideal.Quotient.maximal_of_isField n (IsArtinianRing.isField_of_isDomain _)

end Stacks.PrimesOver.KrullAkizuki

/-!
# Primes over a maximal ideal of a one-dimensional Noetherian domain

Let `R` be a Noetherian domain of Krull dimension at most one with fraction field `K`, let `L/K`
be a finite field extension, and let `S` be a domain sitting in between, that is, an `R`-algebra
which is a domain with fraction field `L`. Then for every maximal ideal `m` of `R` the fibre ring
`S/mS` is a finite-dimensional `κ(m) = R/m`-vector space. Consequently every prime `n` of `S`
lying over `m` is maximal, there are only finitely many such primes, and each residue field
extension `κ(n)/κ(m)` is finite.

The mechanism is the finite length of `S/xS`: choosing a nonzero `x ∈ m`, the ring `S` is an
`R`-submodule of `L ≅ K^{[L : K]}`, so `S/xS` has finite length over `R`, hence so does its
quotient `S/mS`; the latter is killed by `m`, so its length over `R` is its dimension over the
field `κ(m)`. A finite-dimensional algebra over a field is Artinian, which gives the maximality
of the primes over `m` and their finiteness, and the finiteness of `κ(n)/κ(m)` is the
finite-dimensionality itself, `κ(n) = S/n` being a quotient of `S/mS`.

Note that `S` is not assumed to be of finite type over `R`: that is the point of this lemma and
of the Krull–Akizuki circle of results it belongs to, where `S` is typically the integral closure
of `R` in `L` and can fail to be a finite `R`-module.

## Main results

* `Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient`: the primes of `S` over a
  maximal ideal `m` of `R` are maximal and finite in number, their residue field extensions over
  `κ(m)` are finite, and `S/mS` is a finite-dimensional `κ(m)`-vector space.

## Implementation notes

The source assumes `R` Noetherian local of dimension one and speaks of *the* maximal ideal
`m`; here `m` is an arbitrary maximal ideal of a Noetherian domain with `Ring.KrullDimLE 1 R`.
The local case is the instantiation `m := IsLocalRing.maximalIdeal R`, and conversely the general
statement follows from the local one by localizing at `m`: neither the set of primes of `S` over
`m` nor the residue fields involved change under `R → R_m`, `S → S ⊗[R] R_m` (a domain with the
same fraction field `L`). The generality is not decoration: the dependents 09IG, 09E5 and 09II
apply this lemma at every maximal ideal of a ring that is not local.

The source's `dim(R) = 1` is weakened to `Ring.KrullDimLE 1 R`, Mathlib's spelling of `dim R ≤ 1`,
which for a domain is equivalent to `Ring.DimensionLEOne R` (every nonzero prime is maximal), the
form carried by `IsDedekindRing` and used in the statement of 09IG. Dimension exactly one is used
by no conclusion: the degenerate case this admits is `R` a field, where `m = ⊥`, `K = R`, `S` is a
domain finite-dimensional over `K` hence a field, and all four conclusions are immediate. The
hypotheses are, on the other hand, sharp in the dimension: for `R = k[x, y]_{(x, y)}`, which has
dimension two, and `S = R[y/x] ⊆ L = K`, one has `mS = xS` with `S/xS ≅ k[y/x]`, so that `xS` is a
non-maximal prime lying over `m` and infinitely many primes lie over `m`.

`K` and `L` are abstract fraction fields (`IsFractionRing`) rather than the constructions
`FractionRing R` and `FractionRing S`. The source's inclusions `R ⊆ S` and `K ⊆ L` are not
assumed: `FaithfulSMul R S` follows from the two scalar towers, since `algebraMap R L` factors as
the injective composite `R → K → L`; and `[Algebra K L]` with `[IsScalarTower R K L]` pins the
`R`-algebra map `K → L` uniquely (by the universal property of the localization `K`), so no
choice of an embedding is left open. It is injective because `K` is a field.

The residue fields are written as the quotients `R ⧸ m` and `S ⧸ n`, which is legitimate for
`S ⧸ n` precisely because of the first conclusion, `n` being maximal; the `Ideal.ResidueField`
form `Module.Finite m.ResidueField n.ResidueField` used by Mathlib's quasi-finiteness API follows
through `Ideal.bijective_algebraMap_quotient_residueField`. The `(R ⧸ m)`-algebra structure on
`S ⧸ n` is the canonical `Ideal.Quotient.algebraOfLiesOver`, and `Ideal.primesOver m S` is
`{n | n.IsPrime ∧ n.LiesOver m}`, so that the second conclusion is the finiteness of the fibre of
`Spec(S) → Spec(R)` over `m`.

The last conjunct, `Module.Finite (R ⧸ m) (S ⧸ mS)`, is what the author's proof establishes
before deducing the three assertions of the tag, and it is strictly stronger than their
conjunction (finitely many primes, all maximal, with finite residue field extensions do not bound
the nilpotents of `S/mS`). It is recorded because a dependent that packages fibres as
`Algebra.QuasiFinite R S` — Mathlib's form of tag 00PL, used in the statement of 09IG — needs
exactly the finite-dimensionality of `κ(m) ⊗[R] S` at the maximal ideals, and because from it the
second conclusion is also available as `Algebra.QuasiFinite.finite_primesOver`.

Faithfulness. (1) No hypothesis is dead: `IsNoetherianRing R` and `Ring.KrullDimLE 1 R` are what
make `S/xS` of finite length over `R` for `0 ≠ x ∈ m`, `FiniteDimensional K L` is what makes `S`
a submodule of a finite-dimensional `K`-space, `IsFractionRing R K` and `IsFractionRing S L` fix
`K` and `L` as the fraction fields of `R` and `S`, `IsDomain R` and `IsDomain S` are the source's
hypothesis that both rings are domains, and `m.IsMaximal` is needed for `S/mS` to be an algebra
over a field (over a non-maximal prime the fibre can be infinite-dimensional). (2) The scalars
and the base are the source's: the finiteness assertions are over `κ(m) = R ⧸ m` and the primes
are ideals of `S` itself, not of a localization, and no conclusion is phrased over `K` or `L`.
(3) The maps the source names are pinned rather than merely assumed to exist: `K → L` by
`IsScalarTower R K L`, the inclusion of `S` in `L` by `IsFractionRing S L` together with
`IsScalarTower R S L`, and `κ(m) → κ(n)` by `Ideal.Quotient.algebraOfLiesOver`. (4) The
instantiation is not degenerate: `R = ℤ`, `K = ℚ`, `L = ℚ(i)`, `S = ℤ[i]` and `m = (5)` gives two
primes `(2 ± i)` over `m`, each maximal with residue field `𝔽₅`, and `S/mS ≅ 𝔽₅ × 𝔽₅` of
dimension `2 = [L : K]`; `S = ℤ[1/2]` with `m = (2)` gives an empty fibre and `S/mS = 0`, which is
why the second conclusion is a `Set.Finite` and not a cardinality bound.

## References

* [StacksProject 031F](https://stacks.math.columbia.edu/tag/031F)

## Tags

Krull-Akizuki, residue field extension, quasi-finite, dimension one, Noetherian domain
-/

namespace Ideal

/-- Let `R` be a Noetherian domain of Krull dimension at most one with fraction field `K`, let
`L/K` be a finite field extension, and let `S` be a domain with fraction field `L` which is an
`R`-algebra compatibly with `K ⊆ L`. Then, for every maximal ideal `m` of `R`, every prime `n` of
`S` lying over `m` is maximal, only finitely many primes of `S` lie over `m`, each residue field
extension `κ(n)/κ(m)` is finite, and moreover `S/mS` is a finite-dimensional `κ(m)`-vector
space. -/
@[stacks 031F "The three assertions of the tag, for an arbitrary maximal ideal `m` of a Noetherian
domain with `Ring.KrullDimLE 1` rather than for the maximal ideal of a local ring of dimension
one, together with the finite-dimensionality of `S/mS` over `κ(m)` from which the author's proof
deduces them. See the module docstring."]
public theorem isMaximal_and_finite_primesOver_and_module_finite_quotient
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L]
    [IsScalarTower R S L] (m : Ideal R) [m.IsMaximal] :
    (∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], n.IsMaximal) ∧
      (m.primesOver S).Finite ∧
      (∀ (n : Ideal S) [n.IsPrime] [n.LiesOver m], Module.Finite (R ⧸ m) (S ⧸ n)) ∧
      Module.Finite (R ⧸ m) (S ⧸ m.map (algebraMap R S)) :=
  Stacks.PrimesOver.KrullAkizuki.solution R S K L m

end Ideal

/-!
# Residue field extensions of a local homomorphism in codimension one

Let `A` be a Noetherian local ring of Krull dimension at most one and let `B` be a local
`A`-algebra, the structure map being a local homomorphism. If `q` is a prime of `B` lying over a
prime `p` of `A` for which the residue field extension `κ(p) ⊆ κ(q)` is finite, then the residue
field extension `κ(A) ⊆ κ(B)` of the closed points is finite as well.

This is the local form of the finiteness half of Krull–Akizuki, and the step which upgrades
generic finiteness to quasi-finiteness over a point of codimension one: geometrically, `p` is the
image of a generic point of `Spec(B)`, and the conclusion says that the closed point of `Spec(B)`
is closed in its fibre over the closed point of `Spec(A)`.

## Main results

* `IsLocalRing.finite_residueField_of_isFractionRing_quotient`: the statement with the two
  residue fields `κ(p)` and `κ(q)` given as abstract fraction fields of `A ⧸ p` and `B ⧸ q`.
* `IsLocalRing.finite_residueField_of_finite_residueField_liesOver`: the same with the two
  residue fields taken to be `Ideal.ResidueField`.
* `IsLocalRing.finite_residueField_of_quasiFiniteAt`: the form in which the hypothesis at `p`
  and `q` is quasi-finiteness of `B` over `A` at `q`.

## Implementation notes

The whole content is `Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient`
(Stacks 031F) applied to the pair of domains `A ⧸ p ⊆ B ⧸ q`: the first is Noetherian of Krull
dimension at most one because `A` is, and `κ(p)` and `κ(q)` are precisely their fraction fields.
The maximal ideal `m` of `A ⧸ p` is the image of the maximal ideal of `A`, the prime of `B ⧸ q`
lying over it is the image of the maximal ideal of `B` — which does lie over it because the
structure map is a local homomorphism — and the two iterated quotients `(A ⧸ p) ⧸ m` and
`(B ⧸ q) ⧸ n` are the residue fields of `A` and of `B` by `DoubleQuot.quotQuotEquivQuotOfLE`.

No lower bound on the dimension of `A` is needed, and `p` is not required to differ from the
maximal ideal of `A`. In that degenerate case the statement is the degenerate case of 031F in
which the base is a field: `B ⧸ q` is then a domain which is finite-dimensional over `κ(A)`,
hence a field, so `q` is the maximal ideal of `B`.

## References

* [Stacks Project, Tag 00PG](https://stacks.math.columbia.edu/tag/00PG)
* [Stacks Project, Tag 031F](https://stacks.math.columbia.edu/tag/031F)
-/

namespace IsLocalRing

/-- **Krull–Akizuki, local residue field form.** Let `A` be a Noetherian local ring of Krull
dimension at most one and let `B` be a local `A`-algebra whose structure map is a local
homomorphism. Let `q` be a prime of `B` lying over a prime `p` of `A`, and let `K` and `L` be
fraction fields of `A ⧸ p` and of `B ⧸ q`, that is, the residue fields `κ(p)` and `κ(q)`, with
`L` finite over `K`. Then the residue field of `B` is finite over the residue field of `A`. -/
public theorem finite_residueField_of_isFractionRing_quotient
    {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (K L : Type*) [Field K] [Field L]
    [Algebra (A ⧸ p) K] [IsFractionRing (A ⧸ p) K]
    [Algebra (B ⧸ q) L] [IsFractionRing (B ⧸ q) L]
    [Algebra K L] [Algebra (A ⧸ p) L] [IsScalarTower (A ⧸ p) K L]
    [IsScalarTower (A ⧸ p) (B ⧸ q) L] [Module.Finite K L]
    (hdim : ringKrullDim A ≤ 1) :
    Module.Finite (ResidueField A) (ResidueField B) := by
  have hpm : p ≤ maximalIdeal A := le_maximalIdeal_of_isPrime p
  have hqm : q ≤ maximalIdeal B := le_maximalIdeal_of_isPrime q
  have hkd : Ring.KrullDimLE 1 (A ⧸ p) :=
    Ring.krullDimLE_iff.mpr ((ringKrullDim_quotient_le p).trans (by exact_mod_cast hdim))
  have hm : ((maximalIdeal A).map (Ideal.Quotient.mk p)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (Ideal.mk_ker.trans_le hpm)
  have hn : ((maximalIdeal B).map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (Ideal.mk_ker.trans_le hqm)
  have hlo : ((maximalIdeal B).map (Ideal.Quotient.mk q)).LiesOver
      ((maximalIdeal A).map (Ideal.Quotient.mk p)) := by
    refine ⟨Ideal.ext fun a => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.mem_quotient_iff_mem hpm, Ideal.mem_comap,
      Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.mem_quotient_iff_mem hqm,
      ← Ideal.mem_comap, ← Ideal.under_def,
      ((maximalIdeal B).over_def (maximalIdeal A)).symm]
  have := (Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient (A ⧸ p) (B ⧸ q) K L
    ((maximalIdeal A).map (Ideal.Quotient.mk p))).2.2.1
    ((maximalIdeal B).map (Ideal.Quotient.mk q))
  refine Module.Finite.of_equiv_equiv (DoubleQuot.quotQuotEquivQuotOfLE hpm)
    (DoubleQuot.quotQuotEquivQuotOfLE hqm) (RingHom.ext fun a => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply]
  rfl

/-- **Krull–Akizuki, local residue field form.** Let `A` be a Noetherian local ring of Krull
dimension at most one and let `B` be a local `A`-algebra whose structure map is a local
homomorphism. If `q` is a prime of `B` lying over a prime `p` of `A` and `κ(q)` is finite over
`κ(p)`, then the residue field of `B` is finite over the residue field of `A`. -/
public theorem finite_residueField_of_finite_residueField_liesOver
    {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q)]
    [Module.Finite p.ResidueField q.ResidueField]
    (hdim : ringKrullDim A ≤ 1) :
    Module.Finite (ResidueField A) (ResidueField B) := by
  let _ : Algebra (A ⧸ p) q.ResidueField :=
    ((algebraMap p.ResidueField q.ResidueField).comp
      (algebraMap (A ⧸ p) p.ResidueField)).toAlgebra
  have _ : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change algebraMap p.ResidueField q.ResidueField
        (algebraMap (A ⧸ p) p.ResidueField (Ideal.Quotient.mk p a)) = _
    rw [Ideal.algebraMap_quotient_residueField_mk, ← IsScalarTower.algebraMap_apply A
      p.ResidueField q.ResidueField, Ideal.Quotient.algebraMap_mk_of_liesOver,
      Ideal.algebraMap_quotient_residueField_mk, ← IsScalarTower.algebraMap_apply A B]
  exact finite_residueField_of_isFractionRing_quotient p q p.ResidueField q.ResidueField hdim

/-- **Krull–Akizuki, local quasi-finiteness form.** Let `A` be a Noetherian local ring of Krull
dimension at most one and let `B` be a local `A`-algebra whose structure map is a local
homomorphism. If `B` is quasi-finite over `A` at some prime `q` of `B`, then the residue field
of `B` is finite over the residue field of `A`. -/
public theorem finite_residueField_of_quasiFiniteAt
    {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (q : Ideal B) [q.IsPrime] [Algebra.QuasiFiniteAt A q]
    (hdim : ringKrullDim A ≤ 1) :
    Module.Finite (ResidueField A) (ResidueField B) := by
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  have _ : IsScalarTower A (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
    inferInstance
  exact finite_residueField_of_finite_residueField_liesOver (q.under A) q hdim

end IsLocalRing
