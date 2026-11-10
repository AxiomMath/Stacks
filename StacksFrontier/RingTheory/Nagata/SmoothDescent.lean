module

import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Unramified.LocalStructure

public import StacksFrontier.RingTheory.Flat.ReducedFibres
public import StacksFrontier.RingTheory.Localization.InjectiveOfLocalization
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.Nagata.IntegralClosure

/-!
# Nagata descends along a smooth ring map surjective on spectra

Let `R → S` be a smooth ring map for which `Spec S → Spec R` is surjective. If `S` is a Nagata
ring, then so is `R`. This is Stacks 0354.

The proof is the source's. The pair of hypotheses on `R → S` says exactly that the map is smooth
and faithfully flat, so `R` is Noetherian by Lemma 033E. For the Japanese half, a quotient `R ⧸ 𝔭`
by a prime is a domain of finite type over `R`, so it suffices to see that every domain `A` of
finite type over `R` is N-2, and by Lemma 0351 it suffices to see that every such `A` is N-1.
Given `A`, put `B = A ⊗_R S`. Then `B` is of finite type over `S`, hence Nagata (Proposition
0334); the ring map `A → B` is smooth, being a base change of `R → S`, so `B` is reduced (Lemma
033B) and faithfully flat over `A`. A reduced Noetherian Nagata ring has finite integral closure
in its total ring of fractions, which is the content the source extracts from the description of
`Q(B)` as the product of the residue fields at the minimal primes. Hence the integral closure `A'`
of `A` in its fraction field satisfies: `B ⊗_A A'` embeds `B`-linearly into that finite
`B`-module, so it is a finite `B`-module, and faithful flatness of `A → B` descends this to
finiteness of `A'` over `A`.

## Main results

* `Stacks.Nagata.SmoothDescent.solution`: the statement of Stacks 0354.

## Implementation notes

Three steps of the source's route are private lemmas here.

* `isJapaneseRing_of_forall_isN1` is Lemma 0351: for a ring `R` it is enough, in order that every
  domain of finite type over `R` be N-2, that every domain of finite type over `R` be N-1. It is
  assembled from the two library lemmas `exists_clearedBasis_spanning` and
  `isN2_of_isN1_of_clearedBasis`, which are the source's argument — replace a finite extension `L`
  of `Frac A` by a finite ring extension `A ⊆ A' ⊆ L` with `Frac A' = L`, use N-1 for `A'`, and
  transport the resulting finiteness back along `A ⊆ A'`.
* `isN1_of_faithfullyFlat_of_isN1` is the ring-theoretic core, and it is stated for an arbitrary
  faithfully flat algebra `B` over a domain `A` with `B` Noetherian and N-1, since that is all the
  argument uses: neither smoothness, nor reducedness of `B`, nor the base `R` enters it. It
  replaces the source's description of the total ring of fractions of `B` as the product of the
  residue fields at the minimal primes (Lemmas 02LX, 00EU and 030C) by N-1 for `B` itself, which
  is what the argument consumes and which Lemma 03GH supplies from `B` being Nagata and reduced.
* `isReduced_of_smooth_of_isNoetherianRing` is the Noetherian case of Lemma 033B, which is all the
  tagged statement needs, `A` being of finite type over the Noetherian ring `R`. It is proved from
  the local structure of a smooth ring map rather than from the source's route through
  regularity: by
  `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` every prime of `B` has a neighbourhood
  `B_f` which is étale over a polynomial ring `A[x_1, …, x_n]`, and `isReduced_of_etale` — the
  general statement that an étale algebra over a reduced Noetherian ring is reduced, obtained by
  feeding the reducedness of a formally unramified algebra over a field
  (`Algebra.FormallyUnramified.isReduced_of_field`) to Lemma 0C21 — makes each `B_f` reduced. A
  nilpotent of `B` then has an annihilator meeting the complement of every maximal ideal, so it
  vanishes. Neither `isReduced_of_etale` nor the ascent of reducedness along a smooth ring map is
  in Mathlib.

The source's injection `Q(A) ⊗_A B = (A ∖ {0})⁻¹ B → Q(B)` is `Algebra.TensorProduct.lift` of
`B → Q(B)` and of the localization map `Frac A → Q(B)`, which exists because a nonzerodivisor of
`A` acts injectively on the flat module `B`; its injectivity is
`injective_of_isLocalization_of_injective`, the general statement that a ring map out of a
localization `S` of `R` that is compatible with `R → T` is injective as soon as `R → T` is. That
statement is missing from Mathlib and would belong beside `IsLocalization.lift_injective_iff`.

The `S`-algebra structure on `A ⊗_R S` is `Algebra.TensorProduct.rightAlgebra`, made a local
instance, and `tensorRightComm` transports finiteness of type over `S` from `S ⊗_R A`, where it is
an instance. Taking the tensor product in this order is what makes `Algebra.Smooth A (A ⊗_R S)`
and `Module.FaithfullyFlat A (A ⊗_R S)` instances as well.

## References

* [StacksProject 0354](https://stacks.math.columbia.edu/tag/0354)
* [StacksProject 0351](https://stacks.math.columbia.edu/tag/0351)
* [StacksProject 0334](https://stacks.math.columbia.edu/tag/0334)
* [StacksProject 033B](https://stacks.math.columbia.edu/tag/033B)
* [StacksProject 033E](https://stacks.math.columbia.edu/tag/033E)
* [StacksProject 0C21](https://stacks.math.columbia.edu/tag/0C21)
* [StacksProject 03GH](https://stacks.math.columbia.edu/tag/03GH)
-/

@[expose] public section

universe u

namespace Stacks.Nagata.SmoothDescent

open TensorProduct


attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A domain that is N-2 is N-1: test the definition on the fraction field itself. -/
private theorem isN1_of_isJapaneseRing {A : Type u} [CommRing A] [IsDomain A]
    (h : IsJapaneseRing A) : IsN1 A :=
  h.finite (FractionRing A)

/-- **Stacks 0351.** If every domain of finite type over `R` is N-1, then every domain of finite
type over `R` is N-2; that is, `R` is universally Japanese. -/
private theorem isJapaneseRing_of_forall_isN1 {R : Type u} [CommRing R]
    (h : ∀ (C : Type u) [CommRing C] [IsDomain C] [Algebra R C] [Algebra.FiniteType R C], IsN1 C)
    (A : Type u) [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A] :
    IsJapaneseRing A := by
  refine { finite := fun L _ _ _ _ _ => ?_ }
  obtain ⟨s, hs, hspan⟩ := exists_clearedBasis_spanning (S := A) (K := FractionRing A) (L := L)
    (1 : A) one_ne_zero
  exact isN2_of_isN1_of_clearedBasis (R := R) (fun T _ _ _ _ => h T) s
    (fun x hx => by obtain ⟨Q, hQm, -, hQe⟩ := hs x hx; exact ⟨Q, hQm, hQe⟩) hspan

/-- An étale algebra over a reduced Noetherian ring is reduced.

Each fibre `κ(𝔭) ⊗_P C` is formally unramified over the field `κ(𝔭)`, hence reduced
(`Algebra.FormallyUnramified.isReduced_of_field`), and reducedness ascends along a flat ring map
of Noetherian rings with reduced fibres (Lemma 0C21). -/
private theorem isReduced_of_etale (P C : Type*) [CommRing P] [CommRing C] [Algebra P C]
    [IsNoetherianRing P] [IsReduced P] [Algebra.Etale P C] : IsReduced C :=
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing P C
  isReduced_of_flat_of_isReduced_fiber (R := P) (S := C) fun p _ =>
    Algebra.FormallyUnramified.isReduced_of_field p.ResidueField (p.Fiber C)

/-- **Stacks 033B** in the Noetherian case: a smooth algebra over a reduced Noetherian ring is
reduced.

Every prime `𝔭` of `B` has `f ∉ 𝔭` with `B_f` étale over a polynomial ring over `A`
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`), so `B_f` is reduced by
`isReduced_of_etale`. A nilpotent `x` of `B` therefore has, for every maximal ideal `𝔪`, a power of
some `f ∉ 𝔪` annihilating it; its annihilator lies in no maximal ideal, so `x = 0`. -/
private theorem isReduced_of_smooth_of_isNoetherianRing (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsReduced A] [Algebra.Smooth A B] : IsReduced B := by
  have key : ∀ p : Ideal B, p.IsPrime → ∃ f ∉ p, IsReduced (Localization.Away f) := by
    intro p hp
    obtain ⟨f, hf, n, alg, htow, hstd⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (S := B) (p := p)
    have : Algebra.Etale (MvPolynomial (Fin n) A) (Localization.Away f) :=
      Algebra.Etale.of_formallyUnramified_of_flat
    exact ⟨f, hf, isReduced_of_etale (MvPolynomial (Fin n) A) (Localization.Away f)⟩
  refine ⟨fun x hx => ?_⟩
  have hJ : (Submodule.span B {x}).annihilator = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hred⟩ := key m hm.isPrime
    have hx0 : algebraMap B (Localization.Away f) x = 0 := (hx.map _).eq_zero
    obtain ⟨⟨g, k, rfl⟩, hgx⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) x).mp hx0
    exact hf (hm.isPrime.mem_of_pow_mem k
      (hle ((Submodule.mem_annihilator_span_singleton x _).mpr (by simpa using hgx))))
  have h1 : (1 : B) ∈ (Submodule.span B {x}).annihilator := hJ ▸ Submodule.mem_top
  simpa using (Submodule.mem_annihilator_span_singleton x 1).mp h1

/-- A reduced Nagata ring is N-1: its integral closure in its total ring of fractions is a finite
module over it, by Lemma 03GH applied to the localization `B → Q(B)`. -/
private theorem isN1_of_isNagataRing (B : Type u) [CommRing B] [IsReduced B]
    (hB : IsNagataRing B) : IsN1 B := by
  have : IsNoetherianRing B := hB.1
  exact IsIntegralClosure.finite_of_essFiniteType_of_isReduced (S := FractionRing B)
    (A := ↥(integralClosure B (FractionRing B))) hB.2

/-- The ring-theoretic core of Stacks 0354: a domain `A` admitting a faithfully flat Noetherian
algebra `B` which is N-1 is itself N-1.

The integral closure `A'` of `A` in `Frac A` has `B ⊗_A A'` embedded `B`-linearly in the finite
`B`-module `integralClosure B (Q B)`, so `B ⊗_A A'` is a finite `B`-module and `A'` is a finite
`A`-module by faithfully flat descent. -/
private theorem isN1_of_faithfullyFlat_of_isN1 (A B : Type u) [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] [IsNoetherianRing B]
    (hB : IsN1 B) : IsN1 A := by
  have hnzd : ∀ y : nonZeroDivisors A, algebraMap A B (y : A) ∈ nonZeroDivisors B := fun y => by
    have key : ∀ z : B, algebraMap A B (y : A) * z = 0 → z = 0 := fun z hz => by
      refine Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) y.2 (a₁ := z) (a₂ := 0) ?_
      simpa [Algebra.smul_def] using hz
    exact ⟨fun z hz => key z hz, fun z hz => key z (by rw [mul_comm]; exact hz)⟩
  have hunit : ∀ y : nonZeroDivisors A, IsUnit (algebraMap A (FractionRing B) (y : A)) := by
    intro y
    rw [IsScalarTower.algebraMap_apply A B (FractionRing B)]
    exact IsLocalization.map_units (FractionRing B) ⟨_, hnzd y⟩
  let ι : FractionRing A →ₐ[A] FractionRing B :=
    AlgHom.mk (IsLocalization.lift (M := nonZeroDivisors A) hunit)
      (IsLocalization.lift_eq hunit)
  let ψ : B ⊗[A] FractionRing A →ₐ[B] FractionRing B :=
    Algebra.TensorProduct.lift (Algebra.ofId B (FractionRing B)) ι fun _ _ => Commute.all _ _
  have hψ : Function.Injective ψ :=
    injective_of_isLocalization_of_injective
      (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) ψ.toRingHom
      (fun x => ψ.commutes x) (IsLocalization.injective (FractionRing B) le_rfl)
  set A' := integralClosure A (FractionRing A) with hA'
  let ν : B ⊗[A] ↥A' →ₗ[B] B ⊗[A] FractionRing A :=
    LinearMap.baseChange B (Subalgebra.val A').toLinearMap
  have hν : Function.Injective ν := by
    simp [ν, LinearMap.baseChange_eq_lTensor]
  have hmem : ∀ z : B ⊗[A] ↥A', ψ (ν z) ∈ integralClosure B (FractionRing B) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b a =>
        have ha : IsIntegral B (ι (a : FractionRing A)) :=
          (IsIntegral.map ι a.2).tower_top
        simpa [ν, ψ] using Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ b) ha
    | add x y hx hy => simpa only [map_add] using Subalgebra.add_mem _ hx hy
  have : Module.Finite B ↥(integralClosure B (FractionRing B)) := hB
  let θ : B ⊗[A] ↥A' →ₗ[B] ↥(integralClosure B (FractionRing B)) :=
    { toFun := fun z => ⟨ψ (ν z), hmem z⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun b x => Subtype.ext (by simp) }
  have : Module.Finite B (B ⊗[A] ↥A') :=
    Module.Finite.of_injective θ fun x y hxy => hν (hψ (Subtype.ext_iff.mp hxy))
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (T := B) (M := ↥A')

/-- `Algebra.TensorProduct.comm` as an `S`-algebra equivalence, for the right `S`-algebra
structure on `A ⊗[R] S`. -/
private noncomputable def tensorRightComm (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] : (A ⊗[R] S) ≃ₐ[S] (S ⊗[R] A) :=
  { Algebra.TensorProduct.comm R A S with
    commutes' := fun s => by
      change (Algebra.TensorProduct.comm R A S) (1 ⊗ₜ s) = s ⊗ₜ 1
      simp }

/-- Under the hypotheses of Stacks 0354, every domain of finite type over `R` is N-1. -/
private theorem isN1_of_smooth_of_isNagataRing {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.Smooth R S] [Module.FaithfullyFlat R S]
    (hS : IsNagataRing S)
    (A : Type u) [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A] : IsN1 A := by
  have hfin : Algebra.FiniteType S (A ⊗[R] S) :=
    Algebra.FiniteType.equiv (inferInstanceAs (Algebra.FiniteType S (S ⊗[R] A)))
      (tensorRightComm R S A).symm
  have hnag : ∀ (T : Type u) [CommRing T] [Algebra S T] [Algebra.FiniteType S T], IsNagataRing T :=
    (isNagataRing_tfae.out 1 2).mp hS
  have hB : IsNagataRing (A ⊗[R] S) := hnag (A ⊗[R] S)
  have : IsNoetherianRing (A ⊗[R] S) := hB.1
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : IsReduced (A ⊗[R] S) := isReduced_of_smooth_of_isNoetherianRing A (A ⊗[R] S)
  exact isN1_of_faithfullyFlat_of_isN1 A (A ⊗[R] S) (isN1_of_isNagataRing _ hB)

/-- Smooth descent of the Nagata property: if `R → S` is smooth and surjective on spectra and
`S` is a Nagata ring, then `R` is a Nagata ring. -/
public theorem solution {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    (hS : IsNagataRing S) : IsNagataRing R := by
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_comap_surjective hsurj
  have : IsNoetherianRing S := hS.1
  have hnoeth : IsNoetherianRing R :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat (A := S)
      (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid R S S).symm.toLinearEquiv)
  refine ⟨hnoeth, fun p _ => ?_⟩
  refine isJapaneseRing_of_forall_isN1 (R := R) ?_ (R ⧸ p)
  intro C _ _ _ _
  exact isN1_of_smooth_of_isNagataRing (R := R) hS C

end Stacks.Nagata.SmoothDescent

/-- **Stacks Tag 0354.** Let `R → S` be a ring map. If it is smooth and the induced map
`Spec S → Spec R` is surjective, and `S` is a Nagata ring — Noetherian, with every quotient
`S ⧸ q` by a prime N-2 — then `R` is a Nagata ring.

Smoothness is `Algebra.Smooth` (Definition 00T2), and together with surjectivity on spectra it is
equivalent to `R → S` being smooth and faithfully flat, by `Algebra.Smooth.flat` and
`Module.FaithfullyFlat.of_comap_surjective`. -/
@[stacks 0354 "Smoothness of the ring map `R → S` is `Algebra.Smooth R S` (Definition 00T2) for \
  an `Algebra R S` instance, and surjectivity on spectra is surjectivity of \
  `PrimeSpectrum.comap (algebraMap R S)`; the pair is equivalent to smooth plus \
  `Module.FaithfullyFlat R S`. Nagata is `IsNagataRing` of Definition 032R(2), whose Noetherian \
  clause is part of the conclusion rather than a hypothesis on `R`. See the module docstring."]
public theorem IsNagataRing.of_smooth_of_comap_surjective {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    (hS : IsNagataRing S) : IsNagataRing R :=
      Stacks.Nagata.SmoothDescent.solution (R := R) (S := S) hsurj hS

end
