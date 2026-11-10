module

public import StacksFrontier.RingTheory.GeometricallyRegular.Reduced
public import StacksFrontier.RingTheory.Smoothing.AnnihilatorStabilizedParameters
public import StacksFrontier.RingTheory.Smoothing.ArtinianApproximationData
public import StacksFrontier.RingTheory.Smoothing.ArtinianFactorizationDescent
public import StacksFrontier.RingTheory.Smoothing.MinimalSingularPrime
public import StacksFrontier.RingTheory.Smoothing.ResolutionReductions
public import StacksFrontier.RingTheory.Smoothing.SeparableResidueFieldResolution
public import StacksFrontier.RingTheory.Smoothing.StrictlyStandardParameterPowers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Resolving a local smoothing situation in positive characteristic

Stacks 07FJ: let `k → A → Λ ⊃ 𝔮` be as in Situation 07F7 with `k` of characteristic `p > 0`,
`Λ` Noetherian and geometrically regular over `k`, and `𝔮` minimal over
`𝔥_A = √(H_{A/k} Λ)`. Then the chain can be resolved at `𝔮`.

This file assembles the twenty-six items of the source's proof out of the general lemmas that
realize them, which are spread over the other files of
`StacksDraft.RingTheory.Smoothing`. Two inputs are proved in files downstream of this one and
are therefore carried here as hypotheses; they are discharged, and the lemma itself proved, in
`StacksFrontier/RingTheory/Smoothing/TwistedQuotientClosure.lean`
(`Stacks.Smoothing.canBeResolvedInPositiveCharacteristic`):

* `Stacks.Smoothing.HasArtinianApproximationData`, item (9) of the proof — Stacks 07FT in full
  generality. The theorem
  `Stacks.Smoothing.exists_mvPolynomial_localArtinianFactorization_mem` is exactly this
  statement under the extra hypothesis that `κ(𝔮)` be essentially of finite type over `k`,
  which is the range in which clauses (2) and (3) of Stacks 07FH are proved here.
* `Stacks.Smoothing.TwistedQuotientResolvable`, items (18)–(26) of the proof.

Separability of `κ(𝔮)` over `k` when `dim Λ_𝔮 = 0` is proved here as
`Stacks.Smoothing.zeroDimensionalSeparableResidue` and so is not a hypothesis.

What is proved here is items (1)–(17): the choices of `N`, of generators of `H_{A/k}`, of `d`,
of the algebras `B` and `C`, of `c`, of the finite set `E`, of the parameters `π_i` and their
rescalings, of the units `δ_i` and the coefficients `λ_{ij}`, and the two reductions of Stacks
07G0 and 07G2 that turn the chain `k → A → Λ ⊃ 𝔮` into the twisted quotient chain of item (22).

## Main definitions

* `Stacks.Smoothing.HasArtinianApproximationData`: Stacks 07FT in full generality.
* `Stacks.Smoothing.TwistedQuotientResolvable`: items (18)–(26) of the proof of Stacks 07FJ.
* `Stacks.Smoothing.ZeroDimensionalSeparableResidue`: separability of `κ(𝔮)` over `k` when
  `dim Λ_𝔮 = 0`.

## Main results

* `Stacks.Smoothing.zeroDimensionalSeparableResidue`: the predicate
  `ZeroDimensionalSeparableResidue`, proved.
* `Stacks.Smoothing.canBeResolvedInPositiveCharacteristic_of_hasArtinianApproximationData`:
  Stacks 07FJ from the two hypotheses above.

## References

* [Stacks Project, Tag 07FJ](https://stacks.math.columbia.edu/tag/07FJ)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace Stacks.Smoothing

universe u

/-- The conclusion of Stacks 07FT at one `(k, Λ, 𝔮, n, E)`: there are `m` and a `k`-algebra map
`φ : k[y_1, …, y_m] → Λ` such that, with `𝔭 = φ^{-1}(𝔮)`, the induced local map
`g : k[y_1, …, y_m]_𝔭 → Λ_𝔮` is flat with `𝔭Λ_𝔮 = 𝔮Λ_𝔮`, and the map
`u : k[y_1, …, y_m]_𝔭/𝔭^n → Λ̄` induced by `g` factors as `D.subtype ∘ a` through a subring `D`
of `Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮` containing `E`, with `a` essentially smooth and `D.subtype` flat; all three
rings of the factorization are local Artinian.

This is the conclusion of `Stacks.Smoothing.exists_mvPolynomial_localArtinianFactorization_mem`
verbatim, which `Stacks.Smoothing.artinianApproximationDataAt_of_essFiniteType` records. -/
def ArtinianApproximationDataAt (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) (E : Finset (primePowerQuotient 𝔮 n)) : Prop :=
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮)
      (u : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* primePowerQuotient 𝔮 n)
      (D : Subring (primePowerQuotient 𝔮 n))
      (a : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* D),
      Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
          (Ideal.comap φ.toRingHom 𝔮)
        = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮 ∧
      (∀ f, g (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
          = algebraMap Λ (Localization.AtPrime 𝔮) (φ f)) ∧
      g.Flat ∧
      (∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
              (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)))
              (Ideal.comap φ.toRingHom 𝔮 ^ n)) y)
          = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))
            (g y)) ∧
      D.subtype.comp a = u ∧
      (∀ e ∈ E, e ∈ D) ∧
      ∃ (_ : IsLocalRing (primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n))
        (_ : IsArtinianRing (primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n))
        (_ : IsLocalRing (primePowerQuotient 𝔮 n))
        (_ : IsArtinianRing (primePowerQuotient 𝔮 n))
        (_ : IsLocalRing D) (_ : IsArtinianRing D),
        a.IsEssentiallySmooth ∧ D.subtype.Flat

/-- **Stacks 07FT in full generality.** For every field `k` of characteristic `p > 0`, every
Noetherian geometrically regular `k`-algebra `Λ`, every prime `𝔮` of `Λ`, every `n ≥ 1` and
every finite subset `E` of `Λ_𝔮/𝔮^nΛ_𝔮`, the Artinian approximation data of
`Stacks.Smoothing.ArtinianApproximationDataAt` exist.

The theorem `Stacks.Smoothing.exists_mvPolynomial_localArtinianFactorization_mem` is
exactly this statement under the extra instance hypothesis
`[Algebra.EssFiniteType k (ResidueField (Localization.AtPrime 𝔮))]`, which is the range in which
clauses (2) and (3) of Stacks 07FH are available in this repository; outside it clause (2) is
open here. See `Stacks.Smoothing.artinianApproximationDataAt_of_essFiniteType`. -/
def HasArtinianApproximationData : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] (𝔮 : Ideal Λ) [𝔮.IsPrime] (p : ℕ) [Fact p.Prime]
    [CharP k p] {n : ℕ}, 1 ≤ n → ∀ (E : Finset (primePowerQuotient 𝔮 n)),
    ArtinianApproximationDataAt k Λ 𝔮 n E

/-- The Artinian approximation data of Stacks 07FT exist whenever the residue field `κ(𝔮)` of
`Λ_𝔮` is essentially of finite type over `k`: this is
`Stacks.Smoothing.exists_mvPolynomial_localArtinianFactorization_mem`, and its acceptance here
is the check that `Stacks.Smoothing.ArtinianApproximationDataAt` is that theorem's conclusion
verbatim. -/
theorem artinianApproximationDataAt_of_essFiniteType (k Λ : Type u) [Field k] [CommRing Λ]
    [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ] (𝔮 : Ideal Λ)
    [𝔮.IsPrime] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Algebra.EssFiniteType k (ResidueField (Localization.AtPrime 𝔮))] {n : ℕ} (hn : 1 ≤ n)
    (E : Finset (primePowerQuotient 𝔮 n)) : ArtinianApproximationDataAt k Λ 𝔮 n E :=
  exists_mvPolynomial_localArtinianFactorization_mem 𝔮 p hn E

/-- If the annihilators of `t` and of `t ^ 2` agree then `x t ^ (n+1) = 0` forces `x t = 0`. -/
private lemma mul_eq_zero_of_mul_pow_succ_eq_zero {T : Type*} [CommRing T] {t : T}
    (h : ∀ x : T, x * t = 0 ↔ x * t ^ 2 = 0) :
    ∀ (n : ℕ) (x : T), x * t ^ (n + 1) = 0 → x * t = 0 := by
  intro n
  induction n with
  | zero => exact fun x hx => by simpa using hx
  | succ n ih =>
    intro x hx
    have h3 := (h (x * t ^ n)).mpr (by rwa [show x * t ^ n * t ^ 2 = x * t ^ (n + 1 + 1) by ring])
    rw [mul_assoc, ← pow_succ] at h3
    exact ih x h3

/-- The annihilator condition of Stacks 07FW and 07FX passes to positive powers: if the
annihilators of `t` and `t ^ 2` agree, so do those of `t ^ c` and `(t ^ c) ^ 2`. -/
private lemma mul_pow_ann_iff {T : Type*} [CommRing T] {t : T}
    (h : ∀ x : T, x * t = 0 ↔ x * t ^ 2 = 0) {c : ℕ} (hc : 0 < c) (x : T) :
    x * t ^ c = 0 ↔ x * (t ^ c) ^ 2 = 0 := by
  have key : ∀ (y : T) (j : ℕ), 0 < j → (y * t ^ j = 0 ↔ y * t = 0) := by
    intro y j hj
    obtain ⟨jj, rfl⟩ : ∃ jj, j = jj + 1 := ⟨j - 1, by omega⟩
    refine ⟨mul_eq_zero_of_mul_pow_succ_eq_zero h jj y, fun hy => ?_⟩
    rw [show y * t ^ (jj + 1) = y * t * t ^ jj by ring, hy, zero_mul]
  rw [key x c hc, show (t ^ c) ^ 2 = t ^ (2 * c) by ring, key x (2 * c) (by omega)]

/-- The annihilator condition transports along an equality of ideals. -/
private lemma forall_mul_ann_iff_of_ideal_eq {T : Type*} [CommRing T] {I J : Ideal T}
    (hIJ : I = J) {t : T}
    (h : ∀ x : T ⧸ J, x * Ideal.Quotient.mk J t = 0 ↔
      x * (Ideal.Quotient.mk J t) ^ 2 = 0) :
    ∀ x : T ⧸ I, x * Ideal.Quotient.mk I t = 0 ↔ x * (Ideal.Quotient.mk I t) ^ 2 = 0 := by
  subst hIJ
  exact h

/-- The annihilator condition in elementwise form. -/
private lemma forall_mul_ann_iff_iff_mem {T : Type*} [CommRing T] (I : Ideal T) (t : T) :
    (∀ x : T ⧸ I, x * Ideal.Quotient.mk I t = 0 ↔ x * (Ideal.Quotient.mk I t) ^ 2 = 0) ↔
      ∀ y : T, (y * t ∈ I ↔ y * t ^ 2 ∈ I) := by
  simp only [Ideal.Quotient.mk_surjective.forall, ← map_pow, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The annihilator condition transports along a ring isomorphism. -/
private lemma forall_mul_ann_iff_of_ringEquiv {T T' : Type*} [CommRing T] [CommRing T']
    (e : T ≃+* T') (I : Ideal T) (t : T)
    (h : ∀ x : T' ⧸ Ideal.map (e : T →+* T') I,
      x * Ideal.Quotient.mk _ (e t) = 0 ↔ x * (Ideal.Quotient.mk _ (e t)) ^ 2 = 0) :
    ∀ x : T ⧸ I, x * Ideal.Quotient.mk I t = 0 ↔ x * (Ideal.Quotient.mk I t) ^ 2 = 0 := by
  have hmem : ∀ z : T, z ∈ I ↔ e z ∈ Ideal.map (e : T →+* T') I := by
    intro z
    refine ⟨fun hz => Ideal.mem_map_of_mem _ hz, fun hz => ?_⟩
    obtain ⟨w, hw, hwz⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp hz
    rwa [e.injective hwz] at hw
  rw [forall_mul_ann_iff_iff_mem] at h ⊢
  intro y
  rw [hmem (y * t), hmem (y * t ^ 2), map_mul, map_mul, map_pow]
  exact h (e y)

/-- The image of the prefix ideal of eighth powers of `γ_j ^ c` along a ring map sending `γ_j` to
`ρ_j`. -/
private lemma map_eighthPowerPrefixIdeal_pow_eq_span {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) {d : ℕ} (γ : Fin d → R) (ρ : Fin d → T) (c : ℕ) (i : Fin d)
    (hγ : ∀ j, f (γ j) = ρ j) :
    Ideal.map f (eighthPowerPrefixIdeal (fun j => γ j ^ c) i) =
      Ideal.span (Set.range fun j : Fin i.val =>
        ρ (j.castLE (Nat.le_of_lt i.isLt)) ^ (8 * c)) := by
  classical
  rw [eighthPowerPrefixIdeal, Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨⟨j.1, hj⟩, ?_⟩
    have hcast : (⟨j.1, hj⟩ : Fin i.val).castLE (Nat.le_of_lt i.isLt) = j := Fin.ext rfl
    beta_reduce
    rw [hcast, map_pow, map_pow, hγ, ← pow_mul, Nat.mul_comm]
  · rintro ⟨j, rfl⟩
    refine ⟨(γ (j.castLE (Nat.le_of_lt i.isLt)) ^ c) ^ 8,
      ⟨j.castLE (Nat.le_of_lt i.isLt), j.isLt, rfl⟩, ?_⟩
    rw [map_pow, map_pow, hγ, ← pow_mul, Nat.mul_comm]

/-- A geometrically regular algebra is a regular ring, so its localizations are regular local
rings. -/
private lemma isRegularLocalRing_atPrime_of_isGeometricallyRegular (k Λ : Type u) [Field k]
    [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ]
    (q : Ideal Λ) [q.IsPrime] : IsRegularLocalRing (Localization.AtPrime q) := by
  have : IsRegularRing (k ⊗[k] Λ) := Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct k
  have : IsRegularRing Λ := IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k Λ).toRingEquiv
  exact IsRegularRing.isRegularLocalRing_of_isLocalization q (Localization.AtPrime q)

/-- The zero-dimensional case: when `dim Λ_q = 0` the residue field `κ(q)` is `Λ_q` itself, a
geometrically regular field extension of `k`, hence separable over `k`. -/
def ZeroDimensionalSeparableResidue : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] (q : Ideal Λ) [q.IsPrime],
    ringKrullDim (Localization.AtPrime q) = 0 → Algebra.IsSeparableExtension k q.ResidueField

/-- **The zero-dimensional case of Stacks 07FJ.** Geometric regularity of `Λ` over `k` passes to
the localization `Λ_q`, which is a regular local ring; as `dim Λ_q = 0`, its maximal ideal is
generated by the empty set, so `Λ_q` is a field and the residue map `Λ_q → κ(q)` is an
isomorphism of `k`-algebras. Hence `κ(q)` is geometrically regular over `k`, so geometrically
reduced over `k`, which for a field extension is separability (Stacks 0322). -/
@[ega "IV 6.7.6" "special case", sga "1 II 5.9" "(ii)"]
theorem zeroDimensionalSeparableResidue : ZeroDimensionalSeparableResidue.{u} := by
  intro k Λ _ _ _ _ _ q _ hdim
  have instGR : Algebra.IsGeometricallyRegular k (Localization.AtPrime q) :=
    Algebra.IsGeometricallyRegular.of_isLocalization q.primeCompl
  have instRLR := isRegularLocalRing_atPrime_of_isGeometricallyRegular k Λ q
  have hspan : (maximalIdeal (Localization.AtPrime q)).spanFinrank = 0 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime q)
    rw [hdim] at h
    exact_mod_cast h
  have hmax : maximalIdeal (Localization.AtPrime q) = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot
      (IsNoetherian.noetherian (maximalIdeal (Localization.AtPrime q)))).1 hspan
  have : IsScalarTower k (Localization.AtPrime q) q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : Localization.AtPrime q ≃ₐ[k] q.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k (Localization.AtPrime q) q.ResidueField)
      ⟨(injective_iff_map_eq_zero _).2 fun a ha => by
        simpa [hmax] using (IsLocalRing.residue_eq_zero_iff a).1 ha,
        Ideal.Quotient.mk_surjective⟩
  have : Algebra.IsGeometricallyRegular k q.ResidueField :=
    Algebra.IsGeometricallyRegular.of_algEquiv e
  exact ((Algebra.isSeparableExtension_of_charZero_and_tfae k q.ResidueField).2.out 3 1).mp
    (Algebra.isGeometricallyReduced_of_isGeometricallyRegular k q.ResidueField)

/-- **The remainder of the proof of Stacks 07FJ: items (18)–(26).**

The data are those produced by items (1)–(13), which
`canBeResolvedInPositiveCharacteristic_of_hasArtinianApproximationData` constructs: generators
`a_1, …, a_t` of `H_{A/k}`, the exponent `N` of item (1), the dimension `d = dim Λ_𝔮` of item
(3), the algebra `C` of item (5) with its `k[x_1, …, x_d]`-algebra retraction `grt : C → B` onto
`B = A[x_i, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} a_j)`, the exponent `c` of item (6), the polynomial
ring `k[y_1, …, y_m]` with its map `φ` of item (9), the parameters `π_1, …, π_d` of items (10)
and (12), and the units `δ_i` together with the coefficients `λ_{ij}` of item (13).

With `R = k[y_1, …, y_m, t_1, …, t_d]` carrying `x_i ↦ γ_i = π_i t_i` over `k[x_1, …, x_d]` and
`y_j ↦ φ(y_j)`, `t_i ↦ δ_i` into `Λ`, and with `I = (γ_1^{8c}, …, γ_d^{8c})`, the statement is
that the chain of item (22) — the quotient by `I` of `R → R ⊗_{k[x_1, …, x_d]} C → Λ` — can be
resolved. That is exactly what items (18)–(26) of the source prove, by Stacks 07G4, 07G6, 07G7,
07G8, 07G9 and 07GA; it is the one part of the proof that is not assembled here. -/
def TwistedQuotientResolvable : Prop :=
  ∀ (k A Λ : Type u) [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
      [Algebra A Λ] [IsScalarTower k A Λ] [Algebra.FinitePresentation k A] [IsNoetherianRing Λ]
      [Algebra.IsGeometricallyRegular k Λ] (q : Ideal Λ) [q.IsPrime]
      {t d m N n c : ℕ} (a : Fin t → A)
      (C : Type u) [CommRing C] [Algebra (MvPolynomial (Fin d) k) C]
      [Algebra (parameterPowerAlgebra A d N a) C]
      [Algebra.FiniteType (parameterPowerAlgebra A d N a) C]
      [Algebra.FinitePresentation (MvPolynomial (Fin d) k) C]
      (grt : C →ₐ[MvPolynomial (Fin d) k] parameterPowerAlgebra A d N a)
      (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (gl : Localization.AtPrime (Ideal.comap φ.toRingHom q) →+* Localization.AtPrime q)
      (u : primePowerQuotient (Ideal.comap φ.toRingHom q) n →+* primePowerQuotient q n)
      (D : Subring (primePowerQuotient q n))
      (aD : primePowerQuotient (Ideal.comap φ.toRingHom q) n →+* D)
      (π : Fin d → MvPolynomial (Fin m) k) (δ : Fin d → Λ) (lam : Fin d → Fin t → Λ)
      (D' : Type u) [CommRing D'] [IsLocalRing D'] [IsArtinianRing D']
      (cc : D →+* D') (b' : D' →+* primePowerQuotient q n),
    -- the numerical choices of items (1), (3), (6) and (7)
    0 < N → 0 < c → 1 ≤ d → 1 ≤ n → N ≤ n → d * (8 * c - 1) + 1 ≤ n →
    -- Situation 07F7 with `𝔮` minimal over `𝔥_A`, and items (1), (2), (3)
    q ∈ (Ideal.map (algebraMap A Λ) (singularIdeal k A)).radical.minimalPrimes →
    Ideal.span (Set.range a) = singularIdeal k A →
    Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ N) ≤
      Ideal.map (algebraMap Λ (Localization.AtPrime q))
        (Ideal.map (algebraMap A Λ) (singularIdeal k A)) →
    ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞) →
    -- items (4) and (5): `C` is a `k[x_1, …, x_d]`-algebra over `B` with a retraction onto `B`
    (∀ y : MvPolynomial (Fin d) k, algebraMap (MvPolynomial (Fin d) k) C y =
      algebraMap (parameterPowerAlgebra A d N a) C
        (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) y)) →
    (∀ x : parameterPowerAlgebra A d N a,
      grt (algebraMap (parameterPowerAlgebra A d N a) C x) = x) →
    -- item (9): the Artinian approximation data, with the image of `A` inside `D`
    Ideal.map ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom)
        (Ideal.comap φ.toRingHom q) = Ideal.map (algebraMap Λ (Localization.AtPrime q)) q →
    (∀ f, gl (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (Ideal.comap φ.toRingHom q)) f)
        = algebraMap Λ (Localization.AtPrime q) (φ f)) →
    gl.Flat →
    (∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom q)))
            (Ideal.comap φ.toRingHom q ^ n)) y)
        = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n))
          (gl y)) →
    D.subtype.comp aD = u →
    (∀ x : A, algebraMap Λ (primePowerQuotient q n) (algebraMap A Λ x) ∈ D) →
    ∀ (_ : IsLocalRing (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
      (_ : IsArtinianRing (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
      (_ : IsLocalRing (primePowerQuotient q n)) (_ : IsArtinianRing (primePowerQuotient q n))
      (_ : IsLocalRing D) (_ : IsArtinianRing D),
    aD.IsEssentiallySmooth → D.subtype.Flat →
    -- items (10) and (12): the regular system of parameters and its rescaling
    ringKrullDim (Localization.AtPrime (Ideal.comap φ.toRingHom q)) = (d : WithBot ℕ∞) →
    (∀ i, π i ∈ Ideal.comap φ.toRingHom q) →
    Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (Ideal.comap φ.toRingHom q)) (π i))
      = IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.comap φ.toRingHom q)) →
    Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (φ (π i)))
      = IsLocalRing.maximalIdeal (Localization.AtPrime q) →
    -- item (13): the essentially smooth Artinian enlargement `D'` and the units `δ_i`
    ∀ (_ : IsLocalHom cc) (_ : IsLocalHom b'),
    cc.IsEssentiallySmooth → b'.Flat → b'.comp cc = D.subtype →
    (∀ i, δ i ∈ q.primeCompl) →
    ∀ hrel : ∀ i, (δ i * φ (π i)) ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j,
    (∀ i j, ∃ w : D', b' w = algebraMap Λ (primePowerQuotient q n) (lam i j)) →
    (∀ i, ∃ w : D', b' w = algebraMap Λ (primePowerQuotient q n) (δ i)) →
    -- item (6): the strictly standard powers
    (∀ i : Fin d, IsStrictlyStandard (R := MvPolynomial (Fin d) k)
      (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i) ^ c)) →
    -- items (11) and (15): the twisted base `R = k[y_1, …, y_m, t_1, …, t_d]`
    letI : Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) :=
      (twistedBaseHom π).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
      (twistedBaseToTarget φ δ).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin d) k) Λ :=
      ((algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ).comp
        (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k))).toAlgebra
    letI : IsScalarTower (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ hcompat : ∀ y : MvPolynomial (Fin d) k,
        algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ
            (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) y) =
          improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
            (algebraMap (MvPolynomial (Fin d) k) C y),
    letI : Algebra (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ :=
      (Algebra.TensorProduct.lift
        (IsScalarTower.toAlgHom (MvPolynomial (Fin d) k)
          (MvPolynomial (Fin m ⊕ Fin d) k) Λ)
        ({ toRingHom := improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt,
            commutes' := fun y => (hcompat y).symm } : C →ₐ[MvPolynomial (Fin d) k] Λ)
        (fun _ _ => Commute.all _ _)).toRingHom.toAlgebra
    let I : Ideal (MvPolynomial (Fin m ⊕ Fin d) k) :=
      Ideal.span (Set.range fun i => twistedParameter π i ^ (8 * c))
    let ID : Ideal (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) :=
      Ideal.map (algebraMap (MvPolynomial (Fin m ⊕ Fin d) k)
        (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C)) I
    let IΛ : Ideal Λ := Ideal.map (algebraMap
      (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ) ID
    letI : Algebra (MvPolynomial (Fin m ⊕ Fin d) k ⧸ I) (Λ ⧸ IΛ) :=
      ((algebraMap ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID)
        (Λ ⧸ IΛ)).comp (algebraMap (MvPolynomial (Fin m ⊕ Fin d) k ⧸ I)
          ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID))).toAlgebra
    letI : IsScalarTower (MvPolynomial (Fin m ⊕ Fin d) k ⧸ I)
        ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID) (Λ ⧸ IΛ) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    CanBeResolved (MvPolynomial (Fin m ⊕ Fin d) k ⧸ I)
      ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID) (Λ ⧸ IΛ)
      (Ideal.map (Ideal.Quotient.mk IΛ) q)

private theorem isLocalHom_of_isArtinianRing {D T : Type*} [CommRing D] [CommRing T]
    [IsLocalRing D] [IsArtinianRing D] [Nontrivial T] (f : D →+* T) : IsLocalHom f := by
  refine ⟨fun x hx => ?_⟩
  by_contra hnu
  obtain ⟨j, hj⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal D).mp inferInstance
  have hxj : x ^ j = 0 := by
    simpa [hj] using Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal x).mpr hnu) j
  have h := hx.pow j
  rw [← map_pow, hxj, map_zero] at h
  exact not_isUnit_zero h

/-- Items (1)–(17) of the proof of Stacks 07FJ, at one chain. -/
private theorem canBeResolved_of_hasArtinianApproximationData
    (h07FT : HasArtinianApproximationData.{u})
    (hback : TwistedQuotientResolvable.{u})
    (k A Λ : Type u) [Field k] [CommRing A]
    [CommRing Λ] [Algebra k A] [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ]
    [Algebra.FinitePresentation k A] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] (p : ℕ) [CharP k p] (hp : 0 < p) (q : Ideal Λ)
    [q.IsPrime]
    (hq : q ∈ (Ideal.map (algebraMap A Λ) (singularIdeal k A)).radical.minimalPrimes) :
    CanBeResolved k A Λ q := by
  classical
  -- `Λ` is a regular ring, so `Λ_q` is a regular local ring.
  have instRLR := isRegularLocalRing_atPrime_of_isGeometricallyRegular k Λ q
  have : NeZero p := ⟨hp.ne'⟩
  have instFactp : Fact p.Prime := CharP.char_is_prime_of_pos k p
  let S : LocalSmoothingSituation.{u, u, u} := { R := k, A := A, Λ := Λ, q := q }
  have hqS : q ∈ S.radicalSingularIdealExtension.minimalPrimes := hq
  -- step (1)
  obtain ⟨N, hN, hqN⟩ := S.exists_pos_map_pow_le_map_singularIdeal hqS
  -- step (2)
  obtain ⟨t, a, ha⟩ := S.exists_fin_span_range_eq_singularIdeal
  -- step (3)
  obtain ⟨d, hd0⟩ := S.exists_nat_eq_ringKrullDim_localization
  have hd : ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞) := hd0
  by_cases hdzero : d = 0
  · have : Algebra.IsSeparableExtension k q.ResidueField :=
      zeroDimensionalSeparableResidue k Λ q (by rw [hd, hdzero]; rfl)
    exact canBeResolved_of_isRegularLocalRing_of_isSeparableExtension k A Λ q hq
  have hd1 : 1 ≤ d := by omega
  -- steps (4), (5)
  obtain ⟨C, instCRC, instkxC, instBC, instTowerBC, instFTBC, instFPC, grt, hretract,
    hC₁, hC₂⟩ := exists_retraction_parameterPowerAlgebra k A d N a
  let := instCRC
  let := instkxC
  let := instBC
  have := instTowerBC
  have := instFTBC
  have := instFPC
  -- step (6)
  obtain ⟨c, hc, hstdC⟩ := exists_pos_isStrictlyStandard_X_pow k A d N a ha C hC₁ hC₂
  -- step (7)
  have hn : 1 ≤ N + 8 * d * c + 1 := by omega
  have hNn : N ≤ N + 8 * d * c + 1 := by omega
  have he : 0 < 8 * c := by omega
  have hnbound : d * (8 * c - 1) + 1 ≤ N + 8 * d * c + 1 := by
    have hmul : d * (8 * c - 1) ≤ d * (8 * c) := Nat.mul_le_mul_left d (by omega)
    have hcomm : d * (8 * c) = 8 * d * c := by ring
    omega
  -- step (8)
  obtain ⟨sgen, E, hsgen, hEimg⟩ :=
    exists_finset_primePowerQuotient_eq_image_generators k A Λ q (N + 8 * d * c + 1)
  -- step (9)
  obtain ⟨m, φ, gl, u, D, aD, hmapφ, hgφ, hgflat, hu, hDsub, hED, hlocP, hartP, hlocQ, hartQ,
    hlocD, hartD, hess, hDflat⟩ := h07FT k Λ q p hn E
  -- step (10)
  obtain ⟨hdimP, π₀, hπ₀mem, hπ₀span⟩ :=
    exists_fin_mem_span_eq_maximalIdeal_of_flat q φ gl hmapφ hgφ hgflat hd
  -- step (12)
  obtain ⟨π, hπscale, hπspan, hannR0⟩ :=
    exists_annihilator_scaledVariable_sq_eq (Ideal.comap φ.toRingHom q) hdimP π₀ hπ₀span he
  have hπmem : ∀ i, π i ∈ Ideal.comap φ.toRingHom q := by
    intro i
    obtain ⟨s, _, hsi⟩ := hπscale i
    rw [hsi]
    exact Ideal.mul_mem_left _ _ (hπ₀mem i)
  -- `Λ̄` is Artinian local, and `D → Λ̄` is a flat local map of Artinian local rings
  have := hlocQ
  have := hartQ
  have := hlocD
  have := hartD
  have instLHD : IsLocalHom D.subtype := isLocalHom_of_isArtinianRing _
  -- the generators of `H_{A/k} Λ`
  have hspanΛ : Ideal.map (algebraMap A Λ) (singularIdeal k A)
      = Ideal.span (Set.range fun j => algebraMap A Λ (a j)) := by
    rw [← ha, Ideal.map_span, ← Set.range_comp]
    rfl
  have hqN' : Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ N) ≤
      Ideal.map (algebraMap Λ (Localization.AtPrime q))
        (Ideal.span (Set.range fun j => algebraMap A Λ (a j))) := by
    rw [← hspanΛ]
    exact hqN
  -- the maximal ideal of `Λ_q` is generated by the images of the `π_i`
  have hmaxmap : Ideal.map gl (maximalIdeal
      (Localization.AtPrime (Ideal.comap φ.toRingHom q)))
      = maximalIdeal (Localization.AtPrime q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := Ideal.comap φ.toRingHom q),
      Ideal.map_map, ← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q),
      ← hmapφ]
    exact congrArg (Ideal.map · (Ideal.comap φ.toRingHom q)) (RingHom.ext fun f => hgφ f)
  have hπΛspan : Ideal.span (Set.range fun i =>
      algebraMap Λ (Localization.AtPrime q) (φ (π i)))
      = maximalIdeal (Localization.AtPrime q) := by
    have hfun : (fun i => algebraMap Λ (Localization.AtPrime q) (φ (π i)))
        = fun i => gl (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom q)) (π i)) := by
      funext i
      exact (hgφ (π i)).symm
    rw [hfun, ← hmaxmap, ← hπspan, Ideal.map_span, ← Set.range_comp]
    rfl
  -- the image of `A` in `Λ̄` lies in `D`
  have hurange : ∀ z, u z ∈ D := by
    intro z
    rw [← hDsub]
    exact (aD z).2
  have hbarmk : ∀ y : Λ, algebraMap Λ (primePowerQuotient q (N + 8 * d * c + 1)) y =
      Ideal.Quotient.mk
          (Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ (N + 8 * d * c + 1)))
        (algebraMap Λ (Localization.AtPrime q) y) := by
    intro y
    rw [IsScalarTower.algebraMap_apply Λ (Localization.AtPrime q)
      (primePowerQuotient q (N + 8 * d * c + 1)), Ideal.Quotient.algebraMap_eq]
  have hφmem : ∀ f : MvPolynomial (Fin m) k,
      algebraMap Λ (primePowerQuotient q (N + 8 * d * c + 1)) (φ f) ∈ D := by
    intro f
    have := hurange (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
      (Localization.AtPrime (Ideal.comap φ.toRingHom q)))
      (Ideal.comap φ.toRingHom q ^ (N + 8 * d * c + 1)))
      (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (Ideal.comap φ.toRingHom q)) f))
    rwa [hu, hgφ f, ← hbarmk] at this
  have hAD : ∀ x : A,
      algebraMap Λ (primePowerQuotient q (N + 8 * d * c + 1)) (algebraMap A Λ x) ∈ D := by
    intro x
    have hx : x ∈ Algebra.adjoin k (sgen : Set A) := by
      rw [hsgen]
      exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      have hyE : algebraMap Λ (primePowerQuotient q (N + 8 * d * c + 1))
          (algebraMap A Λ y) ∈ E := by
        have hmem : toPrimePowerQuotient q (N + 8 * d * c + 1)
            (algebraMap A Λ y) ∈ (E : Set _) := by
          rw [hEimg]
          exact ⟨algebraMap A Λ y, ⟨y, hy, rfl⟩, rfl⟩
        rw [hbarmk]
        exact hmem
      exact hED _ hyE
    | algebraMap r =>
      have : algebraMap A Λ (algebraMap k A r) = φ (algebraMap k (MvPolynomial (Fin m) k) r) := by
        rw [φ.commutes, ← IsScalarTower.algebraMap_apply k A Λ]
      rw [this]
      exact hφmem _
    | add y z _ _ hy hz => simpa using Subring.add_mem D hy hz
    | mul y z _ _ hy hz => simpa using Subring.mul_mem D hy hz
  have haD' : ∀ j, ∃ w : D, D.subtype w =
      algebraMap Λ (truncatedLocalization Λ q (N + 8 * d * c + 1)) (algebraMap A Λ (a j)) :=
    fun j => ⟨⟨_, hAD (a j)⟩, rfl⟩
  have hπD' : ∀ i, ∃ w : D, D.subtype w =
      algebraMap Λ (truncatedLocalization Λ q (N + 8 * d * c + 1)) (φ (π i)) :=
    fun i => ⟨⟨_, hφmem (π i)⟩, rfl⟩
  -- step (13)
  obtain ⟨δ, lam, D', instCRD', instLRD', instARD', cc, b', instLHcc, instLHb', hess', hflat',
    hcomp', hδq, hrel, hlamD', hδD', hannΛ0⟩ :=
    exists_essentiallySmooth_enlargement_annihilator_sq_eq k p hp Λ q hd hN hNn he
      (fun j => algebraMap A Λ (a j)) hqN' (fun i => φ (π i))
      (fun i => Ideal.mem_comap.mp (hπmem i)) hπΛspan D.subtype hDflat haD' hπD'
  -- step (14): the maps `B → Λ` and `C → Λ`
  -- step (15): the twisted base `R = k[y, t]` with its two structure maps
  let instkxR : Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) :=
    (twistedBaseHom π).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) :=
    IsScalarTower.of_algebraMap_eq fun x => ((twistedBaseHom π).commutes x).symm
  let instRΛ : Algebra (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
    (twistedBaseToTarget φ δ).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
    IsScalarTower.of_algebraMap_eq fun x => ((twistedBaseToTarget φ δ).commutes x).symm
  let instkC : Algebra k C := ((algebraMap (MvPolynomial (Fin d) k) C).comp
    (algebraMap k (MvPolynomial (Fin d) k))).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin d) k) C :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := MvPolynomial (Fin d) k) (A := C) fun x => rfl
  let instAC : Algebra A C := ((algebraMap (parameterPowerAlgebra A d N a) C).comp
    (algebraMap A (parameterPowerAlgebra A d N a))).toAlgebra
  have : IsScalarTower A (parameterPowerAlgebra A d N a) C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := parameterPowerAlgebra A d N a) (A := C)
      fun x => rfl
  have : IsScalarTower k A C := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change algebraMap (MvPolynomial (Fin d) k) C (algebraMap k (MvPolynomial (Fin d) k) x) =
      algebraMap (parameterPowerAlgebra A d N a) C
        (algebraMap A (parameterPowerAlgebra A d N a) (algebraMap k A x))
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) C,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k)
        (parameterPowerAlgebra A d N a),
      ← IsScalarTower.algebraMap_apply k A (parameterPowerAlgebra A d N a)]
  -- the maps `k[x] → R → Λ` and `k[x] → C → Λ` agree
  have hgrtB : ∀ x : parameterPowerAlgebra A d N a,
      grt (algebraMap (parameterPowerAlgebra A d N a) C x) = x :=
    fun x => AlgHom.congr_fun hretract x
  have halgR : ∀ y : MvPolynomial (Fin m ⊕ Fin d) k,
      algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ y = twistedBaseToTarget φ δ y :=
    fun _ => rfl
  have hvalγ : ∀ i, twistedBaseToTarget φ δ (twistedParameter π i) = φ (π i) * δ i := by
    intro i
    rw [twistedParameter, map_mul, twistedBaseToTarget_X_inr]
    congr 1
    exact AlgHom.congr_fun (twistedBaseToTarget_comp_rename φ δ) (π i)
  have hAC : ∀ x : A, improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
      (algebraMap A C x) = algebraMap A Λ x := by
    intro x
    rw [improvedAlgebraToTarget_apply]
    change parameterPowerAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel
      (grt (algebraMap (parameterPowerAlgebra A d N a) C
        (algebraMap A (parameterPowerAlgebra A d N a) x))) = _
    rw [hgrtB]
    exact (parameterPowerAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel).commutes x
  have hfCk : ∀ r : k, improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
      (algebraMap k C r) = algebraMap k Λ r := by
    intro r
    rw [IsScalarTower.algebraMap_apply k A C, hAC, ← IsScalarTower.algebraMap_apply k A Λ]
  have hcompat : ∀ y : MvPolynomial (Fin d) k,
      algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ
          (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) y) =
        improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
          (algebraMap (MvPolynomial (Fin d) k) C y) := by
    intro y
    have key : ((IsScalarTower.toAlgHom k (MvPolynomial (Fin m ⊕ Fin d) k) Λ).comp
          (twistedBaseHom π) : MvPolynomial (Fin d) k →ₐ[k] Λ)
        = (({ toRingHom := improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
              commutes' := hfCk } : C →ₐ[k] Λ)).comp
            (IsScalarTower.toAlgHom k (MvPolynomial (Fin d) k) C) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      change algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ
          (twistedBaseHom π (MvPolynomial.X i)) =
        improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
          (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i))
      rw [twistedBaseHom_X, halgR, hvalγ i,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k)
          (parameterPowerAlgebra A d N a) C,
        algebraMap_mvPolynomial_parameterPowerAlgebra_X, improvedAlgebraToTarget_apply,
        hgrtB, parameterPowerAlgebraToTarget_X_inl]
      ring
    exact AlgHom.congr_fun key y
  -- the ring map `R ⊗_{k[x]} C → Λ`
  let instkxΛ : Algebra (MvPolynomial (Fin d) k) Λ :=
    ((algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ).comp
      (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
    IsScalarTower.of_algebraMap_eq' rfl
  let fRalg : MvPolynomial (Fin m ⊕ Fin d) k →ₐ[MvPolynomial (Fin d) k] Λ :=
    IsScalarTower.toAlgHom _ _ _
  let fCalg : C →ₐ[MvPolynomial (Fin d) k] Λ :=
    { toRingHom := improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
      commutes' := fun y => (hcompat y).symm }
  let instTensΛ : Algebra
      (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ :=
    (Algebra.TensorProduct.lift fRalg fCalg fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  have : IsScalarTower (MvPolynomial (Fin m ⊕ Fin d) k)
      (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ := by
    refine IsScalarTower.of_algebraMap_eq (R := MvPolynomial (Fin m ⊕ Fin d) k)
      (S := MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) (A := Λ) fun x => ?_
    change (algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ) x =
      Algebra.TensorProduct.lift fRalg fCalg (fun _ _ => Commute.all _ _)
        (x ⊗ₜ[MvPolynomial (Fin d) k] (1 : C))
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  -- step (16): Stacks 07G0
  have hmemsing : ∀ j, a j ∈ singularIdeal k A := fun j => ha ▸ Ideal.subset_span ⟨j, rfl⟩
  have : Algebra.Smooth k (MvPolynomial (Fin m ⊕ Fin d) k) := ⟨inferInstance, inferInstance⟩
  have hAΛ : ∀ x : A,
      algebraMap (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ
          (Algebra.TensorProduct.includeRight (algebraMap A C x)) = algebraMap A Λ x := by
    intro x
    change Algebra.TensorProduct.lift fRalg fCalg (fun _ _ => Commute.all _ _)
      (Algebra.TensorProduct.includeRight (algebraMap A C x)) = _
    rw [show Algebra.TensorProduct.lift fRalg fCalg (fun _ _ => Commute.all _ _)
      (Algebra.TensorProduct.includeRight (algebraMap A C x)) = fCalg (algebraMap A C x) from
      AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeRight' fRalg fCalg
        (fun _ _ => Commute.all _ _)) (algebraMap A C x)]
    exact hAC x
  refine canBeResolved_of_canBeResolved_tensorProduct
    (R := MvPolynomial (Fin m ⊕ Fin d) k) (C := C) q ha hAΛ
    (forall_algebraMap_mem_singularIdeal_parameterPowerAlgebra k A d N a hmemsing)
    (fun b hb => (hC₁ b hb).1) ?_
  -- step (17): Stacks 07G2
  set eeq : MvPolynomial (Fin m ⊕ Fin d) k ≃+* MvPolynomial (Fin d) (MvPolynomial (Fin m) k) :=
    ((MvPolynomial.renameEquiv k (Equiv.sumComm (Fin m) (Fin d))).trans
      (MvPolynomial.sumAlgEquiv k (Fin d) (Fin m))).toRingEquiv with heeq
  refine canBeResolved_of_quotient_span_pow q hd1 (twistedParameter π) c _ rfl ?_ ?_ ?_ ?_ ?_
  · intro i
    rw [map_pow]
    refine Ideal.pow_mem_of_mem _ ?_ _ hc
    rw [halgR, hvalγ i]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_comap.mp (hπmem i))
  · intro i
    refine annihilator_span_singleton_eq_sq_of_forall _ ?_
    have hγe : ∀ j, (eeq : MvPolynomial (Fin m ⊕ Fin d) k ≃+* _) (twistedParameter π j)
        = scaledVariable π j := by
      intro j
      change (MvPolynomial.sumAlgEquiv k (Fin d) (Fin m))
        ((MvPolynomial.renameEquiv k (Equiv.sumComm (Fin m) (Fin d)))
          (twistedParameter π j)) = scaledVariable π j
      rw [twistedParameter, map_mul, map_mul, scaledVariable_apply]
      congr 1
      · rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
        exact AlgHom.congr_fun
          (MvPolynomial.sumAlgEquiv_comp_rename_inr k (Fin d) (Fin m)) (π j)
      · simp
    refine forall_mul_ann_iff_of_ringEquiv eeq _ (twistedParameter π i ^ c) ?_
    have hK : Ideal.map (eeq : MvPolynomial (Fin m ⊕ Fin d) k →+* _)
        (eighthPowerPrefixIdeal (fun j => twistedParameter π j ^ c) i)
        = Ideal.span (Set.range fun j : Fin i.1 =>
            scaledVariable π (j.castLE (Nat.le_of_lt i.isLt)) ^ (8 * c)) :=
      map_eighthPowerPrefixIdeal_pow_eq_span _ _ _ c i hγe
    refine forall_mul_ann_iff_of_ideal_eq hK ?_
    have hel : eeq (twistedParameter π i ^ c) = scaledVariable π i ^ c := by
      rw [map_pow]
      exact congrArg (· ^ c) (hγe i)
    intro x
    rw [hel, map_pow]
    exact mul_pow_ann_iff (fun y => by simpa only [map_pow] using hannR0 i y) hc x
  · intro i
    have hz : algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ (twistedParameter π i ^ c)
        = (δ i * φ (π i)) ^ c := by
      rw [map_pow, halgR, hvalγ i, mul_comm]
    rw [hz]
    refine annihilator_span_singleton_eq_sq_of_forall _ ?_
    have hK : Ideal.map (algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ)
        (eighthPowerPrefixIdeal (fun j => twistedParameter π j ^ c) i)
        = Ideal.span (Set.range fun j : Fin i.1 =>
            (δ (j.castLE (Nat.le_of_lt i.isLt)) * φ (π (j.castLE (Nat.le_of_lt i.isLt))))
              ^ (8 * c)) :=
      map_eighthPowerPrefixIdeal_pow_eq_span (algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ)
        (twistedParameter π) (fun j => δ j * φ (π j)) c i
        fun j => by rw [halgR, hvalγ j, mul_comm]
    refine forall_mul_ann_iff_of_ideal_eq hK ?_
    intro x
    rw [map_pow]
    exact mul_pow_ann_iff (fun y => by simpa only [map_pow] using hannΛ0 i y) hc x
  · intro i
    have hss := isStrictlyStandard_tensorProduct_pow_X (k := k) (d := d)
      (R := MvPolynomial (Fin m ⊕ Fin d) k) (C := C) c i (hstdC i)
    rwa [show algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k)
      (MvPolynomial.X i) = twistedParameter π i from twistedBaseHom_X π i] at hss
  · exact hback k A Λ q a C grt φ gl u D aD π δ lam D' cc b' hN hc hd1 hn hNn hnbound hq ha
      hqN hd
      (fun y => IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k)
        (parameterPowerAlgebra A d N a) C y)
      hgrtB hmapφ hgφ hgflat hu hDsub hAD hlocP hartP hlocQ hartQ hlocD hartD hess hDflat
      hdimP hπmem hπspan hπΛspan instLHcc instLHb' hess' hflat' hcomp' hδq hrel hlamD' hδD'
      hstdC hcompat

/-- **The reduction of Stacks 07FJ.** Let `k → A → Λ ⊃ 𝔮` be as in Situation 07F7 with `k` of
characteristic `p > 0`, `Λ` Noetherian and geometrically regular over `k`, and `𝔮` minimal over
`𝔥_A = √(H_{A/k} Λ)`. Granting the hypotheses below, `k → A → Λ ⊃ 𝔮` can be resolved; that is,
`Stacks.Smoothing.CanBeResolvedInPositiveCharacteristic` holds.

This is a reduction, not a proof of Stacks 07FJ, and it carries no `@[stacks 07FJ]` tag: a
result conditional on a hypothesis is not a formalization of the result. Both hypotheses are
proved downstream of this file, where the tag sits
(`Stacks.Smoothing.canBeResolvedInPositiveCharacteristic`). They are:

* `HasArtinianApproximationData`, item (9) of the source's proof — Stacks 07FT in full
  generality, which is clauses (2) and (3) of Stacks 07FH without the restriction to residue
  fields essentially of finite type over `k`. This is the deep input: with both hypotheses
  discharged the theorem is Stacks 07FJ, hence Popescu's theorem 07GC and then 07QY, 07QZ,
  0AH5 and 0CAR — all of which are proved unconditionally.
* `TwistedQuotientResolvable`, items (18)–(26) of the source's proof.

The case `dim Λ_𝔮 = 0` is not a hypothesis: `zeroDimensionalSeparableResidue` proves it
and the reduction to Stacks 07FE uses that theorem directly.

Items (1)–(17) are proved here: the choices of `N`, of generators `a_1, …, a_t` of `H_{A/k}`, of
`d = dim Λ_𝔮`, of the algebras `B` and `C` with the retraction `C → B`, of `c`, of the finite
set `E`, of the parameters `π_i` and their rescalings, of the units `δ_i` and the coefficients
`λ_{ij}`, together with the two reductions of Stacks 07G0 and 07G2 that turn the chain
`k → A → Λ ⊃ 𝔮` into the twisted quotient chain of item (22). -/
theorem canBeResolvedInPositiveCharacteristic_of_hasArtinianApproximationData
    (h07FT : HasArtinianApproximationData.{u})
    (hback : TwistedQuotientResolvable.{u}) :
    CanBeResolvedInPositiveCharacteristic.{u} := by
  intro k A Λ _ _ _ _ _ _ _ _ _ _ p _ hp q _ hq
  exact canBeResolved_of_hasArtinianApproximationData h07FT hback k A Λ p hp q hq

end Stacks.Smoothing

end
