module

public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Index
public import StacksFrontier.RingTheory.Localization.GenericFibreComponents

/-!
# The branches at a point and the components dominating the base, as one index set

Let `O` be a domain, `C` an `O`-algebra, `T` the localization of `C` at the nonzero elements of
`O`, and `𝔮` a prime of `C` with `S` a localization of `C` at `𝔮`. Geometrically: `V = Spec O` is
integral, `U = Spec C` is a `V`-scheme, `T` is the ring of the fibre `G` of `U → V` over the
generic point of `V`, and `S = 𝒪_{U, u}` is the local ring of `U` at the point `u` cut out by
`𝔮`.

Two index sets attached to this picture occur in the proof of **Stacks 0EQ4**:

* the *branches of `U` at `u`*, that is the minimal primes of the local ring `S`, which is what
  `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_finsum_minimalPrimeOrd` (Stacks 0ENM) sums the
  order of vanishing over; and
* the *components of `U` dominating `V`*, that is the primes `P` of `C` with `P ∩ O = 0`, which
  is what `AlgebraicGeometry.Space.norm_eq_finprod_norm_quotient_of_isPushout_fibre` takes the
  product of norms over, and which `Stacks.GenericFibre.primeSpectrumEquivDominatingOfLocalization`
  identifies with the primes of the generic fibre `T`.

Contraction `Ideal.under C` carries the minimal primes of `S` onto the minimal primes of `C`
contained in `𝔮` — the components of `U` through `u` — and, restricted to those which dominate `V`,
onto the primes of `T` whose component passes through `u`:

`{𝔭 ⊆ S minimal : 𝔭 ∩ O = 0}  ≃  {p ⊆ T prime : (p ∩ C) ⊆ 𝔮}`.

The only hypothesis is `IsArtinianRing T`, which makes a dominating prime of `C` a *minimal*
prime of `C`; it holds when `C` is finite over `O`
(`Stacks.GenericFibre.isArtinianRing_of_localization`).

## Main definitions and results

* `Stacks.GenericFibre.disjoint_primeCompl_iff_le`: a prime complement is disjoint from an ideal
  exactly when the ideal is contained in the prime.
* `Stacks.GenericFibre.minimalPrimesStalkEquiv`: **the branches at `u` are the components of `U`
  through `u`.** The minimal primes of a localization of `C` at a prime `𝔮` are, by contraction,
  the minimal primes of `C` contained in `𝔮`.
* `Stacks.GenericFibre.minimalPrimesStalkEquivOfIsAffine`: that statement for the local ring of an
  affine scheme at a point.
* `Stacks.GenericFibre.mem_minimalPrimes_of_under_eq_bot`: a prime of `C` contracting to the zero
  ideal of `O` is a minimal prime of `C`, when the generic fibre is Artinian.
* `Stacks.GenericFibre.minimalPrimesDominatingEquivPrimeSpectrum`: the dominating components of
  `U` recorded as minimal primes of `C` and merely as primes of `C` are the same index set.
* `Stacks.GenericFibre.minimalPrimesStalkDominatingEquivDominatingComponents` and
  `Stacks.GenericFibre.primeSpectrumFibreThroughEquivDominatingComponents`: the two halves of the
  reconciliation, each landing on the dominating components of `U` through `u`, with
  `Stacks.GenericFibre.asIdeal_minimalPrimesStalkDominatingEquivDominatingComponents` and
  `Stacks.GenericFibre.asIdeal_primeSpectrumFibreThroughEquivDominatingComponents` saying that
  each is contraction.
* `Stacks.GenericFibre.minimalPrimesStalkDominatingEquivPrimeSpectrumFibre`: **the
  reconciliation.** The branches of `U` at `u` which dominate `V` are the primes of the generic
  fibre whose component contains `u`.
* `Stacks.GenericFibre.under_minimalPrimesStalkDominatingEquivPrimeSpectrumFibre`: that bijection
  is contraction.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

open scoped nonZeroDivisors

universe u

namespace Stacks.GenericFibre

/-! ### The branches at a point as the components through it -/

section Branches

variable (C : Type u) [CommRing C] (𝔮 : Ideal C) [𝔮.IsPrime]
  (S : Type u) [CommRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔮]

/-- **A prime complement is disjoint from an ideal exactly when the ideal lies in the prime.** -/
theorem disjoint_primeCompl_iff_le {I : Ideal C} :
    Disjoint (𝔮.primeCompl : Set C) (I : Set C) ↔ I ≤ 𝔮 := by
  simp [Ideal.primeCompl, Set.disjoint_compl_left_iff_subset, SetLike.coe_subset_coe]

/-- **The branches of `U = Spec C` at a point `u` are the components of `U` through `u`.** For `S`
a localization of `C` at the prime `𝔮` of `u`, contraction is a bijection from the minimal primes
of `S` onto the minimal primes of `C` contained in `𝔮`.

This is `Stacks.MinimalPrimeResidueLocalization.minimalPrimesEquivDisjoint` at
`M = 𝔮.primeCompl`, where disjointness from `M` is containment in `𝔮`. -/
def minimalPrimesStalkEquiv :
    ↥(minimalPrimes S) ≃ {P : ↥(minimalPrimes C) // (P : Ideal C) ≤ 𝔮} :=
  (Stacks.MinimalPrimeResidueLocalization.minimalPrimesEquivDisjoint C 𝔮.primeCompl S).trans
    (Equiv.subtypeEquivRight fun _ => disjoint_primeCompl_iff_le C 𝔮)

/-- The bijection of `Stacks.GenericFibre.minimalPrimesStalkEquiv` is contraction of ideals. -/
theorem under_minimalPrimesStalkEquiv (𝔭 : ↥(minimalPrimes S)) :
    ((minimalPrimesStalkEquiv C 𝔮 S 𝔭).1 : Ideal C) = (𝔭 : Ideal S).under C :=
  rfl

end Branches

/-- **The branches of an affine scheme at a point are its components through that point.** For
`X` an affine scheme and `u` a point of it, contraction is a bijection from the minimal primes of
the local ring `𝒪_{X, u}` onto the minimal primes of `Γ(X)` contained in the prime of `u`.

This is `Stacks.GenericFibre.minimalPrimesStalkEquiv` at `S = 𝒪_{X, u}`, whose
`Γ(X)`-algebra structure and localization property are
`AlgebraicGeometry.Scheme.Presheaf.algebra_section_stalk` and
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` at the open `⊤`. -/
def minimalPrimesStalkEquivOfIsAffine (X : Scheme.{u}) [IsAffine X] (u : X) :
    ↥(minimalPrimes ↥(X.presheaf.stalk u)) ≃
      {P : ↥(minimalPrimes ↥Γ(X, ⊤)) //
        (P : Ideal ↥Γ(X, ⊤)) ≤ ((isAffineOpen_top X).primeIdealOf ⟨u, trivial⟩).asIdeal} :=
  letI : Algebra ↥Γ(X, ⊤) ↥(X.presheaf.stalk u) :=
    X.presheaf.algebra_section_stalk (⟨u, trivial⟩ : (⊤ : X.Opens))
  haveI : IsLocalization.AtPrime ↥(X.presheaf.stalk u)
      ((isAffineOpen_top X).primeIdealOf ⟨u, trivial⟩).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨u, trivial⟩
  minimalPrimesStalkEquiv ↥Γ(X, ⊤) ((isAffineOpen_top X).primeIdealOf ⟨u, trivial⟩).asIdeal
    ↥(X.presheaf.stalk u)

/-! ### The dominating components are minimal -/

section Dominating

variable (O : Type*) [CommRing O] [IsDomain O] (C : Type u) [CommRing C] [Algebra O C]
  (T : Type*) [CommRing T] [Algebra C T] [IsLocalization (Algebra.algebraMapSubmonoid C O⁰) T]

include O T in
/-- **A component of `U = Spec C` dominating `V = Spec O` is an irreducible component of `U`.**
If the generic fibre `T` is Artinian then every prime `P` of `C` with `P ∩ O = 0` is a minimal
prime of `C`. -/
theorem mem_minimalPrimes_of_under_eq_bot [IsArtinianRing T] (P : Ideal C) [hP : P.IsPrime]
    (hPO : P.under O = ⊥) : P ∈ minimalPrimes C := by
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid C O⁰ : Set C) (P : Set C) :=
    (Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot P).mpr hPO
  have : (P.map (algebraMap C T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P hP hdisj
  have h := under_mem_minimalPrimes_of_localization O C T (P.map (algebraMap C T))
  rwa [IsLocalization.under_map_of_isPrime_disjoint _ _ hP hdisj] at h

/-- **The dominating components of `U`, recorded as minimal primes or merely as primes.** If the
generic fibre is Artinian, the minimal primes of `C` contracting to the zero ideal of `O` and
contained in `𝔮` are the primes of `C` with these two properties. -/
def minimalPrimesDominatingEquivPrimeSpectrum [IsArtinianRing T] (𝔮 : Ideal C) :
    {P : ↥(minimalPrimes C) // (P : Ideal C).under O = ⊥ ∧ (P : Ideal C) ≤ 𝔮} ≃
      {P : PrimeSpectrum C // P.asIdeal.under O = ⊥ ∧ P.asIdeal ≤ 𝔮} where
  toFun P := ⟨⟨(P.1 : Ideal C), P.1.2.1.1⟩, P.2⟩
  invFun P :=
    ⟨⟨P.1.asIdeal, haveI := P.1.isPrime
        mem_minimalPrimes_of_under_eq_bot O C T P.1.asIdeal P.2.1⟩, P.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Dominating

/-! ### The reconciliation -/

section Reconciliation

variable (O : Type*) [CommRing O] [IsDomain O] (C : Type u) [CommRing C] [Algebra O C]
  (T : Type*) [CommRing T] [Algebra C T] [IsLocalization (Algebra.algebraMapSubmonoid C O⁰) T]
  (𝔮 : Ideal C) [𝔮.IsPrime] (S : Type u) [CommRing S] [Algebra C S]
  [IsLocalization.AtPrime S 𝔮]

/-- **The dominating branches at `u`, as dominating components of `U` through `u`.** Contraction
carries a minimal prime of `S` contracting to the zero ideal of `O` to a prime of `C` which
dominates `V` and is contained in `𝔮`. -/
def minimalPrimesStalkDominatingEquivDominatingComponents [IsArtinianRing T] :
    {𝔭 : ↥(minimalPrimes S) // ((𝔭 : Ideal S).under C).under O = ⊥} ≃
      {P : PrimeSpectrum C // P.asIdeal.under O = ⊥ ∧ P.asIdeal ≤ 𝔮} :=
  (Equiv.subtypeEquiv (minimalPrimesStalkEquiv C 𝔮 S) fun _ => Iff.rfl).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter
        (p := fun P : ↥(minimalPrimes C) => (P : Ideal C) ≤ 𝔮)
        (q := fun P : ↥(minimalPrimes C) => (P : Ideal C).under O = ⊥)).trans
      ((Equiv.subtypeEquivRight fun _ => and_comm).trans
        (minimalPrimesDominatingEquivPrimeSpectrum O C T 𝔮)))

/-- The bijection of
`Stacks.GenericFibre.minimalPrimesStalkDominatingEquivDominatingComponents` is contraction. -/
theorem asIdeal_minimalPrimesStalkDominatingEquivDominatingComponents [IsArtinianRing T]
    (𝔭 : {𝔭 : ↥(minimalPrimes S) // ((𝔭 : Ideal S).under C).under O = ⊥}) :
    (minimalPrimesStalkDominatingEquivDominatingComponents O C T 𝔮 S 𝔭 :
      PrimeSpectrum C).asIdeal = (𝔭.1 : Ideal S).under C :=
  rfl

/-- **The primes of the generic fibre whose component passes through `u`, as dominating
components of `U` through `u`.** Contraction is a bijection from the primes `p` of the generic
fibre `T` with `p ∩ C ⊆ 𝔮` onto the primes of `C` which dominate `V` and are contained in `𝔮`. -/
def primeSpectrumFibreThroughEquivDominatingComponents :
    {p : PrimeSpectrum T // p.asIdeal.under C ≤ 𝔮} ≃
      {P : PrimeSpectrum C // P.asIdeal.under O = ⊥ ∧ P.asIdeal ≤ 𝔮} :=
  (Equiv.subtypeEquiv (primeSpectrumEquivDominatingOfLocalization O C T) fun _ => Iff.rfl).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (p := fun P : PrimeSpectrum C => P.asIdeal.under O = ⊥)
      (q := fun P : PrimeSpectrum C => P.asIdeal ≤ 𝔮))

omit [𝔮.IsPrime] in
/-- The bijection of `Stacks.GenericFibre.primeSpectrumFibreThroughEquivDominatingComponents` is
contraction. -/
theorem asIdeal_primeSpectrumFibreThroughEquivDominatingComponents
    (p : {p : PrimeSpectrum T // p.asIdeal.under C ≤ 𝔮}) :
    (primeSpectrumFibreThroughEquivDominatingComponents O C T 𝔮 p :
      PrimeSpectrum C).asIdeal = (p.1 : PrimeSpectrum T).asIdeal.under C :=
  rfl

/-- **The branches of `U` at `u` which dominate `V`, as primes of the generic fibre.** Let `O` be
a domain, `C` an `O`-algebra whose generic fibre `T` — the localization of `C` at `O⁰` — is
Artinian, let `𝔮` be a prime of `C` and `S` a localization of `C` at `𝔮`. Then contraction is a
bijection

`{𝔭 ⊆ S minimal : 𝔭 ∩ O = 0}  ≃  {p ⊆ T prime : (p ∩ C) ⊆ 𝔮}`

between the branches of `U = Spec C` at the point `u` cut out by `𝔮` which dominate `V = Spec O`,
and the primes of the generic fibre whose component of `U` passes through `u`.

This is the index reconciliation the proof of Stacks 0EQ4 needs between the sum of Stacks 0ENM
over the branches of a chart and the product over the components dominating the base in
`AlgebraicGeometry.Space.norm_eq_finprod_norm_quotient_of_isPushout_fibre`. It is
`Stacks.GenericFibre.minimalPrimesStalkEquiv` on the left,
`Stacks.GenericFibre.primeSpectrumEquivDominatingOfLocalization` on the right, and
`Stacks.GenericFibre.minimalPrimesDominatingEquivPrimeSpectrum` in the middle. -/
def minimalPrimesStalkDominatingEquivPrimeSpectrumFibre [IsArtinianRing T] :
    {𝔭 : ↥(minimalPrimes S) // ((𝔭 : Ideal S).under C).under O = ⊥} ≃
      {p : PrimeSpectrum T // p.asIdeal.under C ≤ 𝔮} :=
  (minimalPrimesStalkDominatingEquivDominatingComponents O C T 𝔮 S).trans
    (primeSpectrumFibreThroughEquivDominatingComponents O C T 𝔮).symm

/-- The bijection of
`Stacks.GenericFibre.minimalPrimesStalkDominatingEquivPrimeSpectrumFibre` is contraction: the
prime of the generic fibre it names contracts to the contraction of the branch. -/
theorem under_minimalPrimesStalkDominatingEquivPrimeSpectrumFibre [IsArtinianRing T]
    (𝔭 : {𝔭 : ↥(minimalPrimes S) // ((𝔭 : Ideal S).under C).under O = ⊥}) :
    ((minimalPrimesStalkDominatingEquivPrimeSpectrumFibre O C T 𝔮 S 𝔭 : PrimeSpectrum T).asIdeal
      ).under C = (𝔭.1 : Ideal S).under C := by
  have h : primeSpectrumFibreThroughEquivDominatingComponents O C T 𝔮
      (minimalPrimesStalkDominatingEquivPrimeSpectrumFibre O C T 𝔮 S 𝔭) =
      minimalPrimesStalkDominatingEquivDominatingComponents O C T 𝔮 S 𝔭 :=
    (primeSpectrumFibreThroughEquivDominatingComponents O C T 𝔮).apply_symm_apply _
  exact (asIdeal_primeSpectrumFibreThroughEquivDominatingComponents O C T 𝔮 _).symm.trans
    (congrArg (fun P : {P : PrimeSpectrum C // P.asIdeal.under O = ⊥ ∧ P.asIdeal ≤ 𝔮} =>
      (P : PrimeSpectrum C).asIdeal) h)

end Reconciliation

end Stacks.GenericFibre

end
