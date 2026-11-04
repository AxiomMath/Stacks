module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.CommonRefinement
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FormulaSymbol
public import StacksFrontier.RingTheory.KrullDimension.GoingUpGoingDown
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0EAR: the formula of Stacks 0EAQ is well defined

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `a` be a family of
nonzerodivisors of `A`, not all units. Stacks 0EAG produces a finite extension `A ⊆ B` carrying a
simultaneous power factorization of the family at each maximal ideal of `B` — an
`AlgebraicGeometry.TameSymbolPreparation` — and the formula of Stacks 0EAQ attaches to it the
element `AlgebraicGeometry.TameSymbolPreparation.symbolValue` of `κ(𝔪)^*`. Stacks 0EAR says that
element depends on neither choice.

This file proves that, at the source's hypotheses and nothing more.

## What this file supplies

The comparison itself is
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_common_refinement`, which routes two
preparations through a common finite refinement `C` of the two extensions and carries, besides
that refinement, the hypotheses of Stacks 0EAT for `A ⊆ C` read at the maximal ideals of `B` and
of `B'`. Everything it carries is produced here from the preparations:

* the refinement is `Stacks.Chow.nonempty_commonRefinement`, the quotient of `B ⊗_A B'` by its
  `𝔪`-power torsion that the source uses;
* `AlgebraicGeometry.TameSymbolPreparation.algebraMap_mem_nonZeroDivisors` makes each member of the
  prepared family a nonzerodivisor of the extension — the local parameters are regular and the
  members are units times their powers — which is what feeds the refinement its nonzerodivisor;
* the non-associated-prime hypotheses on `B`, `B'`, `C` and on the semilocalizations `C_𝔮` are
  `Stacks.Chow.not_isAssociatedPrime_maximalIdeal_of_smul_injective`: a nonzerodivisor in the
  maximal ideal kills no nonzero element, so the maximal ideal is nobody's annihilator;
* the four instances the formula and Stacks 0EAT ask for at the maximal ideals of the extensions
  — Noetherian, Krull dimension at most one, locality of the structure map, and finiteness of the
  maximal spectrum of each semilocalization — are
  `Stacks.Chow.isNoetherianRing_localization_of_moduleFinite`,
  `Stacks.Chow.krullDimLE_one_localization_of_moduleFinite`,
  `Stacks.Length.isLocalHom_algebraMap_localization` and
  `Stacks.Localization.finite_maximalSpectrum_semilocalization`;
* the family of tame symbols on the local rings of the refinement is
  `Stacks.Chow.regularTameSymbolOfKrullDimOne` of each of them, available because
  `Stacks.Chow.ringKrullDim_localization_eq_one_of_nonZeroDivisor` makes each one-dimensional.

## Main results

* `AlgebraicGeometry.TameSymbolPreparation.algebraMap_mem_nonZeroDivisors` — a prepared element is
  a nonzerodivisor of the extension.
* `Stacks.Chow.not_isAssociatedPrime_maximalIdeal_of_smul_injective` — a nonzerodivisor in the
  maximal ideal rules the maximal ideal out of the associated primes.
* `Stacks.Chow.krullDimLE_one_of_moduleFinite`,
  `Stacks.Chow.isNoetherianRing_localization_of_moduleFinite`,
  `Stacks.Chow.krullDimLE_one_localization_of_moduleFinite` — the Noetherian and dimension
  hypotheses at the maximal ideals of a finite extension, derived from those on the base.
* `Stacks.Chow.ringKrullDim_localization_eq_one_of_nonZeroDivisor` — a maximal ideal of a finite
  extension carrying a nonzerodivisor from the maximal ideal of the base localizes to a
  one-dimensional ring.

## References

* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v w

namespace Stacks.Chow

/-! ### The maximal ideal is not an associated prime -/

/-- **A nonzerodivisor in the maximal ideal rules the maximal ideal out of the associated
primes.** If `s ∈ 𝔪` kills no nonzero element of `M`, then the annihilator of a nonzero element
misses `s`, so it is not `𝔪`; and the annihilator of `0` is the whole ring. -/
theorem not_isAssociatedPrime_maximalIdeal_of_smul_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {s : R} (hsm : s ∈ maximalIdeal R)
    (hs : ∀ x : M, s • x = 0 → x = 0) : ¬ IsAssociatedPrime (maximalIdeal R) M := by
  intro h
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp h
  have hx0 : x = 0 := by
    refine hs x ?_
    have hmem : s ∈ (⊥ : Submodule R M).colon {x} := hx ▸ hsm
    simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using hmem
  refine hprime.ne_top ?_
  rw [hx, hx0, eq_top_iff]
  intro t _
  rw [Submodule.mem_colon_singleton, smul_zero]
  exact Submodule.zero_mem _

/-- **The maximal ideal of the base is not an associated prime of an algebra in which an element
of it stays a nonzerodivisor.** -/
theorem not_isAssociatedPrime_maximalIdeal_of_mem_nonZeroDivisors
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] {s : R} (hsm : s ∈ maximalIdeal R)
    (hs : algebraMap R S s ∈ nonZeroDivisors S) : ¬ IsAssociatedPrime (maximalIdeal R) S :=
  not_isAssociatedPrime_maximalIdeal_of_smul_injective hsm fun x hx =>
    (mem_nonZeroDivisors_iff.mp hs).1 x (by rwa [← Algebra.smul_def])

/-! ### The hypotheses at the maximal ideals of a finite extension -/

section Localized

variable {A : Type u} [CommRing A] [IsLocalRing A] {C : Type w} [CommRing C] [Algebra A C]
  [Module.Finite A C]

omit [IsLocalRing A] in
/-- **A finite extension of a ring of Krull dimension at most one has Krull dimension at most
one.** A finite ring map is integral, and an integral extension does not raise the dimension
(Stacks 00OJ). -/
@[ega "0 16.1.5" "special case"]
theorem krullDimLE_one_of_moduleFinite [Ring.KrullDimLE 1 A] : Ring.KrullDimLE 1 C := by
  rw [Ring.krullDimLE_iff]
  refine le_trans (integral_dim_up (algebraMap A C) ?_).1
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A))
  exact (Algebra.IsIntegral.of_finite A C).isIntegral

omit [IsLocalRing A] in
/-- **The localizations of a finite extension of a Noetherian ring at its maximal ideals are
Noetherian.** -/
theorem isNoetherianRing_localization_of_moduleFinite [IsNoetherianRing A]
    (q : MaximalSpectrum C) : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
  have : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance

omit [IsLocalRing A] in
/-- **The localizations of a finite extension at its maximal ideals have Krull dimension at most
one** when the base does. -/
theorem krullDimLE_one_localization_of_moduleFinite [Ring.KrullDimLE 1 A]
    (q : MaximalSpectrum C) : Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) :=
  have : Ring.KrullDimLE 1 C := krullDimLE_one_of_moduleFinite (A := A)
  Stacks.Localization.krullDimLE_one_localizationAtPrime q.asIdeal

omit [IsLocalRing A] [Module.Finite A C] in
/-- **An element of the maximal ideal of the base that is a nonzerodivisor of a finite extension
stays a nonzerodivisor in the localization at a maximal ideal, and lies in its maximal ideal.** -/
theorem algebraMap_localization_mem_nonZeroDivisors {s : A}
    (hs : algebraMap A C s ∈ nonZeroDivisors C) (q : MaximalSpectrum C) :
    algebraMap A (Localization.AtPrime q.asIdeal) s ∈
      nonZeroDivisors (Localization.AtPrime q.asIdeal) := by
  rw [IsScalarTower.algebraMap_apply A C (Localization.AtPrime q.asIdeal)]
  exact IsLocalization.map_nonZeroDivisors_le q.asIdeal.primeCompl _ ⟨_, hs, rfl⟩

/-- **The localization of a finite extension at a maximal ideal is one-dimensional** as soon as
some element of the maximal ideal of the base is a nonzerodivisor there: the dimension is at most
one because the base's is, and the nonzerodivisor in the maximal ideal makes it exactly one. -/
theorem ringKrullDim_localization_eq_one_of_nonZeroDivisor [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {s : A} (hsm : s ∈ maximalIdeal A)
    (hs : algebraMap A C s ∈ nonZeroDivisors C) (q : MaximalSpectrum C) :
    ringKrullDim (Localization.AtPrime q.asIdeal) = 1 := by
  let := Stacks.Length.isLocalHom_algebraMap_localization (A := A) q
  let := krullDimLE_one_localization_of_moduleFinite (A := A) q
  refine ringKrullDim_eq_one_of_mem_maximalIdeal
    (algebraMap_localization_mem_nonZeroDivisors (A := A) hs q) ?_
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact mem_nonunits_iff.mp ((mem_maximalIdeal s).mp hsm)
    (isUnit_of_map_unit (algebraMap A (Localization.AtPrime q.asIdeal)) s hu)

end Localized


/-! ### The hypotheses at the maximal ideals of the base of a tower -/

section Fibre

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  {C : Type w} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **A semilocalization of an injective extension is again injective.** An element of `B_𝔮`
dying in `C_𝔮` is `b/u` with `v b` zero in `C` for some `v ∉ 𝔮`, hence with `v b = 0` in `B`. -/
theorem injective_algebraMap_semilocalization
    (hinj : Function.Injective (algebraMap B C)) (q : MaximalSpectrum B) :
    Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨⟨b, u⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl x
  rw [IsLocalization.algebraMap_mk' C (Localization.AtPrime q.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)) b u,
    IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨m, v, hv, hvm⟩, hm⟩ := hx
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨v, hv⟩, hinj ?_⟩
  rw [map_zero, map_mul, hvm]
  exact hm

/-- **The maximal ideal of a semilocalization of the base is not an associated prime of the
semilocalization of the extension**, when an element of the maximal ideal of the base is a
nonzerodivisor of the extension: its image is a nonzerodivisor of the semilocalization and lies
in the maximal ideal of `B_𝔮`. -/
theorem not_isAssociatedPrime_maximalIdeal_semilocalization [IsNoetherianRing A]
    [Module.Finite A B] [Module.Finite A C] {s : A} (hsm : s ∈ maximalIdeal A)
    (hs : algebraMap A C s ∈ nonZeroDivisors C) (q : MaximalSpectrum B) :
    ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)) := by
  let := Stacks.Length.isLocalHom_algebraMap_localization (A := A) (B := B) q
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    isNoetherianRing_localization_of_moduleFinite (A := A) q
  set Bq := Localization.AtPrime q.asIdeal
  set Cq := Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)
  have hmem : algebraMap A Bq s ∈ maximalIdeal Bq := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact mem_nonunits_iff.mp ((mem_maximalIdeal s).mp hsm)
      (isUnit_of_map_unit (algebraMap A Bq) s hu)
  refine not_isAssociatedPrime_maximalIdeal_of_smul_injective hmem fun z hz => ?_
  have hnzd : algebraMap C Cq (algebraMap A C s) ∈ nonZeroDivisors Cq :=
    IsLocalization.map_nonZeroDivisors_le (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl) _
      ⟨_, hs, rfl⟩
  refine (mem_nonZeroDivisors_iff.mp hnzd).1 z ?_
  rw [← hz, Algebra.smul_def, IsScalarTower.algebraMap_apply A B Bq]
  congr 1
  rw [← IsScalarTower.algebraMap_apply B Bq Cq, IsScalarTower.algebraMap_apply B C Cq,
    ← IsScalarTower.algebraMap_apply A B C]


/-- **A power of the maximal ideal of `B_𝔮` annihilates `C_𝔮 / B_𝔮`.** A power of `s` carries `C`
into the image of `A`, and a power of the maximal ideal of `B_𝔮` lies in the ideal that power of
`s` generates there, because `s` stays a nonzerodivisor and `B_𝔮` is a one-dimensional Noetherian
local ring. -/
theorem maximalIdeal_pow_smul_top_le_range_semilocalization [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Module.Finite A B] [Module.Finite A C] {s : A}
    (hsm : s ∈ maximalIdeal A) (hsB : algebraMap A B s ∈ nonZeroDivisors B)
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C))
    (q : MaximalSpectrum B) :
    ∃ N : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ N •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
      LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) := by
  classical
  obtain ⟨n, hn⟩ := hquot
  have hn1 : maximalIdeal A ^ (n + 1) • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C) :=
    le_trans (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) hn
  let := Stacks.Length.isLocalHom_algebraMap_localization (A := A) (B := B) q
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    isNoetherianRing_localization_of_moduleFinite (A := A) q
  set Bq := Localization.AtPrime q.asIdeal
  set Cq := Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)
  have hspow : algebraMap A B (s ^ (n + 1)) ∈ nonZeroDivisors B := by
    rw [map_pow]; exact pow_mem hsB (n + 1)
  have hsmpow : s ^ (n + 1) ∈ maximalIdeal A := Ideal.pow_mem_of_mem _ hsm _ n.succ_pos
  set t : Bq := algebraMap A Bq (s ^ (n + 1)) with ht
  have htnzd : t ∈ nonZeroDivisors Bq :=
    algebraMap_localization_mem_nonZeroDivisors (A := A) hspow q
  have htm : t ∈ maximalIdeal Bq := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hsmpow)
      (isUnit_of_map_unit (algebraMap A Bq) _ hu)
  have hdim : ringKrullDim Bq = 1 :=
    ringKrullDim_localization_eq_one_of_nonZeroDivisor (A := A) hsm hsB q
  have hrad : (Ideal.span {t}).radical = maximalIdeal Bq :=
    (IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes hdim htm).2
      fun p hp hmem => notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hp htnzd
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (le_of_eq hrad.symm)
    (IsNoetherian.noetherian _)
  refine ⟨N, ?_⟩
  rw [Submodule.smul_le]
  intro ρ hρ z hz
  clear hz
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp (hN hρ)
  rw [← hβ, mul_smul]
  refine Submodule.smul_mem _ β ?_
  obtain ⟨⟨c, ⟨m, v, hv, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl) z
  obtain ⟨α, hα⟩ := smul_mem_range_of_mem_maximalIdeal_pow hn1
    ((maximalIdeal A).pow_mem_pow hsm (n + 1)) c
  refine ⟨IsLocalization.mk' Bq (algebraMap A B α) ⟨v, hv⟩, ?_⟩
  have htC : algebraMap Bq Cq t = algebraMap C Cq (algebraMap A C (s ^ (n + 1))) := by
    rw [ht, IsScalarTower.algebraMap_apply A B Bq, ← IsScalarTower.algebraMap_apply B Bq Cq,
      IsScalarTower.algebraMap_apply B C Cq, ← IsScalarTower.algebraMap_apply A B C]
  rw [Algebra.linearMap_apply, IsLocalization.algebraMap_mk' C Bq Cq (algebraMap A B α) ⟨v, hv⟩,
    Algebra.smul_def, htC,
    ← IsLocalization.mk'_one (M := Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl) Cq
      (algebraMap A C (s ^ (n + 1))),
    ← IsLocalization.mk'_mul, one_mul, ← Algebra.smul_def, hα,
    ← IsScalarTower.algebraMap_apply A B C]

end Fibre


end Stacks.Chow

namespace AlgebraicGeometry.TameSymbolPreparation

open Stacks.Chow

/-! ### A prepared element is a nonzerodivisor of the extension -/

/-- **Every member of a prepared family is a nonzerodivisor of the extension.** At each maximal
ideal of `B` the member is a unit times a power of the local parameter, which is regular; and an
element of `B` killing it would be killed in every localization, hence zero. -/
theorem algebraMap_mem_nonZeroDivisors
    {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i : Fin r) :
    algebraMap A B (a i) ∈ nonZeroDivisors B := by
  have key : ∀ y : B, algebraMap A B (a i) * y = 0 → y = 0 := by
    intro y hy
    refine eq_zero_of_localization y fun J hJ => ?_
    let := hJ
    have hreg : IsRegular (algebraMap B (Localization.AtPrime J) (algebraMap A B (a i))) := by
      rw [P.factorization J i]
      exact isRegular_mul_iff.mpr ⟨(P.factorUnit J i).isUnit.isRegular,
        (P.parameter_isRegular J).pow (P.exponent J i)⟩
    have hmul : algebraMap B (Localization.AtPrime J) (algebraMap A B (a i)) *
          algebraMap B (Localization.AtPrime J) y =
        algebraMap B (Localization.AtPrime J) (algebraMap A B (a i)) * 0 := by
      rw [mul_zero, ← map_mul, hy, map_zero]
    exact hreg.left hmul
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun y hy => key y (by rw [mul_comm]; exact hy)⟩

/-! ### Stacks 0EAR -/

/-- **Every member of a prepared family is a nonzerodivisor of the base.** -/
theorem mem_nonZeroDivisors
    {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i : Fin r) :
    a i ∈ nonZeroDivisors A := by
  have key : ∀ y : A, a i * y = 0 → y = 0 := by
    intro y hy
    refine P.algebraMap_injective ?_
    rw [map_zero]
    refine (mem_nonZeroDivisors_iff.mp (P.algebraMap_mem_nonZeroDivisors i)).1 _ ?_
    rw [← map_mul, hy, map_zero]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun y hy => key y (by rw [mul_comm]; exact hy)⟩

section Zero

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {r : ℕ} {a : Fin r → A}

open Stacks.Chow Stacks.Localization in
/-- **Stacks 0EAR.** Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `a` be a
family of elements of `A`, not all units, admitting a simultaneous power factorization after a
finite modification — that is, a `AlgebraicGeometry.TameSymbolPreparation`, which Stacks 0EAG
produces for any family of nonzerodivisors not all units. Then the right-hand side of the formula
Stacks 0EAQ,

`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_i e_j} ū_i^{e_j} ū_j^{-e_i})^{m_𝔮}`,

depends on neither the finite modification nor the factorizations: two preparations of the same
family, over any two finite modifications, give the same element of `κ(𝔪)^*`.

This is the source's proof. The two modifications `A ⊆ B` and `A ⊆ B'` are compared through the
common refinement `C = (B ⊗_A B')/(𝔪`-power torsion`)`, built by
`Stacks.Chow.nonempty_commonRefinement`; against `C` the comparison is
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_common_refinement`, which regroups the
product over the maximal ideals of `C` into a product over those of `B` by transitivity of norms
(Stacks 0BIJ) and recognizes each fibre factor as the local factor of Stacks 0EAQ. The
nonzerodivisor the refinement is built from is a nonunit member of the family itself, which the
preparation makes regular
(`AlgebraicGeometry.TameSymbolPreparation.algebraMap_mem_nonZeroDivisors`), and every hypothesis of
Stacks 0EAT for `A ⊆ C` — at `A` and at each maximal ideal of `B` and of `B'` — is derived from
that.

Nothing is assumed. `AlgebraicGeometry.TameSymbolPreparation.symbolValue` cannot be written down
without a `Fintype` on the maximal spectrum of its extension and the locality of the structure map
at each maximal ideal, and those two are not hypotheses here either: each preparation proves them
itself, by `AlgebraicGeometry.TameSymbolPreparation.finite_maximalSpectrum` and
`AlgebraicGeometry.TameSymbolPreparation.isLocalHom`, and the statement below installs them from
the preparations rather than binding them. No generality is lost by fixing the `Fintype`: a type
has at most one of them (`Subsingleton (Fintype _)`), so the equation at the installed instance is
the equation at every instance. -/
@[stacks 0EAR "both clauses for the whole symbol: the value of the formula of Stacks 0EAQ \
depends neither on the choice of the local factorizations nor on the choice of B.  Two \
arbitrary extensions B and B' of A, in unrelated universes, each carrying its own preparation \
of the family, give the same value; the common refinement that compares them is CONSTRUCTED \
here, by Stacks.Chow.nonempty_commonRefinement, not supposed.  The hypotheses are the source's \
own: A Noetherian local of Krull dimension at most one, and the family not all units, which is \
the standing context of Stacks 0EAG in which the formula is written.  The factorization clause \
alone, at a single maximal ideal, is \
Stacks.Chow.factorizationValue_eq_of_factorizations"]
theorem symbolValue_eq_of_preparations (hunit : ¬ ∀ i, IsUnit (a i))
    {B : Type v} [CommRing B] [Algebra A B] {B' : Type w} [CommRing B'] [Algebra A B']
    (P : TameSymbolPreparation a B) (P' : TameSymbolPreparation a B') (i j : Fin r) :
    letI : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
    letI : ∀ q : MaximalSpectrum B,
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
    letI : Fintype (MaximalSpectrum B') := @Fintype.ofFinite _ P'.finite_maximalSpectrum
    letI : ∀ q : MaximalSpectrum B',
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P'.isLocalHom
    P.symbolValue i j = P'.symbolValue i j := by
  classical
  let : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
  let : ∀ q : MaximalSpectrum B,
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
  let : Fintype (MaximalSpectrum B') := @Fintype.ofFinite _ P'.finite_maximalSpectrum
  let : ∀ q : MaximalSpectrum B',
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P'.isLocalHom
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hunit
  let := P.finite
  let := P'.finite
  set s := a i₀ with hs
  have hsm : s ∈ maximalIdeal A := (mem_maximalIdeal s).2 hi₀
  have hsB : algebraMap A B s ∈ nonZeroDivisors B := P.algebraMap_mem_nonZeroDivisors i₀
  have hsB' : algebraMap A B' s ∈ nonZeroDivisors B' := P'.algebraMap_mem_nonZeroDivisors i₀
  obtain ⟨R⟩ := nonempty_commonRefinement P.algebraMap_injective P'.algebraMap_injective
    hsB hsB' hsm P.quotient_annihilated_by_maximalIdeal_power
    P'.quotient_annihilated_by_maximalIdeal_power
  let := R.moduleFinite_left
  let := R.moduleFinite_right
  let : Algebra.IsIntegral B R.carrier := Algebra.IsIntegral.of_finite B R.carrier
  let : Algebra.IsIntegral B' R.carrier := Algebra.IsIntegral.of_finite B' R.carrier
  let : Finite (MaximalSpectrum R.carrier) := Stacks.Length.finite_maximalSpectrum (A := A)
  let : Fintype (MaximalSpectrum R.carrier) := Fintype.ofFinite _
  let : ∀ t : MaximalSpectrum R.carrier,
      IsLocalHom (algebraMap A (Localization.AtPrime t.asIdeal)) := fun t =>
    Stacks.Length.isLocalHom_algebraMap_localization t
  let : ∀ t : MaximalSpectrum R.carrier,
      IsNoetherianRing (Localization.AtPrime t.asIdeal) := fun t =>
    isNoetherianRing_localization_of_moduleFinite (A := A) t
  let : ∀ t : MaximalSpectrum R.carrier,
      Ring.KrullDimLE 1 (Localization.AtPrime t.asIdeal) := fun t =>
    krullDimLE_one_localization_of_moduleFinite (A := A) t
  let : ∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal) := fun q =>
    isNoetherianRing_localization_of_moduleFinite (A := A) q
  let : ∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) := fun q =>
    krullDimLE_one_localization_of_moduleFinite (A := A) q
  let : ∀ q : MaximalSpectrum B', IsNoetherianRing (Localization.AtPrime q.asIdeal) := fun q =>
    isNoetherianRing_localization_of_moduleFinite (A := A) q
  let : ∀ q : MaximalSpectrum B', Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) := fun q =>
    krullDimLE_one_localization_of_moduleFinite (A := A) q
  let : ∀ q : MaximalSpectrum B,
      Fintype (MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid R.carrier q.asIdeal.primeCompl))) := fun q =>
    @Fintype.ofFinite _ (finite_maximalSpectrum_semilocalization B R.carrier q)
  let : ∀ q : MaximalSpectrum B',
      Fintype (MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid R.carrier q.asIdeal.primeCompl))) := fun q =>
    @Fintype.ofFinite _ (finite_maximalSpectrum_semilocalization B' R.carrier q)
  let : ∀ (q : MaximalSpectrum B)
      (v : MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid R.carrier q.asIdeal.primeCompl))),
      (v.asIdeal.under R.carrier).LiesOver q.asIdeal := fun q v =>
    ⟨(IsLocalization.under_under_eq_of_isMaximal q.asIdeal v.asIdeal).symm⟩
  let : ∀ (q : MaximalSpectrum B')
      (v : MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid R.carrier q.asIdeal.primeCompl))),
      (v.asIdeal.under R.carrier).LiesOver q.asIdeal := fun q v =>
    ⟨(IsLocalization.under_under_eq_of_isMaximal q.asIdeal v.asIdeal).symm⟩
  let : ∀ (q : MaximalSpectrum B)
      (v : MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid R.carrier q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime (v.asIdeal.under R.carrier)) := fun q v =>
    Localization.AtPrime.algebraOfLiesOver q.asIdeal (v.asIdeal.under R.carrier)
  let : ∀ (q : MaximalSpectrum B')
      (v : MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid R.carrier q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime (v.asIdeal.under R.carrier)) := fun q v =>
    Localization.AtPrime.algebraOfLiesOver q.asIdeal (v.asIdeal.under R.carrier)
  let : ∀ (q : MaximalSpectrum B)
      (v : MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid R.carrier q.asIdeal.primeCompl))),
      Localization.AtPrime.IsLiesOverAlgebra q.asIdeal (v.asIdeal.under R.carrier) :=
    fun _ _ => ⟨rfl⟩
  let : ∀ (q : MaximalSpectrum B')
      (v : MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid R.carrier q.asIdeal.primeCompl))),
      Localization.AtPrime.IsLiesOverAlgebra q.asIdeal (v.asIdeal.under R.carrier) :=
    fun _ _ => ⟨rfl⟩
  refine symbolValue_eq_of_common_refinement
    (not_isAssociatedPrime_maximalIdeal_of_mem_nonZeroDivisors hsm hsB)
    (not_isAssociatedPrime_maximalIdeal_of_mem_nonZeroDivisors hsm hsB')
    (not_isAssociatedPrime_maximalIdeal_of_mem_nonZeroDivisors hsm R.param_mem_nonZeroDivisors)
    (fun q => not_isAssociatedPrime_maximalIdeal_semilocalization hsm
      R.param_mem_nonZeroDivisors q)
    (fun q => not_isAssociatedPrime_maximalIdeal_semilocalization hsm
      R.param_mem_nonZeroDivisors q)
    (fun t => regularTameSymbolOfKrullDimOne
      (ringKrullDim_localization_eq_one_of_nonZeroDivisor (A := A) hsm
        R.param_mem_nonZeroDivisors t))
    R.injBase R.quot
    (fun q => injective_algebraMap_semilocalization R.injLeft q)
    (fun q => injective_algebraMap_semilocalization R.injRight q)
    (fun q => maximalIdeal_pow_smul_top_le_range_semilocalization hsm hsB R.quot q)
    (fun q => maximalIdeal_pow_smul_top_le_range_semilocalization hsm hsB' R.quot q)
    P P' i j ⟨a i, P.mem_nonZeroDivisors i⟩ ⟨a j, P.mem_nonZeroDivisors j⟩ rfl rfl

end Zero

end AlgebraicGeometry.TameSymbolPreparation

end
