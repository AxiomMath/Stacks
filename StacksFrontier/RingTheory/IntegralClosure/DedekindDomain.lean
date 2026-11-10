module

public import StacksFrontier.RingTheory.Ideal.Over.HeightOne
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Krull–Akizuki for the integral closure of a one-dimensional Noetherian domain

Proof of `IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite` (Stacks 09IG).

Let `A` be a Noetherian domain of Krull dimension at most one with fraction field `K`, let `L/K`
be a finite extension and let `C` be the integral closure of `A` in `L`. Mathlib supplies every
constituent of `IsDedekindDomain C` except Noetherianness: `L` is the fraction field of `C`,
`Ring.DimensionLEOne.of_isIntegral` transports the dimension bound along the integral extension
`A ⊆ C`, and `C` is integrally closed in `L` because integrality is transitive. Noetherianness is
Krull–Akizuki, which Mathlib does not have, so it is proved here.

The argument replaces the source's length computation by the co-finite generation
(`Submodule.CoFG`) of the `A`-submodules `𝔞C` of `C`, that is, the finiteness of the `A`-modules
`C ⧸ 𝔞C`. What carries the proof is that `𝔞 ↦ (𝔞 • ⊤ : Submodule A M).CoFG` is multiplicative:
choosing `P` finitely generated with `P + IM = M` and `Q` with `Q + JM = M` gives
`IM = IQ + IJM`, hence `M = P + IQ + IJM` with `P + IQ` finitely generated
(`cofg_mul_smul_top`). Since `A` is Noetherian of dimension at most one, every nonzero `x ∈ A`
has finitely many primes above it, all maximal, and some power of their product lies in `(x)`;
the fibre statement 031F makes `C ⧸ 𝔪C` a finite `κ(𝔪)`-module, hence a finite `A`-module, for
each maximal `𝔪`, so `xC` is co-finitely generated (`cofg_span_singleton_smul_top`). A nonzero
ideal `I` of `C` contains a nonzero element of `A`, and then `I ⧸ xC` is an `A`-submodule of the
Noetherian `A`-module `C ⧸ xC`, so `I` is a finitely generated ideal.

Quasi-finiteness is the same fibre computation: at a maximal ideal `𝔪` the fibre `κ(𝔪) ⊗[A] C`
is `C ⧸ 𝔪C` and 031F applies, while the generic fibre `κ(⊥) ⊗[A] C` is a `κ(⊥)`-subspace of
`κ(⊥) ⊗[A] L`, because `κ(⊥)` is flat over `A` and `C → L` is injective, and that space is
finite-dimensional because `Algebra.QuasiFinite` composes along `A ⊆ K ⊆ L`.

## Implementation notes

Mathlib's `Submodule.CoFG` API has the implication `Submodule.FG.cofg_of_codisjoint` but not its
converse `exists_fg_codisjoint`, which is what lets one choose the finitely many generators of
`M` modulo `IM`; the converse is proved here.

## References

* [StacksProject 09IG](https://stacks.math.columbia.edu/tag/09IG)
-/

open scoped nonZeroDivisors TensorProduct

namespace Stacks.IntegralClosure.KrullAkizuki

section CoFG

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- Converse of `Submodule.FG.cofg_of_codisjoint`: a co-finitely generated submodule `N` is
codisjoint from a finitely generated submodule, namely the span of lifts of generators of
`M ⧸ N`. -/
private lemma exists_fg_codisjoint {N : Submodule A M} (hN : N.CoFG) :
    ∃ P : Submodule A M, P.FG ∧ Codisjoint P N := by
  classical
  have := hN
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M ⧸ N)
  choose g hg using N.mkQ_surjective
  refine ⟨Submodule.span A (g '' s), Submodule.fg_span (s.finite_toSet.image g),
    codisjoint_iff.mpr ?_⟩
  have h1 : Submodule.map N.mkQ (Submodule.span A (g '' s)) = ⊤ := by
    rw [Submodule.map_span, Set.image_image]
    simpa [hg] using hs
  have h2 := Submodule.comap_map_eq N.mkQ (Submodule.span A (g '' s))
  rw [h1, Submodule.ker_mkQ, Submodule.comap_top] at h2
  exact h2.symm

/-- **Co-finite generation of `𝔞M` is multiplicative in `𝔞`.** This is the heart of
Krull–Akizuki: if `P + IM = M` with `P` finitely generated and `Q + JM = M` with `Q` finitely
generated, then `IM = IQ + IJM`, so `(P + IQ) + IJM = M` with `P + IQ` finitely generated. -/
private lemma cofg_mul_smul_top [IsNoetherianRing A] {I J : Ideal A}
    (hI : (I • (⊤ : Submodule A M)).CoFG) (hJ : (J • (⊤ : Submodule A M)).CoFG) :
    ((I * J) • (⊤ : Submodule A M)).CoFG := by
  obtain ⟨P, hPfg, hP⟩ := exists_fg_codisjoint hI
  obtain ⟨Q, hQfg, hQ⟩ := exists_fg_codisjoint hJ
  refine (hPfg.sup (Submodule.FG.smul (IsNoetherian.noetherian I) hQfg)).cofg_of_codisjoint
    (codisjoint_iff.mpr ?_)
  have key : I • (⊤ : Submodule A M) = I • Q ⊔ (I * J) • (⊤ : Submodule A M) := by
    conv_lhs => rw [← codisjoint_iff.mp hQ]
    rw [Submodule.smul_sup, mul_smul]
  rw [sup_assoc, ← key]
  exact codisjoint_iff.mp hP

/-- Co-finite generation of `𝔞M` in `𝔞` passes to any product of ideals; the empty product is
the statement that `⊤` is co-finitely generated. -/
private lemma cofg_multisetProd_smul_top [IsNoetherianRing A] {T : Multiset (Ideal A)}
    (h : ∀ I ∈ T, (I • (⊤ : Submodule A M)).CoFG) :
    (T.prod • (⊤ : Submodule A M)).CoFG := by
  induction T using Multiset.induction with
  | empty => simp
  | cons I T ih =>
    rw [Multiset.prod_cons]
    exact cofg_mul_smul_top (h I (T.mem_cons_self I))
      (ih fun J hJ => h J (Multiset.mem_cons_of_mem hJ))

/-- **The finiteness behind Krull–Akizuki.** Over a Noetherian ring of dimension at most one, if
`M ⧸ 𝔪M` is a finite module for every maximal ideal `𝔪`, then `M ⧸ xM` is finite for every
nonzero `x`: the minimal primes of `(x)` are finitely many and maximal, and some power of their
product lies in `(x)`. -/
private lemma cofg_span_singleton_smul_top [IsNoetherianRing A] [Ring.DimensionLEOne A]
    (h : ∀ m : Ideal A, m.IsMaximal → (m • (⊤ : Submodule A M)).CoFG) {x : A} (hx : x ≠ 0) :
    ((Ideal.span {x} : Ideal A) • (⊤ : Submodule A M)).CoFG := by
  classical
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (Ideal.span {x})
    (IsNoetherian.noetherian _)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Ideal A), ∀ p, p ∈ F ↔ p ∈ (Ideal.span {x}).minimalPrimes :=
    ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {x})).toFinset,
      fun _ => Set.Finite.mem_toFinset _⟩
  have hmem : ∀ p ∈ (n + 1) • F.val, p ∈ (Ideal.span {x}).minimalPrimes := fun p hp =>
    (hF p).mp (Finset.mem_val.mp (Multiset.mem_nsmul.mp hp).2)
  have hmax : ∀ p ∈ (n + 1) • F.val, p.IsMaximal := fun p hp => by
    refine Ring.DimensionLEOne.maximalOfPrime (fun h0 => hx ?_) (hmem p hp).1.1
    have hxp := (hmem p hp).1.2
    rw [h0, Ideal.span_le, Set.singleton_subset_iff] at hxp
    simpa using hxp
  have hle : ((n + 1) • F.val).prod ≤ Ideal.span {x} := by
    have h1 : F.val.prod ≤ (Ideal.span {x} : Ideal A).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      exact le_sInf fun q hq => Ideal.le_of_dvd (Multiset.dvd_prod ((hF q).mpr hq))
    calc ((n + 1) • F.val).prod = F.val.prod ^ (n + 1) := Multiset.prod_nsmul _ _
      _ ≤ (Ideal.span {x} : Ideal A).radical ^ (n + 1) := Ideal.pow_right_mono h1 _
      _ ≤ (Ideal.span {x} : Ideal A).radical ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ ≤ Ideal.span {x} := hn
  exact Submodule.CoFG.of_le (Submodule.smul_mono_left hle)
    (cofg_multisetProd_smul_top fun p hp => h p (hmax p hp))

end CoFG

/-- **Krull–Akizuki**, in the form used for 09IG: an integral extension `C` of a Noetherian ring
`A` of dimension at most one, with `C` a domain, is Noetherian as soon as `𝔪C` is co-finitely
generated as an `A`-submodule of `C` for every maximal ideal `𝔪` of `A`. A nonzero ideal `I` of
`C` contains a nonzero `x ∈ A`, and `I ⧸ xC` is an `A`-submodule of the Noetherian `A`-module
`C ⧸ xC`. -/
private lemma isNoetherianRing_of_cofg_maximal_smul_top {A : Type*} [CommRing A] [Nontrivial A]
    [IsNoetherianRing A] [Ring.DimensionLEOne A] {C : Type*} [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra.IsIntegral A C]
    (h : ∀ m : Ideal A, m.IsMaximal → (m • (⊤ : Submodule A C)).CoFG) :
    IsNoetherianRing C := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact Submodule.fg_bot
  obtain ⟨y, hyI, hy0⟩ := I.ne_bot_iff.mp hI
  obtain ⟨x, hxI, hx⟩ := (Submodule.ne_bot_iff _).mp
    (Ideal.under_ne_bot_of_integral_mem hy0 hyI (Algebra.IsIntegral.isIntegral (R := A) y))
  set J : Ideal C := Ideal.span {algebraMap A C x} with hJ
  have hJI : J ≤ I := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxI)
  have hres : Submodule.restrictScalars A J = (Ideal.span {x} : Ideal A) • (⊤ : Submodule A C) := by
    rw [Ideal.smul_top_eq_map, Ideal.map_span, Set.image_singleton, hJ]
  have : Module.Finite A (C ⧸ Submodule.restrictScalars A J) := by
    rw [hres]
    exact cofg_span_singleton_smul_top h hx
  have : Module.Finite A (C ⧸ J) :=
    Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv A J)
  refine Submodule.fg_of_fg_map_of_fg_inf_ker J.mkQ
    (Submodule.FG.of_restrictScalars A (IsNoetherian.noetherian _)) ?_
  rw [Submodule.ker_mkQ, inf_of_le_right hJI, hJ]
  exact Submodule.fg_span (Set.finite_singleton _)

/-- The generic fibre of `Spec C → Spec A` is finite: it is a `κ(⊥)`-subspace of the generic
fibre of `Spec L → Spec A`, which is finite because quasi-finiteness composes along
`A ⊆ K ⊆ L`. -/
private lemma finite_fiber_bot (A K L C : Type*) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L]
    [CommRing C] [Algebra A C] [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    Module.Finite (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber C) := by
  have : Algebra.QuasiFinite A L := .trans A K L
  have : Module.Finite (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber L) :=
    Algebra.QuasiFinite.finite_fiber ⊥
  have : Module.Flat A (⊥ : Ideal A).ResidueField := IsLocalization.flat _ A⁰
  refine Module.Finite.of_injective
    (LinearMap.baseChange _ ((Algebra.linearMap C L).restrictScalars A)) ?_
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (IsIntegralClosure.algebraMap_injective C A L)

/-- The fibre of `Spec C → Spec A` over a maximal ideal is finite: it is `C ⧸ 𝔪C`, which 031F
makes a finite `κ(𝔪)`-module, hence a finite `A`-module. -/
private lemma finite_fiber_of_isMaximal (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    (m : Ideal A) [m.IsMaximal] [Module.Finite A (C ⧸ m.map (algebraMap A C))] :
    Module.Finite m.ResidueField (m.Fiber C) := by
  let e : m.Fiber C ≃ₐ[A] C ⧸ m.map (algebraMap A C) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField m)) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C m).symm.restrictScalars _)
  have : Module.Finite A (m.Fiber C) := .of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_restrictScalars_finite A m.ResidueField (m.Fiber C)

public theorem solution
    (A K L C : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L]
    [CommRing C] [Algebra A C] [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    IsDedekindDomain C ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap A C)) ∧
      Algebra.QuasiFinite A C := by
  have : IsDomain C :=
    (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain _
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr fun u v huv =>
    hAL (by rw [IsScalarTower.algebraMap_apply A C L, huv,
      ← IsScalarTower.algebraMap_apply A C L])
  -- the closed fibres, from 031F
  have hfib : ∀ (m : Ideal A) [m.IsMaximal],
      Module.Finite (A ⧸ m) (C ⧸ m.map (algebraMap A C)) := fun m _ =>
    (Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient A C K L m).2.2.2
  have hfin : ∀ (m : Ideal A) [m.IsMaximal], Module.Finite A (C ⧸ m.map (algebraMap A C)) :=
    fun m _ => Module.Finite.trans (A ⧸ m) _
  have : IsNoetherianRing C := isNoetherianRing_of_cofg_maximal_smul_top fun m hm => by
    have := hfin m
    rw [Ideal.smul_top_eq_map]
    assumption
  have : Ring.DimensionLEOne C := Ring.DimensionLEOne.of_isIntegral A C
  have : IsIntegrallyClosed C := (isIntegrallyClosed_iff L).mpr fun {x} hx =>
    ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
      IsIntegralClosure.algebraMap_mk' _ _ _⟩
  refine ⟨{ ‹IsNoetherianRing C›, ‹Ring.DimensionLEOne C›, ‹IsIntegrallyClosed C› with },
    Algebra.IsIntegral.comap_surjective A C, ?_⟩
  constructor
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | h0
  · exact finite_fiber_bot A K L C
  · have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h0 hP
    have := hfin P
    exact finite_fiber_of_isMaximal A C P

end Stacks.IntegralClosure.KrullAkizuki

/-!
# The integral closure of a one-dimensional Noetherian domain in a finite field extension

Let `A` be a Noetherian domain of Krull dimension at most one, let `K` be its fraction field, let
`L/K` be a finite field extension and let `C` be the integral closure of `A` in `L`. Then `C` is a
Dedekind domain, the induced map `Spec(C) → Spec(A)` is surjective, its fibres are finite, and the
residue field extensions `κ(𝔭) ⊆ κ(𝔮)` it induces are finite.

This is a variant of the Krull–Akizuki theorem, and its point is that `A` is *not* assumed
integrally closed and `L/K` is *not* assumed separable: `C` need be neither a finite nor even a
finite-type `A`-algebra, yet it is Noetherian because every nonzero ideal of a ring between `A`
and `L` meets `A` nontrivially and `C/xC` has finite length over `A` for `x ∈ A` nonzero. Krull
dimension is preserved by an integral extension, so `dim C ≤ 1`, and `C` is integrally closed in
`L`, which is its own fraction field; that is the three conditions defining a Dedekind domain.
Surjectivity on spectra is the going-up property of the integral extension `A ⊆ C`, and the
finiteness of the fibres and of the residue field extensions both come from the finite length of
`C/xC`, which makes each fibre `κ(𝔭) ⊗[A] C` a finite-dimensional `κ(𝔭)`-algebra.

## Main results

* `IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite`: the integral closure
  of a Noetherian domain of dimension at most one in a finite extension of its fraction field is
  a Dedekind domain, quasi-finite over the base, and surjective on spectra.

## Implementation notes

The integral closure is taken abstractly, as a ring `C` with `IsIntegralClosure C A L`, rather
than as the concrete subring `integralClosure A L`; the concrete case is the instantiation
`C := integralClosure A L`. This matches Mathlib's `IsIntegralClosure.isDedekindDomain`, of which
this statement is a strict generalization: that lemma assumes `IsDedekindDomain A` (in particular
`IsIntegrallyClosed A`) and `Algebra.IsSeparable K L`, both of which are dropped here, at the cost
of no longer having `C` finite over `A`.

The source's `dim A = 1` is weakened to `Ring.DimensionLEOne A`, Mathlib's spelling of
"every nonzero prime ideal is maximal" and the hypothesis carried by `IsDedekindRing`. The
degenerate case this admits is `A` a field, where `K = A`, `C = L` and all four conclusions are
immediate; no conclusion needs `dim A` to be exactly one, so carrying `A` not a field would be
decoration.

The last two conclusions of the tag are packaged as `Algebra.QuasiFinite A C`, Mathlib's predicate
saying that the fibre `κ(𝔭) ⊗[A] C` (spelled `Ideal.Fiber`) is a finite-dimensional
`κ(𝔭)`-vector space for every prime `𝔭` of `A`, where `κ(𝔭) = Ideal.ResidueField 𝔭` is the residue
field of `Localization.AtPrime 𝔭`. The tag's own two assertions are recovered from it by name and
need no separate conjunct: `Algebra.QuasiFinite.finite_comap_preimage_singleton` says each fibre
of `Spec(C) → Spec(A)` is finite (equivalently `Algebra.QuasiFinite.finite_primesOver` for the set
of primes of `C` over a given ideal), and typeclass inference supplies
`Module.Finite 𝔭.ResidueField 𝔮.ResidueField` for `𝔮` lying over `𝔭`, the finiteness of the
residue field extension along the canonical embedding `Ideal.ResidueField.map`. Quasi-finiteness
is what the author's argument actually proves — the finite length of `C/xC` over `A` — so this
is a faithful packaging rather than an added burden, and it is Mathlib's form of tag 00PL.

`IsDomain C` is not assumed, unlike in `IsIntegralClosure.isDedekindDomain`: it follows from
`IsIntegralClosure.algebraMap_injective` and `Function.Injective.isDomain`, and it is part of the
conclusion `IsDedekindDomain C`.

Faithfulness. (1) Every hypothesis is used: `IsNoetherianRing A` and `Ring.DimensionLEOne A` are
what make `C/xC` of finite length over `A` for nonzero `x ∈ A`, hence `C` Noetherian, and the
second also bounds `dim C`; `FiniteDimensional K L` bounds the fibres and the residue field
degrees; `IsFractionRing A K` fixes `K` as the fraction field; `IsDomain A` makes `A ⊆ C ⊆ L` a
chain of domains; and `IsIntegralClosure C A L` is what `C` is. (2) The
scalars and the base are the source's: `Algebra.QuasiFinite A C` and
`PrimeSpectrum.comap (algebraMap A C)` are over `A` itself, not over `K` or over a localization,
and `IsDedekindDomain C` is a statement about `C` with its own fraction field, which is `L`. (3)
The map the source names, `Spec(C) → Spec(A)`, is pinned as `PrimeSpectrum.comap (algebraMap A C)`
rather than asserted to exist, and the residue field extensions are along its canonical
`Ideal.ResidueField.map`. (4) The instantiation is not degenerate: `A = ℤ[√-3]`, `K = L = ℚ(√-3)`,
`C = ℤ[(1 + √-3)/2]` is an instance with `A` not integrally closed, and
`A = 𝔽ₚ[t] ⊆ L = 𝔽ₚ(t^(1/p))` is one with `L/K` purely inseparable of degree `p`; neither is
covered by `IsIntegralClosure.isDedekindDomain`, and `A = ℤ`, `L` a number field, `C` its ring of
integers is the classical case, where the conclusions are respectively that `𝒪_L` is Dedekind,
that every prime of `ℤ` has a prime of `𝒪_L` above it, that only finitely many do, and that the
residue degrees are finite.

## References

* [StacksProject 09IG](https://stacks.math.columbia.edu/tag/09IG)

## Tags

Krull-Akizuki, Dedekind domain, integral closure, quasi-finite, residue field extension
-/

namespace IsIntegralClosure

/-- **Variant of Krull–Akizuki.** Let `A` be a Noetherian domain of Krull dimension at most one
with fraction field `K`, let `L/K` be a finite field extension and let `C` be the integral closure
of `A` in `L`. Then `C` is a Dedekind domain, the map `Spec(C) → Spec(A)` is surjective, and `C`
is quasi-finite over `A`; the latter says that every fibre `κ(𝔭) ⊗[A] C` is a finite-dimensional
`κ(𝔭)`-vector space, whence `Spec(C) → Spec(A)` has finite fibres and induces finite residue field
extensions. Neither `A` integrally closed nor `L/K` separable is assumed, so `C` need not be a
finite `A`-algebra. -/
@[stacks 09IG "Finite fibres and finiteness of the induced residue field extensions are packaged
as `Algebra.QuasiFinite A C`, from which they follow by name; `dim A = 1` is weakened to
`Ring.DimensionLEOne A`. See the module docstring.",
  ega "0 23.2.6" "residue extensions",
  ega "0 23.2.8" "(ii), dim ≤ 1",
  ega "0 23.2.7" "partial",
  ega "IV 18.9.7.8" "more general",
  ega "IV 9.5.7" "B is a Dedekind ring"]
public theorem isDedekindDomain_and_comap_surjective_and_quasiFinite
    (A K L C : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L]
    [CommRing C] [Algebra A C] [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    IsDedekindDomain C ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap A C)) ∧
      Algebra.QuasiFinite A C :=
  Stacks.IntegralClosure.KrullAkizuki.solution A K L C

end IsIntegralClosure
