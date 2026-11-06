module

import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat

public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.RingTheory.QuasiFinite.Dimension
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.RingTheory.CohenMacaulay.FlatLocalHom

/-!
# The flat locus of a quasi-finite map from a polynomial ring is its Cohen–Macaulay locus

Let `S` be a finite type algebra over a field `k`, let `φ : k[y_1, …, y_d] → S` be a map of
`k`-algebras which is quasi-finite at a prime `𝔮` of `S`, and let `𝔭 = φ⁻¹(𝔮)`. This file proves
Stacks 00RE: the local ring `S_𝔮` is flat over `k[y_1, …, y_d]` if and only if `S_𝔮` is
Cohen–Macaulay and `dim_𝔮(S/k) = d`.

Both sides are compared with the single numerical condition `dim(S_𝔮) = dim(k[y]_𝔭)`, that is
`height 𝔮 = height 𝔭`.

* Flatness of `S_𝔮` over `k[y]` is flatness over `k[y]_𝔭` (`Module.flat_iff_of_isLocalization`),
  and `k[y]_𝔭` is a regular, hence Cohen–Macaulay, local ring. So 00R5 applied to the flat local
  homomorphism `k[y]_𝔭 → S_𝔮` — whose dimension hypothesis is 00QF — gives that `S_𝔮` is
  Cohen–Macaulay with `dim(S_𝔮) = dim(k[y]_𝔭)`. Conversely, quasi-finiteness at `𝔮` makes the
  fibre ring `S_𝔮/𝔭S_𝔮` zero-dimensional, because a prime of `S` below `𝔮` and over `𝔭` is `𝔮`
  itself; so `dim(S_𝔮) = dim(k[y]_𝔭) + dim(S_𝔮/𝔭S_𝔮)` and miracle flatness 00R4 gives flatness.
* The passage between `height 𝔮 = height 𝔭` and `dim_𝔮(S/k) = d` is the source's transcendence
  degree computation. Over the field `k` the fibre of `Spec S → Spec k` through `𝔮` is all of
  `Spec S`, so `dim_𝔮(S/k)` is the local dimension of `Spec S` at `𝔮`, which 00P1 evaluates as
  `height 𝔮 + trdeg_k κ(𝔮)`. For `k[y_1, …, y_d]` the same formula together with 00OT and 00P0
  gives `height 𝔭 + trdeg_k κ(𝔭) = d`, every maximal ideal of a `d`-dimensional polynomial ring
  having height `d`. Finally `κ(𝔮)/κ(𝔭)` is finite by quasi-finiteness, so the two transcendence
  degrees agree and the two conditions are the same.

## Main results

* `Stacks.CohenMacaulay.FlatLocus.solution`: Stacks 00RE, in the form of
  `Module.Flat.atPrime_iff_isMaximalCohenMacaulay_and_relativeDimensionAt_eq`.

## Implementation notes

The abstract localization `Sq` of the statement is made an algebra over `k[y]_𝔭` by
`IsLocalization.lift`: every element of `k[y] ∖ 𝔭` maps to a unit of `S_𝔮`. This keeps `Sq`
abstract, so that Cohen–Macaulayness — a statement about `Sq` — never has to be transported
along a ring isomorphism.

The two conditions are separated into the two lemmas that carry them:
`Stacks.CohenMacaulay.FlatLocus.flat_iff_isMaximalCohenMacaulay_and_height_eq` is the commutative
algebra, stated
for an arbitrary local homomorphism of localizations with regular source and discrete fibre at
`𝔮`, and `Stacks.CohenMacaulay.FlatLocus.relativeDimensionAt_eq_iff_height_eq_height` is the
dimension theory over `k`, which is where the polynomial ring and the field enter.

## References

* [StacksProject 00RE](https://stacks.math.columbia.edu/tag/00RE)
* [StacksProject 00QD](https://stacks.math.columbia.edu/tag/00QD)
-/


namespace Stacks.CohenMacaulay.FlatLocus

open IsLocalRing TopologicalSpace Algebra

/-! ### The relative dimension over a field -/

/-- Over a field the fibre of `Spec S → Spec k` through a prime `𝔮` is all of `Spec S`, so the
relative dimension `dim_𝔮(S/k)` of Definition 00QD is the local dimension of `Spec S` at `𝔮`. -/
private lemma relativeDimensionAt_eq_localKrullDim (k : Type*) {S : Type*} [Field k] [CommRing S]
    [Algebra k S] (𝔮 : Ideal S) [𝔮.IsPrime] :
    Algebra.relativeDimensionAt k 𝔮 = localKrullDim (PrimeSpectrum S) ⟨𝔮, ‹_›⟩ := by
  have hset : PrimeSpectrum.comap (algebraMap k S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap k S) (⟨𝔮, ‹_›⟩ : PrimeSpectrum S)} = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun y ↦ Subsingleton.elim _ _
  rw [Algebra.relativeDimensionAt, ← topologicalKrullDimAt_eq_localKrullDim]
  exact topologicalKrullDimAt_eq_of_homeomorph
    ((Homeomorph.setCongr hset).trans (Homeomorph.Set.univ (PrimeSpectrum S))) _

/-- For a finite type algebra `S` over a field `k` the relative dimension of Definition 00QD at a
prime `𝔮` is `dim_𝔮(S/k) = height 𝔮 + trdeg_k κ(𝔮)`: it is a local dimension by
`relativeDimensionAt_eq_localKrullDim`, which 00P1 evaluates. -/
private lemma relativeDimensionAt_eq_height_add_toENat_trdeg_residueField (k : Type*) {S : Type*}
    [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (𝔮 : Ideal S) [𝔮.IsPrime] :
    Algebra.relativeDimensionAt k 𝔮 =
      ((𝔮.height + Cardinal.toENat (Algebra.trdeg k 𝔮.ResidueField) : ℕ∞) : WithBot ℕ∞) := by
  rw [relativeDimensionAt_eq_localKrullDim k 𝔮,
    PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField k (⟨𝔮, ‹_›⟩ : PrimeSpectrum S)]

/-- An algebraic field extension does not change the transcendence degree over a subfield. -/
private lemma toENat_trdeg_eq_of_isAlgebraic (k : Type*) (F : Type*) (E : Type*) [Field k]
    [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    [Algebra.IsAlgebraic F E] :
    Cardinal.toENat (Algebra.trdeg k F) = Cardinal.toENat (Algebra.trdeg k E) := by
  have h := lift_trdeg_add_eq (R := k) (S := F) (A := E)
  rw [trdeg_eq_zero (R := F) (A := E), Cardinal.lift_zero, add_zero] at h
  rw [← Cardinal.toENat_lift (c := trdeg k F), ← Cardinal.toENat_lift (c := trdeg k E), h]

/-- Every maximal ideal of `k[y_1, …, y_d]` has height `d`: the localization at it has Krull
dimension `trdeg_k k(y_1, …, y_d)` by 00P0, and that is `d`. -/
private lemma height_eq_of_isMaximal_mvPolynomial (k : Type*) [Field k] {σ : Type*} [Finite σ]
    (𝔪 : Ideal (MvPolynomial σ k)) [𝔪.IsMaximal] : 𝔪.height = (Nat.card σ : ℕ∞) := by
  have H := ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg k (MvPolynomial σ k)
    (FractionRing (MvPolynomial σ k))
  have h : (𝔪.height : WithBot ℕ∞) = ((Nat.card σ : ℕ) : WithBot ℕ∞) := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (Localization.AtPrime 𝔪),
      H.2 𝔪 (Localization.AtPrime 𝔪), ← H.1,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field k, zero_add]
  exact_mod_cast h

/-- For a prime `𝔭` of `k[y_1, …, y_d]` we have `height 𝔭 + trdeg_k κ(𝔭) = d`: the left-hand side
is the local dimension of `Spec k[y_1, …, y_d]` at `𝔭` by 00P1, and by 00OT that is the least
height of a maximal ideal containing `𝔭`, each of which is `d`. -/
private lemma height_add_toENat_trdeg_residueField_mvPolynomial (k : Type*) [Field k]
    {σ : Type*} [Finite σ] (𝔭 : Ideal (MvPolynomial σ k)) [𝔭.IsPrime] :
    𝔭.height + Cardinal.toENat (Algebra.trdeg k 𝔭.ResidueField) = (Nat.card σ : ℕ∞) := by
  obtain ⟨𝔪₀, h𝔪₀, hle₀⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top ‹_›)
  have hne : {𝔪 : Ideal (MvPolynomial σ k) | 𝔪.IsMaximal ∧ 𝔭 ≤ 𝔪}.Nonempty := ⟨𝔪₀, h𝔪₀, hle₀⟩
  have hiInf : (⨅ 𝔪 ∈ {𝔪 : Ideal (MvPolynomial σ k) | 𝔪.IsMaximal ∧ 𝔭 ≤ 𝔪},
      (𝔪.height : WithBot ℕ∞)) = ((Nat.card σ : ℕ∞) : WithBot ℕ∞) :=
    (iInf_congr fun 𝔪 ↦ iInf_congr fun h𝔪 ↦ by
      have := h𝔪.1; rw [height_eq_of_isMaximal_mvPolynomial]).trans (biInf_const hne)
  have h := (PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k
    (⟨𝔭, ‹_›⟩ : PrimeSpectrum (MvPolynomial σ k))).2
  rw [PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField k
    (⟨𝔭, ‹_›⟩ : PrimeSpectrum (MvPolynomial σ k)), hiInf] at h
  exact_mod_cast h

/-- **The source's transcendence degree computation.** For a `k`-algebra map
`k[y_1, …, y_d] → S` of finite type algebras over a field `k` which is quasi-finite at a prime
`𝔮` of `S` lying over `𝔭`, the relative dimension `dim_𝔮(S/k)` equals `d` exactly when
`height 𝔮 = height 𝔭`: both `dim_𝔮(S/k)` and `d` are a height plus a transcendence degree over
`k`, and the two transcendence degrees agree because `κ(𝔮)/κ(𝔭)` is finite. -/
private lemma relativeDimensionAt_eq_iff_height_eq_height (k : Type*) [Field k] {S : Type*}
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S] {σ : Type*} [Finite σ]
    [Algebra (MvPolynomial σ k) S] [IsScalarTower k (MvPolynomial σ k) S]
    (𝔭 : Ideal (MvPolynomial σ k)) (𝔮 : Ideal S) [𝔭.IsPrime] [𝔮.IsPrime] [𝔮.LiesOver 𝔭]
    [Algebra.QuasiFiniteAt (MvPolynomial σ k) 𝔮] :
    Algebra.relativeDimensionAt k 𝔮 = Nat.card σ ↔ 𝔮.height = 𝔭.height := by
  let := Localization.AtPrime.algebraOfLiesOver 𝔭 𝔮
  have : Algebra.IsAlgebraic 𝔭.ResidueField 𝔮.ResidueField :=
    have : Module.Finite 𝔭.ResidueField 𝔮.ResidueField := inferInstance
    Algebra.IsAlgebraic.of_finite 𝔭.ResidueField 𝔮.ResidueField
  have : IsScalarTower k 𝔭.ResidueField 𝔮.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by simp [← IsScalarTower.algebraMap_apply]
  have hR : 𝔭.height + Cardinal.toENat (Algebra.trdeg k 𝔮.ResidueField) = (Nat.card σ : ℕ∞) := by
    rw [← toENat_trdeg_eq_of_isAlgebraic k 𝔭.ResidueField 𝔮.ResidueField]
    exact height_add_toENat_trdeg_residueField_mvPolynomial k 𝔭
  have htop : Cardinal.toENat (Algebra.trdeg k 𝔮.ResidueField) ≠ ⊤ := fun h ↦ by
    rw [h] at hR; simp at hR
  have key : 𝔮.height + Cardinal.toENat (Algebra.trdeg k 𝔮.ResidueField) = (Nat.card σ : ℕ∞) ↔
      𝔮.height = 𝔭.height := by
    rw [← hR]
    exact ⟨WithTop.add_right_cancel htop, fun h ↦ by rw [h]⟩
  rw [relativeDimensionAt_eq_height_add_toENat_trdeg_residueField k 𝔮]
  exact ⟨fun h ↦ key.mp (by exact_mod_cast h), fun h ↦ by exact_mod_cast key.mpr h⟩

/-! ### The fibre of a quasi-finite map -/

section Fibre

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (𝔭 : Ideal R) (𝔮 : Ideal S)
  [𝔮.IsPrime] [𝔮.LiesOver 𝔭] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
  [IsLocalization.AtPrime Sq 𝔮] [IsLocalRing Sq] [Algebra R Sq] [IsScalarTower R S Sq]

include S 𝔮 in
/-- The prime of `R` under the maximal ideal of `S_𝔮` is `𝔭`. -/
private lemma under_maximalIdeal_eq : (maximalIdeal Sq).under R = 𝔭 := by
  rw [← Ideal.under_under (A := R) (B := S) (maximalIdeal Sq),
    IsLocalization.AtPrime.under_maximalIdeal Sq 𝔮, ← 𝔮.over_def 𝔭]

include S 𝔮 in
/-- The ideal `𝔭 S_𝔮` generated by `𝔭` in `S_𝔮` is contained in the maximal ideal. -/
private lemma map_le_maximalIdeal : 𝔭.map (algebraMap R Sq) ≤ maximalIdeal Sq :=
  Ideal.map_le_iff_le_comap.mpr (under_maximalIdeal_eq 𝔭 𝔮 Sq).ge

/-- **The fibre of `Spec S_𝔮 → Spec R_𝔭` is the single point `𝔮`.** If `𝔮` is the only prime of
`S` below `𝔮` lying over `𝔭` — which is what quasi-finiteness at `𝔮` gives — then a prime of
`S_𝔮` containing `𝔭 S_𝔮` is the maximal ideal. -/
private lemma eq_maximalIdeal_of_map_le
    (hqf : ∀ 𝔮' : Ideal S, 𝔮'.IsPrime → 𝔮' ≤ 𝔮 → 𝔮'.under R = 𝔭 → 𝔮' = 𝔮)
    (J : Ideal Sq) [J.IsPrime] (hJ : 𝔭.map (algebraMap R Sq) ≤ J) : J = maximalIdeal Sq := by
  have hJle : J.under S ≤ (maximalIdeal Sq).under S :=
    Ideal.comap_mono (le_maximalIdeal_of_isPrime J)
  have h1 : J.under S ≤ 𝔮 := hJle.trans_eq (IsLocalization.AtPrime.under_maximalIdeal Sq 𝔮)
  have h2 : (J.under S).under R = 𝔭 := by
    refine le_antisymm ((Ideal.comap_mono hJle).trans_eq
      ((Ideal.under_under (maximalIdeal Sq)).trans (under_maximalIdeal_eq 𝔭 𝔮 Sq))) ?_
    rw [Ideal.under_under]
    exact Ideal.map_le_iff_le_comap.mp hJ
  rw [← IsLocalization.map_under 𝔮.primeCompl Sq J,
    hqf (J.under S) (Ideal.IsPrime.under S J) h1 h2,
    IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 Sq]

/-- Under the hypothesis of `eq_maximalIdeal_of_map_le` the fibre ring `S_𝔮/𝔭 S_𝔮` is
zero-dimensional: it is nonzero, and its only prime is the image of the maximal ideal. -/
private lemma ringKrullDim_quotient_map_eq_zero
    (hqf : ∀ 𝔮' : Ideal S, 𝔮'.IsPrime → 𝔮' ≤ 𝔮 → 𝔮'.under R = 𝔭 → 𝔮' = 𝔮) :
    ringKrullDim (Sq ⧸ 𝔭.map (algebraMap R Sq)) = 0 := by
  have hIle := map_le_maximalIdeal 𝔭 𝔮 Sq
  have : Nontrivial (Sq ⧸ 𝔭.map (algebraMap R Sq)) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal Sq).ne_top hIle
  refine ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
    (Ring.krullDimLE_zero_iff.mpr fun J hJ ↦ ?_)
  have := hJ
  have hcomap : J.comap (Ideal.Quotient.mk (𝔭.map (algebraMap R Sq))) = maximalIdeal Sq :=
    eq_maximalIdeal_of_map_le 𝔭 𝔮 Sq hqf _
      (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_quotient_self]; exact bot_le))
  rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J, hcomap]
  exact (maximalIdeal.isMaximal Sq).map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (Ideal.mk_ker.trans_le hIle)

/-- **The commutative algebra of Stacks 00RE.** For a local homomorphism `R_𝔭 → S_𝔮` of
localizations at primes `𝔭` and `𝔮` with `R_𝔭` regular, in which `𝔮` is the only prime below `𝔮`
lying over `𝔭`, flatness of `S_𝔮` over `R` is Cohen–Macaulayness of `S_𝔮` together with
`height 𝔮 = height 𝔭`. Forwards this is 00R5, backwards miracle flatness 00R4 applied to the
zero-dimensional fibre ring. -/
private lemma flat_iff_isMaximalCohenMacaulay_and_height_eq [IsNoetherianRing S] [𝔭.IsPrime]
    {Rp : Type*} [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp 𝔭]
    [IsRegularLocalRing Rp] [Algebra Rp Sq] [IsScalarTower R Rp Sq]
    (hqf : ∀ 𝔮' : Ideal S, 𝔮'.IsPrime → 𝔮' ≤ 𝔮 → 𝔮'.under R = 𝔭 → 𝔮' = 𝔮)
    (hle : 𝔮.height ≤ 𝔭.height) :
    Module.Flat R Sq ↔ Module.IsMaximalCohenMacaulay Sq Sq ∧ 𝔮.height = 𝔭.height := by
  have : IsNoetherianRing Sq := IsLocalization.isNoetherianRing 𝔮.primeCompl Sq ‹_›
  have hdimRp : ringKrullDim Rp = (𝔭.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 Rp
  have hdimSq : ringKrullDim Sq = (𝔮.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 Sq
  have hImap : (maximalIdeal Rp).map (algebraMap Rp Sq) = 𝔭.map (algebraMap R Sq) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 Rp, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  have : IsLocalHom (algebraMap Rp Sq) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap Rp Sq)).out 3 1).mp
      (hImap.trans_le (map_le_maximalIdeal 𝔭 𝔮 Sq))
  rw [← Module.flat_iff_of_isLocalization Rp 𝔭.primeCompl Sq]
  refine ⟨fun hF ↦ ?_, fun ⟨hCM, hh⟩ ↦ Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add
    (R := Rp) (S := Sq) hCM ?_⟩
  · have hCMRp : Module.IsMaximalCohenMacaulay Rp Rp :=
      (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
        Rp).2
    obtain ⟨hCM, hdim⟩ := Module.isMaximalCohenMacaulay_self_and_ringKrullDim_eq_of_flat
      (R := Rp) (S := Sq) hCMRp (Or.inr (by rw [hdimRp, hdimSq, WithBot.coe_le_coe]; exact hle))
    rw [hdimRp, hdimSq, WithBot.coe_inj] at hdim
    exact ⟨hCM, hdim.symm⟩
  · rw [hImap, ringKrullDim_quotient_map_eq_zero 𝔭 𝔮 Sq hqf, add_zero, hdimRp, hdimSq, hh]

end Fibre

/-- Let `S` be a finite type algebra over a field `k` with a `k`-algebra map
`k[y_1, …, y_d] → S`, `d = Nat.card σ`, quasi-finite at a prime `𝔮` of `S`, and let `Sq` be a
localization of `S` at `𝔮`. Then `Sq` is flat over `k[y_1, …, y_d]` if and only if `Sq` is
Cohen–Macaulay and `dim_𝔮(S/k) = d`. -/
public theorem solution
    {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] {σ : Type*}
    [Finite σ] [Algebra (MvPolynomial σ k) S] [IsScalarTower k (MvPolynomial σ k) S]
    (𝔮 : Ideal S) [𝔮.IsPrime] [Algebra.QuasiFiniteAt (MvPolynomial σ k) 𝔮] (Sq : Type*)
    [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq 𝔮] [IsLocalRing Sq]
    [Algebra (MvPolynomial σ k) Sq] [IsScalarTower (MvPolynomial σ k) S Sq] :
    Module.Flat (MvPolynomial σ k) Sq ↔
      Module.IsMaximalCohenMacaulay Sq Sq ∧
        Algebra.relativeDimensionAt k 𝔮 = Nat.card σ := by
  have : Algebra.FiniteType (MvPolynomial σ k) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial σ k) S
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  set 𝔭 : Ideal (MvPolynomial σ k) := 𝔮.under (MvPolynomial σ k) with h𝔭
  have : 𝔭.IsPrime := Ideal.IsPrime.under _ 𝔮
  have : 𝔮.LiesOver 𝔭 := ⟨rfl⟩
  -- `Sq` is an algebra over `k[y]_𝔭`, since `k[y] ∖ 𝔭` maps to units of `S_𝔮`
  have hunit : ∀ y : 𝔭.primeCompl,
      IsUnit (algebraMap (MvPolynomial σ k) Sq (y : MvPolynomial σ k)) := fun y ↦ by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k) S Sq]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Sq 𝔮 _).mpr y.2
  let : Algebra (Localization.AtPrime 𝔭) Sq := (IsLocalization.lift hunit).toAlgebra
  have : IsScalarTower (MvPolynomial σ k) (Localization.AtPrime 𝔭) Sq :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (IsLocalization.lift_eq hunit x).symm
  -- quasi-finiteness at `𝔮`: the fibre through `𝔮` is discrete
  have hqf (𝔮' : Ideal S) (h𝔮' : 𝔮'.IsPrime) (hle : 𝔮' ≤ 𝔮)
      (heq : 𝔮'.under (MvPolynomial σ k) = 𝔭) : 𝔮' = 𝔮 := by
    have := h𝔮'
    exact Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := MvPolynomial σ k) hle
      (by rw [heq, h𝔭])
  rw [flat_iff_isMaximalCohenMacaulay_and_height_eq 𝔭 𝔮 Sq (Rp := Localization.AtPrime 𝔭) hqf
      (Ideal.height_le_height_of_liesOver_of_quasiFiniteAt 𝔭 𝔮),
    relativeDimensionAt_eq_iff_height_eq_height k 𝔭 𝔮]

end Stacks.CohenMacaulay.FlatLocus


/-!
# The flat locus of a quasi-finite map from a polynomial ring is its Cohen–Macaulay locus

Let `S` be a finite type algebra over a field `k` and let `φ : k[y_1, …, y_d] → S` be a
quasi-finite `k`-algebra map. Then for a prime `𝔮` of `S` the local ring `S_𝔮` is flat over
`k[y_1, …, y_d]` if and only if `S_𝔮` is Cohen–Macaulay and `dim_𝔮(S/k) = d`. As subsets of
`Spec(S)` the flat locus of `φ` and the locus of Cohen–Macaulay points of relative dimension `d`
therefore coincide, which is the form the source gives the lemma.

Both directions compare `dim(S_𝔮)` with `dim(k[y]_𝔭)`, where `𝔭 = φ⁻¹(𝔮)`. Quasi-finiteness at
`𝔮` gives `dim(S_𝔮) ≤ dim(k[y]_𝔭)` (00QF) and makes `κ(𝔮)/κ(𝔭)` finite, hence
`trdeg_k κ(𝔭) = trdeg_k κ(𝔮)`. If `S_𝔮` is flat, then applying 00R5 to the flat local
homomorphism `k[y]_𝔭 → S_𝔮`, whose source is regular and so Cohen–Macaulay, shows both that
`S_𝔮` is Cohen–Macaulay and that `dim(S_𝔮) = dim(k[y]_𝔭)`; with the equality of transcendence
degrees and 00P1 the latter is `dim_𝔮(S/k) = d`. Conversely `dim_𝔮(S/k) = d` and 00P1 give
`dim(S_𝔮) = dim(k[y]_𝔭)`, and then miracle flatness 00R4 over the regular local ring `k[y]_𝔭`
gives flatness.

## Main results

* `Module.Flat.atPrime_iff_isMaximalCohenMacaulay_and_relativeDimensionAt_eq`: Stacks 00RE.

## Implementation notes

Cohen–Macaulayness of the Noetherian local ring `S_𝔮` (Definition 00N8: it is Cohen–Macaulay as
a module over itself) is spelled `Module.IsMaximalCohenMacaulay Sq Sq`, that is
`depth_{𝔪}(S_𝔮) = dim(S_𝔮)` (tag 00NF), as in the companion statements for tags 00NA, 00NB, 00R4 and
00R5; for `M = A` the module notion of Definition 00N3 agrees with the maximal one because
`Supp(A) = Spec(A)`.

The polynomial algebra `k[y_1, …, y_d]` is `MvPolynomial σ k` for a finite index type `σ`, with
`d = Nat.card σ`. This is the generality of Mathlib's dimension theory of polynomial rings
(`MvPolynomial.ringKrullDim_of_isNoetherianRing`) and of the companion statement for tag 00ND; the
source's `k[y_1, …, y_d]` is the case `σ = Fin d`.

The map `φ` is the `Algebra (MvPolynomial σ k) S` structure, so it is pinned rather than merely
assumed to exist, and `IsScalarTower k (MvPolynomial σ k) S` says that it is a map of
`k`-algebras. The source leaves that compatibility implicit in writing `dim_𝔮(S/k)` for the
`k`-algebra `S` alongside a ring map from `k[y_1, …, y_d]`; it is used, since the comparison of
transcendence degrees over `k` of `κ(𝔭)` and `κ(𝔮)` is a statement about the two `k`-structures
at once.

The localization `S_𝔮` is abstract: any `S`-algebra `Sq` with `IsLocalization.AtPrime Sq 𝔮`,
as in the statements for tags 00NB and 00ND, its `k[y_1, …, y_d]`-algebra structure pinned to the
composite by `IsScalarTower (MvPolynomial σ k) S Sq`. `IsLocalRing Sq` is assumed because
instance search does not derive it from `IsLocalization.AtPrime`.

Two departures from the source's form, both of which strengthen the statement. First, the source
assumes `φ` quasi-finite, that is of finite type and quasi-finite at every prime, equivalently
that every fibre `S ⊗_{k[y]} κ(𝔭)` is finite over `κ(𝔭)` (00PM), which is Mathlib's
`Algebra.QuasiFinite`. A statement at one prime `𝔮` uses only quasi-finiteness at `𝔮`, so that is
what is assumed: `Algebra.QuasiFiniteAt (MvPolynomial σ k) 𝔮`, the property of Definition 00PL,
which the global hypothesis supplies at every prime by instance. Finite type over `k` is kept,
being the source's hypothesis and what makes `S` of finite type over `k[y_1, …, y_d]`, as the
translation 00PM of quasi-finiteness and Lemma 00QF both need. Second, the source's equality of
subsets of `Spec(S)` is stated pointwise as an `Iff` at `𝔮`, Mathlib's shape for a membership
criterion; the equality of the two subsets of `Spec S` is `Set.ext` of it, taken at the concrete
`Localization.AtPrime`.

Faithfulness to [StackProject 00RE]:

1. No hypothesis is idle: `Field k` and `Algebra.FiniteType k S` are the source's and carry the
   dimension theory over `k` used by 00P1; `Finite σ` gives the finite `d` occurring in the
   conclusion; the algebra and scalar tower instances are `φ` and its `k`-linearity;
   quasi-finiteness at `𝔮` is what forces `dim(S_𝔮) ≤ dim(k[y]_𝔭)`, and without it the
   statement is false (`k[y] → k[y, x]` at `𝔮 = 0` is flat, with `dim_𝔮(S/k) = 2 ≠ 1`).
2. The scalars and base are the source's: flatness is over `MvPolynomial σ k` itself, not over its
   localization at `𝔭`; the relative dimension is `dim_𝔮(S/k)`, taken over the field `k` and not
   over the polynomial ring; and Cohen–Macaulayness is depth against dimension for `S_𝔮` over
   itself.
3. The maps and quantities are pinned: `φ` is `algebraMap (MvPolynomial σ k) S`, the localization
   is pinned by `IsLocalization.AtPrime Sq 𝔮` and `IsScalarTower (MvPolynomial σ k) S Sq`, and
   both members of the conclusion are equations between named quantities, not existence claims.
4. The instantiation is not degenerate: for `S = MvPolynomial σ k` and `φ` the identity every
   prime lies on both sides, `S_𝔮` being regular of `dim_𝔮(S/k) = Nat.card σ`; and both sides can
   fail together, as for `σ = Fin 1`, `S = k[y] × k` and `φ(y) = (y, 0)`, which is quasi-finite,
   at the prime `𝔮 = k[y] × 0`, where `S_𝔮 = k` is Cohen–Macaulay but is not flat over `k[y]`
   and has `dim_𝔮(S/k) = 0 ≠ 1`. So neither side is implied by the hypotheses alone.

## References

* [StackProject 00RE](https://stacks.math.columbia.edu/tag/00RE)
* [StackProject 00QD](https://stacks.math.columbia.edu/tag/00QD)
* [StackProject 00PM](https://stacks.math.columbia.edu/tag/00PM)

## Tags

Cohen-Macaulay ring, flatness, quasi-finite ring map, relative dimension, polynomial ring
-/


/-- **Stacks 00RE.** Let `S` be a finite type algebra over a field `k`, let
`φ : k[y_1, …, y_d] → S` be a map of `k`-algebras from a polynomial ring in `d = Nat.card σ`
variables, and let `𝔮` be a prime of `S` at which `φ` is quasi-finite, with localization
`S_𝔮 = Sq`. Then `S_𝔮` is flat over `k[y_1, …, y_d]` if and only if `S_𝔮` is Cohen–Macaulay and
`dim_𝔮(S/k) = d`. Taking `Sq = Localization.AtPrime 𝔮` and `Set.ext`, this is the source's
equality of the flat locus and the Cohen–Macaulay locus of relative dimension `d` inside
`Spec(S)`. -/
@[stacks 00RE "Cohen-Macaulayness of the Noetherian local ring `S_𝔮` (Definition 00N8) is
`Module.IsMaximalCohenMacaulay Sq Sq`; `k[y_1, …, y_d]` is `MvPolynomial σ k` with
`d = Nat.card σ`; the localization is an abstract `IsLocalization.AtPrime`; and the equality of
subsets of `Spec S` is stated pointwise at `𝔮`, with the source's global quasi-finiteness of `φ`
weakened to quasi-finiteness at `𝔮` (Definition 00PL). See the module docstring."]
public theorem Module.Flat.atPrime_iff_isMaximalCohenMacaulay_and_relativeDimensionAt_eq
    {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] {σ : Type*}
    [Finite σ] [Algebra (MvPolynomial σ k) S] [IsScalarTower k (MvPolynomial σ k) S]
    (𝔮 : Ideal S) [𝔮.IsPrime] [Algebra.QuasiFiniteAt (MvPolynomial σ k) 𝔮] (Sq : Type*)
    [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq 𝔮] [IsLocalRing Sq]
    [Algebra (MvPolynomial σ k) Sq] [IsScalarTower (MvPolynomial σ k) S Sq] :
    Module.Flat (MvPolynomial σ k) Sq ↔
      Module.IsMaximalCohenMacaulay Sq Sq ∧ Algebra.relativeDimensionAt k 𝔮 = Nat.card σ :=
    by apply Stacks.CohenMacaulay.FlatLocus.solution
