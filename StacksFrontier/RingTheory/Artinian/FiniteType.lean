module

public import StacksFrontier.Topology.Dimension.Krull
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.Finiteness.NilpotentKer
import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# Isolated points of the spectrum of an algebra of finite type

Let `k` be an artinian ring, let `S` be a `k`-algebra of finite type and let `𝔮` be a prime of
`S`. This file proves Stacks 00PJ: the six conditions "`𝔮` is an isolated point of `Spec S`",
"`S_𝔮` is finite over `k`", "`D(g) = {𝔮}` for some `g ∉ 𝔮`", "`Spec S` has dimension `0` at
`𝔮`", "`𝔮` is a closed point of `Spec S` and `dim S_𝔮 = 0`" and "`κ(𝔮)` is finite over `k` and
`dim S_𝔮 = 0`" are equivalent, and that when they hold `S` splits as `S_𝔮 × S'` with `S'` again
of finite type over `k`, the first component of the splitting being the localization map.

## Main results

* `Stacks.Artinian.IsolatedPoint.solution`: Stacks 00PJ, the equivalence of the six conditions
  and the splitting.

## Implementation notes

Conditions (1), (2) and (3) are Mathlib's quasi-finiteness API read at the prime `𝔮`: condition
(2) is `Algebra.QuasiFiniteAt k 𝔮` (`finite_iff_quasiFiniteAt`, using that `k` is artinian), and
the cycle (1) → (2) → (3) → (1) is `Algebra.QuasiFiniteAt.of_isOpen_singleton`,
`Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton` and the fact that a basic open is open.

The source deduces (4) → (2) by shrinking a zero-dimensional open neighbourhood of `𝔮` to a
basic open `D(g)`, observing that `S_g` is then artinian and that `Spec S_g` is therefore finite
and discrete. The route taken here is purely topological and reaches (5) instead of (2): in a
`T0` space of Krull dimension at most `0` the specialization order is trivial
(`Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero`), and a Jacobson space has closed points in
every nonempty locally closed subset, so a point at which a `T0` Jacobson space has dimension
`0` is a closed point minimal for specialization
(`isClosed_singleton_and_forall_specializes_of_topologicalKrullDimAt_le_zero`). Since `Spec S` is
`T0` and, `S` being of finite type over an artinian ring, Jacobson, that is exactly (5), and (5)
→ (1) is then Mathlib's `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`.
Both statements are about arbitrary topological spaces and neither mentions rings; they are what
the source's use of Lemmas 00G1, 00G3, 00KJ and 00OU amounts to here.

The remaining implication (6) → (2) is `Module.finite_of_surjective_of_ker_le_nilradical` applied
to the residue map of `S_𝔮`: `dim S_𝔮 = 0` makes the maximal ideal of `S_𝔮` its nilradical, and
that ideal is finitely generated because `S` — hence `S_𝔮` — is noetherian.

The product decomposition is read off the idempotent attached to the clopen set `{𝔮}` by Stacks
00EE, in Mathlib's form `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen` together with
`AlgEquiv.prodQuotientOfIsIdempotentElem`: for `e` idempotent with `D(e) = {𝔮}` the first factor
`S ⧸ (1 - e)` is the localization of `S` away from `e`
(`IsLocalization.Away.quotient_of_isIdempotentElem`), and away from `e` is at `𝔮`
(`PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`), which identifies it
with `Sq` compatibly with the localization map.

## References

* [StacksProject 00PJ](https://stacks.math.columbia.edu/tag/00PJ)
-/

@[expose] public section

namespace Stacks.Artinian.IsolatedPoint

open PrimeSpectrum TopologicalSpace

section Topology

variable {X : Type*} [TopologicalSpace X]

private instance nonempty_irreducibleCloseds [Nonempty X] : Nonempty (IrreducibleCloseds X) :=
  ⟨closure {Classical.arbitrary X}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- A nonempty subsingleton space has Krull dimension `0`: its only irreducible closed subset is
the whole space. -/
private lemma topologicalKrullDim_eq_zero_of_subsingleton [Nonempty X] [Subsingleton X] :
    topologicalKrullDim X = 0 :=
  haveI : Subsingleton (IrreducibleCloseds X) := ⟨fun T T' ↦ IrreducibleCloseds.ext <| by
    have h : ∀ s : Set X, s.Nonempty → s = Set.univ := fun s ⟨y, hy⟩ ↦
      Set.eq_univ_of_forall fun x ↦ Subsingleton.elim y x ▸ hy
    rw [h _ T.isIrreducible.nonempty, h _ T'.isIrreducible.nonempty]⟩
  Order.krullDim_eq_zero

/-- An isolated point is a point at which the space has dimension `0`. -/
private lemma topologicalKrullDimAt_eq_zero_of_isOpen_singleton (x : X) (h : IsOpen {x}) :
    topologicalKrullDimAt X x = 0 := by
  obtain ⟨⟨U, hxU, hU, hdim⟩, hle⟩ := topologicalKrullDimAt_isLeast X x
  refine le_antisymm ?_ ?_
  · have : Nonempty ↥({x} : Set X) := ⟨⟨x, rfl⟩⟩
    have : Subsingleton ↥({x} : Set X) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    exact (hle ⟨{x}, rfl, h, rfl⟩).trans topologicalKrullDim_eq_zero_of_subsingleton.le
  · have : Nonempty ↥U := ⟨⟨x, hxU⟩⟩
    exact hdim ▸ Order.krullDim_nonneg

/-- A point at which a `T0` Jacobson space has Krull dimension `0` is a closed point, and it is
minimal for specialization. The dimension is attained on some open neighbourhood `U` of the
point, on which the specialization order is therefore trivial; every generalization of the point
lies in `U` because `U` is open, and `U` meets the closure of the point in a nonempty locally
closed set, which contains a closed point of the ambient space. -/
private theorem isClosed_singleton_and_forall_specializes_of_topologicalKrullDimAt_le_zero
    [T0Space X] [JacobsonSpace X] (x : X) (h : topologicalKrullDimAt X x ≤ 0) :
    IsClosed {x} ∧ ∀ y, y ⤳ x → y = x := by
  obtain ⟨⟨U, hxU, hU, hdim⟩, -⟩ := topologicalKrullDimAt_isLeast X x
  have hU0 : topologicalKrullDim ↥U ≤ 0 := hdim ▸ h
  have key : ∀ y ∈ U, ∀ z ∈ U, y ⤳ z → y = z := fun y hy z hz hyz ↦
    congrArg Subtype.val (Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero hU0
      (X := ↥U) (x := ⟨y, hy⟩) (y := ⟨z, hz⟩)
      (Topology.IsInducing.subtypeVal.specializes_iff.mp hyz))
  have hgen : ∀ y, y ⤳ x → y ∈ U := fun y hy ↦ by
    by_contra hyU
    exact absurd hxU (hU.isClosed_compl.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hyU) (specializes_iff_mem_closure.mp hy))
  refine ⟨?_, fun y hy ↦ key y (hgen y hy) x hxU hy⟩
  obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := jacobsonSpace_iff_locallyClosed.mp ‹_› (closure {x} ∩ U)
    ⟨x, subset_closure rfl, hxU⟩ ⟨U, closure {x}, hU, isClosed_closure, Set.inter_comm _ _⟩
  exact key x hxU z hz2 (specializes_iff_mem_closure.mpr hz1) ▸ mem_closedPoints_iff.mp hz3

end Topology

section Algebra

variable (k : Type*) {S : Type*} [CommRing k] [CommRing S] [Algebra k S] (𝔮 : Ideal S)
  [𝔮.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq 𝔮]
  [Algebra k Sq] [IsScalarTower k S Sq]

/-- Any model `Sq` of the local ring of `S` at `𝔮` is `k`-algebra isomorphic to
`Localization.AtPrime 𝔮`. -/
private noncomputable def localizationAtPrimeAlgEquiv : Localization.AtPrime 𝔮 ≃ₐ[k] Sq :=
  (IsLocalization.algEquiv 𝔮.primeCompl (Localization.AtPrime 𝔮) Sq).restrictScalars k

/-- Any model of the local ring at `𝔮` is finite over `k` exactly when `Localization.AtPrime 𝔮`
is. -/
private lemma finite_iff_finite_localizationAtPrime :
    Module.Finite k Sq ↔ Module.Finite k (Localization.AtPrime 𝔮) := by
  constructor
  · intro h
    exact .of_surjective (localizationAtPrimeAlgEquiv k 𝔮 Sq).symm.toLinearMap
      (localizationAtPrimeAlgEquiv k 𝔮 Sq).symm.surjective
  · intro h
    exact .of_surjective (localizationAtPrimeAlgEquiv k 𝔮 Sq).toLinearMap
      (localizationAtPrimeAlgEquiv k 𝔮 Sq).surjective

/-- Over an artinian base, `S_𝔮` being finite is quasi-finiteness of `S` at `𝔮`. -/
private lemma finite_iff_quasiFiniteAt [IsArtinianRing k] :
    Module.Finite k Sq ↔ Algebra.QuasiFiniteAt k 𝔮 :=
  (finite_iff_finite_localizationAtPrime k 𝔮 Sq).trans
    Algebra.QuasiFinite.iff_of_isArtinianRing.symm

/-- The residue field at `𝔮` is a quotient of the local ring at `𝔮`. -/
private lemma finite_residueField_of_finite (h : Module.Finite k Sq) :
    Module.Finite k 𝔮.ResidueField := by
  have : Module.Finite k (Localization.AtPrime 𝔮) :=
    (finite_iff_finite_localizationAtPrime k 𝔮 Sq).mp h
  exact .of_surjective
    (IsScalarTower.toAlgHom k (Localization.AtPrime 𝔮) 𝔮.ResidueField).toLinearMap
    Ideal.Quotient.mk_surjective

/-- A prime of height `0` whose residue field is finite over `k` has a local ring finite over
`k`: the maximal ideal of `S_𝔮` is its nilradical, and it is finitely generated because `S`, and
hence `S_𝔮`, is noetherian. -/
private lemma finite_of_finite_residueField [IsNoetherianRing S]
    (h : Module.Finite k 𝔮.ResidueField) (hht : 𝔮.height = 0) : Module.Finite k Sq := by
  rw [finite_iff_finite_localizationAtPrime k 𝔮 Sq]
  have : Ring.KrullDimLE 0 (Localization.AtPrime 𝔮) := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (Localization.AtPrime 𝔮), hht]; rfl)
  refine Module.finite_of_surjective_of_ker_le_nilradical
    (IsScalarTower.toAlgHom k (Localization.AtPrime 𝔮) 𝔮.ResidueField)
    Ideal.Quotient.mk_surjective ?_ (IsNoetherian.noetherian _)
  rw [Ring.KrullDimLE.nilradical_eq_maximalIdeal]
  intro x hx
  have hx' : algebraMap (Localization.AtPrime 𝔮) 𝔮.ResidueField x = 0 := hx
  rwa [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff] at hx'

end Algebra

public theorem solution (k : Type u)
    {S : Type v} [CommRing k] [IsArtinianRing k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (𝔮 : Ideal S) [𝔮.IsPrime] (Sq : Type w) [CommRing Sq]
    [Algebra S Sq] [IsLocalization.AtPrime Sq 𝔮] [Algebra k Sq] [IsScalarTower k S Sq] :
    List.TFAE
        [IsOpen {(⟨𝔮, ‹_›⟩ : PrimeSpectrum S)},
          Module.Finite k Sq,
          ∃ g ∉ 𝔮, (basicOpen g : Set (PrimeSpectrum S)) = {⟨𝔮, ‹_›⟩},
          topologicalKrullDimAt (PrimeSpectrum S) ⟨𝔮, ‹_›⟩ = 0,
          IsClosed {(⟨𝔮, ‹_›⟩ : PrimeSpectrum S)} ∧ 𝔮.height = 0,
          Module.Finite k 𝔮.ResidueField ∧ 𝔮.height = 0] ∧
      (IsOpen {(⟨𝔮, ‹_›⟩ : PrimeSpectrum S)} →
        ∃ (S' : Type v) (_ : CommRing S') (_ : Algebra k S'), Algebra.FiniteType k S' ∧
          ∃ e : S ≃ₐ[k] Sq × S', ∀ x, (e x).1 = algebraMap S Sq x) := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  refine ⟨?_, ?_⟩
  · tfae_have 1 → 2 := fun h ↦
      (finite_iff_quasiFiniteAt k 𝔮 Sq).mpr (Algebra.QuasiFiniteAt.of_isOpen_singleton ⟨𝔮, ‹_›⟩ h)
    tfae_have 2 → 3 := fun h ↦
      have := (finite_iff_quasiFiniteAt k 𝔮 Sq).mp h
      Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton (R := k) 𝔮
    tfae_have 3 → 1 := fun ⟨g, _, hg⟩ ↦ hg ▸ (basicOpen g).isOpen
    tfae_have 1 → 4 := fun h ↦ topologicalKrullDimAt_eq_zero_of_isOpen_singleton _ h
    tfae_have 4 → 5 := fun h ↦ by
      obtain ⟨hc, hgen⟩ :=
        isClosed_singleton_and_forall_specializes_of_topologicalKrullDimAt_le_zero _ h.le
      refine ⟨hc, Ideal.height_eq_zero_iff.mpr
        ((PrimeSpectrum.isMin_iff (x := (⟨𝔮, ‹_›⟩ : PrimeSpectrum S))).mp fun b hb ↦ ?_)⟩
      exact le_of_eq (hgen b ((PrimeSpectrum.le_iff_specializes b _).mp hb)).symm
    tfae_have 5 → 1 := fun ⟨hc, hht⟩ ↦ by
      have hmin : IsMin (⟨𝔮, ‹_›⟩ : PrimeSpectrum S) :=
        PrimeSpectrum.isMin_iff.mpr (Ideal.height_eq_zero_iff.mp hht)
      have hst : StableUnderGeneralization {(⟨𝔮, ‹_›⟩ : PrimeSpectrum S)} := by
        intro x y hyx hx
        simp only [Set.mem_singleton_iff] at hx ⊢
        subst hx
        exact le_antisymm ((PrimeSpectrum.le_iff_specializes y _).mpr hyx)
          (hmin ((PrimeSpectrum.le_iff_specializes y _).mpr hyx))
      have H := (PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing
        (⟨𝔮, ‹_›⟩ : PrimeSpectrum S)).out 3 1
      exact H.mp ⟨hc, hst⟩
    tfae_have 1 → 6 := fun h ↦
      ⟨finite_residueField_of_finite k 𝔮 Sq (tfae_1_to_2 h), (tfae_4_to_5 (tfae_1_to_4 h)).2⟩
    tfae_have 6 → 2 := fun ⟨h₁, h₂⟩ ↦ finite_of_finite_residueField k 𝔮 Sq h₁ h₂
    tfae_finish
  · intro h
    have : Algebra.QuasiFiniteAt k 𝔮 := Algebra.QuasiFiniteAt.of_isOpen_singleton ⟨𝔮, ‹_›⟩ h
    obtain ⟨e, he, hb⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
      (Algebra.QuasiFiniteAt.isClopen_singleton (R := k) (⟨𝔮, ‹_›⟩ : PrimeSpectrum S))
    have : IsLocalization.Away e (S ⧸ Ideal.span {1 - e}) :=
      IsLocalization.Away.quotient_of_isIdempotentElem he
    have : IsLocalization.AtPrime (S ⧸ Ideal.span {1 - e}) 𝔮 :=
      (PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton
        (p := (⟨𝔮, ‹_›⟩ : PrimeSpectrum S)) hb.symm).mp ‹_›
    refine ⟨S ⧸ Ideal.span {e}, inferInstance, inferInstance, inferInstance,
      (AlgEquiv.prodQuotientOfIsIdempotentElem k he.one_sub he (by ring)
          (by rw [sub_mul, one_mul, he.eq, sub_self])).trans
        (AlgEquiv.prodCongr ((IsLocalization.algEquiv 𝔮.primeCompl
          (S ⧸ Ideal.span {1 - e}) Sq).restrictScalars k) AlgEquiv.refl), fun x ↦ ?_⟩
    rw [AlgEquiv.trans_apply, AlgEquiv.prodQuotientOfIsIdempotentElem_apply]
    exact (IsLocalization.algEquiv 𝔮.primeCompl (S ⧸ Ideal.span {1 - e}) Sq).commutes x

end Stacks.Artinian.IsolatedPoint

end

/-!
# Isolated points of the spectrum of an algebra of finite type

Let `k` be an artinian ring, let `S` be a `k`-algebra of finite type and let `𝔮` be a prime of
`S`. Then the following are equivalent: `𝔮` is an isolated point of `Spec S`; the local ring
`S_𝔮` is finite over `k`; there is a `g ∉ 𝔮` with `D(g) = {𝔮}`; the dimension of `Spec S` at
`𝔮` is `0`; `𝔮` is a closed point of `Spec S` and `dim S_𝔮 = 0`; the residue field `κ(𝔮)` is
finite over `k` and `dim S_𝔮 = 0`. When these hold, `S` splits as a product `S_𝔮 × S'` with `S'`
again of finite type over `k`, the projection to the first factor being the localization map.

The source's other closing assertion, that `S_g = S_𝔮` for `g` as in the third condition, holds
for every `g` with `D(g) = {𝔮}` over any commutative base and is
`PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`.

## Main results

* `PrimeSpectrum.isOpen_singleton_tfae_and_exists_algEquiv_prod_of_finiteType`: the six equivalent
  conditions of the source together with the product decomposition.

## Implementation notes

The source takes `k` to be a field; the statement here only asks that `k` be artinian, which is
the generality of Mathlib's quasi-finiteness API (`Algebra.QuasiFiniteAt.of_isOpen_singleton`,
`Module.Finite.of_quasiFinite` and `Algebra.QuasiFiniteAt.isClopen_singleton` all assume
`IsArtinianRing R`) and the generality the arguments have: of `k` they use that it is Noetherian,
that it is Jacobson and that it is zero dimensional, which together are exactly artinian.
Instantiating `k` at a field is the source's statement. Condition (2) is also
`Algebra.QuasiFiniteAt k 𝔮` in Mathlib's language, by `Algebra.QuasiFinite.iff_of_isArtinianRing`;
the six conditions are stated as the source states them rather than through that class.

The local ring `S_𝔮` is an abstract model `Sq`: any `S`-algebra with `IsLocalization.AtPrime Sq 𝔮`
and a compatible `k`-algebra structure, `Localization.AtPrime 𝔮` being one instantiation.

The source's closing assertion `S_𝔮 = S_g` is not part of the theorem below: for `D(g) = {𝔮}` the
localizations of `S` away from `g` are exactly the localizations at `𝔮`, over any commutative
base and with no finiteness hypothesis on it, which is Mathlib's
`PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`. Stating it here would
mean restating a strictly more general lemma under the five hypotheses its proof does not use
(`IsArtinianRing k`, `Algebra k S`, `Algebra.FiniteType k S`, `Algebra k Sq` and
`IsScalarTower k S Sq`), so the tag is realized jointly with that lemma instead.

"`𝔮` is an isolated point of `Spec S`" is `IsOpen {𝔮}`, as in Mathlib's
`PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`, and "`𝔮` is a closed
point" is `IsClosed {𝔮}`, equivalently `𝔮.IsMaximal` by
`PrimeSpectrum.isClosed_singleton_iff_isMaximal`. The dimension `dim_𝔮 Spec S` of the source is
`topologicalKrullDimAt`, the project's form of Stacks 0055 (4), and `dim S_𝔮` is `𝔮.height`, which
is intrinsic to `S` and agrees with `ringKrullDim Sq` by
`IsLocalization.AtPrime.ringKrullDim_eq_height`. The residue field `κ(𝔮)` is Mathlib's
`𝔮.ResidueField`, which does not depend on the chosen `Sq`.

In the product decomposition the canonical map is pinned: the first component of the `k`-algebra
equivalence `S ≃ₐ[k] Sq × S'` is `algebraMap S Sq`, so the first factor is the local ring together
with its localization map and not merely a ring abstractly isomorphic to it.

Faithfulness. (1) No hypothesis is idle: `Algebra.FiniteType k S` is needed already for (1) → (2)
(for `k = ℚ` and `S = ℚ(x)` the unique point of `Spec S` is isolated while `S_𝔮 = ℚ(x)` is not
finite over `ℚ`), and so is `IsArtinianRing k` (for `k` a discrete valuation ring with fraction
field `K` and `S = K = k[t⁻¹]`, of finite type over `k`, the prime `𝔮 = 0` is again isolated with
`S_𝔮 = K` not finite over `k`); `IsScalarTower k S Sq` is what makes conditions (2) and (6)
statements about the given `k`-structure of `S`. (2) The scalars and base are the source's:
finiteness in (2) and (6) is over `k`, the localization is at `𝔮` over `S`, and the product
decomposition is one of `k`-algebras. (3) The canonical maps are pinned: `IsLocalization.AtPrime`
pins `Sq` along `algebraMap S Sq`, and the decomposition pins that same map as the first component
of the equivalence. (4) The instantiation is not degenerate: for `k` a field, `S = k × k[x]` and
`𝔮` the prime `0 × k[x]` all six conditions hold, with `g = (1, 0)`, `S_𝔮 = k`, `S' = k[x]` and
`κ(𝔮) = k`; for `S = k[x]` and `𝔮 = (x)` all six fail, `𝔮` being a closed point of height `1`.

## References

* [StacksProject 00PJ](https://stacks.math.columbia.edu/tag/00PJ)
-/

@[expose] public section

namespace PrimeSpectrum

/-- **Stacks 00PJ.** Let `k` be an artinian ring (a field, in the source), `S` a `k`-algebra of
finite type, `𝔮` a prime of `S` and `Sq` a model of the local ring `S_𝔮`. The following are
equivalent: `𝔮` is an isolated point of `Spec S`; `S_𝔮` is finite over `k`; `D(g) = {𝔮}` for some
`g ∉ 𝔮`; `Spec S` has dimension `0` at `𝔮`; `𝔮` is a closed point and `dim S_𝔮 = 0`; the residue
field `κ(𝔮)` is finite over `k` and `dim S_𝔮 = 0`. In that case `S = S_𝔮 × S'` for a finite type
`k`-algebra `S'`, compatibly with the localization map. -/
@[stacks 00PJ "The source's field `k` is weakened to an artinian ring; `S_𝔮` is an abstract
localization `Sq`, `dim_𝔮 Spec S` is `topologicalKrullDimAt` and `dim S_𝔮` is `𝔮.height`. The
closing assertion `S_𝔮 = S_g` is Mathlib's more general
`PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`, with which this tag is
realized jointly. See the module docstring.",
  ega "0 14.1.10" "(1)⇔(4), Spec f.t. alg",
  ega "II 6.2.2" "affine, base a field"]
public theorem isOpen_singleton_tfae_and_exists_algEquiv_prod_of_finiteType (k : Type u)
    {S : Type v} [CommRing k] [IsArtinianRing k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (𝔮 : Ideal S) [𝔮.IsPrime] (Sq : Type w) [CommRing Sq]
    [Algebra S Sq] [IsLocalization.AtPrime Sq 𝔮] [Algebra k Sq] [IsScalarTower k S Sq] :
    List.TFAE
        [IsOpen {(⟨𝔮, ‹_›⟩ : PrimeSpectrum S)},
          Module.Finite k Sq,
          ∃ g ∉ 𝔮, (basicOpen g : Set (PrimeSpectrum S)) = {⟨𝔮, ‹_›⟩},
          topologicalKrullDimAt (PrimeSpectrum S) ⟨𝔮, ‹_›⟩ = 0,
          IsClosed {(⟨𝔮, ‹_›⟩ : PrimeSpectrum S)} ∧ 𝔮.height = 0,
          Module.Finite k 𝔮.ResidueField ∧ 𝔮.height = 0] ∧
      (IsOpen {(⟨𝔮, ‹_›⟩ : PrimeSpectrum S)} →
        ∃ (S' : Type v) (_ : CommRing S') (_ : Algebra k S'), Algebra.FiniteType k S' ∧
          ∃ e : S ≃ₐ[k] Sq × S', ∀ x, (e x).1 = algebraMap S Sq x) :=
            by apply Stacks.Artinian.IsolatedPoint.solution

end PrimeSpectrum

end

/-!
# Zero-dimensional finite type algebras over an Artinian ring

Proof of `Algebra.FiniteType.krullDimLE_zero_tfae`: for an algebra `S` of finite type over an
Artinian ring `R`, the eight conditions `dim S ≤ 0`, `Spec S` finite, `Max S` finite, `Spec S`
Hausdorff, `S` finite as an `R`-module, `S` Artinian, `Spec S` discrete, and `Spec S` totally
disconnected are equivalent.

The route is the source's, with the three chains it uses. The first chain is
`dim S ≤ 0 ⇒ S` finite over `R` `⇒ S` Artinian `⇒ Spec S` discrete `⇒ Spec S` finite
`⇒ Max S` finite `⇒ Spec S` discrete `⇒ dim S ≤ 0`: the first two steps are the Nullstellensatz
for an Artinian base (`Module.finite_iff_krullDimLE_zero`, `Module.finite_iff_isArtinianRing`,
which is where the source's residue fields `κ(𝔪ᵢ)` and the finite length of `S` over itself are
used), the third is Hopkins–Levitzki, and the last two are the description of a discrete
`Spec S` as a finite one of dimension `0`. The step from finitely many maximal ideals back to
discreteness is the source's appeal to a Jacobson `Spec S`: a finite Jacobson space is discrete,
and `S` is Jacobson because `R` is (having dimension `0`) and `S` is of finite type over it. The
second and third chains are the Hausdorff and the totally disconnected condition, each
equivalent to every prime of `S` being maximal by [StackProject 04MG], which is `dim S ≤ 0`.

## Main results

* `Stacks.Artinian.ZeroDimFiniteType.solution`: the eight conditions are equivalent.

## Implementation notes

The source deduces "finitely many primes" from "dimension `0`" by counting irreducible
components of the Noetherian space `Spec S`, and "dimension `0`" from "finitely many maximal
ideals" by a topological lemma on Jacobson spaces. Only the second of these is taken from
topology here (`instDiscreteTopologyOfFiniteOfJacobsonSpace`, used through
`PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical`); the first is the
ring-theoretic `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero` applied to the
Artinian `S`, which the chain has already produced. The source's route through Noether
normalization is the one it explicitly avoids, and is avoided here too.

Two steps are stated as `private` lemmas because they are general facts of the theory that
Mathlib does not have in this form and that the source does not state separately: that the Jacobson
radical of a Jacobson ring is its nilradical, and that a Jacobson ring with finitely many
maximal ideals has discrete prime spectrum. The second is the source's Topology, Lemma 07JU in
the shape this proof needs; the first is what feeds the nilradical condition of its Mathlib
sibling.

## References

* [StackProject 0ALW](https://stacks.math.columbia.edu/tag/0ALW)
* [StackProject 04MG](https://stacks.math.columbia.edu/tag/04MG)
-/

/-- In a Jacobson ring the Jacobson radical coincides with the nilradical. This is the
`IsJacobsonRing` sibling of `Ring.jacobson_eq_nilradical_of_krullDimLE_zero`. -/
@[ega "IV 10.10.3" "partial"]
private theorem Ring.jacobson_eq_nilradical_of_isJacobsonRing (R : Type*) [CommRing R]
    [IsJacobsonRing R] : Ring.jacobson R = nilradical R :=
  Ideal.jacobson_bot.symm.trans (Ideal.radical_eq_jacobson ⊥).symm

/-- A Jacobson ring with only finitely many maximal ideals has discrete prime spectrum.
This is the ring-theoretic form of "a finite Jacobson space is discrete". -/
private theorem PrimeSpectrum.discreteTopology_of_isJacobsonRing_of_finite_maximalSpectrum
    (R : Type*) [CommRing R] [IsJacobsonRing R] [Finite (MaximalSpectrum R)] :
    DiscreteTopology (PrimeSpectrum R) := by
  rw [PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical]
  refine ⟨Finite.of_injective (fun I : {I : Ideal R | I.IsMaximal} ↦
    (⟨I.1, I.2⟩ : MaximalSpectrum R))
    fun I J h ↦ Subtype.ext (congrArg MaximalSpectrum.asIdeal h), ?_⟩
  rw [← Ring.jacobson_eq_sInf_isMaximal, Ring.jacobson_eq_nilradical_of_isJacobsonRing]

namespace Stacks.Artinian.ZeroDimFiniteType

public theorem solution (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsArtinianRing R] [Algebra.FiniteType R S] :
    List.TFAE
      [ Ring.KrullDimLE 0 S,
        Finite (PrimeSpectrum S),
        Finite (MaximalSpectrum S),
        T2Space (PrimeSpectrum S),
        Module.Finite R S,
        IsArtinianRing S,
        DiscreteTopology (PrimeSpectrum S),
        TotallyDisconnectedSpace (PrimeSpectrum S) ] := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R) (B := S)
  -- The eight conditions of [StackProject 04MG] on `Spec S`, in the order (1)-(8) there.
  have h04MG := spec_profinite_tfae S
  tfae_have 1 → 5 := fun h ↦ (Module.finite_iff_krullDimLE_zero R S).mpr h
  tfae_have 5 → 6 := fun h ↦ (Module.finite_iff_isArtinianRing R S).mp h
  tfae_have 6 → 7 := fun h ↦ by have := h; infer_instance
  tfae_have 7 → 2 := fun h ↦
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp h).1
  tfae_have 7 → 1 := fun h ↦
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp h).2
  tfae_have 2 → 3 := fun h ↦ by
    have := h
    exact Finite.of_injective _ MaximalSpectrum.toPrimeSpectrum_injective
  tfae_have 3 → 7 := fun h ↦ by
    have := h
    exact PrimeSpectrum.discreteTopology_of_isJacobsonRing_of_finite_maximalSpectrum S
  -- Items (2) and (3) of 04MG are its item (6), that every prime of `S` is maximal.
  tfae_have 1 → 4 := fun h ↦ (h04MG.out 6 2).mp (Ring.krullDimLE_zero_iff.mp h)
  tfae_have 1 → 8 := fun h ↦ (h04MG.out 6 3).mp (Ring.krullDimLE_zero_iff.mp h)
  tfae_have 4 → 1 := fun h ↦ Ring.KrullDimLE.mk₀ ((h04MG.out 2 6).mp h)
  tfae_have 8 → 1 := fun h ↦ Ring.KrullDimLE.mk₀ ((h04MG.out 3 6).mp h)
  tfae_finish

end Stacks.Artinian.ZeroDimFiniteType

/-!
# Zero-dimensional finite type algebras over an Artinian ring

Let `R` be an Artinian ring and let `S` be an `R`-algebra of finite type. Then `S` is Noetherian
and Jacobson, and for such an `S` eight conditions agree: `dim S = 0`; `S` has finitely many
primes; `S` has finitely many maximal ideals; `Spec S` is Hausdorff; `S` is finite as an
`R`-module; `S` is Artinian; `Spec S` is discrete; `Spec S` is totally disconnected. Over a
field `R = k` the fifth condition reads `dim_k S < ∞`, and the list is the source's.

That `Spec S` is sober, Noetherian and Jacobson drives the first three: a zero-dimensional
`Spec S` has one irreducible component per point and only finitely many components, so there
are finitely many primes and a fortiori finitely many maximal ideals; conversely, in a Jacobson
ring a non-maximal prime is the intersection of the maximal ideals above it, so if there are
only finitely many of those it would equal one of them, and the dimension is `0` after all. The
Hausdorff and totally disconnected conditions are two of the topological ones of
[StackProject 04MG]: over any ring each already forces every prime to be maximal, and
conversely a zero-dimensional Noetherian `Spec S` is a finite discrete space, hence both, and
hence also discrete as in the source's item (7). Finally `S` is
finite over `R` exactly when `dim S = 0`, and Noetherian of dimension `0` is Artinian
(Hopkins–Levitzki); over a field the first of these is the source's route through the Hilbert
Nullstellensatz, which makes each of the finitely many residue fields `κ(𝔪ᵢ)` finite over `k`
and `S` of finite length over itself.

## Main results

* `Algebra.FiniteType.krullDimLE_zero_tfae`: for a finite type algebra `S` over an Artinian ring
  `R`, the eight conditions above are equivalent.

## Implementation notes

The base is an arbitrary Artinian ring rather than the source's field, and that hypothesis is
sharp: instantiating `S := R` makes item (5) hold, so items (1) and (6) force `R` to be
Noetherian of dimension `0`, which is to say Artinian. Both halves are needed — `R = ℤ` is
Noetherian with `Module.Finite ℤ ℤ` but `dim ℤ = 1`, and a zero-dimensional non-Noetherian ring
such as `k[x₁, x₂, …]/(xᵢxⱼ)` is not Artinian. A field is Artinian, so the source's statement is
the case `R := k`, where item (5) is `FiniteDimensional k S`; the generality is the one Mathlib
already uses for the implication (1) ⟺ (5) (`Module.finite_iff_krullDimLE_zero`).

The source's `dim(S) = 0` is `Ring.KrullDimLE 0 S` rather than `ringKrullDim S = 0`. The two
agree for a nontrivial ring (`ringKrullDimZero_iff_ringKrullDim_eq_zero`), and the source's
hypothesis `S ≠ 0` is there only to make the literal equality meaningful: the zero ring has
`ringKrullDim = ⊥` while satisfying the other seven conditions. With `Ring.KrullDimLE` the
equivalence holds for the zero ring too, so `Nontrivial S` is dropped; this is also the
spelling used for this tag's neighbour [StackProject 00KJ].

The source's items (1)–(7) are entries 1–7 of the `List.TFAE` in the source's order, and
`TFAE.out` is `1`-based, so `out i j` addresses the source's numbering unshifted. Item (8), the
source's "add more here", is the totally disconnected condition.

The source's item (4) — "`Spec S` satisfies one of the equivalent conditions of
[StackProject 04MG]" — is realized by items (4) and (8). Those are the two conditions of 04MG
that are not a rewrite away from item (1), and since `Spec S` is quasi-compact
(`PrimeSpectrum.compactSpace`) the two of them together say that `Spec S` is profinite, which
is 04MG (1). The remaining conditions of 04MG — every prime is maximal, every prime is minimal,
every quasi-compact open is closed, every `D(f)` is closed — are `Ring.krullDimLE_zero_iff` and
04MG itself applied to item (1), and are not repeated here; 04MG is `spec_profinite_tfae`.

Faithfulness. (1) Every hypothesis is used: without `Algebra.FiniteType R S` the field
`S = k(t)` over `R = k` has dimension `0` and one prime but is not finite over `k`, and without
`IsArtinianRing R` the equivalence already fails for `S := R`, as above. (2) The base is the
source's: item (5) is finiteness of `S` as a module over `R` itself, the ring the algebra
structure is taken over, and every other item is a condition on `S` and its own spectrum. (3)
The source names no canonical map; what has to be pinned is the dimension and the module
structure, and `Ring.KrullDimLE 0 S` pins the former as a bound on the Krull dimension of the
prime spectrum of `S` while `Module.Finite R S` pins the latter along the given algebra map,
rather than asserting that some finite generating set exists over some base. (4) The
instantiation is not degenerate: `R = k` a field and `S = k[x]/(x²)` satisfies all eight items
with `Spec S` a one-point space and `dim_k S = 2`, while `S = k[x]` satisfies none of them.

## References

* [StackProject 0ALW](https://stacks.math.columbia.edu/tag/0ALW)
* [StackProject 04MG](https://stacks.math.columbia.edu/tag/04MG)
-/

namespace Algebra.FiniteType

/-- **Zero-dimensional finite type algebras.** For an algebra `S` of finite type over an
Artinian ring `R` the following are equivalent: `S` has Krull dimension at most `0`; `S` has
finitely many prime ideals; `S` has finitely many maximal ideals; `Spec S` is Hausdorff; `S` is
finite as an `R`-module; `S` is Artinian; `Spec S` is discrete; and `Spec S` is totally
disconnected. Over a field `R = k` the fifth condition says that `S` is finite dimensional
as a `k`-vector space. -/
@[stacks 0ALW "Items (1)-(8); (4) via 04MG's Hausdorff and totally disconnected conditions.",
  ega "I 6.4.4" "affine case"]
public theorem krullDimLE_zero_tfae (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsArtinianRing R] [Algebra.FiniteType R S] :
    List.TFAE
      [ Ring.KrullDimLE 0 S,
        Finite (PrimeSpectrum S),
        Finite (MaximalSpectrum S),
        T2Space (PrimeSpectrum S),
        Module.Finite R S,
        IsArtinianRing S,
        DiscreteTopology (PrimeSpectrum S),
        TotallyDisconnectedSpace (PrimeSpectrum S) ] :=
    by apply Stacks.Artinian.ZeroDimFiniteType.solution

end Algebra.FiniteType
