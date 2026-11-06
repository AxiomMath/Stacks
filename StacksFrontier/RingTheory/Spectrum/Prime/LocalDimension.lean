module

public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
import StacksCore.Tactic.EgaSgaAttribute
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

@[expose] public section

universe u v

/-!
# Local dimension of an affine finite type scheme over a field: three descriptions

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `X = Spec S`, and let `x ∈ X` be
the point given by a prime ideal `𝔭 ⊆ S`. This file proves Stacks 00OT: the dimension `dim_x X` of
`X` at `x`, the largest dimension of an irreducible component of `X` through `x`, and the smallest
of the dimensions `dim S_𝔪 = height 𝔪` over the maximal ideals `𝔪 ⊇ 𝔭`, are all equal.

All three numbers are read in the poset `Spec S`, against the fourth quantity
`sup {coheight 𝔮 | 𝔮 a minimal prime, 𝔮 ⊆ 𝔭}`. That the second number is this supremum is the
correspondence between the components through `x` and the minimal primes below `𝔭`, together with
`dim V(𝔮) = coheight 𝔮`. The other two comparisons rest on two facts:

* *(00OS)* for `𝔮 ⊆ 𝔪` with `𝔪` maximal, `coheight 𝔮 = dim S/𝔮 ≤ height 𝔪`, because `S/𝔮` is a
  finite type domain over `k` and so has `dim S/𝔮 = height (𝔪/𝔮)`;
* *(Jacobson)* every nonempty locally closed subset of `Spec S` contains a closed point, so for
  every open `U ∋ x` there is a maximal ideal `𝔪 ⊇ 𝔭` with `𝔪 ∈ U`.

The elementary half of both comparisons is that a chain of primes contained in a set `V` all of
whose minimal primes below lie below `𝔭` has length at most that supremum: prepend a minimal prime
below the head. Applied to `V = U₀`, the complement of the union of the components *not* through
`x` — an open neighbourhood of `x`, as `Spec S` is Noetherian — this bounds `dim U₀`, and applied
to `V = ↓𝔪` for a maximal `𝔪 ∈ U₀` produced by Jacobson it bounds `height 𝔪`. In the other
direction, for an arbitrary open `U ∋ x` Jacobson produces a maximal `𝔪 ⊇ 𝔭` in `U`; then
`↓𝔪 ⊆ U`, since an open set contains every generalization of its points, so 00OS gives
`coheight 𝔮 ≤ height 𝔪 = dim ↓𝔪 ≤ dim U` for every minimal `𝔮 ⊆ 𝔭`.

## Main results

* `Stacks.Spectrum.LocalDimension.solution`: the statement of Stacks 00OT.

## Implementation notes

*The dimension of a subspace of `Spec R` is an order-theoretic Krull dimension.* A quasi-sober
subspace `U ⊆ Spec R` has `IrreducibleCloseds U ≃o Uᵒᵈ`, so `topologicalKrullDim U` is
`Order.krullDim U` computed in the poset of primes. Mathlib has this for `U` a zero locus
(`PrimeSpectrum.zeroLocusEquivIrreducibleCloseds`); the private lemmas
`subtypeEquivIrreducibleCloseds` and `topologicalKrullDim_eq_krullDim` are its verbatim
generalization to any quasi-sober subspace, which is what an open neighbourhood of `x` needs.

*Lemma 00ET is not used.* The source cites it for the minimal primes of `S_𝔪`; here the same step
is the order-theoretic observation that any chain of primes descending from `𝔪` extends to one
starting at a minimal prime, which is `Ideal.exists_minimalPrimes_le`. The formalized
correspondence (`PrimeSpectrum.irreducibleComponentsThroughEquiv`) is a bijection of sets, carrying
no dimension data, so it could not have been used for the inequality as stated.

## References

* [StacksProject 00OT](https://stacks.math.columbia.edu/tag/00OT)
-/



namespace Stacks.Spectrum.LocalDimension

open Order PrimeSpectrum TopologicalSpace

section Spectrum

variable {R : Type*} [CommRing R]

/-- The irreducible closed subsets of a quasi-sober subspace `U` of `Spec R`, ordered by
inclusion, are the points of `U` ordered by reverse inclusion of primes. This is
`PrimeSpectrum.zeroLocusEquivIrreducibleCloseds` with the zero locus replaced by any quasi-sober
subspace. -/
@[ega "0 16.1.1" "more general", sga "4 IV 4.2.2" "special case"]
public noncomputable def subtypeEquivIrreducibleCloseds (U : Set (PrimeSpectrum R))
    [QuasiSober U] : U ≃o (IrreducibleCloseds U)ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} := (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
    ((subtype_specializes_iff p q).trans (le_iff_specializes p.1 q.1).symm)

/-- The topological Krull dimension of a quasi-sober subspace of `Spec R` is the Krull dimension
of its poset of primes. -/
@[ega "IV 5.1.1" "more general"]
public lemma topologicalKrullDim_eq_krullDim (U : Set (PrimeSpectrum R)) [QuasiSober U] :
    topologicalKrullDim U = krullDim U := by
  rw [topologicalKrullDim, ← krullDim_orderDual (α := IrreducibleCloseds U)]
  exact (krullDim_eq_of_orderIso (subtypeEquivIrreducibleCloseds U)).symm

/-- The zero locus of a prime ideal is the set of primes containing it. -/
public lemma zeroLocus_asIdeal (q : PrimeSpectrum R) :
    zeroLocus (q.asIdeal : Set R) = Set.Ici q := by
  ext p
  simp [mem_zeroLocus, Set.mem_Ici, ← asIdeal_le_asIdeal, SetLike.coe_subset_coe]

/-- The dimension of the irreducible closed subset `V(𝔮)` is the coheight of `𝔮`. -/
@[ega "IV 5.1.1" "5.1.1.2 for prime ideals"]
public lemma topologicalKrullDim_zeroLocus (q : PrimeSpectrum R) :
    topologicalKrullDim (zeroLocus (q.asIdeal : Set R)) = (coheight q : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_krullDim, zeroLocus_asIdeal, ← coheight_eq_krullDim_Ici]

/-- An open subset of `Spec R` contains every generalization of each of its points. -/
public lemma mem_of_le_of_isOpen {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {p p' : PrimeSpectrum R} (h : p ≤ p') (h' : p' ∈ U) : p ∈ U :=
  ((le_iff_specializes p p').mp h).mem_open hU h'

/-- In a Jacobson ring, every open subset of `Spec R` containing a point `x` contains a closed
point of `Spec R` above `x`, because the locally closed set `V(x) ∩ U` is nonempty. -/
public lemma exists_isMaximal_mem [IsJacobsonRing R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {x : PrimeSpectrum R} (hx : x ∈ U) :
    ∃ m : PrimeSpectrum R, m.asIdeal.IsMaximal ∧ x ≤ m ∧ m ∈ U := by
  obtain ⟨m, ⟨hm₁, hm₂⟩, hm₃⟩ := nonempty_inter_closedPoints
    (Z := zeroLocus (x.asIdeal : Set R) ∩ U) ⟨x, by simp [zeroLocus_asIdeal], hx⟩
    ((isClosed_zeroLocus _).isLocallyClosed.inter hU.isLocallyClosed)
  exact ⟨m, (isClosed_singleton_iff_isMaximal m).mp hm₃,
    by simpa [zeroLocus_asIdeal] using hm₁, hm₂⟩

/-- A minimal prime ideal is the ideal of a minimal point of `Spec R`. -/
private lemma exists_isMin_asIdeal_eq {I : Ideal R} (hI : I ∈ minimalPrimes R) :
    ∃ q : PrimeSpectrum R, IsMin q ∧ q.asIdeal = I :=
  ⟨⟨I, hI.1.1⟩, isMin_iff.mpr hI, rfl⟩

/-- The source's number (2), the largest dimension of an irreducible component of `Spec R` through
`x`, is the largest coheight of a minimal prime below `x`. -/
public lemma iSup_irreducibleComponents_eq (x : PrimeSpectrum R) :
    (⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum R) | x ∈ Z}, topologicalKrullDim Z) =
      ⨆ q ∈ {q : PrimeSpectrum R | IsMin q ∧ q ≤ x}, (coheight q : WithBot ℕ∞) := by
  refine le_antisymm (iSup₂_le fun Z hZ => ?_) (iSup₂_le fun q hq => ?_)
  · obtain ⟨hZc, hxZ⟩ := hZ
    have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZc
    have hI : vanishingIdeal Z ∈ minimalPrimes R := by
      rwa [vanishingIdeal_mem_minimalPrimes, hZcl.closure_eq]
    obtain ⟨q, hmin, hq⟩ := exists_isMin_asIdeal_eq hI
    have hZq : Z = zeroLocus (q.asIdeal : Set R) := by
      rw [hq, zeroLocus_vanishingIdeal_eq_closure, hZcl.closure_eq]
    have hle : q ≤ x :=
      (asIdeal_le_asIdeal _ _).mp
        (SetLike.coe_subset_coe.mp ((mem_zeroLocus _ _).mp (hZq ▸ hxZ)))
    exact le_iSup₂_of_le q ⟨hmin, hle⟩ (by rw [hZq, topologicalKrullDim_zeroLocus])
  · obtain ⟨hmin, hle⟩ := hq
    have hZ : zeroLocus (q.asIdeal : Set R) ∈ irreducibleComponents (PrimeSpectrum R) := by
      rw [zeroLocus_ideal_mem_irreducibleComponents, q.isPrime.radical]
      exact isMin_iff.mp hmin
    have hmem : zeroLocus (q.asIdeal : Set R) ∈
        {Z ∈ irreducibleComponents (PrimeSpectrum R) | x ∈ Z} :=
      ⟨hZ, by rwa [zeroLocus_asIdeal]⟩
    exact (topologicalKrullDim_zeroLocus q).symm.trans_le
      (le_biSup (fun Z : Set (PrimeSpectrum R) => topologicalKrullDim Z) hmem)

/-- If every minimal prime below a point of `V` lies below `x`, then every chain of primes in `V`
is at most as long as the coheight of some minimal prime below `x`: pass to a minimal prime below
the head of the chain. -/
public lemma krullDim_le_iSup_coheight {x : PrimeSpectrum R} (V : Set (PrimeSpectrum R))
    (hV : ∀ p ∈ V, ∀ q : PrimeSpectrum R, IsMin q → q ≤ p → q ≤ x) :
    krullDim V ≤ ⨆ q ∈ {q : PrimeSpectrum R | IsMin q ∧ q ≤ x}, (coheight q : WithBot ℕ∞) := by
  refine iSup_le fun p => ?_
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥)
    (J := (p.head : PrimeSpectrum R).asIdeal) bot_le
  obtain ⟨q, hmin, rfl⟩ := exists_isMin_asIdeal_eq hQ
  have hqhead : q ≤ (p.head : PrimeSpectrum R) := (asIdeal_le_asIdeal _ _).mp hQle
  have hlen : (p.length : ℕ∞) ≤ coheight q :=
    length_le_coheight_head.trans
      ((coheight_le_coheight_apply_of_strictMono Subtype.val (fun _ _ h => h) p.head).trans
        (coheight_anti hqhead))
  exact le_iSup₂_of_le q ⟨hmin, hV _ p.head.2 q hmin hqhead⟩ (by exact_mod_cast hlen)

/-- The set of points of `Spec R` through which no irreducible component other than the ones
through `x` passes is open: its complement is the union of the finitely many other components. -/
public lemma isOpen_setOf_forall_isMin_le [IsNoetherianRing R] (x : PrimeSpectrum R) :
    IsOpen {p : PrimeSpectrum R | ∀ q : PrimeSpectrum R, IsMin q → q ≤ p → q ≤ x} := by
  have hfin : {q : PrimeSpectrum R | IsMin q ∧ ¬ q ≤ x}.Finite :=
    ((minimalPrimes.finite_of_isNoetherianRing R).preimage
      fun _ _ _ _ h => PrimeSpectrum.ext h).subset fun q hq => isMin_iff.mp hq.1
  have hset : {p : PrimeSpectrum R | ∀ q : PrimeSpectrum R, IsMin q → q ≤ p → q ≤ x} =
      (⋃ q ∈ {q : PrimeSpectrum R | IsMin q ∧ ¬ q ≤ x}, Set.Ici q)ᶜ := by
    ext p
    refine ⟨fun h hp => ?_, fun h q hmin hqp => ?_⟩
    · obtain ⟨q, hqB, hqp⟩ := Set.mem_iUnion₂.mp hp
      exact hqB.2 (h q hqB.1 hqp)
    · by_contra hnle
      exact h (Set.mem_iUnion₂.mpr ⟨q, ⟨hmin, hnle⟩, hqp⟩)
  rw [hset, isOpen_compl_iff]
  refine hfin.isClosed_biUnion fun q _ => ?_
  rw [← zeroLocus_asIdeal]
  exact isClosed_zeroLocus _

end Spectrum

section FiniteType

/-- **Stacks 00OS, read at `S/𝔮`.** For a prime `𝔮` below a maximal ideal `𝔪` of a finite type
`k`-algebra, `dim S/𝔮 = coheight 𝔮` is at most `height 𝔪`: the finite type domain `S/𝔮` has
`dim S/𝔮 = height (𝔪/𝔮)`, and a chain of primes of `S/𝔮` below `𝔪/𝔮` is one of `S` below `𝔪`. -/
public lemma coheight_le_height (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] {q m : PrimeSpectrum S} (hm : IsMax m) (hqm : q ≤ m) :
    coheight q ≤ height m := by
  have hz : zeroLocus (q.asIdeal : Set S) = Set.Ici q := zeroLocus_asIdeal q
  set e := Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (Ideal.Quotient.mk q.asIdeal)
    Ideal.Quotient.mk_surjective Ideal.mk_ker
  set m' : ↥(zeroLocus (q.asIdeal : Set S)) := ⟨m, by rwa [hz]⟩
  have hm'' : IsMax m' := fun b hb => Subtype.coe_le_coe.mp (hm (Subtype.coe_le_coe.mpr hb))
  have hmax : IsMax (e.symm m') := by
    intro b hb
    have h₁ : m' ≤ e b := by simpa using e.monotone hb
    simpa using e.symm.monotone (hm'' h₁)
  have : (e.symm m').asIdeal.IsMaximal := isMax_iff.mp hmax
  have h00OS := (Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim
    k (S ⧸ q.asIdeal)).1 (e.symm m').asIdeal
  have key : (coheight q : WithBot ℕ∞) = (height m' : WithBot ℕ∞) := by
    rw [coheight_eq_krullDim_Ici, ← hz, ← ringKrullDim_quotient, h00OS,
      PrimeSpectrum.height_eq_orderHeight, height_orderIso e.symm m']
  rw [show coheight q = height m' by exact_mod_cast key]
  exact height_le_height_apply_of_strictMono Subtype.val (fun _ _ h => h) m'

/-- The source's number (1), the dimension of `Spec S` at `x`, is the largest coheight of a
minimal prime below `x`. -/
public lemma localKrullDim_eq_iSup_coheight (k : Type u) [Field k] {S : Type v} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (x : PrimeSpectrum S) :
    localKrullDim (PrimeSpectrum S) x =
      ⨆ q ∈ {q : PrimeSpectrum S | IsMin q ∧ q ≤ x}, (coheight q : WithBot ℕ∞) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  refine le_antisymm ?_ ?_
  · refine iInf_le_of_le {p : PrimeSpectrum S | ∀ q : PrimeSpectrum S, IsMin q → q ≤ p → q ≤ x}
      (iInf_le_of_le (isOpen_setOf_forall_isMin_le x) (iInf_le_of_le (fun _ _ h => h) ?_))
    have := (isOpen_setOf_forall_isMin_le x).isOpenEmbedding_subtypeVal.quasiSober
    rw [topologicalKrullDim_eq_krullDim]
    exact krullDim_le_iSup_coheight _ fun _ hp => hp
  · refine le_iInf fun U => le_iInf fun hU => le_iInf fun hxU => iSup₂_le fun q hq => ?_
    obtain ⟨m, hmax, hxm, hmU⟩ := exists_isMaximal_mem hU hxU
    have := hU.isOpenEmbedding_subtypeVal.quasiSober
    rw [topologicalKrullDim_eq_krullDim]
    calc (coheight q : WithBot ℕ∞) ≤ (height m : WithBot ℕ∞) := by
          exact_mod_cast coheight_le_height k (isMax_iff.mpr hmax) (hq.2.trans hxm)
      _ = krullDim (Set.Iic m) := height_eq_krullDim_Iic m
      _ ≤ krullDim U := krullDim_le_of_strictMono
          (fun p => (⟨p.1, mem_of_le_of_isOpen hU p.2 hmU⟩ : U)) fun _ _ h => h

/-- The source's number (3), the smallest height of a maximal ideal above `x`, is the largest
coheight of a minimal prime below `x`. -/
public lemma iInf_height_eq_iSup_coheight (k : Type u) [Field k] {S : Type v} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (x : PrimeSpectrum S) :
    (⨅ 𝔪 ∈ {𝔪 : Ideal S | 𝔪.IsMaximal ∧ x.asIdeal ≤ 𝔪}, (𝔪.height : WithBot ℕ∞)) =
      ⨆ q ∈ {q : PrimeSpectrum S | IsMin q ∧ q ≤ x}, (coheight q : WithBot ℕ∞) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  refine le_antisymm ?_ (le_iInf₂ fun 𝔪 h𝔪 => ?_)
  · obtain ⟨m, hmax, hxm, hmU⟩ :=
      exists_isMaximal_mem (isOpen_setOf_forall_isMin_le x) (fun _ _ h => h)
    refine (iInf₂_le m.asIdeal ⟨hmax, (asIdeal_le_asIdeal _ _).mpr hxm⟩).trans ?_
    rw [PrimeSpectrum.height_eq_orderHeight, height_eq_krullDim_Iic]
    exact krullDim_le_iSup_coheight _ fun p hp q hq hqp => hmU q hq (hqp.trans hp)
  · have h𝔪p : 𝔪.IsPrime := h𝔪.1.isPrime
    refine iSup₂_le fun q hq => ?_
    have hxm : x ≤ (⟨𝔪, h𝔪p⟩ : PrimeSpectrum S) := (asIdeal_le_asIdeal _ _).mp h𝔪.2
    rw [PrimeSpectrum.height_eq_orderHeight (⟨𝔪, h𝔪p⟩ : PrimeSpectrum S)]
    exact_mod_cast coheight_le_height k (isMax_iff.mpr h𝔪.1) (hq.2.trans hxm)

end FiniteType

/-- The statement of Stacks 00OT: for `S` of finite type over a field `k` and `x ∈ Spec S`, the
dimension of `Spec S` at `x` is both the largest dimension of an irreducible component through `x`
and the smallest height of a maximal ideal containing `x`. Both are identified with the largest
coheight of a minimal prime below `x`. -/
public theorem solution
    (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) :
    (TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
        ⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | x ∈ Z}, topologicalKrullDim Z) ∧
      (TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
        ⨅ 𝔪 ∈ {𝔪 : Ideal S | 𝔪.IsMaximal ∧ x.asIdeal ≤ 𝔪}, (𝔪.height : WithBot ℕ∞)) :=
  ⟨(localKrullDim_eq_iSup_coheight k x).trans (iSup_irreducibleComponents_eq x).symm,
    (localKrullDim_eq_iSup_coheight k x).trans (iInf_height_eq_iSup_coheight k x).symm⟩

end Stacks.Spectrum.LocalDimension

/-!
# Local dimension of an affine finite type scheme over a field: three descriptions

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `X = Spec S`, and let `x ∈ X`
be the point given by a prime ideal `𝔭 ⊆ S`. Three numbers attached to `x` agree:

1. the dimension `dim_x X` of `X` at `x`, the least dimension of an open neighbourhood of `x`;
2. the largest dimension of an irreducible component of `X` through `x`;
3. the smallest of the dimensions `dim S_𝔪` over the maximal ideals `𝔪 ⊇ 𝔭`.

Both extrema can be strictly smaller than `dim X`: on the union of a plane and a line meeting it,
all three numbers are `1` at the generic point of the line, while `dim X = 2`.

The source's proof: `X` has finitely many irreducible components, so removing those that miss `x`
leaves an open `U ∋ x` whose components are exactly the `Z ∩ U` for the components `Z` through
`x`; each is a nonempty open subset of `Z` containing a closed point, because `S` is Jacobson, and
so has the full dimension of `Z` by Lemma 00OS — this gives (1) = (2). For a maximal ideal
`𝔪 ⊇ 𝔭` the minimal primes of `S_𝔪` are the `𝔮_i S_𝔪` for the minimal primes `𝔮_i ⊆ 𝔪`
(Lemma 00ET), whence `dim S_𝔪` is the largest dimension of a component through the point of `𝔪`,
again by Lemma 00OS; choosing `𝔪` inside `V(𝔭)` minus the other components — possible since `S`
is Jacobson and `𝔭` itself lies there — realizes (2) as one such `dim S_𝔪`, and no `𝔪` gives less.

## Main results

* `PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height`: the three
  numbers agree.

## Implementation notes

*`dim_x X` is `TopologicalSpace.localKrullDim`.* That definition is Topology Definition 0055 (4) —
the infimum of `topologicalKrullDim U` over the open neighbourhoods `U` of `x` — and
`topologicalKrullDim` is the source's dimension of a space, the supremum of lengths of chains of
irreducible closed subsets. The point `x` and its prime ideal are one datum, `x : PrimeSpectrum S`
with `𝔭 = x.asIdeal`, rather than a prime together with the assertion that `x` corresponds to it;
Stacks 00P1 is stated the same way.

*`dim S_𝔪` is `𝔪.height`.* The Krull dimension of any model of the local ring of `S` at `𝔪` is
`𝔪.height`, by `IsLocalization.AtPrime.ringKrullDim_eq_height`, so the model-independent
`Ideal.height` says the source's `dim(S_𝔪)` with no localization data in the statement, as in
Stacks 00OS and 00P1. Reading the third number at a given `A` with `[IsLocalization.AtPrime A 𝔪]`
is that one rewrite.

*The components are Mathlib's `irreducibleComponents`, and their dimension is again
`topologicalKrullDim`.* "Passing through `x`" is `x ∈ Z`, so the family of the source's second
number is the set `{Z ∈ irreducibleComponents (PrimeSpectrum S) | x ∈ Z}`. Stating (2) inside the
topology of `X`, rather than as `⨆ 𝔮 ∈ minimalPrimes S, 𝔮 ≤ 𝔭 → ringKrullDim (S ⧸ 𝔮)`, keeps the
statement about the space the source's `dim_x` is about; the translation is the inclusion-reversing
order isomorphism `PrimeSpectrum.pointsEquivIrreducibleCloseds` together with
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.

*The source's `max` and `min` are `iSup` and `iInf` in `WithBot ℕ∞`.* This is no weakening: `X` is
a Noetherian space so it has finitely many components, at least one through `x`, and the maximal
ideals containing `𝔭` are nonempty, `WithBot ℕ∞` is a complete linear order, and a nonempty
finite family and a nonempty family of naturals both attain their extremum. The values live in
`WithBot ℕ∞ ≃ {-∞} ∪ ℤ≥0 ∪ {+∞}` because that is where `topologicalKrullDim` lives; the heights,
which are `ℕ∞`, are coerced.

Faithfulness to [StacksProject 00OT].

1. No hypothesis is dead. `Field k` cannot be relaxed to a commutative ring: for `k = S = ℤ_p`,
   a finite type `k`-algebra, at the generic point `x = ⊥` of the two-point space `Spec ℤ_p`, the
   open set `{⊥}` makes the first number `0` while the only component is all of `Spec ℤ_p` and the
   second number is `1`. `Algebra.FiniteType k S` cannot be dropped: for the non-finite-type
   `k`-algebra `S = k[t]_{(t)}` the same computation at `x = ⊥` gives `0 ≠ 1`. The point `x`
   occurs in all three numbers.
2. The base and the ring are the source's: `k` is a field, `S` is a `k`-algebra of finite type,
   and the topology, the components and the heights are all those of `S` itself — no base change,
   no polynomial ring presenting `S`, and no localization appearing as data.
3. The quantities the source names are pinned, not asserted to exist: the neighbourhoods are the
   open sets of `PrimeSpectrum S` containing `x`, the components are `irreducibleComponents`, the
   third family is indexed by the maximal ideals above `x.asIdeal`, and the conclusion is a pair
   of equations determining `dim_x X`, not bounds on it.
4. The instantiation is not degenerate: for `S = k[X, Y]` and `x = (X)` all three numbers are `2`;
   for `S = k[X, Y, Z] ⧸ (XY, XZ)` — the plane `X = 0` meeting the line `Y = Z = 0` — at the
   generic point `x = (Y, Z)` of the line all three are `1`, strictly less than `dim S = 2`, and
   there the infimum over `𝔪` is essential: the origin `(X, Y, Z)` contributes height `2`. At the
   point of `S = k` all three are `0`.

## References

* [StacksProject 00OT](https://stacks.math.columbia.edu/tag/00OT)

## Tags

dimension, local dimension, Krull dimension, height, irreducible component, finite type algebra,
Jacobson
-/

@[expose] public section



namespace PrimeSpectrum

/-- **Stacks 00OT.** Let `k` be a field, let `S` be a finite type `k`-algebra, let `X = Spec S`,
and let `x ∈ X` be a point, with prime ideal `𝔭 = x.asIdeal`. Then the dimension of `X` at `x` is
both the largest dimension of an irreducible component of `X` through `x` and the smallest of the
dimensions `dim S_𝔪 = height 𝔪` over the maximal ideals `𝔪 ⊇ 𝔭`. -/
@[stacks 00OT "`dim_x X` is `TopologicalSpace.localKrullDim`, Topology Definition 0055 (4);
`dim(S_𝔪)` is `𝔪.height`; the components are `irreducibleComponents` and their dimension is
`topologicalKrullDim`, and the source's `max`/`min` are `iSup`/`iInf` in `WithBot ℕ∞`. See the
module docstring."]
public theorem localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height
    (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) :
    (TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
        ⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | x ∈ Z}, topologicalKrullDim Z) ∧
      (TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
        ⨅ 𝔪 ∈ {𝔪 : Ideal S | 𝔪.IsMaximal ∧ x.asIdeal ≤ 𝔪}, (𝔪.height : WithBot ℕ∞)) :=
  Stacks.Spectrum.LocalDimension.solution k x

end PrimeSpectrum

end

/-!
# Local dimension of an affine finite type scheme over a field

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `X = Spec S`, and let `x ∈ X` be
the point given by a prime ideal `𝔭 ⊆ S`. This file proves Stacks 00P1:
`dim_x X = dim S_𝔭 + trdeg_k κ(𝔭)`, that is, the local dimension of `X` at `x` is the height of
`𝔭` plus the transcendence degree over `k` of the residue field at `𝔭`.

Write `r = trdeg_k κ(𝔭)`, which is `dim S ⧸ 𝔭` by Lemma 00P0. Both inequalities read the local
dimension off Lemma 00OT, which describes `dim_x X` both as the largest dimension of an
irreducible component of `X` through `x` and as the smallest of the heights of the maximal ideals
containing `𝔭`, and each is then one statement about a pair of primes `𝔮 ⊆ 𝔭`:

* `≤`: the components through `x` are the `V(𝔮)` for `𝔮` a minimal prime contained in `𝔭`, and
  `dim V(𝔮) = dim S ⧸ 𝔮 ≤ height 𝔭 + r`;
* `≥`: for a maximal ideal `𝔪 ⊇ 𝔭` one has `height 𝔭 + r ≤ height 𝔪`.

Both rest on the dimension formula `dim T = height 𝔮 + dim T ⧸ 𝔮` for a finite type domain `T`
over `k`, which is the source's own argument and the only place a chain of primes is required to
be *maximal*: a chain of primes below `𝔮` of maximal length has all its steps covering pairs and
starts at a minimal prime, and likewise for a chain from `𝔮` to a maximal ideal, so their
concatenation is a maximal chain, whose length is `dim T` by Lemma 00OS. The same concatenation,
over a Noetherian ring and without maximality, gives `height 𝔮 + height 𝔭/𝔮 ≤ height 𝔭`.

For `≤` the formula applied to `T = S ⧸ 𝔮` reads
`dim S ⧸ 𝔮 = height 𝔭/𝔮 + dim (S ⧸ 𝔮) ⧸ (𝔭/𝔮) = height 𝔭/𝔮 + r`, and `height 𝔭/𝔮 ≤ height 𝔭`.
For `≥` Lemma 00OS applied to `S ⧸ 𝔭` gives `height 𝔪/𝔭 = dim S ⧸ 𝔭 = r`, and heights add.

## Main results

* `Stacks.Spectrum.LocalDimensionFormula.solution`: the statement of Stacks 00P1,
  `PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField`.

## Implementation notes

A chain of primes with all steps covering pairs is a `RelSeries` for the relation `⋖` on
`PrimeSpectrum`, as in the statement of Lemma 00OS. That a prime of height `n < ∞` is the last
term of such a chain whose head is minimal is `exists_covBy_relSeries`, proved for an arbitrary
partial order by induction on `n` from `Order.height_eq_coe_add_one_iff`: an element of maximal
height below the top of the chain is automatically covered by it, which is
`covBy_of_height_le`.

Chains are moved across a quotient by `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`, the order
isomorphism `Spec (R ⧸ I) ≃o V(I)`, read in `Spec R` as contraction along `R → R ⧸ I`. Because
`V(I)` is upward closed, a covering pair inside it is a covering pair of `Spec R`: a prime lying
strictly between two primes containing `I` contains `I` too. This is what lets a chain from `𝔭/𝔮`
down to the zero ideal of `S ⧸ 𝔮` be read as a chain from `𝔭` down to `𝔮` in `S`.

## References

* [StacksProject 00P1](https://stacks.math.columbia.edu/tag/00P1)
-/

namespace Stacks.Spectrum.LocalDimensionFormula



open PrimeSpectrum

/-! ### Chains of covering pairs realizing a height -/

section Order

variable {α : Type*}

/-- If `y < x` and no element strictly below `x` has height exceeding the (finite) height of `y`,
then `x` covers `y`: an element between them would have height `height y + 1`. -/
public lemma covBy_of_height_le [Preorder α] {x y : α} (hyx : y < x)
    (hy : Order.height y ≠ ⊤) (hle : ∀ z < x, Order.height z ≤ Order.height y) : y ⋖ x :=
  ⟨hyx, fun z hyz hzx =>
    absurd ((ENat.add_one_le_iff hy).mp ((Order.height_add_one_le hyz).trans (hle z hzx)))
      (lt_irrefl _)⟩

/-- In a partial order, an element of finite height `n` is the last term of a chain of covering
pairs of length `n` whose head is a minimal element: a chain below `a` of maximal length cannot be
refined, so each of its steps is a covering pair, and its head is minimal. -/
public lemma exists_covBy_relSeries [PartialOrder α] (n : ℕ) (a : α) (ha : Order.height a = n) :
    ∃ s : RelSeries {p : α × α | p.1 ⋖ p.2}, IsMin s.head ∧ s.last = a ∧ s.length = n := by
  induction n generalizing a with
  | zero =>
      exact ⟨RelSeries.singleton _ a, Order.height_eq_zero.mp (by simpa using ha), rfl, rfl⟩
  | succ n ih =>
      obtain ⟨-, ⟨y, hy, hyh⟩, hle⟩ :=
        Order.height_eq_coe_add_one_iff.mp (by exact_mod_cast ha)
      obtain ⟨s, hmin, hlast, hlen⟩ := ih y hyh
      have hcov : y ⋖ a :=
        covBy_of_height_le hy (by simp [hyh]) fun z hz => (hle z hz).trans_eq hyh.symm
      exact ⟨s.snoc a (by simpa [hlast] using hcov), by simpa using hmin, by simp, by simp [hlen]⟩

/-- A covering pair of an upward closed subset of a preorder is a covering pair of the preorder:
an element lying strictly between the two already belongs to the subset. -/
public lemma covBy_coe_of_isUpperSet [Preorder α] {s : Set α} (hs : IsUpperSet s) {a b : s}
    (h : a ⋖ b) : (a : α) ⋖ (b : α) :=
  ⟨h.lt, fun z hz₁ hz₂ => h.2 (c := ⟨z, hs hz₁.le a.2⟩) hz₁ hz₂⟩

end Order

/-! ### Primes of a quotient ring -/

section Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- A closed subset of `Spec R` is upward closed for the inclusion of prime ideals. -/
public lemma isUpperSet_zeroLocus (s : Set R) : IsUpperSet (zeroLocus s) :=
  fun _ _ hab (ha : s ⊆ _) => ha.trans ((asIdeal_le_asIdeal _ _).mpr hab)

/-- `Spec (R ⧸ I) → Spec R` takes covering pairs to covering pairs: it is
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus` read in `Spec R`, and `V(I)` is upward closed. -/
public lemma covBy_comap_quotientMk {a b : PrimeSpectrum (R ⧸ I)} (h : a ⋖ b) :
    comap (Ideal.Quotient.mk I) a ⋖ comap (Ideal.Quotient.mk I) b :=
  covBy_coe_of_isUpperSet (isUpperSet_zeroLocus (I : Set R))
    ((apply_covBy_apply_iff I.primeSpectrumQuotientOrderIsoZeroLocus).mpr h)

/-- The dimension of the closed subscheme `V(I) ⊆ Spec R` is the dimension of `R ⧸ I`: the
contraction along `R → R ⧸ I` is a closed embedding with image `V(I)`. -/
public lemma topologicalKrullDim_zeroLocus :
    topologicalKrullDim ↥(zeroLocus (I : Set R)) = ringKrullDim (R ⧸ I) := by
  have hrange : Set.range (comap (Ideal.Quotient.mk I)) = zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  have e : PrimeSpectrum (R ⧸ I) ≃ₜ ↥(zeroLocus (I : Set R)) :=
    (isEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  rw [← topologicalKrullDim_eq_ringKrullDim, IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]

end Quotient

/-! ### Chains of primes through a given prime -/

section Chains

variable {R : Type*} [CommRing R]

/-- A prime ideal of finite height is the last term of a chain of covering pairs of primes of that
length whose head is a minimal prime. -/
public lemma exists_covBy_relSeries_last_eq (p : Ideal R) [p.IsPrime] [p.FiniteHeight] :
    ∃ s : RelSeries {q : PrimeSpectrum R × PrimeSpectrum R | q.1 ⋖ q.2},
      IsMin s.head ∧ s.last = ⟨p, inferInstance⟩ ∧ (s.length : ℕ∞) = p.height := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := p))
  obtain ⟨s, hmin, hlast, hlen⟩ :=
    exists_covBy_relSeries n (⟨p, inferInstance⟩ : PrimeSpectrum R)
      (by rw [← height_eq_orderHeight, ← hn])
  exact ⟨s, hmin, hlast, by rw [hlen, hn]⟩

variable [IsNoetherianRing R] (p q : Ideal R) [p.IsPrime] [q.IsPrime]

/-- For primes `p ≤ q` there is a chain of covering pairs of primes from a minimal prime to `q` of
length `height p + height q/p`: concatenate a chain below `p` of length `height p` with the
contraction of a chain below the image of `q` in `R ⧸ p`. -/
public lemma exists_covBy_relSeries_through (hpq : p ≤ q) :
    ∃ z : RelSeries {t : PrimeSpectrum R × PrimeSpectrum R | t.1 ⋖ t.2},
      IsMin z.head ∧ z.last = ⟨q, inferInstance⟩ ∧
        (z.length : ℕ∞) = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have : (q.map (Ideal.Quotient.mk p)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  obtain ⟨w, hwmin, hwlast, hwlen⟩ := exists_covBy_relSeries_last_eq p
  obtain ⟨u, humin, hulast, hulen⟩ := exists_covBy_relSeries_last_eq (q.map (Ideal.Quotient.mk p))
  let v : RelSeries {t : PrimeSpectrum R × PrimeSpectrum R | t.1 ⋖ t.2} :=
    { length := u.length
      toFun := fun i => comap (Ideal.Quotient.mk p) (u.toFun i)
      step := fun i => covBy_comap_quotientMk p (u.step i) }
  have hbot : u.head = ⟨⊥, inferInstance⟩ :=
    have h : (⟨⊥, inferInstance⟩ : PrimeSpectrum (R ⧸ p)) ≤ u.head :=
      (asIdeal_le_asIdeal _ _).mp bot_le
    le_antisymm (humin h) h
  have hvhead : v.head = ⟨p, inferInstance⟩ := by
    change comap (Ideal.Quotient.mk p) u.head = _
    rw [hbot]
    exact PrimeSpectrum.ext Ideal.mk_ker
  have hvlast : v.last = ⟨q, inferInstance⟩ := by
    change comap (Ideal.Quotient.mk p) u.last = _
    rw [hulast]
    exact PrimeSpectrum.ext (Ideal.comap_map_mk hpq)
  refine ⟨w.smash v (hwlast.trans hvhead.symm), by simpa using hwmin, by simpa using hvlast, ?_⟩
  change ((w.length + u.length : ℕ) : ℕ∞) = _
  rw [Nat.cast_add, hwlen, hulen]

/-- **Heights add along a quotient.** For primes `p ≤ q` of a Noetherian ring,
`height p + height q/p ≤ height q`: the chain of `exists_covBy_relSeries_through` has that length
and ends at `q`. -/
public lemma height_add_height_map_quotientMk_le (hpq : p ≤ q) :
    p.height + (q.map (Ideal.Quotient.mk p)).height ≤ q.height := by
  obtain ⟨z, -, hzlast, hzlen⟩ := exists_covBy_relSeries_through p q hpq
  calc p.height + (q.map (Ideal.Quotient.mk p)).height = (z.length : ℕ∞) := hzlen.symm
    _ ≤ z.last.asIdeal.height := by
        rw [height_eq_orderHeight]
        exact Order.length_le_height_last (p := z.ofLE fun _ hp => CovBy.lt hp)
    _ = q.height := by rw [hzlast]

end Chains

/-! ### The dimension formula -/

/-- For a finite type `k`-algebra `T`, a prime `q` and a maximal ideal `𝔪 ⊇ q`, the dimension of
`T ⧸ q` is the height of `𝔪/q`: Lemma 00OS applied to the finite type domain `T ⧸ q`. -/
public lemma ringKrullDim_quotient_eq_height_map_quotientMk (k : Type u) [Field k]
    {T : Type v} [CommRing T] [Algebra k T] [Algebra.FiniteType k T] (q 𝔪 : Ideal T) [q.IsPrime]
    (h𝔪 : 𝔪.IsMaximal) (hq𝔪 : q ≤ 𝔪) :
    ringKrullDim (T ⧸ q) = ((𝔪.map (Ideal.Quotient.mk q)).height : WithBot ℕ∞) :=
  have : (𝔪.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  (Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim k (T ⧸ q)).1 _

/-- **The dimension formula for a finite type domain over a field.** For `T` a finite type domain
over a field `k` and a prime `q` of `T`, `dim T = height q + dim T ⧸ q`. A chain of primes below
`q` of length `height q` and a chain from `q` to a maximal ideal `𝔪 ⊇ q` of length `height 𝔪/q`
concatenate to a maximal chain of primes of `T`, so its length is `dim T` by Lemma 00OS, while
`height 𝔪/q` is `dim T ⧸ q` by the same lemma applied to `T ⧸ q`. -/
@[ega "0 16.1.4" "special case"]
public lemma ringKrullDim_eq_height_add_ringKrullDim_quotient (k : Type u) [Field k]
    (T : Type v) [CommRing T] [IsDomain T] [Algebra k T] [Algebra.FiniteType k T]
    (q : Ideal T) [q.IsPrime] :
    ringKrullDim T = (q.height : WithBot ℕ∞) + ringKrullDim (T ⧸ q) := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing k T
  obtain ⟨𝔪, h𝔪, hq𝔪⟩ := q.exists_le_maximal (Ideal.IsPrime.ne_top ‹q.IsPrime›)
  have : 𝔪.IsPrime := h𝔪.isPrime
  obtain ⟨z, hzmin, hzlast, hzlen⟩ := exists_covBy_relSeries_through q 𝔪 hq𝔪
  rw [← (Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim k T).2 z
      hzmin (isMax_iff.mpr (by rwa [hzlast])),
    ringKrullDim_quotient_eq_height_map_quotientMk k q 𝔪 h𝔪 hq𝔪, ← WithBot.coe_add, ← hzlen]
  norm_cast

/-- **An exact codimension, as an equation between Krull dimensions.** For `T` a finite type
domain over a field `k` and `q` a prime of `T` of height `e`, one has
`dim T ⧸ q + e = dim T`. -/
public lemma ringKrullDim_quotient_add_eq_ringKrullDim (k : Type u) [Field k]
    (T : Type v) [CommRing T] [IsDomain T] [Algebra k T] [Algebra.FiniteType k T]
    (q : Ideal T) [q.IsPrime] {e : ℕ∞} (hq : q.height = e) :
    ringKrullDim (T ⧸ q) + (e : WithBot ℕ∞) = ringKrullDim T := by
  rw [ringKrullDim_eq_height_add_ringKrullDim_quotient k T q, hq, add_comm]

/-! ### The two inequalities of the formula -/

section Bounds

variable (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-- For a prime `p` of a finite type `k`-algebra, `dim S ⧸ p = trdeg_k κ(p)`: Lemma 00P0 applied
to the finite type domain `S ⧸ p`, whose field of fractions is the residue field at `p`. -/
public lemma ringKrullDim_quotient_eq_trdeg_residueField (p : Ideal S) [p.IsPrime] :
    ringKrullDim (S ⧸ p) = (Cardinal.toENat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) :=
  (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, v, v, 0} k (S ⧸ p)
    p.ResidueField).1

/-- For primes `q ≤ p` of a finite type `k`-algebra, `dim S ⧸ q ≤ height p + trdeg_k κ(p)`: the
dimension formula splits `dim S ⧸ q` as `height p/q + dim (S ⧸ q) ⧸ (p/q)`, whose second summand
is `dim S ⧸ p = trdeg_k κ(p)` and whose first is at most `height p`. -/
public lemma ringKrullDim_quotient_le_height_add_trdeg (q p : Ideal S) [q.IsPrime] [p.IsPrime]
    (hqp : q ≤ p) :
    ringKrullDim (S ⧸ q) ≤
      ((p.height + Cardinal.toENat (Algebra.trdeg k p.ResidueField) : ℕ∞) : WithBot ℕ∞) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : (p.map (Ideal.Quotient.mk q)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
  rw [ringKrullDim_eq_height_add_ringKrullDim_quotient k (S ⧸ q) (p.map (Ideal.Quotient.mk q)),
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hqp),
    ringKrullDim_quotient_eq_trdeg_residueField k p, ← WithBot.coe_add]
  exact WithBot.coe_le_coe.mpr
    (add_le_add (le_add_self.trans (height_add_height_map_quotientMk_le q p hqp)) le_rfl)

/-- For a prime `p` and a maximal ideal `𝔪 ⊇ p` of a finite type `k`-algebra,
`height p + trdeg_k κ(p) ≤ height 𝔪`: heights add along the quotient by `p`, and `height 𝔪/p` is
`dim S ⧸ p = trdeg_k κ(p)`. -/
public lemma height_add_trdeg_le_height (p 𝔪 : Ideal S) [p.IsPrime] (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : p ≤ 𝔪) :
    p.height + Cardinal.toENat (Algebra.trdeg k p.ResidueField) ≤ 𝔪.height := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : 𝔪.IsPrime := h𝔪.isPrime
  have hr : (𝔪.map (Ideal.Quotient.mk p)).height
      = Cardinal.toENat (Algebra.trdeg k p.ResidueField) := by
    exact_mod_cast ((ringKrullDim_quotient_eq_trdeg_residueField k p).symm.trans
      (ringKrullDim_quotient_eq_height_map_quotientMk k p 𝔪 h𝔪 hp𝔪)).symm
  rw [← hr]
  exact height_add_height_map_quotientMk_le p 𝔪 hp𝔪

end Bounds

/-! ### The local dimension formula -/

/-- The statement of Stacks 00P1: for `S` of finite type over a field `k` and `x ∈ Spec S`, the
dimension of `Spec S` at `x` is `height 𝔭 + trdeg_k κ(𝔭)`, where `𝔭 = x.asIdeal`. The upper bound
runs over the irreducible components through `x`, the lower bound over the maximal ideals
containing `𝔭`, via the two descriptions of Stacks 00OT. -/
public theorem solution
    (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) :
    TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
      ((x.asIdeal.height + Cardinal.toENat (Algebra.trdeg k x.asIdeal.ResidueField) : ℕ∞) :
        WithBot ℕ∞) := by
  obtain ⟨hOT1, hOT2⟩ := localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k x
  refine le_antisymm (hOT1.trans_le (iSup₂_le fun Z hZ => ?_))
    (hOT2.trans_ge (le_iInf₂ fun 𝔪 h𝔪 => ?_))
  · -- the components through `x` are the `V(𝔮)` for `𝔮` a minimal prime contained in `𝔭`
    obtain ⟨hZc, hxZ⟩ := hZ
    rw [← zeroLocus_minimalPrimes] at hZc
    obtain ⟨𝔮, h𝔮, rfl⟩ := hZc
    have : (𝔮 : Ideal S).IsPrime := h𝔮.1.1
    simp only [Function.comp_apply, mem_zeroLocus] at hxZ
    rw [Function.comp_apply, topologicalKrullDim_zeroLocus]
    exact ringKrullDim_quotient_le_height_add_trdeg k 𝔮 x.asIdeal (SetLike.coe_subset_coe.mp hxZ)
  · -- every maximal ideal containing `𝔭` has height at least `height 𝔭 + trdeg_k κ(𝔭)`
    exact WithBot.coe_le_coe.mpr (height_add_trdeg_le_height k x.asIdeal 𝔪 h𝔪.1 h𝔪.2)

end Stacks.Spectrum.LocalDimensionFormula

/-!
# Local dimension of an affine finite type scheme over a field

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `X = Spec S`, and let `x ∈ X` be
the point given by a prime ideal `𝔭 ⊆ S`. Then the dimension of `X` at `x` is
$$
  \dim_x X = \dim S_𝔭 + \operatorname{trdeg}_k κ(𝔭),
$$
the height of `𝔭` plus the transcendence degree over `k` of the residue field at `𝔭`. This
generalizes Lemma 00OU, the case of a closed point, where `κ(𝔭)` is algebraic over `k` and the
second summand vanishes.

The source's proof: `r = trdeg_k κ(𝔭)` is the dimension of `V(𝔭)` (Lemma 00P0), so `𝔭` sits at
the bottom of a maximal chain `𝔭 ⊊ 𝔭_1 ⊊ ⋯ ⊊ 𝔭_r` of primes of `S`, of length `r` by Lemma 00OS;
the minimal primes `𝔮_j` of `S` contained in `𝔭` correspond to the minimal primes of `S_𝔭`, so
`dim S_𝔭 = max_j s(j)` with `s(j)` the length of a maximal chain from `𝔮_j` to `𝔭`; concatenating
the two chains gives a maximal chain of `S ⧸ 𝔮_j` of length `r + s(j)`, and `dim_x X` is the
maximum of the `dim S ⧸ 𝔮_j` over the irreducible components through `x` (Lemma 00OT).

## Main results

* `PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField`: the dimension formula.

## Implementation notes

*`dim_x X` is `TopologicalSpace.localKrullDim`.* That definition is Definition 0055 (4) — the
infimum of `topologicalKrullDim U` over the open neighbourhoods `U` of `x` — with Mathlib's
`topologicalKrullDim` for the dimension of a space, the same notion as the source's (the supremum
of lengths of chains of irreducible closed subsets). The infimum stands for the source's minimum
with no loss: `WithBot ℕ∞` is well-founded for `<` and the family is nonempty (`U = Set.univ`), so
the infimum is attained. The point `x` and its prime ideal are one datum, `x : PrimeSpectrum S`
with `𝔭 = x.asIdeal`, rather than a prime together with the assertion that `x` corresponds to it.

*`dim S_𝔭` is `𝔭.height`.* The Krull dimension of any model of the local ring of `S` at `𝔭` is
`𝔭.height`, by `IsLocalization.AtPrime.ringKrullDim_eq_height`, so the model-independent
`Ideal.height` says the source's `dim(S_𝔭)` with no localization data in the statement;
Stacks 00NA and 00OS are stated the same way, and reading the summand at a given `A` with
`[IsLocalization.AtPrime A 𝔭]` is that one rewrite.

*`κ(𝔭)` is `Ideal.ResidueField`, and the degrees are compared through `Cardinal.toENat`.* As in
Stacks 06RP and 00P0, the residue field is Mathlib's `𝔭.ResidueField`, which carries
`IsFractionRing (S ⧸ 𝔭) 𝔭.ResidueField`, so it is the field of fractions of `S ⧸ 𝔭` that the
source writes, and its `k`-algebra structure is the one induced by `Algebra k S` rather than an
extra datum; a reader holding another model of `κ(𝔭)` transports along the canonical `k`-algebra
isomorphism, under which `Algebra.trdeg` is invariant. `Algebra.trdeg` is a `Cardinal` while
`Ideal.height` is an `ℕ∞`, so the sum is formed in `ℕ∞` after `Cardinal.toENat`; this loses
nothing, since `k ⊆ κ(𝔭)` is essentially of finite type and hence `trdeg_k κ(𝔭) < ℵ₀`
(`Algebra.trdeg_lt_aleph0`), and `Cardinal.toENat` is injective on the finite cardinals.

Faithfulness. (1) No hypothesis is dead: `Field k` is used — over the base `ℤ` with `S = ℤ`, at
the generic point `x = ⊥` of `Spec ℤ`, every nonempty open contains a closed point so the left
side is `1`, while `height ⊥ = 0` and `trdeg_ℤ ℚ = 0` make the right side `0`; and
`Algebra.FiniteType k S` is used — for `k = ℚ`, `S = ℝ`, at the unique point the left side is `0`
while `trdeg_ℚ ℝ = 2 ^ ℵ₀` sends the right side to `⊤`. The point `x` is used by both sides.
(2) The scalars and base are the source's: the transcendence degree is taken over `k` through the
given `Algebra k S`, and the height and the topology are those of `S` itself — no base change, no
localization of `k`, no polynomial ring presenting `S`. (3) The objects the source names are
pinned, not asserted to exist: `x.asIdeal.ResidueField` is the residue field at `x`, the structure
map from `S` having kernel exactly `x.asIdeal`, the open sets are those of `PrimeSpectrum S`
containing `x`, and the conclusion is an equation determining `dim_x X`, not a bound on it.
(4) The instantiation is not degenerate: for `S = k[X, Y]` and `x = (X)` the formula reads
`2 = 1 + 1`, the left side being `2` because every nonempty open of the plane has dimension `2`;
for the reducible `S = k[X, Y, Z] ⧸ (XY, XZ)` — the plane `X = 0` meeting the line `Y = Z = 0` —
it reads `1 = 0 + 1` at the generic point of the line, where the left side is *smaller* than
`dim S = 2`, which is what makes the statement one about a local quantity. At the point of
`S = k` it reads `0 = 0 + 0`.

## References

* [StacksProject 00P1](https://stacks.math.columbia.edu/tag/00P1)
-/

@[expose] public section



namespace PrimeSpectrum

/-- **Stacks 00P1.** Let `k` be a field, let `S` be a finite type `k`-algebra, let `X = Spec S`,
and let `x ∈ X` be a point, with prime ideal `𝔭 = x.asIdeal`. Then the dimension of `X` at `x` —
the least dimension of an open neighbourhood of `x` — is the height of `𝔭` plus the transcendence
degree over `k` of the residue field `κ(𝔭)`. -/
@[stacks 00P1 "`dim_x X` is `TopologicalSpace.localKrullDim`, Definition 0055 (4); `dim(S_𝔭)` is
`𝔭.height`, `κ(𝔭)` is `Ideal.ResidueField`, and the transcendence degree is compared through
`Cardinal.toENat`. See the module docstring.", ega "IV 17.15.8" "special case"]
public theorem localKrullDim_eq_height_add_trdeg_residueField
    (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) :
    TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
      ((x.asIdeal.height + Cardinal.toENat (Algebra.trdeg k x.asIdeal.ResidueField) : ℕ∞) :
        WithBot ℕ∞) :=
  Stacks.Spectrum.LocalDimensionFormula.solution k x

end PrimeSpectrum

end
