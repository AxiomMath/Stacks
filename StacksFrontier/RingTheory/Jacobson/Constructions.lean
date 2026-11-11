module

public import StacksCore.Tactic.StacksAttribute
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

@[expose] public section

/-! # Localization of a Jacobson ring at an element

Stacks 00G6 is Mathlib's: the localization of a Jacobson ring at the powers of an element is
Jacobson, and its maximal ideals are in order-preserving bijection with the maximal ideals of the
base ring that do not contain the element.
-/

add_to_stacks 00G6 "`R_f` is Jacobson; Mathlib states it for any `S` with \
`IsLocalization.Away f S`, so `S := Localization.Away f` gives the Stacks form."
  isJacobsonRing_localization

add_to_stacks 00G6 "the maximal ideals of `R_f` correspond to the maximal ideals of `R` not \
containing `f`; Mathlib packages the correspondence as an order isomorphism, whose forward map is \
contraction along `algebraMap R R_f`." IsLocalization.orderIsoOfMaximal

-- ===== merged from StacksDraft.Ch10.Sec35.Tag00G9 =====

section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The preimage of a maximal ideal of `R ⧸ I` under the quotient map is maximal in `R`
and contains `I`. -/
private lemma comap_maximal_aux (M : Ideal (R ⧸ I)) (hM : M.IsMaximal) :
    (Ideal.comap (Ideal.Quotient.mk I) M).IsMaximal ∧
      I ≤ Ideal.comap (Ideal.Quotient.mk I) M :=
  ⟨Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective,
    fun _ hx => by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx, M.zero_mem]⟩

/-- For any ideal `J` of `R` containing `I`, the comap of its image under
`Ideal.Quotient.mk I` recovers `J`. -/
private lemma comap_map_eq (J : Ideal R) (hIJ : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J := by
  simp [Ideal.comap_map_quotientMk, sup_of_le_right, hIJ]

/-- The image under `Ideal.Quotient.mk I` of a maximal ideal of `R` containing `I`
is maximal in `R ⧸ I`. -/
private lemma map_maximal_aux (J : Ideal R) (hJ : J.IsMaximal) (hIJ : I ≤ J) :
    (Ideal.map (Ideal.Quotient.mk I) J).IsMaximal :=
  (Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective hJ).resolve_left fun hTop =>
      hJ.ne_top (by rw [← comap_map_eq I J hIJ, hTop, Ideal.comap_top])

end

/-- Let `R` be a Jacobson ring and `I ⊆ R` an ideal. Then `R ⧸ I` is Jacobson, and
maximal ideals of `R ⧸ I` correspond (via `Ideal.comap (Ideal.Quotient.mk I)`) to
maximal ideals of `R` containing `I`. -/
@[stacks 00G9]
theorem jacobson_quotient
    {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R) :
    IsJacobsonRing (R ⧸ I) ∧
      ∃ e : {M : Ideal (R ⧸ I) // M.IsMaximal} ≃
            {J : Ideal R // J.IsMaximal ∧ I ≤ J},
        ∀ (M : {M : Ideal (R ⧸ I) // M.IsMaximal}),
          (e M).1 = Ideal.comap (Ideal.Quotient.mk I) M.1 :=
  ⟨inferInstance,
    { toFun := fun M => ⟨_, comap_maximal_aux I M.val M.property⟩
      invFun := fun J => ⟨_, map_maximal_aux I J.val J.property.left J.property.right⟩
      left_inv := fun M => Subtype.ext
        (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M.val)
      right_inv := fun J => Subtype.ext (comap_map_eq I J.val J.property.right) },
    fun _ => rfl⟩

-- ===== merged from StacksDraft.Ch10.Sec35.Tag00GA =====


/-!
# A prime with algebraic residue extension over a maximal ideal is maximal

Let `R → S` be a ring map, let `m ⊆ R` be a maximal ideal, and let `q ⊆ S` be a
prime ideal lying over `m` (so `m = q.comap f`).  If the residue field extension
`κ(q)/κ(m)` is algebraic, then `q` is a maximal ideal of `S`.

The residue fields are `Ideal.ResidueField`, and `κ(q)/κ(m)` is realised through
`Ideal.ResidueField.map`, the canonical embedding `κ(m) ↪ κ(q)` attached to
`m = q.comap f`.  The algebra structure on `κ(q)` over `κ(m)` is taken as an
instance argument pinned to that embedding via `hcompat`.

The proof transfers algebraicity down the square

```
R ⧸ m ──→ κ(m)
  │          │
  ▼          ▼
S ⧸ q ──→ κ(q)
```

to obtain that the domain `S ⧸ q` is algebraic, hence integral, over the field
`R ⧸ m`; a domain integral over a field is a field, so `q` is maximal.
-/


/-- Stacks tag 00GA: if `q ⊆ S` is a prime lying over a maximal ideal `m ⊆ R` and
the residue field extension `κ(q)/κ(m)` is algebraic, then `q` is maximal. -/
@[stacks 00GA]
theorem isMaximal_of_isAlgebraic_residueField
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {m : Ideal R} [m.IsMaximal] {q : Ideal S} [q.IsPrime]
    (hlies : m = q.comap f)
    [Algebra m.ResidueField q.ResidueField]
    (hcompat : (algebraMap m.ResidueField q.ResidueField) =
      Ideal.ResidueField.map m q f hlies)
    [Algebra.IsAlgebraic m.ResidueField q.ResidueField] :
    q.IsMaximal := by
  -- The induced map `R ⧸ m → S ⧸ q` makes `S ⧸ q` an algebra over the field `R ⧸ m`.
  let : Algebra (R ⧸ m) (S ⧸ q) := (Ideal.quotientMap q f hlies.le).toAlgebra
  -- Transfer algebraicity of `κ(q)/κ(m)` to `(S ⧸ q)/(R ⧸ m)` along the commuting square.
  have halg : Algebra.IsAlgebraic (R ⧸ m) (S ⧸ q) := by
    refine Algebra.IsAlgebraic.of_ringHom_of_comp_eq
      (f := algebraMap (R ⧸ m) m.ResidueField)
      (g := algebraMap (S ⧸ q) q.ResidueField)
      (m.bijective_algebraMap_quotient_residueField).surjective
      q.injective_algebraMap_quotient_residueField ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    rw [hcompat]
    change Ideal.ResidueField.map m q f hlies (algebraMap R m.ResidueField x)
      = algebraMap S q.ResidueField (f x)
    exact Ideal.ResidueField.map_algebraMap m q f hlies x
  -- A domain algebraic over a field is a field, hence `q` is maximal.
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  exact Ideal.Quotient.maximal_of_isField q
    (isField_of_isIntegral_of_isField' (Field.toIsField (R ⧸ m)))

-- ===== merged from StacksDraft.Ch10.Sec35.Tag00GD =====


/-!
# Closed points of the image of a constructible set under a ring-spectra map

For a finite-type map of Jacobson rings `φ : R →+* S` and a constructible
subset `E ⊆ Spec S`, Stacks tag 00GD asserts (in part) the equality
`f(E)₀ = X₀ ∩ f(E)`, where `f = Spec(φ) : Spec S → Spec R`, `X = Spec R`,
and the subscript `₀` denotes the set of closed points (in the subspace
topology for the left-hand side, in the ambient space for the right-hand
side).

This file records the *trivial inclusion* of that equality, namely
`X₀ ∩ f(E) ⊆ f(E)₀`, which the Stacks proof itself flags as immediate:
any point closed in the ambient space and lying in a subset is *a fortiori*
closed in the subset's subspace topology. The reverse inclusion, together
with the more substantial part (2) of the tag, requires the Jacobson-ring
hypothesis to push closed points of the source forward to closed points of
the target, and is not formalized here.

The auxiliary topological lemmas below are also provided independently:
* `subspaceClosedPoints` packages the "closed in the subspace topology" set
  into the ambient space.
* `closedPoints_inter_subset_subspaceClosedPoints` is the trivial inclusion
  in any topological space.
* `exists_closedPoint_of_isConstructible` shows that any nonempty
  constructible subset of a Jacobson space meets the ambient closed points.
-/

open PrimeSpectrum TopologicalSpace Topology


/-- For a subset `A` of a topological space `Z`, `subspaceClosedPoints A` is
the set of points of `Z` lying in `A` which are closed in `A` when `A` is
given the subspace topology.  Concretely, it is the image of `closedPoints A`
(where `A` is viewed as a topological subspace) under the inclusion `A ↪ Z`.

This is the meaning of the subscript "`₀`" applied to a subset in the Stacks
statement of Tag 00GD. -/
def subspaceClosedPoints {Z : Type*} [TopologicalSpace Z] (A : Set Z) : Set Z :=
  Subtype.val '' (closedPoints A)

/-- A point in `subspaceClosedPoints A` lies in `A`. -/
lemma subspaceClosedPoints_subset {Z : Type*} [TopologicalSpace Z] (A : Set Z) :
    subspaceClosedPoints A ⊆ A :=
  Subtype.coe_image_subset _ _

/-- Any ambient closed point of `Z` lying in `A` is closed in the subspace
topology on `A`.  No hypotheses on `A` or `Z` are required. -/
lemma closedPoints_inter_subset_subspaceClosedPoints {Z : Type*} [TopologicalSpace Z] (A : Set Z) :
    closedPoints Z ∩ A ⊆ subspaceClosedPoints A := fun x ⟨hxc, hxA⟩ =>
  ⟨⟨x, hxA⟩,
    preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val hxc, rfl⟩

/-- In a Jacobson space, every nonempty constructible subset contains an
ambient closed point. -/
@[ega "IV 10.3.1" "partial",
  ega "IV 10.4.10" "partial",
  ega "IV 8.1.3" "more general",
  sga "3 V 7.2" "partial"]
lemma exists_closedPoint_of_isConstructible
    {Z : Type*} [TopologicalSpace Z] [JacobsonSpace Z]
    {C : Set Z} (hC : IsConstructible C) (hne : C.Nonempty) :
    ∃ z ∈ C, z ∈ closedPoints Z := by
  have hSL : IsSublattice {U : Set Z | IsOpen U ∧ IsRetrocompact U} :=
    ⟨fun _ ha _ hb => ⟨ha.left.union hb.left, ha.right.union hb.right⟩,
     fun _ ha _ hb => ⟨ha.left.inter hb.left, ha.right.inter_isOpen hb.right hb.left⟩⟩
  have hbot : (⊥ : Set Z) ∈ {U : Set Z | IsOpen U ∧ IsRetrocompact U} :=
    ⟨isOpen_empty, IsRetrocompact.empty⟩
  have htop : (⊤ : Set Z) ∈ {U : Set Z | IsOpen U ∧ IsRetrocompact U} :=
    ⟨isOpen_univ, IsRetrocompact.univ⟩
  obtain ⟨t, ht⟩ := (BooleanSubalgebra.mem_closure_iff_sup_sdiff hSL hbot htop).mp hC
  obtain ⟨c, hc⟩ := hne
  rw [ht, Finset.sup_set_eq_biUnion] at hc
  simp only [Set.mem_iUnion] at hc
  obtain ⟨p, hpt, hcp⟩ := hc
  obtain ⟨⟨U, hU⟩, ⟨V, hV⟩⟩ := p
  set L : Set Z := U \ V with hLdef
  have hLne : L.Nonempty := ⟨c, hcp⟩
  have hLlc : IsLocallyClosed L :=
    ⟨U, Vᶜ, hU.left, hV.left.isClosed_compl, by rw [hLdef, Set.sdiff_eq]⟩
  obtain ⟨z, hzL, hzc⟩ := nonempty_inter_closedPoints hLne hLlc
  refine ⟨z, ?_, hzc⟩
  rw [ht, Finset.sup_set_eq_biUnion]
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hpt, hzL⟩⟩

/-- Let `φ : R →+* S` be any ring map and let `E ⊆ Spec S` be any subset; write
`f = Spec(φ) : Spec S → Spec R`.  Any closed point of `Spec R` lying in the
image `f(E)` is closed in the subspace topology on `f(E)`, i.e. `X₀ ∩ f(E) ⊆ f(E)₀`.

This is the inclusion the proof of Stacks 00GD calls trivial; the full statement of
00GD is `comap_image_subspaceClosedPoints_and_mem_comap_image_iff`. -/
theorem stacks00GD_closedPoints_inter_image_subset_subspaceClosedPoints
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (E : Set (PrimeSpectrum S)) :
    closedPoints (PrimeSpectrum R) ∩ (PrimeSpectrum.comap φ '' E)
      ⊆ subspaceClosedPoints (PrimeSpectrum.comap φ '' E) :=
  closedPoints_inter_subset_subspaceClosedPoints _

-- ===== merged from StacksDraft.Ch10.Sec35.Tag034J =====

/-!
# Characterizing Jacobson rings by the sets `V(p) ∩ D(f)`

Let `R` be a commutative ring and let `Spec(R)` be its prime spectrum, the set of
prime ideals with the Zariski topology. This file proves the two halves of Stacks
Lemma 10.35.5 (tag 034J), "characterize-jacobson".

1. (Non-Jacobson direction.) If `R` is not Jacobson, then there exist a prime
   ideal `p` and an element `f ∈ R` such that (1a) `p` is not maximal;
   (1b) `f ∉ p`; (1c) `V(p) ∩ D(f) = {p}`; and (1d) `(R/p)_f` is a field.
2. (Jacobson direction.) If `R` is Jacobson, then for every prime `p` that is not
   maximal and every `f ∉ p`, the set `V(p) ∩ D(f)` is infinite.

Here `V(I) = { q ∈ Spec(R) : I ⊆ q }` is the zero locus of an ideal `I`, so for a
prime `p` the set `V(p)` consists of the primes containing `p`; `D(f) =
{ q ∈ Spec(R) : f ∉ q }` is the basic open where `f` does not vanish; and
`(R/p)_f` is the localization of `R/p` away from the image `f̄` of `f`. When
`f ∉ p` we have `f̄ ≠ 0` in the domain `R/p`, so `(R/p)_f` is a subring of the
fraction field of `R/p`.

## Main results

* `exists_prime_vCapD_singleton_isField_of_not_isJacobsonRing`: part (1), assembled from
  `not_jacobson_exists_vCapD_singleton` for (1a)–(1c) and
  `isField_localization_of_vCapD_singleton` for (1d).
* `vCapD_infinite_of_isJacobsonRing`: part (2), assembled from
  `isMaximal_of_jacobson_vCapD_singleton` and
  `exists_mul_vCapD_singleton_of_finite`.

## Implementation notes

All the notions involved — `PrimeSpectrum.zeroLocus`, `PrimeSpectrum.basicOpen`,
`Ideal.IsMaximal`, `IsJacobsonRing`, `Localization.Away`, `IsField` and
`Set.Infinite` — are already in Mathlib, so no new mathematical definition is
introduced. The only addition is the abbreviation `vCapD p f` for `V(p) ∩ D(f)`,
which keeps the statements readable. That `R` is Jacobson exactly when `Spec(R)`
is a Jacobson topological space is Stacks 00G3, available in Mathlib as
`PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace`.
-/

@[expose] public section

open PrimeSpectrum

/-- `V(p) ∩ D(f)` as a subset of `Spec(R)`: the set of primes `q` containing `p`
with `f ∉ q`. -/
def vCapD {R : Type*} [CommRing R] (p : PrimeSpectrum R) (f : R) :
    Set (PrimeSpectrum R) :=
  zeroLocus (p.asIdeal : Set R) ∩ (basicOpen f : Set (PrimeSpectrum R))

/- ===========================================================================
   The non-Jacobson direction (Stacks 034J part 1)

   `R` is not Jacobson exactly when `Spec R` is not a Jacobson topological space.
   By `jacobsonSpace_iff_locallyClosed`, the negation supplies a nonempty locally
   closed subset `Z ⊆ Spec R` containing no closed point of `Spec R`, that is
   `Z ∩ closedPoints (Spec R) = ∅`; closed points are exactly the maximal ideals.

   A locally closed set is `Z = C ∩ U` with `C = V(I)` closed and `U` open.
   Choosing a point `q ∈ Z` and a basic open `D(g) ⊆ U` containing `q` produces a
   nonempty `W := V(I) ∩ D(g) ⊆ Z`, which therefore also contains no closed point
   of `Spec R`.  Now `W` is the image of `Spec((R/I)_g)`, which is affine and so
   has a maximal ideal; the image of that ideal is a point `p ∈ W` closed *in the
   subspace* `W`.  Closedness in `W = V(I) ∩ D(g)`, together with `I ⊆ p`, means
   `V(p) ∩ W = {p}`, that is `V(p) ∩ D(g) = {p}`.  Since `p ∈ W ⊆ Z` and `Z` has
   no closed point of `Spec R`, the prime `p` is not maximal, and `g ∉ p` because
   `p ∈ D(g)`.  This is `(p, f := g)` with parts (1a), (1b), (1c); part (1d), that
   `(R/p)_g` is a field, then follows from (1c).
   =========================================================================== -/

/-- For an ideal `I` and `g : R`, the image of `Spec((R⧸I)_ḡ) → Spec(R)` is
`V(I) ∩ D(g)`. -/
theorem range_comap_quotient_localization_away {R : Type*} [CommRing R] (I : Ideal R) (g : R) :
    Set.range (comap ((algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I g))).comp
      (Ideal.Quotient.mk I))) = zeroLocus (I : Set R) ∩ ↑(basicOpen g) := by
  rw [comap_comp, Set.range_comp,
    localization_away_comap_range (Localization.Away (Ideal.Quotient.mk I g))
      (Ideal.Quotient.mk I g)]
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, mem_basicOpen, Set.mem_inter_iff, mem_zeroLocus]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun a ha => ?_, ?_⟩
    · simpa only [SetLike.mem_coe, comap_asIdeal, Ideal.mem_comap,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha] using y.asIdeal.zero_mem
    · simpa only [comap_asIdeal, Ideal.mem_comap] using hy
  · rintro ⟨hIx, hgx⟩
    obtain ⟨y, rfl⟩ : x ∈ Set.range (comap (Ideal.Quotient.mk I)) := by
      rwa [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, mem_zeroLocus,
        Ideal.mk_ker]
    exact ⟨y, by simpa only [comap_asIdeal, Ideal.mem_comap] using hgx, rfl⟩

/-- A nonempty `V(I) ∩ D(g)` contains a point `p` with `V(p) ∩ D(g) = {p}`: the image of a
closed point of `Spec((R⧸I)_ḡ)`. -/
theorem exists_vCapD_singleton_of_mem {R : Type*} [CommRing R] {I : Ideal R} {g : R}
    {q : PrimeSpectrum R} (hq : q ∈ zeroLocus (I : Set R) ∩ ↑(basicOpen g)) :
    ∃ p ∈ zeroLocus (I : Set R) ∩ ↑(basicOpen g), vCapD p g = {p} := by
  have hW := range_comap_quotient_localization_away I g
  set A := Localization.Away (Ideal.Quotient.mk I g)
  rw [← hW] at hq
  obtain ⟨y, -⟩ := hq
  have := y.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have hpW := hW ▸ Set.mem_range_self (f := comap _) (⟨m, hm.isPrime⟩ : PrimeSpectrum A)
  refine ⟨_, hpW, Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨by rw [mem_zeroLocus], hpW.2⟩, ?_⟩⟩
  rintro r ⟨hrz, hrg⟩
  have hrW : r ∈ zeroLocus (I : Set R) ∩ ↑(basicOpen g) :=
    ⟨Set.Subset.trans hpW.1 hrz, hrg⟩
  rw [← hW] at hrW
  obtain ⟨S, rfl⟩ := hrW
  have hle : Ideal.comap (Ideal.Quotient.mk I) (Ideal.comap (algebraMap (R ⧸ I) A) m) ≤
      Ideal.comap (Ideal.Quotient.mk I) (Ideal.comap (algebraMap (R ⧸ I) A) S.asIdeal) := hrz
  rw [Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hle
  have hmS : m ≤ S.asIdeal := by
    rw [← IsLocalization.map_under (Submonoid.powers (Ideal.Quotient.mk I g)) A m,
      ← IsLocalization.map_under (Submonoid.powers (Ideal.Quotient.mk I g)) A S.asIdeal]
    exact Ideal.map_mono hle
  rw [show (⟨m, hm.isPrime⟩ : PrimeSpectrum A) = S from
    PrimeSpectrum.ext (hm.eq_of_le S.isPrime.ne_top hmS)]

/-- Parts (1a)–(1c) of Stacks 034J.  If `R` is not a Jacobson ring, there is a
prime `p`, not maximal, and an `f ∉ p` with `V(p) ∩ D(f) = {p}`.

Failure of `IsJacobsonRing R` gives, through
`isJacobsonRing_iff_jacobsonSpace` and `jacobsonSpace_iff_locallyClosed`, a
nonempty locally closed `Z` with `Z ∩ closedPoints (PrimeSpectrum R) = ∅`. Write
`Z = U ∩ C` with `U` open and `C = zeroLocus I` closed, using
`isClosed_iff_zeroLocus`. Take `q ∈ Z`; the basic opens form a basis
(`isTopologicalBasis_basic_opens`), so there is `g` with `q ∈ basicOpen g ⊆ U`.
Set `W := zeroLocus I ∩ basicOpen g`, so `q ∈ W` and `W ⊆ C ∩ U = Z`, whence `W`
too misses `closedPoints`.

`W` is the range of `comap (algebraMap R ((R⧸I)_g))`: the composite
`R → R⧸I → (R⧸I)_g` has spectrum-image `zeroLocus I ∩ basicOpen g`, by
`range_comap_of_surjective` for the quotient factor and
`localization_away_comap_range` for the localization factor. The ring `(R⧸I)_g`
is nonzero, its spectrum `W` being nonempty, so it has a maximal ideal `m`; the
corresponding point `p` is a closed point of the affine `Spec((R⧸I)_g)`, and its
image is closed in the subspace `W` because `localization_comap_isEmbedding` and
`localization_away_isOpenEmbedding` realize `W` as that spectrum.

That `{p}` is closed in `W` says `closure {p} ∩ W = {p}`. Since
`closure {p} = zeroLocus p.asIdeal = V(p)` and `I ⊆ p.asIdeal` (as
`p ∈ zeroLocus I`), we get `V(p) ⊆ zeroLocus I` and hence
`V(p) ∩ W = V(p) ∩ basicOpen g`, so `vCapD p g = {p}`. Also `g ∉ p.asIdeal`
because `p ∈ basicOpen g`, and `p` is not maximal because `p ∈ W` and `W`
contains no closed point of `Spec R`, using
`isClosed_singleton_iff_isMaximal`. Take `f := g`. -/
theorem not_jacobson_exists_vCapD_singleton {R : Type*} [CommRing R]
    (hR : ¬ IsJacobsonRing R) :
    ∃ (p : PrimeSpectrum R) (f : R),
      (¬ p.asIdeal.IsMaximal) ∧ (f ∉ p.asIdeal) ∧ (vCapD p f = {p}) := by
  rw [isJacobsonRing_iff_jacobsonSpace, jacobsonSpace_iff_locallyClosed] at hR
  push Not at hR
  obtain ⟨Z, ⟨q, hqZ⟩, ⟨U, C, hU, hC, rfl⟩, hZcp⟩ := hR
  obtain ⟨hqU, hqC⟩ := hqZ
  obtain ⟨s, rfl⟩ := isClosed_iff_zeroLocus _ |>.mp hC
  obtain ⟨_, ⟨g, rfl⟩, hqV, hVU⟩ :=
    (isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hqU hU
  rw [← zeroLocus_span] at hqC hZcp
  obtain ⟨p, hpW, hp⟩ := exists_vCapD_singleton_of_mem (I := Ideal.span s) ⟨hqC, hqV⟩
  refine ⟨p, g, fun hmax => ?_, hpW.2, hp⟩
  refine (Set.eq_empty_iff_forall_notMem.mp hZcp p) ⟨⟨hVU hpW.2, hpW.1⟩, ?_⟩
  rwa [mem_closedPoints_iff, isClosed_singleton_iff_isMaximal]

/-- Part (1d) of Stacks 034J.  If `f ∉ p` and `V(p) ∩ D(f) = {p}`, then `(R/p)_f`
is a field.

`A := (R⧸p)_f` is a domain: `R⧸p` is a domain (`p` prime) and
`f̄ ≠ 0` (since `f ∉ p`), so the localization away from `f̄` embeds in the
fraction field (`IsLocalization.isDomain_of_le_nonZeroDivisors` with
`powers_le_nonZeroDivisors_of_noZeroDivisors`).  A domain is a field as soon as
it has Krull dimension `≤ 0` (`Ring.KrullDimLE.isField_of_isDomain`).  And
`Ring.KrullDimLE 0 A` holds because `Spec A` is a single point: the composite
`R → R⧸p → A` realizes `Spec A` as `V(p) ∩ D(f)` (via
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus` identifying `Spec(R⧸p)` with
`V(p)`, and `localization_away_comap_range`/`localization_comap_isEmbedding`
cutting down to `D(f)`); the hypothesis `vCapD p f = {p}` says that set is a
singleton, so `Spec A` is a subsingleton, whence every prime of `A` is maximal
and `KrullDimLE 0 A`.  (Equivalently: `(0)` is the unique prime of `A`, i.e. it
is the maximal ideal, so `A` is a field directly.) -/
theorem isField_localization_of_vCapD_singleton {R : Type*} [CommRing R]
    (p : PrimeSpectrum R) (f : R) (hf : f ∉ p.asIdeal) (hV : vCapD p f = {p}) :
    IsField (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) := by
  have : p.asIdeal.IsPrime := p.isPrime
  have : IsDomain (R ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
  have hfne : (Ideal.Quotient.mk p.asIdeal f) ≠ 0 := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hf
  have : IsDomain (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hfne)
  have : Ring.KrullDimLE 0 (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) := by
    set A := Localization.Away (Ideal.Quotient.mk p.asIdeal f)
    set φ : R →+* A := (algebraMap (R ⧸ p.asIdeal) A).comp (Ideal.Quotient.mk p.asIdeal)
    have hinj : Function.Injective (comap φ) := by
      rw [comap_comp]
      exact (comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).comp
        (localization_comap_injective A (Submonoid.powers (Ideal.Quotient.mk p.asIdeal f)))
    have hrange : Set.range (comap φ) = vCapD p f :=
      range_comap_quotient_localization_away p.asIdeal f
    have hss : Subsingleton (PrimeSpectrum A) := by
      have hP : ∀ P : PrimeSpectrum A, comap φ P = p := fun P => by
        have : comap φ P ∈ vCapD p f := hrange ▸ Set.mem_range_self P
        rwa [hV] at this
      exact ⟨fun P Q => hinj ((hP P).trans (hP Q).symm)⟩
    exact Order.instKrullDimLEOfNatNatOfSubsingleton
  exact Ring.KrullDimLE.isField_of_isDomain

/-- (Non-Jacobson direction, Stacks 034J (1).) If `R` is not a Jacobson ring, then
there exist a prime ideal `p` and an element `f` such that `p` is not maximal,
`f ∉ p`, `V(p) ∩ D(f) = {p}`, and `(R/p)_f` is a field. -/
@[stacks 034J "(1)", ega "IV 10.4.5" "b) => a)"]
theorem exists_prime_vCapD_singleton_isField_of_not_isJacobsonRing {R : Type*} [CommRing R]
    (hR : ¬ IsJacobsonRing R) :
    ∃ (p : PrimeSpectrum R) (f : R),
      (¬ p.asIdeal.IsMaximal) ∧
      (f ∉ p.asIdeal) ∧
      (vCapD p f = {p}) ∧
      IsField (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) := by
  obtain ⟨p, f, hpmax, hf, hV⟩ := not_jacobson_exists_vCapD_singleton hR
  exact ⟨p, f, hpmax, hf, hV, isField_localization_of_vCapD_singleton p f hf hV⟩

/- ===========================================================================
   The Jacobson direction (Stacks 034J part 2), second paragraph of the
   Stacks proof of Lemma 10.35.5.

   Suppose `R` is Jacobson, `p` is not maximal and `f ∉ p`, but for contradiction
   `V(p) ∩ D(f)` is FINITE.  It contains `p` (as `f ∉ p`), say it equals
   `{p, q₁, …, q_t}` with each `q_i ≠ p`.  Each `q_i ∈ V(p)` so `p ⊆ q_i`, and
   `q_i ≠ p`, hence `q_i ⊋ p`, i.e. `q_i ⊄ p`.  By prime avoidance
   (`Ideal.IsPrime.prod_le`) the product `∏_i q_i ⊄ p`, so we may pick
   `g ∈ ∏_i q_i ⊆ ⋂_i q_i` with `g ∉ p`.  Then `g ∈ q_i` for all `i`.

   Now `V(p) ∩ D(fg) = {p}`: any `r ∈ V(p) ∩ D(fg)` has `p ⊆ r`, `fg ∉ r`, so
   `f ∉ r` and `g ∉ r`, giving `r ∈ V(p) ∩ D(f) = {p, q₁, …, q_t}`; but `g ∈ q_i`
   excludes `r = q_i`, so `r = p`.  Conversely `p ∈ V(p) ∩ D(fg)` since `fg ∉ p`
   (`p` prime, `f ∉ p`, `g ∉ p`).  Thus `vCapD p (f*g) = {p}`.

   By `isMaximal_of_jacobson_vCapD_singleton` (which only needs `R` Jacobson and
   the singleton equation), `p` is maximal — contradicting `hp`.  Hence the set
   is infinite.

   The two steps are:
   * `isMaximal_of_jacobson_vCapD_singleton` — the Jacobson-space closed-point
     step;
   * `exists_mul_vCapD_singleton_of_finite` — the prime-avoidance construction
     of `g` cutting the finite set down to `{p}`.
   =========================================================================== -/

/-- Jacobson-space step: if `R` is Jacobson and `V(p) ∩ D(f) = {p}` (with `f ∉ p`,
so the set is nonempty), then `p` is maximal.  A nonempty locally closed set in a
Jacobson space contains a closed point of `Spec R`; here the only point is `p`,
and closed points of `Spec R` are exactly the maximal ideals
(`isClosed_singleton_iff_isMaximal`). -/
theorem isMaximal_of_jacobson_vCapD_singleton {R : Type*} [CommRing R]
    (hR : IsJacobsonRing R) (p : PrimeSpectrum R) (f : R)
    (hf : f ∉ p.asIdeal) (hV : vCapD p f = {p}) : p.asIdeal.IsMaximal := by
  have hlc : IsLocallyClosed (vCapD p f) := by
    unfold vCapD
    exact (isClosed_zeroLocus _).isLocallyClosed.inter (basicOpen f).isOpen.isLocallyClosed
  have hne : (vCapD p f).Nonempty := ⟨p, by simp [vCapD, mem_zeroLocus, hf]⟩
  have hcp := jacobsonSpace_iff_locallyClosed.mp (isJacobsonRing_iff_jacobsonSpace.mp hR)
    (vCapD p f) hne hlc
  rw [hV] at hcp
  obtain ⟨_, rfl, hq⟩ := hcp
  rwa [mem_closedPoints_iff, isClosed_singleton_iff_isMaximal] at hq

/-- Prime-avoidance construction.  If `f ∉ p` and `V(p) ∩ D(f)` is finite, there is
`g ∉ p` with `V(p) ∩ D(f*g) = {p}`.

Let `S := (vCapD p f) \ {p}`, a finite set of primes (each `q ∈ S`
satisfies `p ⊆ q.asIdeal` since `q ∈ zeroLocus p`, and `q ≠ p`, hence
`q.asIdeal ⊄ p.asIdeal`).  By prime avoidance for the prime `p.asIdeal`
(`Ideal.IsPrime.prod_le`: `∏_{q∈S} q.asIdeal ≤ p ↔ ∃ q ∈ S, q.asIdeal ≤ p`), since
no `q.asIdeal ≤ p.asIdeal`, the product `∏_{q∈S} q.asIdeal` is not `≤ p.asIdeal`;
pick `g` in that product (hence `g ∈ q.asIdeal` for every `q ∈ S`, as the product is
contained in each factor) with `g ∉ p.asIdeal`.  Then `f*g ∉ p.asIdeal` (`p` prime).
For the singleton equation: `p ∈ vCapD p (f*g)` because `f*g ∉ p`; and any
`r ∈ vCapD p (f*g)` has `p ⊆ r` and `f*g ∉ r`, so `f ∉ r` and `g ∉ r`, whence
`r ∈ vCapD p f`; if `r ≠ p` then `r ∈ S`, forcing `g ∈ r.asIdeal`, contradicting
`g ∉ r`; therefore `r = p`.  Hence `vCapD p (f*g) = {p}`. -/
theorem exists_mul_vCapD_singleton_of_finite {R : Type*} [CommRing R]
    (p : PrimeSpectrum R) (f : R) (hf : f ∉ p.asIdeal) (hfin : (vCapD p f).Finite) :
    ∃ g : R, g ∉ p.asIdeal ∧ vCapD p (f * g) = {p} := by
  have hmem : ∀ q : PrimeSpectrum R, ∀ h : R,
      q ∈ vCapD p h ↔ p.asIdeal ≤ q.asIdeal ∧ h ∉ q.asIdeal := by
    intro q h
    simp only [vCapD, Set.mem_inter_iff, mem_zeroLocus]
    rfl
  have hSfin : (vCapD p f \ {p}).Finite := hfin.sdiff
  set S := hSfin.toFinset with hSdef
  have hSmem : ∀ q : PrimeSpectrum R, q ∈ S ↔ q ∈ vCapD p f ∧ q ≠ p := by
    intro q
    rw [hSdef, Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff]
  have hnotle : ∀ q ∈ S, ¬ (q.asIdeal ≤ p.asIdeal) := by
    intro q hq hle
    obtain ⟨hqv, hqne⟩ := (hSmem q).1 hq
    obtain ⟨hpq, -⟩ := (hmem q f).1 hqv
    exact hqne (PrimeSpectrum.ext (le_antisymm hpq hle).symm)
  have hprodnotle : ¬ ((∏ q ∈ S, q.asIdeal) ≤ p.asIdeal) := by
    rw [p.isPrime.prod_le]
    rintro ⟨q, hq, hle⟩
    exact hnotle q hq hle
  obtain ⟨g, hgprod, hgnp⟩ := IsConcreteLE.not_le_iff_exists.mp hprodnotle
  refine ⟨g, hgnp, ?_⟩
  have hginq : ∀ q ∈ S, g ∈ q.asIdeal := fun q hq =>
    (Ideal.prod_le_inf.trans (Finset.inf_le (f := fun i => i.asIdeal) hq)) hgprod
  have hfgp : f * g ∉ p.asIdeal := p.isPrime.mul_notMem hf hgnp
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨(hmem p _).2 ⟨le_rfl, hfgp⟩, fun r hr => ?_⟩
  obtain ⟨hpr, hfgr⟩ := (hmem r _).1 hr
  by_contra hrne
  have hrS : r ∈ S := by
    rw [hSmem, hmem]
    exact ⟨⟨hpr, fun h => hfgr (r.asIdeal.mul_mem_right g h)⟩, hrne⟩
  exact hfgr (r.asIdeal.mul_mem_left f (hginq r hrS))

/-- (Jacobson direction, Stacks 034J (2).) If `R` is a Jacobson ring, then for every
prime ideal `p` that is not maximal and every element `f ∉ p`, the set
`V(p) ∩ D(f)` is infinite. -/
@[stacks 034J "(2)", ega "IV 10.4.5" "a) => b)"]
theorem vCapD_infinite_of_isJacobsonRing {R : Type*} [CommRing R]
    (hR : IsJacobsonRing R) (p : PrimeSpectrum R) (f : R)
    (hp : ¬ p.asIdeal.IsMaximal) (hf : f ∉ p.asIdeal) :
    (vCapD p f).Infinite := by
  -- By contradiction: if finite, prime avoidance gives `g ∉ p` with
  -- `V(p) ∩ D(f*g) = {p}`; then `isMaximal_of_jacobson_vCapD_singleton` makes `p`
  -- maximal, contradicting `hp`.
  intro hfin
  obtain ⟨g, hg, hsingle⟩ := exists_mul_vCapD_singleton_of_finite p f hf hfin
  exact hp (isMaximal_of_jacobson_vCapD_singleton hR p (f * g)
    (p.isPrime.mul_notMem hf hg) hsingle)
