module

public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.NodalAwayFromAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.AttachingPointStalk
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.AttachingPointNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDeltaBranchesDescent
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.MinimalPrimeComponents

/-!
# The closure of the complement of a rational tail is smooth at the attaching point

Let `k` be a field, let `X` be a proper one-dimensional nodal curve over `k` with only constant
global functions, let `C ⊆ X` be a rational tail and let `X'` be the scheme-theoretic closure of
the complement of `C`. At the attaching point `x₀` the curve `X` has a node, so its local ring
`A = 𝒪_{X, x₀}` is reduced with delta invariant one and exactly two minimal primes. This file
identifies the second of those minimal primes as the stalk of the ideal sheaf cutting out `X'`,
deduces that `𝒪_{X', y}` is a discrete valuation ring, and concludes that `X'` is smooth over
`k` at `y`.

## Main results

* `Stacks.Curves.exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal`: a point
  of the closure of the complement lies on an irreducible component not contained in the
  subscheme removed, and the ideal sheaf of the closure is below that component's vanishing
  ideal.
* `Stacks.Curves.stalk_mem_minimalPrimes_of_isRationalTail`: the stalk of a rational tail at its
  attaching point is a minimal prime of the local ring there.
* `Stacks.Curves.encard_minimalPrimes_stalk_attachingPoint_eq_two`: that local ring has exactly
  two minimal primes.
* `Stacks.Curves.stalk_complementaryCurveIdeal_mem_minimalPrimes`: the stalk of the ideal sheaf
  cutting out the closure of the complement is the other one.
* `Stacks.Curves.ringKrullDim_stalk_complementaryCurve_eq_one`: the local ring of the closure at
  the attaching point is one-dimensional.
* `Stacks.Curves.isRegularLocalRing_stalk_complementaryCurve`: it is a regular local ring.
* `Stacks.Curves.smoothAt_complementaryCurve_attachingPoint`: so the closure is smooth over `k`
  at the attaching point.
* `Stacks.Curves.nodal_complementaryCurve`: the at-worst-nodal clause of Tag 0E3H for the
  closure of the complement of a rational tail.

## Implementation notes

The smooth disjunct of `Stacks.Curves.HasAtWorstNodalSingularities` is what holds at the
attaching point: the node of `X` is replaced there by a single branch of itself, and that branch
is smooth. The identification of the branch is ring-theoretic rather than geometric — the local
ring of the closure is the quotient of the local ring of `X` by one of its two minimal primes,
and `Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one` makes such a
quotient a discrete valuation ring. So the stalk-level fibre-product route of Tag 0C4J is not
needed, and neither is clause (2)(c) of Tag 0E38.

Identifying the stalk of the complementary ideal sheaf as a minimal prime needs the count of
minimal primes to be *exactly* two, not merely at least two: with three of them the
ring-theoretic step
`AlgebraicGeometry.eq_of_le_of_sup_eq_maximalIdeal_of_minimalPrimes_eq_pair` is false, as the
counterexample in its docstring shows.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-! ### The second irreducible component through the attaching point -/

/-- **A point of the closure of the complement of a closed subscheme of a nodal curve lies on an
irreducible component not contained in that subscheme, and the ideal sheaf of the closure is
below the vanishing ideal of that component.** The closure of the complement is the reduced union
of the irreducible components not contained in the subscheme
(`AlgebraicGeometry.complementaryCurveIdeal_eq_union_irreducibleComponents`), so a point of it
lies on one of them, and the vanishing ideal of a single component dominates the vanishing ideal
of the union. -/
theorem exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hnodal : HasAtWorstNodalSingularities k X) (I : X.IdealSheafData) {x : X}
    (hx : x ∈ ((complementaryCurveIdeal I).support : Set X)) :
    ∃ D : Closeds X, (D : Set X) ∈ irreducibleComponents X ∧
      ¬ (D : Set X) ⊆ (I.support : Set X) ∧ x ∈ (D : Set X) ∧
        complementaryCurveIdeal I ≤ Scheme.IdealSheafData.vanishingIdeal D := by
  classical
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let Zcomps := {C : Set X // C ∈ irreducibleComponents X ∧ ¬ C ⊆ (I.support : Set X)}
  have hZcomp : complementaryCurveIdeal I = Scheme.IdealSheafData.vanishingIdeal
      (⨆ C : Zcomps, Closeds.closure C.1) :=
    complementaryCurveIdeal_eq_union_irreducibleComponents hnodal I
  have hcomponents : LocallyFinite (fun C : irreducibleComponents X => (C : Set X)) := by
    simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
  have hZcomps_closed : IsClosed (⋃ C : Zcomps, (C.1 : Set X)) :=
    (locallyFinite_component_subfamily hcomponents _).isClosed_iUnion fun C =>
      isClosed_of_mem_irreducibleComponents C.1 C.2.1
  have hZsup : (↑(⨆ C : Zcomps, Closeds.closure C.1) : Set X) = ⋃ C : Zcomps, (C.1 : Set X) :=
    coe_iSup_closure_eq_iUnion_of_isClosed (fun C : Zcomps => C.1)
      (fun C => isClosed_of_mem_irreducibleComponents C.1 C.2.1) hZcomps_closed
  have hxV : x ∈ ((Scheme.IdealSheafData.vanishingIdeal
      (⨆ C : Zcomps, Closeds.closure C.1)).support : Set X) := by rw [← hZcomp]; exact hx
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hZsup] at hxV
  obtain ⟨D, hxD⟩ := Set.mem_iUnion.mp hxV
  have hDclosed : IsClosed (D.1 : Set X) := isClosed_of_mem_irreducibleComponents D.1 D.2.1
  refine ⟨Closeds.closure D.1, ?_, ?_, ?_, ?_⟩
  · rw [show (↑(Closeds.closure D.1) : Set X) = D.1 from hDclosed.closure_eq]; exact D.2.1
  · rw [show (↑(Closeds.closure D.1) : Set X) = D.1 from hDclosed.closure_eq]; exact D.2.2
  · rw [show (↑(Closeds.closure D.1) : Set X) = D.1 from hDclosed.closure_eq]; exact hxD
  · rw [hZcomp]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono
      (le_iSup (fun C : Zcomps => Closeds.closure C.1) D)

/-! ### The stalk of a rational tail is a minimal prime at the attaching point -/

/-- **The stalk of a rational tail at its attaching point is a minimal prime of the local ring
there.** A rational tail is integral, hence reduced, so it is the reduced closed subscheme on its
support; that support is an irreducible component through the attaching point, and the stalk at a
point of the vanishing ideal of an irreducible component through it is a minimal prime. -/
theorem stalk_mem_minimalPrimes_of_isRationalTail
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    IdealSheafData.stalk C (C.subschemeι hC.attachingPoint) ∈
      minimalPrimes (X.presheaf.stalk (C.subschemeι hC.attachingPoint)) := by
  have : IsIntegral C.subscheme := hC.isIntegral
  have hmem : (C.support : Set X) ∈ irreducibleComponents X := hC.support_mem_irreducibleComponents
  have hx : C.subschemeι hC.attachingPoint ∈ (C.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨hC.attachingPoint, rfl⟩
  have hCeq : C = Scheme.IdealSheafData.vanishingIdeal C.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme C C.support rfl
  have hstalk : IdealSheafData.stalk C (C.subschemeι hC.attachingPoint) =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          ⟨(C.support : Set X), isClosed_of_mem_irreducibleComponents _ hmem⟩)
        (C.subschemeι hC.attachingPoint) :=
    congrArg (fun I : X.IdealSheafData =>
      IdealSheafData.stalk I (C.subschemeι hC.attachingPoint)) hCeq
  rw [hstalk]
  exact stalk_vanishingIdeal_mem_minimalPrimes _ ⟨(C.support : Set X), hmem⟩ hx

/-! ### A minimal prime of a local ring with several of them is not the maximal ideal -/

/-- **In a local ring with more than one minimal prime no minimal prime is the maximal ideal.**
Were a minimal prime equal to the maximal ideal, every other prime would lie below it, so by
minimality there would be only one. -/
theorem ne_maximalIdeal_of_mem_minimalPrimes_of_one_lt_encard
    {A : Type u} [CommRing A] [IsLocalRing A] {J : Ideal A}
    (hJ : J ∈ minimalPrimes A) (h : 1 < Set.encard (minimalPrimes A)) :
    J ≠ IsLocalRing.maximalIdeal A := by
  intro hJm
  obtain ⟨r, hr, s, hs, hrs⟩ := Set.one_lt_encard_iff_nontrivial.mp h
  obtain ⟨t, ht, htJ⟩ : ∃ t ∈ minimalPrimes A, t ≠ J := by
    rcases eq_or_ne r J with rfl | hrJ
    · exact ⟨s, hs, fun h' => hrs h'.symm⟩
    · exact ⟨r, hr, hrJ⟩
  have htle : t ≤ J := hJm ▸ IsLocalRing.le_maximalIdeal ht.1.1.ne_top
  exact htJ (le_antisymm htle (hJ.2 ⟨ht.1.1, bot_le⟩ htle))

/-! ### Exactly two minimal primes at the attaching point -/

/-- **The local ring of a nodal curve at the attaching point of a rational tail has exactly two
minimal primes.** The attaching point is a node (`Stacks.Curves.isNode_attachingPoint`), so the
curve has two geometric branches there, and it lies both on the rational tail — an irreducible
component — and on a second irreducible component, namely one of those making up the closure of
the complement. -/
theorem encard_minimalPrimes_stalk_attachingPoint_eq_two
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    Set.encard (minimalPrimes
        (X.presheaf.stalk (C.subschemeι hC.attachingPoint))) = 2 := by
  obtain ⟨-, -, hbr⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim (C.subschemeι hC.attachingPoint) (isNode_attachingPoint k X hdim hnodal C hC)
  obtain ⟨y, hy⟩ := exists_base_eq_attachingPoint hC
  have hx₀compl : C.subschemeι hC.attachingPoint ∈
      ((complementaryCurveIdeal C).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, hy⟩
  obtain ⟨D, hD, hDC, hxD, -⟩ :=
    exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal hnodal C hx₀compl
  have hxZ : C.subschemeι hC.attachingPoint ∈ (C.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨hC.attachingPoint, rfl⟩
  exact encard_minimalPrimes_stalk_eq_two X _ hC.support_mem_irreducibleComponents hD
    (fun h => hDC (h ▸ subset_rfl)) hxZ hxD hbr

/-! ### The stalk of the closure of the complement is the second minimal prime -/

/-- **Stacks 0E3H, step (iii): the stalk at the attaching point of the ideal sheaf cutting out the
closure of the complement of a rational tail is a minimal prime of the local ring there.** The
local ring `A` at the attaching point has exactly two minimal primes
(`Stacks.Curves.encard_minimalPrimes_stalk_attachingPoint_eq_two`); one of them, `p`, is the
stalk of the rational tail itself, and the stalk `J` of the complementary ideal sheaf lies below
the other, `q`, because the closure of the complement is contained in a single irreducible
component through the attaching point. Since `p ⊔ J` is the maximal ideal and `A` is reduced,
`J = q`. -/
theorem stalk_complementaryCurveIdeal_mem_minimalPrimes
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    IdealSheafData.stalk (complementaryCurveIdeal C) (C.subschemeι hC.attachingPoint) ∈
      minimalPrimes (X.presheaf.stalk (C.subschemeι hC.attachingPoint)) := by
  obtain ⟨hred, -, hbr⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim (C.subschemeι hC.attachingPoint) (isNode_attachingPoint k X hdim hnodal C hC)
  have : _root_.IsReduced (X.presheaf.stalk (C.subschemeι hC.attachingPoint)) := hred
  obtain ⟨y, hy⟩ := exists_base_eq_attachingPoint hC
  have hx₀compl : C.subschemeι hC.attachingPoint ∈
      ((complementaryCurveIdeal C).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, hy⟩
  obtain ⟨D, hD, -, hxD, hle⟩ :=
    exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal hnodal C hx₀compl
  -- the two minimal primes: the tail, and the component carrying the complement
  have hp := stalk_mem_minimalPrimes_of_isRationalTail hC
  have hq : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal D)
      (C.subschemeι hC.attachingPoint) ∈
      minimalPrimes (X.presheaf.stalk (C.subschemeι hC.attachingPoint)) :=
    stalk_vanishingIdeal_mem_minimalPrimes _ ⟨(D : Set X), hD⟩ hxD
  have htwo := encard_minimalPrimes_stalk_attachingPoint_eq_two k X hdim hnodal C hC
  have hJq : IdealSheafData.stalk (complementaryCurveIdeal C)
        (C.subschemeι hC.attachingPoint) ≤
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal D)
        (C.subschemeι hC.attachingPoint) :=
    IdealSheafData.stalk_mono hle _
  have hsup := stalk_sup_stalk_complementaryCurveIdeal_eq_maximalIdeal hC
  have honelt : 1 < Set.encard (minimalPrimes
      (X.presheaf.stalk (C.subschemeι hC.attachingPoint))) := by
    rw [htwo]; decide
  -- the tail's stalk is not the maximal ideal, so the two minimal primes found are distinct
  have hpm := ne_maximalIdeal_of_mem_minimalPrimes_of_one_lt_encard hp honelt
  have hpq : IdealSheafData.stalk C (C.subschemeι hC.attachingPoint) ≠
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal D)
        (C.subschemeι hC.attachingPoint) := by
    intro h
    exact hpm (by rw [← hsup, sup_eq_left.mpr (h ▸ hJq)])
  -- so they exhaust the minimal primes
  obtain ⟨a, b, hab, hset⟩ := Set.encard_eq_two.mp htwo
  have hpair : minimalPrimes (X.presheaf.stalk (C.subschemeι hC.attachingPoint)) =
      {IdealSheafData.stalk C (C.subschemeι hC.attachingPoint),
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal D)
          (C.subschemeι hC.attachingPoint)} := by
    have hpab := by rw [hset] at hp; simpa using hp
    have hqab := by rw [hset] at hq; simpa using hq
    rcases hpab with hpa | hpb
    · rcases hqab with hqa | hqb
      · exact absurd (hpa.trans hqa.symm) hpq
      · rw [hset, hpa, hqb]
    · rcases hqab with hqa | hqb
      · rw [hset, hpb, hqa]; exact Set.pair_comm a b
      · exact absurd (hpb.trans hqb.symm) hpq
  rw [eq_of_le_of_sup_eq_maximalIdeal_of_minimalPrimes_eq_pair hpair hJq hsup]
  exact hq

/-! ### The local ring of the closure of the complement at the attaching point -/

/-- The stalk of the complementary ideal sheaf is a minimal prime at any point of the closure of
the complement lying over the attaching point. This is
`Stacks.Curves.stalk_complementaryCurveIdeal_mem_minimalPrimes` transported along the equality of
points. -/
theorem stalk_complementaryCurveIdeal_base_mem_minimalPrimes
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint) :
    IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y) ∈
      minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y)) := by
  rw [hy]
  exact stalk_complementaryCurveIdeal_mem_minimalPrimes k X hdim hnodal C hC

/-- The stalk of the complementary ideal sheaf at a point over the attaching point is not the
maximal ideal: it is one of two distinct minimal primes. -/
theorem stalk_complementaryCurveIdeal_base_ne_maximalIdeal
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint) :
    IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y) ≠
      IsLocalRing.maximalIdeal (X.presheaf.stalk ((complementaryCurveι C).base y)) := by
  refine ne_maximalIdeal_of_mem_minimalPrimes_of_one_lt_encard
    (stalk_complementaryCurveIdeal_base_mem_minimalPrimes k X hdim hnodal C hC y hy) ?_
  rw [show Set.encard (minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y))) = 2 by
    rw [hy]; exact encard_minimalPrimes_stalk_attachingPoint_eq_two k X hdim hnodal C hC]
  decide

/-- **Stacks 0E3H, step (iv): the local ring of the closure of the complement of a rational tail
at the attaching point is one-dimensional.** The closure is one-dimensional
(`Stacks.Curves.topologicalKrullDim_complementaryCurve`), which bounds the dimension of the local
ring above; and the local ring is the quotient of the ambient local ring by a minimal prime which
is not the maximal ideal, so it is a local domain which is not a field. -/
theorem ringKrullDim_stalk_complementaryCurve_eq_one
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint) :
    ringKrullDim ((complementaryCurve C).presheaf.stalk y) = 1 := by
  have hJmin := stalk_complementaryCurveIdeal_base_mem_minimalPrimes k X hdim hnodal C hC y hy
  have hJne := stalk_complementaryCurveIdeal_base_ne_maximalIdeal k X hdim hnodal C hC y hy
  have : (IdealSheafData.stalk (complementaryCurveIdeal C)
      ((complementaryCurveι C).base y)).IsPrime := hJmin.1.1
  have : IsDomain (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) :=
    Ideal.Quotient.isDomain _
  obtain ⟨e⟩ := nonempty_ringEquiv_stalk_complementaryCurve C y
  rw [ker_stalkMap_complementaryCurveι C y] at e
  -- the quotient is not a field, since the minimal prime is not the maximal ideal
  have hone : 1 ≤ ringKrullDim (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) := by
    have hnk : ¬ Ring.KrullDimLE 0 (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
        IdealSheafData.stalk (complementaryCurveIdeal C)
          ((complementaryCurveι C).base y)) := fun _ =>
      hJne (IsLocalRing.eq_maximalIdeal ((Ideal.Quotient.maximal_ideal_iff_isField_quotient
        _).mpr Ring.KrullDimLE.isField_of_isDomain))
    rw [Ring.krullDimLE_iff] at hnk
    exact (WithBot.one_le_iff_pos _).2 (lt_of_not_ge hnk)
  rw [ringKrullDim_eq_of_ringEquiv e] at hone
  refine le_antisymm ?_ hone
  rw [← topologicalKrullDim_complementaryCurve k X hdim C hC]
  exact ringKrullDim_stalk_le_topologicalKrullDim y

/-- **Stacks 0E3H, step (v), the ring-theoretic half: the local ring of the closure of the
complement of a rational tail at the attaching point is a regular local ring.** The ambient local
ring is reduced with delta invariant one and exactly two minimal primes
(`Stacks.Curves.encard_minimalPrimes_stalk_attachingPoint_eq_two`), and the quotient by a minimal
prime of such a ring is a discrete valuation ring once it is one-dimensional
(`Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one`). A
one-dimensional Noetherian local domain is regular exactly when it is a discrete valuation ring,
which is `AlgebraicGeometry.isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one`. -/
theorem isRegularLocalRing_stalk_complementaryCurve
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint) :
    IsRegularLocalRing ((complementaryCurve C).presheaf.stalk y) := by
  obtain ⟨hred, hδ, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim (C.subschemeι hC.attachingPoint) (isNode_attachingPoint k X hdim hnodal C hC)
  have hredy : _root_.IsReduced (X.presheaf.stalk ((complementaryCurveι C).base y)) := by
    rw [hy]; exact hred
  have hδy : Ring.deltaInvariant (X.presheaf.stalk ((complementaryCurveι C).base y)) = 1 := by
    rw [hy]; exact hδ
  have htwo : Set.encard (minimalPrimes
      (X.presheaf.stalk ((complementaryCurveι C).base y))) = 2 := by
    rw [hy]; exact encard_minimalPrimes_stalk_attachingPoint_eq_two k X hdim hnodal C hC
  have := hredy
  have : IsNagataRing (X.presheaf.stalk ((complementaryCurveι C).base y)) :=
    isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) _
  have hJmin := stalk_complementaryCurveIdeal_base_mem_minimalPrimes k X hdim hnodal C hC y hy
  have : (IdealSheafData.stalk (complementaryCurveIdeal C)
      ((complementaryCurveι C).base y)).IsPrime := hJmin.1.1
  have : IsDomain (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) :=
    Ideal.Quotient.isDomain _
  have : IsLocalRing (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨e⟩ := nonempty_ringEquiv_stalk_complementaryCurve C y
  rw [ker_stalkMap_complementaryCurveι C y] at e
  have hdimq : ringKrullDim (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C)
        ((complementaryCurveι C).base y)) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact ringKrullDim_stalk_complementaryCurve_eq_one k X hdim hnodal C hC y hy
  -- two distinct minimal primes, and finitely many of them
  obtain ⟨a, b, hab, hset⟩ := Set.encard_eq_two.mp htwo
  have ha : a ∈ minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y)) := by
    rw [hset]; exact Set.mem_insert _ _
  have hb : b ∈ minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y)) := by
    rw [hset]; exact Set.mem_insert_of_mem _ rfl
  have hNag : IsNagataRing (X.presheaf.stalk ((complementaryCurveι C).base y)) := inferInstance
  have hfin : (minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y))).Finite :=
    Set.encard_ne_top_iff.mp (by rw [htwo]; decide)
  have hab' : (⟨a, ha⟩ : minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y))) ≠
      ⟨b, hb⟩ := fun h => hab (Subtype.ext_iff.mp h)
  have hpack := Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one
    (X.presheaf.stalk ((complementaryCurveι C).base y)) hNag hfin hab' hδy ⟨_, hJmin⟩ hdimq
  obtain ⟨hdom, hdvr⟩ := hpack
  have := hdom
  have : IsRegularLocalRing (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) :=
    ((isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one _ hdimq).out 3 1).mp hdvr
  exact IsRegularLocalRing.of_ringEquiv e

/-! ### Smoothness at the attaching point -/

/-- **A closed immersion induces an isomorphism on residue fields.** The map on local rings is
surjective, hence so is the induced map of residue fields, and a ring homomorphism out of a field
is injective. -/
theorem bijective_residueFieldMap_of_isClosedImmersion {Y V : Scheme.{u}} (π : Y ⟶ V)
    [IsClosedImmersion π] (x : Y) : Function.Bijective (π.residueFieldMap x) := by
  have hst : Function.Surjective (π.stalkMap x) := π.stalkMap_surjective x
  have hcomp : Function.Surjective (V.residue (π.base x) ≫ π.residueFieldMap x) := by
    rw [Scheme.residue_residueFieldMap]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (Y.residue_surjective x).comp hst
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hcomp
  exact ⟨(π.residueFieldMap x).hom.injective, hcomp.of_comp⟩

/-- **The residue field of the closure of the complement of a rational tail at the attaching
point is separable over the base field.** The residue field extension of the attaching point is
finite and separable (`Stacks.Curves.isFiniteSeparable_residueField_attachingPoint`), and the
closed immersion of the closure into the ambient curve identifies the two residue fields as
extensions of `k`. -/
theorem isSeparableExtension_residueField_complementaryCurve
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint) :
    letI : Algebra k ((complementaryCurve C).residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop ≫
          (complementaryCurve C).Γevaluation y).hom.toAlgebra
    Algebra.IsSeparableExtension k ((complementaryCurve C).residueField y) := by
  have key : ∀ z : X, z = C.subschemeι hC.attachingPoint →
      @Algebra.IsSeparableExtension k (X.residueField z) _ _
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
          X.Γevaluation z).hom.toAlgebra) := by
    intro z hz
    subst hz
    exact (isFiniteSeparable_residueField_attachingPoint k X hdim hnodal C hC).2
  let algX : Algebra k (X.residueField ((complementaryCurveι C).base y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.Γevaluation ((complementaryCurveι C).base y)).hom.toAlgebra
  have hsepX : @Algebra.IsSeparableExtension k
      (X.residueField ((complementaryCurveι C).base y)) _ _ algX := key _ hy
  let algX' : Algebra k ((complementaryCurve C).residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop ≫
        (complementaryCurve C).Γevaluation y).hom.toAlgebra
  exact Algebra.IsSeparableExtension.of_algEquiv
    { __ := RingEquiv.ofBijective ((complementaryCurveι C).residueFieldMap y).hom
        (bijective_residueFieldMap_of_isClosedImmersion (complementaryCurveι C) y)
      commutes' := fun r => by
        simp only [algX, RingHom.algebraMap_toAlgebra,
          CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          Scheme.Hom.comp_appTop]
        exact Scheme.Γevaluation_naturality_apply (complementaryCurveι C) y _ }

/-- **Stacks 0E3H, step (v): the closure of the complement of a rational tail is smooth over the
base field at the attaching point.** Its local ring there is regular
(`Stacks.Curves.isRegularLocalRing_stalk_complementaryCurve`) and its residue field is separable
over `k`, and over a field smoothness at a point with separable residue field is exactly
regularity of the local ring
(`AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk`). -/
theorem smoothAt_complementaryCurve_attachingPoint
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint) :
    InfinitesimalLifting.SmoothAt (complementaryCurveι C ≫ (X ↘ Spec (.of k))) y := by
  have : IsProper (complementaryCurveι C ≫ (X ↘ Spec (.of k))) :=
    isProper_complementaryCurve k X C
  rw [smoothAt_iff_isRegularLocalRing_stalk (complementaryCurveι C ≫ (X ↘ Spec (.of k))) y
    (isSeparableExtension_residueField_complementaryCurve k X hdim hnodal C hC y hy)]
  exact isRegularLocalRing_stalk_complementaryCurve k X hdim hnodal C hC y hy

/-! ### The at-worst-nodal clause of Tag 0E3H -/

/-- **Stacks 0E3H: the scheme-theoretic closure of the complement of a rational tail of a proper
one-dimensional nodal curve with only constant global functions again has at-worst-nodal
singularities.** Away from the attaching point this is the étale transport of
`Stacks.Curves.smoothAt_or_isNode_complementaryCurve_of_notMem_support`; at the attaching point
the closure is in fact *smooth* over `k`, by
`Stacks.Curves.smoothAt_complementaryCurve_attachingPoint`. -/
@[stacks 0E3H "complementary_curve_has_at_worst_nodal_singularities"]
theorem nodal_complementaryCurve
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    letI : (complementaryCurve C).Over (Spec (.of k)) :=
      ⟨complementaryCurveι C ≫ (X ↘ Spec (.of k))⟩
    HasAtWorstNodalSingularities k (complementaryCurve C) :=
  hasAtWorstNodalSingularities_complementaryCurve_of_attachingPoint k X hdim hnodal C hC
    fun y _ hy =>
      Or.inl (smoothAt_complementaryCurve_attachingPoint k X hdim hnodal C hC y hy)


end Stacks.Curves

end
