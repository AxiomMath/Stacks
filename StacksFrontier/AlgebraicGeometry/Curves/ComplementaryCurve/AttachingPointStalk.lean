module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionNodes
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchCount

/-!
# The local ring of a curve at a point lying on two components

Let `X` be a scheme and `x` a point lying on two distinct irreducible components of `X`. The
components through `x` are counted by the minimal primes of the local ring `𝒪_{X, x}`, so the
local ring there has at least two minimal primes. When moreover `X` has two geometric branches
at `x` — which is the case at a node — that count is exactly two, because the number of
irreducible components through a point is bounded by the number of branches and that in turn by
the number of geometric branches.

This is the input the ring-theoretic analysis of a node needs: the lemmas
`Ring.deltaInvariant_quotient_minimalPrimes_eq_zero_of_deltaInvariant_eq_one` and
`Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one` ask for two
distinct minimal primes, and identifying a particular ideal as one of them asks for the count to
be exactly two.

The second half of the file records the local ring of the scheme-theoretic closure of the
complement of a closed subscheme. That closure is a closed subscheme of `X`, cut out by
`AlgebraicGeometry.complementaryCurveIdeal`, so the kernel of its stalk map is the stalk of that
ideal sheaf and the quotient by it is the local ring of the closure.

## Main results

* `AlgebraicGeometry.exists_ne_mem_minimalPrimes_stalk_of_irreducibleComponents`: two distinct
  irreducible components through a point give two distinct minimal primes of the local ring.
* `AlgebraicGeometry.encard_minimalPrimes_stalk_eq_two`: at a point with two geometric branches
  lying on two distinct irreducible components, the local ring has exactly two minimal primes.
* `AlgebraicGeometry.ker_stalkMap_complementaryCurveι`: the kernel of the stalk map of the
  closure of the complement is the stalk of `complementaryCurveIdeal`.
* `AlgebraicGeometry.nonempty_ringEquiv_stalk_complementaryCurve`: the local ring of the closure
  of the complement is the quotient of the ambient local ring by that kernel.
* `AlgebraicGeometry.eq_of_le_of_sup_eq_maximalIdeal_of_minimalPrimes_eq_pair`: an ideal below
  one of the two minimal primes of a reduced local ring and summing with the other to the
  maximal ideal is that minimal prime.
* `AlgebraicGeometry.stalk_sup_stalk_complementaryCurveIdeal_eq_maximalIdeal`: at the attaching
  point of a rational tail the two stalks sum to the maximal ideal.

## Implementation notes

`AlgebraicGeometry.complementaryCurve` is defined as the scheme-theoretic image of the inclusion
of the open complement, and `Scheme.Hom.image` and `Scheme.Hom.imageι` are abbreviations for
`Scheme.Hom.ker.subscheme` and `Scheme.Hom.ker.subschemeι`. So the closure of the complement is
literally the closed subscheme cut out by `complementaryCurveIdeal`, and the closed-immersion
API applies to `complementaryCurveι` with no transport.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Minimal primes of the local ring at a point on two components -/

/-- Two distinct irreducible components through a point give more than one minimal prime of the
local ring there. -/
private theorem one_lt_encard_minimalPrimes_stalk
    (X : Scheme.{u}) (x : X) {Z W : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X) (hZW : Z ≠ W)
    (hxZ : x ∈ Z) (hxW : x ∈ W) :
    1 < Set.encard (minimalPrimes (X.presheaf.stalk x)) := by
  rw [← encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk X x,
    Set.one_lt_encard_iff_nontrivial]
  exact ⟨Z, ⟨hZ, hxZ⟩, W, ⟨hW, hxW⟩, hZW⟩

/-- **Two distinct irreducible components through a point give two distinct minimal primes of
the local ring there.** The irreducible components through the point are counted by the minimal
primes of the stalk, so a pair of distinct components makes that set nontrivial. -/
theorem exists_ne_mem_minimalPrimes_stalk_of_irreducibleComponents
    (X : Scheme.{u}) (x : X) {Z W : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X) (hZW : Z ≠ W)
    (hxZ : x ∈ Z) (hxW : x ∈ W) :
    ∃ p q : minimalPrimes (X.presheaf.stalk x), p ≠ q := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.one_lt_encard_iff_nontrivial.mp
    (one_lt_encard_minimalPrimes_stalk X x hZ hW hZW hxZ hxW)
  exact ⟨⟨p, hp⟩, ⟨q, hq⟩, fun h => hpq (Subtype.ext_iff.mp h)⟩

/-- **At a point of a scheme with two geometric branches lying on two distinct irreducible
components, the local ring has exactly two minimal primes.** The minimal primes of the stalk are
counted by the irreducible components through the point, that count is at most the number of
branches, and the number of branches is at most the number of geometric branches. The two
distinct components supply the reverse inequality. -/
theorem encard_minimalPrimes_stalk_eq_two
    (X : Scheme.{u}) (x : X) {Z W : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X) (hZW : Z ≠ W)
    (hxZ : x ∈ Z) (hxW : x ∈ W)
    (hbr : numberOfGeometricBranches X x = 2) :
    Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2 := by
  refine le_antisymm ?_ ?_
  · calc Set.encard (minimalPrimes (X.presheaf.stalk x))
        = Set.encard {Z' ∈ irreducibleComponents X | x ∈ Z'} :=
          (encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk X x).symm
      _ ≤ numberOfBranches X x := encard_irreducibleComponentsThrough_le_numberOfBranches X x
      _ ≤ numberOfGeometricBranches X x := numberOfBranches_le_numberOfGeometricBranches X x
      _ = 2 := hbr
  · exact Order.add_one_le_of_lt (one_lt_encard_minimalPrimes_stalk X x hZ hW hZW hxZ hxW)

/-! ### The local ring of the closure of the complement -/

/-- **The kernel of the stalk map of the closure of the complement of a closed subscheme is the
stalk of the ideal sheaf cutting that closure out.** The closure is the closed subscheme cut out
by `AlgebraicGeometry.complementaryCurveIdeal`, so this is the closed-immersion computation of
the stalk of a kernel ideal sheaf. -/
theorem ker_stalkMap_complementaryCurveι {X : Scheme.{u}} (C : X.IdealSheafData)
    (y : complementaryCurve C) :
    RingHom.ker ((complementaryCurveι C).stalkMap y).hom =
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y) := by
  rw [← IdealSheafData.stalk_ker_of_isClosedImmersion (complementaryCurveι C) y,
    Scheme.IdealSheafData.ker_subschemeι]

/-- **The local ring of the closure of the complement of a closed subscheme is the quotient of
the ambient local ring by the kernel of the stalk map.** The stalk map of a closed immersion is
surjective. -/
theorem nonempty_ringEquiv_stalk_complementaryCurve {X : Scheme.{u}} (C : X.IdealSheafData)
    (y : complementaryCurve C) :
    Nonempty ((X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
        RingHom.ker ((complementaryCurveι C).stalkMap y).hom) ≃+*
      (complementaryCurve C).presheaf.stalk y) :=
  ⟨RingHom.quotientKerEquivOfSurjective ((complementaryCurveι C).stalkMap_surjective y)⟩

/-! ### The ring-theoretic identification of the second minimal prime -/

/-- **An ideal below one of the two minimal primes of a reduced local ring, and complementary to
the other in the maximal ideal, is that minimal prime.** For `a` in `q`, write `a = b + c` with
`b ∈ p` and `c ∈ J`; then `c ∈ q`, so `b = a - c` lies in `p ⊓ q`, which is the nilradical and
hence zero because the ring is reduced. So `a = c ∈ J`, and `J = q` with the given inclusion.

This is the ring-theoretic step that identifies the ideal cutting out the closure of the
complement of a rational tail as a minimal prime of the local ring at the attaching point. It
needs the minimal primes to be exactly two: with three of them the conclusion fails, as
`k[x,y,z]/(xy,yz,zx)` shows, where `p = (y,z)` is prime and `J = (x)` satisfies both
hypotheses without being prime. -/
theorem eq_of_le_of_sup_eq_maximalIdeal_of_minimalPrimes_eq_pair
    {A : Type u} [CommRing A] [IsLocalRing A] [_root_.IsReduced A] {p q J : Ideal A}
    (htwo : minimalPrimes A = {p, q}) (hJq : J ≤ q)
    (hsup : p ⊔ J = IsLocalRing.maximalIdeal A) :
    J = q := by
  have hq : q ∈ minimalPrimes A := by rw [htwo]; exact Set.mem_insert_of_mem _ rfl
  have hqprime : q.IsPrime := hq.1.1
  -- the two minimal primes meet in the nilradical, which vanishes
  have hinf : p ⊓ q = ⊥ := by
    have h : sInf (minimalPrimes A) = (⊥ : Ideal A).radical := Ideal.sInf_minimalPrimes
    rw [htwo, sInf_pair] at h
    rw [h]
    exact nilradical_eq_zero A
  refine le_antisymm hJq fun a ha => ?_
  have hmem : a ∈ p ⊔ J := by
    rw [hsup]
    exact IsLocalRing.le_maximalIdeal hqprime.ne_top ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hmem
  have hcq : c ∈ q := hJq hc
  have hbq : b ∈ q := by
    have : b = b + c - c := by ring
    rw [this]
    exact Ideal.sub_mem _ ha hcq
  have hb0 : b = 0 := by
    have : b ∈ p ⊓ q := ⟨hb, hbq⟩
    rw [hinf] at this
    simpa using this
  rw [hb0, zero_add]
  exact hc

/-! ### The maximal ideal as the sum of the two stalks at the attaching point -/

/-- **At the attaching point of a rational tail the stalks of the tail and of the closure of its
complement sum to the maximal ideal.** The scheme-theoretic intersection of the two is the
reduced attaching point, so the sum of the two ideal sheaves is the vanishing ideal of that
point; taking stalks turns the sum of ideal sheaves into the sum of ideals and the vanishing
ideal of the point into the maximal ideal. -/
theorem stalk_sup_stalk_complementaryCurveIdeal_eq_maximalIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    IdealSheafData.stalk C (C.subschemeι hC.attachingPoint) ⊔
        IdealSheafData.stalk (complementaryCurveIdeal C)
          (C.subschemeι hC.attachingPoint) =
      IsLocalRing.maximalIdeal
        (X.presheaf.stalk (C.subschemeι hC.attachingPoint)) := by
  rw [← IdealSheafData.stalk_sup]
  exact (congrArg (fun I : X.IdealSheafData =>
      IdealSheafData.stalk I (C.subschemeι hC.attachingPoint))
    hC.intersectionWithComplementaryCurveIdeal_eq).trans
      (IdealSheafData.stalk_vanishingIdeal_singleton _ hC.attachingPoint_isClosed)

end AlgebraicGeometry

end
