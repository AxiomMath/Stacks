module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresQuotient
public import StacksFrontier.RingTheory.GeometricallyIntegral.HypersurfaceFibreIrreducibility0559
public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre loci and the scheme-theoretic fibres

The constructibility chain below Stacks 05FT is phrased ring-theoretically: a prime `p` of `A` lies
in `Algebra.geometricallyIrreducibleFibreLocus A C` when `Spec (C ⊗[A] K)` is irreducible for
**every** field `K` carrying an `A`-algebra structure with `ker (A → K) = p`, and likewise for
`Algebra.geometricallyReducedFibreLocus` and `Algebra.geometricallyIntegralFibreLocus`. The
scheme-theoretic statements of Stacks 0550, 0552, 054X and 0555 are phrased with Mathlib's morphism
properties `AlgebraicGeometry.GeometricallyIrreducible`,
`AlgebraicGeometry.GeometricallyReduced` and `AlgebraicGeometry.GeometricallyIntegral` applied to
the single morphism `f.fiberToSpecResidueField y`. This file identifies the two.

## What was already there, and what is added

The *ring-side* half of the identification is already available, in
`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibre`: the quantifier over all fields `K`
with `ker (A → K) = p` is the quantifier over all field extensions of `κ(p)`
(`Algebra.mem_fibreLocus_iff_forall_residueFieldExtension`), so each locus is described one point
at a time by a condition on the single algebra `κ(p) ⊗[A] C` over `κ(p)`
(`Algebra.mem_geometricallyIrreducibleFibreLocus_iff`,
`Algebra.mem_geometricallyReducedFibreLocus_iff`). That file does the work of the test-field
quantifier — the factorisation `Ideal.ResidueField p → K` and the comparison
`C ⊗[A] K ≅ (κ(p) ⊗[A] C) ⊗[κ(p)] K` — and nothing of it is redone here.

What was missing is the last step, from `κ(p) ⊗[A] C` as an **algebra** to the scheme-theoretic
fibre as a **morphism**, and it is short: `κ(p) ⊗[A] C` is `Ideal.Fiber p C` on the nose, and
`AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso` is an isomorphism of arrows between
`f.fiberToSpecResidueField p` and `Spec.map (algebraMap κ(p) (p.Fiber C))`. Transporting a morphism
property along it needs only `MorphismProperty.RespectsIso`. So the per-fibre bridge is three lines
per locus once the ring side is in hand, which is why it is worth having: no scheme-level file
mentioned a fibre locus at all, and the four prerequisites of Stacks 055A — 054Q, 0550,
0552, 054X — could not be composed with the ring-level chain without it.

Two further gaps are filled on the way.

* `AlgebraicGeometry.geometricallyReduced_algebraMap_iff_isGeometricallyReduced` relates the
  scheme-level morphism property `AlgebraicGeometry.GeometricallyReduced` of `Spec S ⟶ Spec k` to
  Mathlib's algebra class `Algebra.IsGeometricallyReduced k S`. The two are *not* definitionally
  comparable: the morphism property quantifies over all field extensions and the class tests
  `AlgebraicClosure k` alone, and the equivalence of those is an open TODO upstream. It is
  available here because `Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct` is
  proved, and it is what makes the reduced locus bridge possible.
* The *shape of the open set*. The ring-side statements produce a basic open `D(f)` with `f ≠ 0`;
  the scheme-side ones a nonempty open. Over a domain these are interchangeable, which is
  `PrimeSpectrum.exists_ne_zero_basicOpen_subset_iff_isOpen`: a basic open attached to a nonzero
  element of a domain contains the generic point, and conversely the basic opens are a topological
  basis, so a nonempty open contains a nonempty basic one.

## Main results

* `AlgebraicGeometry.geometricallyReduced_algebraMap_iff`: the fibrewise form of geometric
  reducedness for a ring map, the companion of
  `Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct`; and
  `AlgebraicGeometry.geometricallyReduced_algebraMap_iff_isGeometricallyReduced`, the comparison
  with Mathlib's `Algebra.IsGeometricallyReduced`.
* `AlgebraicGeometry.geometricallyIrreducible_fiberToSpecResidueField_iff`,
  `AlgebraicGeometry.geometricallyReduced_fiberToSpecResidueField_iff`,
  `AlgebraicGeometry.geometricallyIntegral_fiberToSpecResidueField_iff`: the scheme-theoretic fibre
  of `Spec C ⟶ Spec A` at `p` is `Spec (p.Fiber C)` over `Spec κ(p)`, for each of the three
  properties.
* `Algebra.mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField`,
  `Algebra.mem_geometricallyReducedFibreLocus_iff_fiberToSpecResidueField`,
  `Algebra.mem_geometricallyIntegralFibreLocus_iff_fiberToSpecResidueField`: **the per-fibre bridge
  for all three loci**, and their set forms
  `Algebra.geometricallyIrreducibleFibreLocus_eq_setOf_fiberToSpecResidueField` and siblings.
* `PrimeSpectrum.exists_ne_zero_basicOpen_subset_iff_isOpen`,
  `PrimeSpectrum.exists_ne_zero_basicOpen_disjoint_iff_isOpen` and
  `PrimeSpectrum.exists_ne_zero_basicOpen_dichotomy_iff_isOpen`: **the open-set bridge**, in the
  three shapes the ring-side statements use.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isOpen` and its
  reduced and integral siblings: **the two bridges composed**, so that a nonzero `f : D` with
  `D(f)` inside a locus and a nonempty open all of whose scheme-theoretic fibres are good are
  interchangeable data.
* `Algebra.exists_ne_zero_basicOpen_dichotomy_geometricallyIrreducibleFibreLocus_iff_isOpen`: the
  same in the dichotomy shape, which is literally the hypothesis `hspread` of
  `Algebra.isConstructible_geometricallyIrreducibleFibreLocus`, the affine `n = 1` level set of
  Stacks 055B.
* `Algebra.exists_isOpen_geometricallyIrreducible_fiberToSpecResidueField_of_irreducible`: the
  hypersurface step of the First proof of Stacks 0559
  (`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible`)
  transported to the scheme side, which is what the bridge was built for.

## Implementation notes

The fibre is written `Ideal.Fiber p C`, that is `κ(p) ⊗[A] C` with the residue field on the
**left**, which is both the form `AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso` produces and
the form the ring-side results use. The opposite order `C ⊗[A] κ(p)` would need
`Algebra.TensorProduct.rightAlgebra`, which is an `abbrev` and not an instance and so has to be
scoped into every statement; nothing here needs it.

`MorphismProperty.RespectsIso` is not found by instance search for any of the three morphism
properties, although each is an instance of `MorphismProperty.IsStableUnderBaseChange`; it is
supplied explicitly from that, as elsewhere in the repository.

The points of `Spec (CommRingCat.of A)` are `PrimeSpectrum A`, so a prime of `A` is already a point
of the base and no transport along a homeomorphism appears in any statement.

Nothing here carries a Stacks tag. These are bridge lemmas between two spellings of one condition,
not statements of the source. That the equivalences are not vacuous is proved rather than asserted:
the two degenerate hypersurfaces of
`StacksFrontier.RingTheory.GeometricallyIntegral.HypersurfaceFibreIrreducibility0559` are transported
in the final section, giving a morphism all of whose fibres satisfy the scheme-side condition and
another, in the same family, none of whose fibres do.

## References

* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ## Geometric reducedness of a ring map, fibrewise and as Mathlib's class -/

/-- **The fibrewise form of geometric reducedness for a ring map.** `Spec S ⟶ Spec R` is
geometrically reduced exactly when `S ⊗[R] K` is reduced for every field `K` carrying an
`R`-algebra structure: the fibre of `Spec S → Spec R` over a field-valued point `Spec K` is
`Spec (S ⊗[R] K)`.

This is the companion of `Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct`, with
the same proof. -/
theorem geometricallyReduced_algebraMap_iff (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] :
    GeometricallyReduced (Spec.map (ofHom (algebraMap R S))) ↔
      ∀ (K : Type u) [Field K] [Algebra R K], _root_.IsReduced (S ⊗[R] K) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  refine forall_congr' fun K => ?_
  refine ⟨fun h _ _ => ?_, fun h _ _ => ?_⟩
  · rw [← affine_isReduced_iff (.of (S ⊗[R] K))]
    exact ObjectProperty.prop_of_iso _ (pullbackSpecIso R S K) (h ..)
  · exact ObjectProperty.prop_of_iso _ (pullbackSpecIso R S K).symm
      ((affine_isReduced_iff (.of (S ⊗[R] K))).mpr h)

/-- **The scheme-level morphism property and Mathlib's algebra class agree.** Over a field `k`, the
morphism `Spec S ⟶ Spec k` is geometrically reduced exactly when `S` is geometrically reduced over
`k` in Mathlib's sense, that is when `AlgebraicClosure k ⊗[k] S` is reduced.

The two are not definitionally comparable: the morphism property quantifies over all field
extensions of `k` and the class tests the single field `AlgebraicClosure k`. The identification of
those two conditions is items (5) and (6) of Stacks 030V, available as
`Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct`; Mathlib itself lists it as an
open problem.

This is the reduced analogue of `Algebra.IsGeometricallyIrreducible` and
`Algebra.IsGeometricallyIntegral`, which are *defined* as the morphism property and so need no such
lemma. -/
@[ega "IV 6.7.6"]
theorem geometricallyReduced_algebraMap_iff_isGeometricallyReduced (k S : Type u) [Field k]
    [CommRing S] [Algebra k S] :
    GeometricallyReduced (Spec.map (ofHom (algebraMap k S))) ↔
      Algebra.IsGeometricallyReduced k S :=
  (geometricallyReduced_algebraMap_iff k S).trans
    (Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct k S).symm

/-! ## The fibre of `Spec C ⟶ Spec A` at `p` is `Spec (p.Fiber C)` over `Spec κ(p)` -/

section Fibre

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] (p : PrimeSpectrum A)

/-- A base-change stable morphism property holds for the fibre morphism at `p` exactly when it holds
for `Spec.map` of the residue field algebra of the fibre ring. -/
private theorem fiberToSpecResidueField_iff_of_isStableUnderBaseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    P ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p) ↔
      P (Spec.map (ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C)))) :=
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := P)
  MorphismProperty.arrow_mk_iso_iff _ (Spec.fiberToSpecResidueFieldIso A C p)

/-- The scheme-theoretic fibre of `Spec C ⟶ Spec A` at `p` is geometrically irreducible over
`Spec κ(p)` exactly when the ring `p.Fiber C` is geometrically irreducible over `κ(p)`. -/
theorem geometricallyIrreducible_fiberToSpecResidueField_iff :
    GeometricallyIrreducible
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p) ↔
      Algebra.IsGeometricallyIrreducible p.asIdeal.ResidueField (p.asIdeal.Fiber C) :=
  fiberToSpecResidueField_iff_of_isStableUnderBaseChange A C p _

/-- The scheme-theoretic fibre of `Spec C ⟶ Spec A` at `p` is geometrically reduced over
`Spec κ(p)` exactly when the ring `p.Fiber C` is geometrically reduced over `κ(p)` in Mathlib's
sense. -/
theorem geometricallyReduced_fiberToSpecResidueField_iff :
    GeometricallyReduced
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p) ↔
      Algebra.IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber C) :=
  (fiberToSpecResidueField_iff_of_isStableUnderBaseChange A C p _).trans
    (geometricallyReduced_algebraMap_iff_isGeometricallyReduced _ _)

/-- The scheme-theoretic fibre of `Spec C ⟶ Spec A` at `p` is geometrically integral over
`Spec κ(p)` exactly when the ring `p.Fiber C` is geometrically integral over `κ(p)`. -/
theorem geometricallyIntegral_fiberToSpecResidueField_iff :
    GeometricallyIntegral
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p) ↔
      Algebra.IsGeometricallyIntegral p.asIdeal.ResidueField (p.asIdeal.Fiber C) :=
  fiberToSpecResidueField_iff_of_isStableUnderBaseChange A C p _

end Fibre

end AlgebraicGeometry

/-! ## The per-fibre bridge for the three loci -/

namespace Algebra

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] (p : PrimeSpectrum A)

/-- **The per-fibre bridge for the geometrically irreducible fibre locus.** A prime `p` of `A` lies
in `Algebra.geometricallyIrreducibleFibreLocus A C` exactly when the scheme-theoretic fibre of
`Spec C ⟶ Spec A` at `p` is geometrically irreducible over `Spec κ(p)`.

The left-hand side quantifies over every field `K` with `ker (A → K) = p`; the right-hand side
tests only the residue field and its extensions. The collapse of the quantifier is
`Algebra.mem_geometricallyIrreducibleFibreLocus_iff`, and the remaining step from the algebra
`κ(p) ⊗[A] C` to the morphism is
`AlgebraicGeometry.geometricallyIrreducible_fiberToSpecResidueField_iff`. -/
theorem mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField :
    p ∈ geometricallyIrreducibleFibreLocus A C ↔
      GeometricallyIrreducible
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p) :=
  have := p.isPrime
  (mem_geometricallyIrreducibleFibreLocus_iff p).trans
    (geometricallyIrreducible_fiberToSpecResidueField_iff A C p).symm

/-- **The per-fibre bridge for the geometrically reduced fibre locus.** A prime `p` of `A` lies in
`Algebra.geometricallyReducedFibreLocus A C` exactly when the scheme-theoretic fibre of
`Spec C ⟶ Spec A` at `p` is geometrically reduced over `Spec κ(p)`.

This is `Algebra.mem_geometricallyReducedFibreLocus_iff` followed by
`AlgebraicGeometry.geometricallyReduced_fiberToSpecResidueField_iff`; the latter is where the
all-extensions form of geometric reducedness is reconciled with Mathlib's algebraic-closure
form. -/
theorem mem_geometricallyReducedFibreLocus_iff_fiberToSpecResidueField :
    p ∈ geometricallyReducedFibreLocus A C ↔
      GeometricallyReduced
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p) :=
  have := p.isPrime
  (mem_geometricallyReducedFibreLocus_iff p).trans
    (geometricallyReduced_fiberToSpecResidueField_iff A C p).symm

/-- **The per-fibre bridge for the geometrically integral fibre locus.** A prime `p` of `A` lies in
`Algebra.geometricallyIntegralFibreLocus A C` exactly when the scheme-theoretic fibre of
`Spec C ⟶ Spec A` at `p` is geometrically integral over `Spec κ(p)`.

The ring side has no integral counterpart of
`Algebra.mem_geometricallyIrreducibleFibreLocus_iff`, so the collapse of the test-field quantifier
is taken directly from `Algebra.mem_fibreLocus_iff_forall_residueFieldExtension` at
`P = IsDomain`. Together with Stacks 05DY, which splits the morphism property
`AlgebraicGeometry.GeometricallyIntegral` into its reduced and irreducible halves, this is the
scheme-level counterpart of `Algebra.geometricallyIntegralFibreLocus_eq_inter`. -/
theorem mem_geometricallyIntegralFibreLocus_iff_fiberToSpecResidueField :
    p ∈ geometricallyIntegralFibreLocus A C ↔
      GeometricallyIntegral
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p) := by
  have := p.isPrime
  rw [geometricallyIntegralFibreLocus_eq_fibreLocus,
    geometricallyIntegral_fiberToSpecResidueField_iff, Algebra.IsGeometricallyIntegral,
    Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct]
  exact mem_fibreLocus_iff_forall_residueFieldExtension (fun _ _ _ _ e => isDomain_congr e) p

/-- The geometrically irreducible fibre locus is exactly the set of points whose scheme-theoretic
fibre is geometrically irreducible. This is the set-level form of
`Algebra.mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField`, matching the shape in
which the scheme-level statements of Stacks 0550 and 054X carry their loci. -/
theorem geometricallyIrreducibleFibreLocus_eq_setOf_fiberToSpecResidueField :
    geometricallyIrreducibleFibreLocus A C =
      {p : PrimeSpectrum A | GeometricallyIrreducible
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p)} :=
  Set.ext fun p => mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField A C p

/-- The geometrically reduced fibre locus is exactly the set of points whose scheme-theoretic fibre
is geometrically reduced. This is the shape in which Stacks 0576 carries the locus, as in
`AlgebraicGeometry.geometricallyReduced_fiber_set_eq_preimage_of_isPullback`. -/
theorem geometricallyReducedFibreLocus_eq_setOf_fiberToSpecResidueField :
    geometricallyReducedFibreLocus A C =
      {p : PrimeSpectrum A | GeometricallyReduced
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p)} :=
  Set.ext fun p => mem_geometricallyReducedFibreLocus_iff_fiberToSpecResidueField A C p

/-- The geometrically integral fibre locus is exactly the set of points whose scheme-theoretic
fibre is geometrically integral. -/
theorem geometricallyIntegralFibreLocus_eq_setOf_fiberToSpecResidueField :
    geometricallyIntegralFibreLocus A C =
      {p : PrimeSpectrum A | GeometricallyIntegral
        ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField p)} :=
  Set.ext fun p => mem_geometricallyIntegralFibreLocus_iff_fiberToSpecResidueField A C p

end Algebra

/-! ## The open-set bridge over a domain -/

namespace PrimeSpectrum

variable {D : Type u} [CommRing D] [IsDomain D]

/-- **A nonempty basic open and a nonempty open are interchangeable over a domain.** For any subset
`S` of `Spec D` with `D` a domain, there is a nonzero `f : D` with `D(f) ⊆ S` if and only if there
is a nonempty open subset contained in `S`.

One direction uses that the generic point `(0)` lies in `D(f)` as soon as `f ≠ 0`; the other that
the basic opens form a topological basis, and that a basic open containing any point at all is
attached to a nonzero element. -/
theorem exists_ne_zero_basicOpen_subset_iff_isOpen (S : Set (PrimeSpectrum D)) :
    (∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆ S) ↔
      ∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
  constructor
  · rintro ⟨f, hf0, hf⟩
    exact ⟨basicOpen f, (basicOpen f).isOpen, ⟨⟨⊥, Ideal.isPrime_bot⟩,
      (mem_basicOpen f _).mpr (by simpa using hf0)⟩, hf⟩
  · rintro ⟨U, hU, ⟨x, hx⟩, hUS⟩
    obtain ⟨_, ⟨f, rfl⟩, hxV, hVU⟩ :=
      isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hU
    exact ⟨f, fun hf0 => (mem_basicOpen f x).mp hxV (hf0 ▸ x.asIdeal.zero_mem), hVU.trans hUS⟩

/-- **The disjoint form of the open-set bridge.** For any subset `S` of `Spec D` with `D` a domain,
there is a nonzero `f : D` with `D(f)` disjoint from `S` if and only if some nonempty open subset
is disjoint from `S`. -/
theorem exists_ne_zero_basicOpen_disjoint_iff_isOpen (S : Set (PrimeSpectrum D)) :
    (∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D)) S) ↔
      ∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ Disjoint U S := by
  simp only [← Set.subset_compl_iff_disjoint_right]
  exact exists_ne_zero_basicOpen_subset_iff_isOpen Sᶜ

/-- **The dichotomy form of the open-set bridge**, which is the shape the ring-side statements of
Stacks 0579 and 055B take: a nonzero `f : D` whose basic open either lies in or misses `S` exists
exactly when some nonempty open either lies in or misses `S`. -/
theorem exists_ne_zero_basicOpen_dichotomy_iff_isOpen (S : Set (PrimeSpectrum D)) :
    (∃ f : D, f ≠ 0 ∧ ((basicOpen f : Set (PrimeSpectrum D)) ⊆ S ∨
        Disjoint (basicOpen f : Set (PrimeSpectrum D)) S)) ↔
      (∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ U ⊆ S) ∨
        ∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ Disjoint U S := by
  rw [← exists_ne_zero_basicOpen_subset_iff_isOpen, ← exists_ne_zero_basicOpen_disjoint_iff_isOpen]
  simp only [and_or_left, exists_or]

end PrimeSpectrum

/-! ## The two bridges composed, at the three loci

These are the statements a consumer actually has in hand: the ring-side results produce a nonzero
`f : D` and a basic open, the scheme-side ones a nonempty open and a condition on each fibre over
it, and the composites below say the two are the same statement.
-/

namespace Algebra

variable (D T : Type u) [CommRing D] [IsDomain D] [CommRing T] [Algebra D T]

/-- **The composed bridge for the geometrically irreducible fibre locus.** Over a domain `D`, a
nonzero `f : D` whose basic open lies in `Algebra.geometricallyIrreducibleFibreLocus D T` exists
exactly when some nonempty open subset of `Spec D` has all its scheme-theoretic fibres
geometrically irreducible.

This is the conclusion of the irreducible good half `hirr` of the generic-fibre dichotomy, with the
two spellings identified; the left-hand side is the shape of
`Algebra.isConstructible_geometricallyIrreducibleFibreLocus`'s hypothesis and the right-hand side
the shape in which Stacks 0550, 0552 and 054X deliver their open sets. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isOpen :
    (∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
        geometricallyIrreducibleFibreLocus D T) ↔
      ∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U, GeometricallyIrreducible
        ((Spec.map (ofHom (algebraMap D T))).fiberToSpecResidueField p) := by
  rw [PrimeSpectrum.exists_ne_zero_basicOpen_subset_iff_isOpen,
    geometricallyIrreducibleFibreLocus_eq_setOf_fiberToSpecResidueField]
  simp only [Set.subset_def, Set.mem_ofPred_eq]

/-- **The composed bridge for the geometrically reduced fibre locus**, the companion of
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isOpen` for the
reduced half of the dichotomy, i.e. for Stacks 0577 and 0578. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_iff_isOpen :
    (∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
        geometricallyReducedFibreLocus D T) ↔
      ∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U, GeometricallyReduced
        ((Spec.map (ofHom (algebraMap D T))).fiberToSpecResidueField p) := by
  rw [PrimeSpectrum.exists_ne_zero_basicOpen_subset_iff_isOpen,
    geometricallyReducedFibreLocus_eq_setOf_fiberToSpecResidueField]
  simp only [Set.subset_def, Set.mem_ofPred_eq]

/-- **The composed bridge for the geometrically integral fibre locus**, which is the form the
generic-fibre dichotomy of EGA IV 9.7.7 feeding Stacks 05FT takes. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyIntegralFibreLocus_iff_isOpen :
    (∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
        geometricallyIntegralFibreLocus D T) ↔
      ∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U, GeometricallyIntegral
        ((Spec.map (ofHom (algebraMap D T))).fiberToSpecResidueField p) := by
  rw [PrimeSpectrum.exists_ne_zero_basicOpen_subset_iff_isOpen,
    geometricallyIntegralFibreLocus_eq_setOf_fiberToSpecResidueField]
  simp only [Set.subset_def, Set.mem_ofPred_eq]

/-- **The dichotomy shape of the composed bridge for the geometrically irreducible fibre locus.**
This is exactly the hypothesis `hspread` of
`Algebra.isConstructible_geometricallyIrreducibleFibreLocus`, the affine `n = 1` level set of
Stacks 055B, rewritten on the scheme side: over a domain some nonempty open subset of `Spec D` has
all its fibres geometrically irreducible, or some nonempty open subset has none of them so.

Supplying the right-hand side for every Noetherian domain `D` and finite type `D`-algebra `T`
therefore discharges `hspread`, which is the step the scheme-level Stacks 055A produces and the
ring-level chain could not previously accept. -/
theorem exists_ne_zero_basicOpen_dichotomy_geometricallyIrreducibleFibreLocus_iff_isOpen :
    (∃ f : D, f ≠ 0 ∧ ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T ∨
        Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D))
          (geometricallyIrreducibleFibreLocus D T))) ↔
      (∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U, GeometricallyIrreducible
          ((Spec.map (ofHom (algebraMap D T))).fiberToSpecResidueField p)) ∨
        ∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U, ¬ GeometricallyIrreducible
          ((Spec.map (ofHom (algebraMap D T))).fiberToSpecResidueField p) := by
  rw [PrimeSpectrum.exists_ne_zero_basicOpen_dichotomy_iff_isOpen,
    geometricallyIrreducibleFibreLocus_eq_setOf_fiberToSpecResidueField]
  simp only [Set.subset_def, Set.mem_ofPred_eq, Set.disjoint_left]

end Algebra

/-! ## The hypersurface step of Stacks 0559 on the scheme side

The bridge is built for exactly this transport, so the transport is carried out here rather than
asserted. The two degenerate hypersurfaces of
`StacksFrontier.RingTheory.GeometricallyIntegral.HypersurfaceFibreIrreducibility0559` come across
too, and they are what shows the per-fibre bridge is not an equivalence between two conditions
that always hold or always fail.
-/

namespace Algebra

/-- **The hypersurface step of the First proof of Stacks 0559, on the scheme side.** Let `D` be a
domain with fraction field `K` and `Kbar` an algebraically closed extension of `K`, and let
`P ∈ D[x_i : i ∈ ι]`, in finitely many variables, be irreducible over `Kbar`. Then there is a
nonempty open subset of `Spec D` over which every scheme-theoretic fibre of
`Spec (D[x_i]/(P)) ⟶ Spec D` is geometrically irreducible.

This is
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible`
transported through
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isOpen`. It is the
form the scheme-level statements of Stacks 0550, 0552 and 054X consume, and it is what lets those
prerequisites be composed with the ring-level hypersurface case. -/
theorem exists_isOpen_geometricallyIrreducible_fiberToSpecResidueField_of_irreducible
    (D : Type u) [CommRing D] [IsDomain D] (ι : Type u) [Finite ι] (P : MvPolynomial ι D)
    (K : Type u) [Field K] [Algebra D K] [IsFractionRing D K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    (hP : Irreducible (P.map ((algebraMap K Kbar).comp (algebraMap D K)))) :
    ∃ U : Set (PrimeSpectrum D), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
      GeometricallyIrreducible ((Spec.map (ofHom (algebraMap D
        (MvPolynomial ι D ⧸ Ideal.span {P})))).fiberToSpecResidueField p) :=
  (exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isOpen D _).mp
    (exists_ne_zero_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_irreducible
      D ι P K Kbar hP)

/-- **The scheme-side fibre condition holds at every point of the base**, for the hypersurface cut
out by the zero polynomial, whose fibres are polynomial rings over fields. This transports
`Algebra.geometricallyIrreducibleFibreLocus_quotient_span_zero` and is one extreme of the per-fibre
bridge. -/
theorem geometricallyIrreducible_fiberToSpecResidueField_quotient_span_zero (D : Type u)
    [CommRing D] (ι : Type u) (p : PrimeSpectrum D) :
    GeometricallyIrreducible ((Spec.map (ofHom (algebraMap D
      (MvPolynomial ι D ⧸ Ideal.span {(0 : MvPolynomial ι D)})))).fiberToSpecResidueField p) :=
  (mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField D _ p).mp
    (geometricallyIrreducibleFibreLocus_quotient_span_zero D ι ▸ Set.mem_univ p)

/-- **The scheme-side fibre condition fails at every point of the base**, for the hypersurface
`D[x₀, x₁]/(x₀x₁)`, whose fibre over any field has a non-prime nilradical. This transports
`Algebra.geometricallyIrreducibleFibreLocus_quotient_span_X_mul_X_eq_empty` and is the other
extreme.

Taken with `Algebra.geometricallyIrreducible_fiberToSpecResidueField_quotient_span_zero` it shows
that `Algebra.mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField` is not an
equivalence between two conditions that are always true, nor between two that are always false:
inside one family of algebras both sides hold at every point for one member and fail at every
point for another. Note that `P = x₀²` would not serve as the failing witness, the dual numbers
being geometrically irreducible (`Algebra.isGeometricallyIrreducible_quotient_span_X_sq`); the
witness has to be reducible, not merely non-reduced. -/
theorem not_geometricallyIrreducible_fiberToSpecResidueField_quotient_span_X_mul_X (D : Type u)
    [CommRing D] (p : PrimeSpectrum D) :
    ¬ GeometricallyIrreducible (Scheme.Hom.fiberToSpecResidueField
      (Spec.map (ofHom (algebraMap D (MvPolynomial (Fin 2) D ⧸ Ideal.span
        {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) D)})))) p) := by
  intro h
  have := (mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField D _ p).mpr h
  rwa [geometricallyIrreducibleFibreLocus_quotient_span_X_mul_X_eq_empty D] at this

end Algebra

end
