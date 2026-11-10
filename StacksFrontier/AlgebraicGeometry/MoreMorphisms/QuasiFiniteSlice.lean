module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen

/-!
# Locally quasi-finite slices of a flat morphism

[Stacks, Tag 0571] says that if `f : X ⟶ S` is flat and locally of finite presentation and
`s ∈ S` lies in the image of `f`, then `f` can be factored through near `s` by a morphism
`g : S' ⟶ S` which is flat, locally of finite presentation and locally quasi-finite, with
`s ∈ g(S')`.

The Stacks proof picks a point `x` of the fibre `X_s` which is closed in `X_s` and at which
`f` is Cohen–Macaulay — possible by [Stacks, Tag 045U] — and then slices `X` down to relative
dimension zero through `x` by [Stacks, Tag 0570] (EGA IV 17.16.1). Here Tag 0570 is isolated as
the hypothesis `AlgebraicGeometry.HasQuasiFiniteSlices`, and nothing in this file is tagged. That
hypothesis is proved as `AlgebraicGeometry.hasQuasiFiniteSlices`, and the unconditional
[Stacks, Tag 0571] is `AlgebraicGeometry.exists_flat_locallyQuasiFinite_factorization_through`,
both in `StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlices`.

## Main definitions

* `AlgebraicGeometry.HasQuasiFiniteSlice` is the conclusion of [Stacks, Tag 0570] for a single
  morphism and point, with the regular-immersion and singleton-fibre clauses dropped: only an
  immersion through the point which is flat, locally of finite presentation and locally
  quasi-finite over the base is asked for. This is all that [Stacks, Tag 0571] needs.
* `AlgebraicGeometry.HasQuasiFiniteSlices` is that statement for every locally finitely
  presented morphism, every Cohen–Macaulay point of it, and every point closed in its fibre.

## Main results

* `AlgebraicGeometry.exists_flat_locallyQuasiFinite_factorization_through_of_hasQuasiFiniteSlices`
  is [Stacks, Tag 0571], granted that hypothesis.

## Implementation notes

In accordance with [Stacks, Tag 01TD], local quasi-finiteness is expressed by
`LocallyOfFiniteType` together with Mathlib's fibrewise predicate `LocallyQuasiFinite`.

The Cohen–Macaulay point is produced as a point of the fibre `f.fiber (f x₀)` which lies in
the (dense, open) Cohen–Macaulay locus and is closed in the fibre; the fibre is a Jacobson
space because it is locally of finite type over a field, so a nonempty locally closed subset
of it meets the closed points. Transporting the closedness statement from the fibre over
`f x₀` to the fibre over `f x` is done through the homeomorphism induced by the equality of
the two set-theoretic fibres.

## References

* [Stacks Project, Tag 0571](https://stacks.math.columbia.edu/tag/0571)
* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The conclusion of [Stacks, Tag 0570]** for a morphism `f : X ⟶ S` and a point `x` of
`X`, weakened to what [Stacks, Tag 0571] consumes: an immersion `i : Z ⟶ X` whose image
contains `x` and for which `Z ⟶ S` is flat, locally of finite presentation and locally
quasi-finite. The regular-immersion clause and the singleton-fibre clause of Tag 0570 are
dropped. -/
def HasQuasiFiniteSlice {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z), IsImmersion i ∧ i z = x ∧
    Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f) ∧ LocallyQuasiFinite (i ≫ f)

/-- **The statement of [Stacks, Tag 0570]** in the form consumed by [Stacks, Tag 0571]: every
point which is closed in its fibre and at which a locally finitely presented morphism is
Cohen–Macaulay admits a locally quasi-finite slice. -/
def HasQuasiFiniteSlices : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), LocallyOfFinitePresentation f → ∀ x : X,
    (∃ hf : ∀ y : S, IsLocallyNoetherian (f.fiber y), f.IsCohenMacaulayAt hf x) →
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) → HasQuasiFiniteSlice f x

/-- **Stacks Project, Tag 0571**, granted [Stacks, Tag 0570] in the form
`AlgebraicGeometry.HasQuasiFiniteSlices`. A point in the image of a flat morphism locally of
finite presentation has a flat, locally finitely presented, locally quasi-finite neighbourhood
which factors through that morphism.

This is not tagged, because it is conditional on `AlgebraicGeometry.HasQuasiFiniteSlices`; the
tagged, unconditional form is
`AlgebraicGeometry.exists_flat_locallyQuasiFinite_factorization_through`. -/
theorem exists_flat_locallyQuasiFinite_factorization_through_of_hasQuasiFiniteSlices
    (h0570 : HasQuasiFiniteSlices.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (s : S) (hs : s ∈ Set.range f) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S) (h : S' ⟶ X),
      h ≫ f = g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
        LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ s ∈ Set.range g := by
  obtain ⟨x₀, rfl⟩ := hs
  let hf : ∀ y : S, IsLocallyNoetherian (f.fiber y) := fun y =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y
  let A : Set (f.fiber (f x₀)) :=
    (f.fiberι (f x₀)) ⁻¹' {x : X | f.IsCohenMacaulayAt hf x}
  have hD : Dense A := dense_cohenMacaulayAt_fiber f (f x₀)
  have hO : IsOpen {x : X | f.IsCohenMacaulayAt hf x} := isOpen_setOf_isCohenMacaulayAt f
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x₀)) := by
    change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x₀)))
    infer_instance
  let : JacobsonSpace (f.fiber (f x₀)) :=
    LocallyOfFiniteType.jacobsonSpace (f.fiberToSpecResidueField (f x₀))
  let : Nonempty (f.fiber (f x₀)) := ⟨f.asFiber x₀⟩
  obtain ⟨y, hyA, hyclosed⟩ := nonempty_inter_closedPoints hD.nonempty
    (hO.preimage (f.fiberι (f x₀)).continuous).isLocallyClosed
  let x : X := f.fiberι (f x₀) y
  have hfx : f x = f x₀ := by
    change (f.fiberι (f x₀) ≫ f) y = f x₀
    rw [f.fiber_fac]
    simp
  have hCM : f.IsCohenMacaulayAt hf x := hyA
  have hsets : f ⁻¹' {f x₀} = f ⁻¹' {f x} := by
    ext t
    simp [hfx]
  let e : f.fiber (f x₀) ≃ₜ f.fiber (f x) :=
    (f.fiberHomeo (f x₀)).trans
      ((Homeomorph.setCongr hsets).trans (f.fiberHomeo (f x)).symm)
  have heq : e y = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    simp [e, x, Homeomorph.setCongr]
  have hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
    simpa [heq] using e.isClosedMap {y} (mem_closedPoints_iff.mp hyclosed)
  obtain ⟨Z, i, z, -, hiz, hflat, hlfp, hqf⟩ :=
    h0570 f inferInstance x ⟨hf, hCM⟩ hclosed
  refine ⟨Z, i ≫ f, i, rfl, hflat, hlfp, inferInstance, hqf, ⟨z, ?_⟩⟩
  change f (i z) = f x₀
  rwa [hiz]

end AlgebraicGeometry

end
