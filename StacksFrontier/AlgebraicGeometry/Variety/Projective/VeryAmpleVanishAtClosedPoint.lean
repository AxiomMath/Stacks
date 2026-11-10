module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.OffDiagonalIncidenceVariety
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.VeryAmpleVanishAtPoint
import StacksCore.Tactic.StacksAttribute

/-!
# A very ample section vanishing at a closed point over an algebraically closed field

[Stacks, Tag 0B58] produces a global section of a very ample invertible module vanishing at a
given **`k`-rational** point and at none of finitely many other given points, and it needs `k`
infinite. Over an algebraically closed field both hypotheses are automatic at *every* closed
point: an algebraically closed field is infinite, and a closed point of a scheme locally of
finite type over it has residue field the base field. This file records that form of the tag,
together with the version in which the avoided points are the generic points of the irreducible
components, which is the form the proof of [Stacks, Tag 0B5H] consumes.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `exists_globalSection_vanishing_at_isClosed`: **[Stacks, Tag 0B58] at a closed point over an
  algebraically closed field.**
* `exists_globalSection_vanishing_at_isClosed_nonvanishing_genericPoint`: the same section, with
  the avoided points taken to be the generic points of the irreducible components of the scheme.

## Implementation notes

`AlgebraicGeometry.IsRationalPoint` of
`StacksFrontier/AlgebraicGeometry/Variety/Projective/RationalPointHyperplane.lean` is by definition
the invertibility of `Spec.preimage (X.fromSpecResidueField x ≫ f)`, and that invertibility is
exactly what Mathlib's `AlgebraicGeometry.residueFieldIsoBase` is built from, so the first result
is that isomorphism read backwards. Mathlib supplies `Infinite k` from `IsAlgClosed k`, so no
hypothesis on the cardinality of the base field is needed either.

The generic points are enumerated by choosing, for each irreducible component, the generic point
that the sobriety of a scheme provides; there are finitely many components because the space is
Noetherian, and a `T0` space has at most one generic point for a given irreducible closed set, so
the choice is immaterial. The point `x` itself is excluded from the family of avoided points: the
section is to vanish at `x`, so no section could avoid `x`, and `x` is a generic point of a
component exactly when `{x}` is an irreducible component of the space.

## References

* [Stacks Project, Tag 0B58](https://stacks.math.columbia.edu/tag/0B58)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.Ample

universe u w

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0B58] at a closed point over an algebraically closed field.** Let `k` be an
algebraically closed field, `X` a scheme of finite type over `k`, `L` a very ample invertible
`𝒪_X`-module, `x` a closed point of `X` and `xs` finitely many points of `X` distinct from `x`.
Then some global section of `L` vanishes at `x` and at none of the `xs j`.

This is `exists_globalSection_vanishing_at_rationalPoint` with its two hypotheses on the base
field discharged: `x` is a rational point by `AlgebraicGeometry.isRationalPoint_of_isClosed`
(`StacksFrontier/AlgebraicGeometry/Intersection/Projections/OffDiagonalIncidenceVariety.lean`),
and an algebraically
closed field is infinite.

[Stacks, Tag 0B58] (not registered here: this is not the whole statement of the tag): the case of
a closed point over an algebraically closed field, where the rationality of the point and the
infinitude of the field are both automatic
-/
theorem exists_globalSection_vanishing_at_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L)
    {ι : Type w} [Finite ι] (x : X) (hx : IsClosed ({x} : Set X)) (xs : ι → X)
    (hne : ∀ j, x ≠ xs j) :
    ∃ s : Γ(L, ⊤), x ∉ nonvanishingLocus L s ∧ ∀ j, xs j ∈ nonvanishingLocus L s :=
  exists_globalSection_vanishing_at_rationalPoint f L hL x xs
    (isRationalPoint_of_isClosed k f x hx) hne

/-- **The section of [Stacks, Tag 0B58] at a closed point, avoiding the generic points.** Over an
algebraically closed field, for a very ample invertible `L` on a Noetherian scheme locally of
finite type and a closed point `x`, there is a global section of `L` vanishing at `x` and
vanishing at no generic point of an irreducible component other than `x` itself.

This is the choice the proof of [Stacks, Tag 0B5H] makes. The avoided points are finitely many
because a Noetherian space has finitely many irreducible components, and each component has a
generic point because a scheme is sober. -/
theorem exists_globalSection_vanishing_at_isClosed_nonvanishing_genericPoint
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] [QuasiCompact f] [NoetherianSpace X]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ s : Γ(L, ⊤), x ∉ nonvanishingLocus L s ∧
      ∀ Z ∈ irreducibleComponents X, ∀ y, IsGenericPoint y Z → y ≠ x →
        y ∈ nonvanishingLocus L s := by
  have : Finite (irreducibleComponents (X : Type u)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let gp : (irreducibleComponents (X : Type u)) → X := fun Z => Z.2.1.genericPoint
  obtain ⟨s, hsx, hsgen⟩ := exists_globalSection_vanishing_at_isClosed f L hL x hx
    (ι := {Z : (irreducibleComponents (X : Type u)) // gp Z ≠ x})
    (fun j => gp j.1) (fun j => j.2.symm)
  refine ⟨s, hsx, fun Z hZ y hy hyx => ?_⟩
  obtain rfl : gp ⟨Z, hZ⟩ = y :=
    (hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)).eq hy
  exact hsgen ⟨⟨Z, hZ⟩, hyx⟩

end AlgebraicGeometry

end
