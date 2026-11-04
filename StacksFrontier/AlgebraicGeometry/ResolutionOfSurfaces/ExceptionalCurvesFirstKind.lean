module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContraction
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# Contracting exceptional curves: the notions

Section 0C2I of the Stacks project ([Stacks, Tag 0C2I]) opens with two notions on a Noetherian
scheme `X`:

* a closed subscheme `E ⊆ X` is an *exceptional curve of the first kind* when it is an effective
  Cartier divisor, there is an isomorphism `𝐏¹_k ≅ E` for some field `k`, and the normal sheaf
  `𝒩_{E/X}` pulls back to `𝒪_{𝐏¹}(-1)`;
* *there exists a contraction of `E`* when there is a proper morphism `X ⟶ X'` carrying `E` to a
  closed point `x ∈ X'` with `𝒪_{X',x}` regular of dimension two, exhibiting `X` as the blowing up
  of `X'` at `x`.

The first is `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`; this file
registers it for the section and defines the second,
`AlgebraicGeometry.Scheme.IdealSheafData.ExistsContraction`, as the existence of a morphism
`AlgebraicGeometry.IsContractionOfExceptionalCurve`.

Between the two the section asserts, by Tag 0AGQ, that for a closed point `x` of a Noetherian
scheme `X'` with `𝒪_{X',x}` regular of dimension two, the exceptional fibre of the blowing up of
`X'` at `x` is an exceptional curve of the first kind. That is
`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal`, proved
for an arbitrary scheme `X'` with `k` the residue field at `x`, which this file registers for the
section; so a blowing up of this
kind is a contraction of an exceptional curve of the first kind
(`AlgebraicGeometry.existsContraction_exceptionalIdeal`).

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.ExistsContraction` — there exists a contraction of the
  closed subscheme cut out by an ideal sheaf.

## Implementation notes

`AlgebraicGeometry.IsContractionOfExceptionalCurve D b` records the whole blowing-up diagram: the
target is Noetherian, `b` is isomorphic over its target to the blowing up of a closed point `x`
with regular local ring of dimension two, and `D` is the inverse image of the ideal of `x`, so
that `E` is carried to `x`. Such a `b` is proper, a blowing up of a Noetherian scheme being
projective over its base (`AlgebraicGeometry.IsContractionOfExceptionalCurve.isProper`), so the
properness asked for in the source is a consequence rather than a condition.

## References

* [Stacks Project, Section 0C2I](https://stacks.math.columbia.edu/tag/0C2I)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

add_to_stacks 0C2I "an exceptional curve of the first kind: an effective Cartier divisor E with \
  an isomorphism 𝐏¹_k ≅ E under which the normal sheaf of E pulls back to 𝒪(-1)"
  AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

add_to_stacks 0C2I "the exceptional fibre E of the blowing up of X' at a closed point x with \
  O_{X',x} regular of dimension 2 is an exceptional curve of the first kind (from Tag 0AGQ)"
  Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal

/-- **There exists a contraction of `E`** (Section 0C2I): for the closed subscheme `E` of `X` cut
out by the ideal sheaf `D`, there is a morphism `X ⟶ X'` carrying `E` to a closed point `x` of a
Noetherian scheme `X'` with `𝒪_{X',x}` regular of dimension two, which exhibits `X` as the
blowing up of `X'` at `x`. -/
@[stacks 0C2I "there exists a contraction of E: a morphism X ⟶ X' to a Noetherian scheme \
carrying E to a closed point x with O_{X',x} regular of dimension 2 and exhibiting X as the \
blowing up of X' at x", sga "7 X 1.14" "partial"]
def Scheme.IdealSheafData.ExistsContraction {X : Scheme.{u}} (D : X.IdealSheafData) : Prop :=
  ∃ (X' : Scheme.{u}) (b : X ⟶ X'), IsContractionOfExceptionalCurve D b

/-- The blowing up of a Noetherian scheme in a closed point with regular local ring of dimension
two is a contraction of its exceptional divisor. -/
theorem existsContraction_exceptionalIdeal {Z : Scheme.{u}} [IsNoetherian Z] (z : Z)
    (hz : IsClosed ({z} : Set Z)) (hreg : IsRegularLocalRing (Z.presheaf.stalk z))
    (hdim : ringKrullDim (Z.presheaf.stalk z) = 2) :
    (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{z}, hz⟩ : TopologicalSpace.Closeds Z))).ExistsContraction :=
  ⟨Z, _, isContractionOfExceptionalCurve_blowUpToBase z hz hreg hdim⟩

end AlgebraicGeometry

end
