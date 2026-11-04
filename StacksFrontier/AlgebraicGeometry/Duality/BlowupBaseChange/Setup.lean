module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSpaceEmbedding
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison

/-!
# The blowup of the affine plane in the origin

The data of [Stacks, Example 0AAC]: for a field `k`, `Y = 𝐀²_k = Spec k[x, y]`, the blowup
`f : X ⟶ Y` of `Y` in the origin, the origin `g : Spec k ⟶ Y`, and the closed immersion
`ι : X ⟶ 𝐏¹_Y` through which `f` factors.

## Main definitions

* `Stacks.Duality.BlowupBaseChange.blowup`: the blowup `X` of `Spec k[x, y]` in the ideal
  `(x, y)` of the origin.
* `Stacks.Duality.BlowupBaseChange.f`: the blowup morphism `X ⟶ 𝐀²_k`.
* `Stacks.Duality.BlowupBaseChange.g`: the origin `Spec k ⟶ 𝐀²_k`.
* `Stacks.Duality.BlowupBaseChange.ι`: the closed immersion `X ⟶ 𝐏¹_{𝐀²_k}` attached to the
  generators `x, y` of the ideal of the origin.

## References

* [Stacks Project, Tag 0AAC](https://stacks.math.columbia.edu/tag/0AAC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.BlowupBaseChange

variable (k : Type u) [Field k]

/-- The polynomial ring `k[x, y]`, the coordinate ring of `𝐀²_k`. -/
abbrev A : Type u := MvPolynomial (Fin 2) k

/-- The ideal `(x, y)` of the origin of `𝐀²_k`. -/
abbrev origin : Ideal (A k) := Ideal.span (Set.range MvPolynomial.X)

/-- The blowup `X` of `𝐀²_k` in the origin. -/
abbrev blowup : Scheme.{u} := Stacks.Blowup.blowUpSpec (origin k)

/-- The blowup morphism `f : X ⟶ 𝐀²_k`. -/
abbrev f : blowup k ⟶ Spec (CommRingCat.of (A k)) := Stacks.Blowup.toSpec (origin k)

/-- The origin `g : Spec k ⟶ 𝐀²_k`, the closed point `x = y = 0`. -/
abbrev g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (A k)) :=
  Spec.map (CommRingCat.ofHom MvPolynomial.constantCoeff)

/-- The closed immersion `ι : X ⟶ 𝐏¹_{𝐀²_k}` of the blowup into the projective line over the
base, attached to the generators `x, y` of the ideal of the origin. -/
abbrev ι : blowup k ⟶ AlgebraicGeometry.Proj (polyGrading (A k) 1) :=
  Stacks.Blowup.blowUpSpecToProjSpace (origin k) MvPolynomial.X
    (fun i => Ideal.subset_span ⟨i, rfl⟩) rfl

/-- The blowup `X` of `𝐀²_k` in the origin is a quasi-separated topological space. -/
instance : QuasiSeparatedSpace (blowup k) :=
  quasiSeparatedSpace_of_quasiSeparated (f k)

end Stacks.Duality.BlowupBaseChange
