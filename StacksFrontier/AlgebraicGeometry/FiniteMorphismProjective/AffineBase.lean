module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Qcoh

/-!
# Over an affine base, the relative homogeneous spectrum is the chart at the top open

Tag 01NQ builds `Proj_S(𝒜)` by glueing the projective spectra `Proj Γ(U, 𝒜)` over the affine
opens `U` of `S`, and records each chart as a cartesian square over its affine open. **When `S`
is itself affine the chart over the top open is therefore an isomorphism**: its square is the
base change of `(⊤ : S.Opens).ι`, which is an isomorphism, and isomorphisms are stable under base
change. So over an affine base the relative homogeneous spectrum *is* `Proj` of the graded ring
of global sections, with its structure morphism, and Mathlib's whole `Proj` API applies to it.

This is recorded here because it is what connects Tag 01W8's projective bundle to the `𝐏ⁿ` of
Tag 01NF: over an affine base the bundle `𝐏(E) = Proj_S(Sym(E))` of
`Stacks.SymGraded.qcohProjectiveBundle` becomes an honest `AlgebraicGeometry.Proj`, so comparing
it with `Proj R[T₀, …, Tₙ]` is reduced to an isomorphism of graded rings.

## Main definitions

* `Stacks.FiniteMorphismProjective.projTopIso`: the chart at the top open, as an isomorphism
  `Proj Γ(⊤, 𝒜) ≅ Proj_S(𝒜)`.
* `Stacks.FiniteMorphismProjective.qcohProjectiveBundleProjTopIso`: the same for the projective
  bundle of a module on an affine scheme.

## Main results

* `Stacks.FiniteMorphismProjective.isIso_chart_top`: **over an affine base the chart at the top open
  is an isomorphism.**
* `Stacks.FiniteMorphismProjective.projTopIso_hom_toBase`,
  `Stacks.FiniteMorphismProjective.qcohProjectiveBundleProjTopIso_hom_toBase`: the identification is
  compatible with the structure morphisms, which is the commuting half of the chart square.

## Implementation notes

The statement is for an arbitrary `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData`,
not for the constructed `relativeProj`, because that is all the argument uses: the chart square
is a field of the structure. It therefore applies verbatim to
`Stacks.SymGraded.qcohProjectiveBundle` and to `Stacks.SymGraded.schemeProjectiveBundle`.

Quasi-coherence of the module is not assumed in the two statements about the bundle: it is not
needed for the bundle to be defined, only for it to be the bundle of that module rather than of
the associated sheaf of its global sections, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Qcoh.lean` record.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.FiniteMorphismProjective

universe u

variable {S : Scheme.{u}} [IsAffine S] (A : SheafGradedAlgebra S)

/-- **Over an affine base the chart at the top open is an isomorphism.** The chart square
exhibits it as the base change of the inclusion of the top open, which is an isomorphism. -/
public theorem isIso_chart_top (D : RelativeProjData A) :
    IsIso (D.chart ⊤ (isAffineOpen_top S)) := by
  have hι : IsIso (⊤ : S.Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  exact (MorphismProperty.isomorphisms Scheme).of_isPullback
    (D.chart_isPullback ⊤ (isAffineOpen_top S)).flip hι

/-- **Over an affine base, the relative homogeneous spectrum is `Proj` of the graded ring of
global sections**, by the chart at the top open. -/
public def projTopIso (D : RelativeProjData A) :
    AlgebraicGeometry.Proj (A.grading ⊤) ≅ D.scheme :=
  have := isIso_chart_top A D
  asIso (D.chart ⊤ (isAffineOpen_top S))

/-- The identification carries the structure morphism of `Proj Γ(⊤, 𝒜)` to the structure
morphism of the relative homogeneous spectrum. -/
public theorem projTopIso_hom_toBase (D : RelativeProjData A) :
    (projTopIso A D).hom ≫ D.toBase =
      projInclusionToOpen A ⊤ (isAffineOpen_top S) ≫ (⊤ : S.Opens).ι :=
  (D.chart_isPullback ⊤ (isAffineOpen_top S)).w

/-! ### The projective bundle over an affine base -/

/-- **The projective bundle of a module on an affine scheme is `Proj` of the graded ring of
global sections of its symmetric algebra.** -/
public def qcohProjectiveBundleProjTopIso {R : CommRingCat.{u}} (E : (Spec R).Modules) :
    AlgebraicGeometry.Proj ((Stacks.SymGraded.qcohSheafGradedAlgebra E).grading ⊤) ≅
      (Stacks.SymGraded.qcohProjectiveBundle E).scheme :=
  projTopIso _ _

/-- The identification of the projective bundle is compatible with its projection to the
base. -/
public theorem qcohProjectiveBundleProjTopIso_hom_toBase {R : CommRingCat.{u}}
    (E : (Spec R).Modules) :
    (qcohProjectiveBundleProjTopIso E).hom ≫ Stacks.SymGraded.qcohProjectiveBundleToBase E =
      projInclusionToOpen (Stacks.SymGraded.qcohSheafGradedAlgebra E) ⊤
          (isAffineOpen_top (Spec R)) ≫ (⊤ : (Spec R).Opens).ι :=
  projTopIso_hom_toBase _ _

end Stacks.FiniteMorphismProjective

end
