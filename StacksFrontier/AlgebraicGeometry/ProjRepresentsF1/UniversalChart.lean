module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.UniversalClass
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartAgreement

/-!
# The universal class of Tag 01O4, chart by chart

`Stacks.AlgebraicGeometry.ProjRepresentsF1.pairClassifyingHom_universalPair` says that the
morphism classified by the universal invertible degree-one quotient is the identity of the
relative homogeneous spectrum. That is a statement about a glued morphism; this file reads it on
the affine charts of the base, where the classifying morphism is the *absolute* one of
[Stacks, Tag 01NA].

The glued morphism attached to a class of quadruples is pinned chart by chart
(`...RelativeProjQcohSheaf.Fd.ι_homDegreeOpen`), so the identity being the glued morphism of the
universal class says exactly that over each affine open `U` of the base the chart-wise class of
the universal class is classified by the inclusion of `X|_U` — equivalently, that the absolute
classifying morphism into `Proj Γ(U, 𝒜)` followed by the chart of `U` is that inclusion.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.classifyingHom_universalQuadrupleClass`: **the
  classifying morphism of the universal class of quadruples is the identity**, in the spelling
  of `...ProjRepresentsF1.classifyingHom`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.chartHom_universalQuadrupleClass`: **over an affine
  open of the base the universal class is classified by the inclusion** of the inverse image of
  that open.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.toProj_chartEquiv_universalQuadrupleClass`: the
  same with the chart-wise morphism unfolded to the absolute classifying morphism of
  [Stacks, Tag 01NA] into `Proj Γ(U, 𝒜)`, composed with the chart.

## Implementation notes

**The chart-wise class is a hypothesis, not a construction.** `...RelativeProjQcohSheaf.Fd.`
`ι_homDegreeOpen` is stated for an arbitrary chart-wise class `η` whose image under
`...RelativeProjQcohSheaf.Fd.chartClassInv` is the restriction of the given class, and such an
`η` exists by `...RelativeProjQcohSheaf.Fd.exists_chartClassInv_eq`; the statements below quantify
over `η` with that compatibility, which is the form that mentions no choice.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S)
  (X : Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData A)
  (hgen : IsGeneratedInDegreeOne A)

/-! ### The universal class is classified by the identity -/

/-- **The classifying morphism of the universal class of quadruples is the identity.** This is
the normalisation clause of Tag 01O4, stated for quadruples rather than pairs. -/
public theorem classifyingHom_universalQuadrupleClass :
    classifyingHom A X
        (⟨X.toBase, universalQuadrupleClass A X hgen⟩ :
          Fd (situationAlgebra A) (1 : ℤ) X.scheme) = 𝟙 X.scheme :=
  congrArg Subtype.val
    ((quadrupleClassEquiv A X hgen X.toBase).apply_symm_apply
      ⟨𝟙 X.scheme, Category.id_comp _⟩)

/-! ### The universal class on an affine chart of the base -/

/-- **Over an affine open of the base the universal class is classified by the inclusion.** Let
`U` be an affine open of `S` and let `η` be a chart-wise class for `𝒜|_U` whose image under
`...RelativeProjQcohSheaf.Fd.chartClassInv` is the restriction of the universal class to
`X|_U`. Then the chart-wise morphism of `η` is the inclusion of `X|_U` into `X`. -/
public theorem chartHom_universalQuadrupleClass (U : S.Opens) (hU : IsAffineOpen U)
    (η : Fd (situationAlgebra (A.restrict U.ι)) ((1 : ℕ) : ℤ) (X.toBase ⁻¹ᵁ U).toScheme)
    (hη : Fd.chartClassInv A U η =
      Fd.pullback (X.toBase ⁻¹ᵁ U).ι
        (⟨X.toBase, universalQuadrupleClass A X hgen⟩ :
          Fd (situationAlgebra A) (1 : ℤ) X.scheme)) :
    Fd.chartHom A U X hU Nat.one_pos _ η = (X.toBase ⁻¹ᵁ U).ι :=
  Eq.trans
    (Fd.ι_homDegreeOpen A X (k := 1) Nat.one_pos
      (⟨X.toBase, universalQuadrupleClass A X hgen⟩ :
        Fd (situationAlgebra A) (1 : ℤ) X.scheme) U hU η hη).symm
    (Eq.trans
      (congrArg ((X.toBase ⁻¹ᵁ U).ι ≫ ·)
        (classifyingHom_universalQuadrupleClass A X hgen))
      (Category.comp_id _))

/-- **The universal class on a chart, through the absolute universal property.** The same
equation with the chart-wise morphism unfolded by
`...RelativeProjQcohSheaf.Fd.chartHom_eq_toProj_comp_chart`: the absolute classifying morphism of
[Stacks, Tag 01NA] attached to the chart-wise class, read into `Proj Γ(U, 𝒜)` and then along the
chart of `U`, is the inclusion of `X|_U`. -/
public theorem toProj_chartEquiv_universalQuadrupleClass (U : S.Opens) (hU : IsAffineOpen U)
    (η : Fd (situationAlgebra (A.restrict U.ι)) ((1 : ℕ) : ℤ) (X.toBase ⁻¹ᵁ U).toScheme)
    (hη : Fd.chartClassInv A U η =
      Fd.pullback (X.toBase ⁻¹ᵁ U).ι
        (⟨X.toBase, universalQuadrupleClass A X hgen⟩ :
          Fd (situationAlgebra A) (1 : ℤ) X.scheme)) :
    toProj (A.grading U) (Fd.chartEquiv A U hU Nat.one_pos _ η) ≫ X.chart U hU =
      (X.toBase ⁻¹ᵁ U).ι :=
  Eq.trans
    (Fd.chartHom_eq_toProj_comp_chart A U X hU Nat.one_pos _ η).symm
    (chartHom_universalQuadrupleClass A X hgen U hU η hη)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
