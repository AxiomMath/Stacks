module

public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge

/-!
# The twists on a relative projective spectrum: the statement, and its chart formulas

Let `S` be a scheme and `A` a commutative, nonnegatively graded, quasi-coherent graded
`𝒪_S`-algebra — Situation 01NN, in the sheaf-level form
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. Tag 01NR asserts that the
graded twists on the projective spectra of the affine section rings of `A` glue to a
quasi-coherent sheaf of graded algebras on the relative Proj of `A`, that the homogeneous
section maps glue with them, and that the resulting structure is unique up to a unique
compatible isomorphism.

`TwistData` is the complete structure Tag 01NR describes; `ChartData` and `IsGradedChartIso` are
its affine-chart half, and `IsUniqueTwistData` and `DeterminesChartIso` are its two uniqueness
assertions. The chart formulas for the product and for the unit, in every integer degree and on
every open of every chart, hold for an arbitrary `TwistData`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` and
  `absoluteTwistUnit`: the canonical product and unit of local sections of the twists on an
  absolute Proj.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra`: a sheaf of graded algebras
  on a scheme, read as one on the scheme's ringed site.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` and `ChartData.mapSection`: the
  degreewise identifications of the glued twists with the absolute twists on an affine chart,
  and the resulting comparison on sections.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.IsGradedChartIso`: the condition that those
  identifications respect the product and the unit.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`: the full structure of Tag 01NR.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.IsUniqueTwistData` and `DeterminesChartIso`: the
  tag's two uniqueness assertions, as propositions.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartIso_mul`: the chart
  identifications carry the canonical product of absolute twist sections to the product of the
  glued algebra, in all integer degrees.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartIso_one`: the same for the unit
  in degree zero.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

universe u w

section Absolute

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The canonical product of two local sections of the absolute Proj twists: tensor the two
sections, push into the sheafified tensor product, then apply the multiplication map
`𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)`. -/
public abbrev absoluteTwistProduct (i j : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 i).val.obj (op V)) (b : (twistingSheaf 𝒜 j).val.obj (op V)) :
    (twistingSheaf 𝒜 (i + j)).val.obj (op V) :=
  (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒜 i j).val.app
    (op V) (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
      (AlgebraicGeometry.Proj 𝒜).toRingedSpace
      (twistingSheaf 𝒜 i) (twistingSheaf 𝒜 j) (op V)
      (a ⊗ₜ[(AlgebraicGeometry.Proj 𝒜).presheaf.obj (op V)] b))

/-- The unit section of the degree-zero absolute Proj twist on an open: the restriction of the
global section attached to the homogeneous element `1` of degree `0`. -/
public abbrev absoluteTwistUnit (V : (AlgebraicGeometry.Proj 𝒜).Opens) :
    (twistingSheaf 𝒜 0).val.obj (op V) :=
  (twistingSheaf 𝒜 0).val.map (homOfLE le_top).op
    (degreeSection 𝒜 0 ⟨1, SetLike.one_mem_graded 𝒜⟩)

end Absolute

section Relative

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- A sheaf of graded algebras on a scheme, read as one on the scheme's ringed site. -/
public abbrev SchemeGradedAlgebra (X : Scheme.{u}) : Type (u + 1) :=
  SheafOfModules.GradedAlgebra.{u, u}
    (Stacks.CategoryTheory.RingedSite.ofScheme X).ringSheaf

/-- The graded-algebra identifications on the projective-spectrum charts of a relative Proj. -/
public structure ChartData (algebra : SchemeGradedAlgebra (relativeProj A).scheme) where
  /-- A projective-spectrum chart is an open immersion. -/
  chart_isOpenImmersion (U : S.Opens) (hU : IsAffineOpen U) :
    IsOpenImmersion ((relativeProj A).chart U hU)
  /-- Its image is precisely the inverse image of the affine base open. -/
  chart_range (U : S.Opens) (hU : IsAffineOpen U) :
    letI := chart_isOpenImmersion U hU
    ((relativeProj A).chart U hU) ''ᵁ ⊤ = (relativeProj A).toBase ⁻¹ᵁ U
  /-- The chart identification in each degree is an isomorphism of module sheaves between the
  restriction of the glued twist and the absolute twist on the chart. -/
  chartIso (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ) :
    letI := chart_isOpenImmersion U hU
    Scheme.Modules.restrict (algebra.piece n) ((relativeProj A).chart U hU) ≅
      twistingSheaf (A.grading U) n

variable {A}

/-- The section comparison induced by a chart identification, with sections of the restriction
identified with sections on the image open. -/
public def ChartData.mapSection {algebra : SchemeGradedAlgebra (relativeProj A).scheme}
    (D : ChartData A algebra) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (a : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    letI := D.chart_isOpenImmersion U hU
    (algebra.piece n).val.obj (op (((relativeProj A).chart U hU) ''ᵁ V)) :=
  let := D.chart_isOpenImmersion U hU
  (Scheme.Modules.restrictAppIso
    ((relativeProj A).chart U hU) (algebra.piece n) V).hom
      ((D.chartIso U hU n).inv.val.app (op V) a)

/-- The chart identifications are identifications of graded algebras when they carry the
canonical product and unit of the absolute twists to those of the glued algebra, on every open
of every chart and in every integer degree. -/
public def IsGradedChartIso {algebra : SchemeGradedAlgebra (relativeProj A).scheme}
    (D : ChartData A algebra) : Prop :=
  (∀ (U : S.Opens) (hU : IsAffineOpen U) (i j : ℤ)
      (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
      (a : (twistingSheaf (A.grading U) i).val.obj (op V))
      (b : (twistingSheaf (A.grading U) j).val.obj (op V)),
    letI := D.chart_isOpenImmersion U hU
    D.mapSection U hU (i + j) V (absoluteTwistProduct (A.grading U) i j V a b) =
      (algebra.mul i j).app
        (op (((relativeProj A).chart U hU) ''ᵁ V))
        (D.mapSection U hU i V a) (D.mapSection U hU j V b)) ∧
  (∀ (U : S.Opens) (hU : IsAffineOpen U)
      (V : (AlgebraicGeometry.Proj (A.grading U)).Opens),
    letI := D.chart_isOpenImmersion U hU
    D.mapSection U hU 0 V (absoluteTwistUnit (A.grading U) V) =
      algebra.one.eval (op (((relativeProj A).chart U hU) ''ᵁ V)))

variable (A)

/-- The twists on a relative Proj: the glued quasi-coherent graded algebra, its identifications
with the absolute twists on every affine chart, and the homogeneous-section map together with
its chart description. -/
public structure TwistData where
  /-- The integer-graded sheaf of algebras on the relative Proj. -/
  algebra : SchemeGradedAlgebra (relativeProj A).scheme
  /-- Every homogeneous twist is quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (algebra.piece n).IsQuasicoherent
  /-- Multiplication in the glued graded algebra is commutative. -/
  mul_comm (i j : ℤ) (V : (relativeProj A).scheme.Opensᵒᵖ)
      (a : (algebra.piece i).val.obj V) (b : (algebra.piece j).val.obj V) :
    HEq ((algebra.mul i j).app V a b) ((algebra.mul j i).app V b a)
  /-- The compatible identifications on the affine charts. -/
  chartData : ChartData A algebra
  /-- The chart comparisons respect the product and the unit. -/
  isGradedChartIso : IsGradedChartIso chartData
  /-- The degreewise map from the base algebra to the direct image of the twists. -/
  ψ (n : ℕ) : A.piece (n : ℤ) ⟶
    (Scheme.Modules.pushforward (relativeProj A).toBase).obj (algebra.piece (n : ℤ))
  /-- The homogeneous maps preserve the unit. -/
  ψ_one (U : S.Opens) :
    (ψ 0).val.app (op U) (A.one U) =
      algebra.one.eval (op ((relativeProj A).toBase ⁻¹ᵁ U))
  /-- The homogeneous maps preserve multiplication. -/
  ψ_mul (U : S.Opens) (n m : ℕ) (a : A.sectionPieces U n) (b : A.sectionPieces U m) :
    HEq
      ((ψ (n + m)).val.app (op U)
        ((Int.natCast_add n m).symm ▸ (A.mul (n : ℤ) (m : ℤ)).app U a b))
      ((algebra.mul (n : ℤ) (m : ℤ)).app
        (op ((relativeProj A).toBase ⁻¹ᵁ U))
          ((ψ n).val.app (op U) a) ((ψ m).val.app (op U) b))
  /-- Under the chart identification, the homogeneous-section map is the absolute degree-section
  map `degreeSection`. -/
  ψ_chart (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) (a : A.sectionPieces U n) :
    letI := chartData.chart_isOpenImmersion U hU
    chartData.mapSection U hU (n : ℤ) ⊤
      (degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩) =
      (chartData.chart_range U hU).symm ▸ ((ψ n).val.app (op U) a)

attribute [instance] TwistData.isQuasicoherent

namespace TwistData

variable {A} (D : TwistData A)

/-- The chart identifications of a `TwistData` preserve the product of twists in all integer
degrees and on every open of every chart. -/
public theorem chartIso_mul (U : S.Opens) (hU : IsAffineOpen U) (i j : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (a : (twistingSheaf (A.grading U) i).val.obj (op V))
    (b : (twistingSheaf (A.grading U) j).val.obj (op V)) :
    letI := D.chartData.chart_isOpenImmersion U hU
    D.chartData.mapSection U hU (i + j) V
      (absoluteTwistProduct (A.grading U) i j V a b) =
      (D.algebra.mul i j).app
        (op (((relativeProj A).chart U hU) ''ᵁ V))
        (D.chartData.mapSection U hU i V a) (D.chartData.mapSection U hU j V b) :=
  D.isGradedChartIso.1 U hU i j V a b

/-- The chart identifications of a `TwistData` preserve the unit in degree zero. -/
public theorem chartIso_one (U : S.Opens) (hU : IsAffineOpen U)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens) :
    letI := D.chartData.chart_isOpenImmersion U hU
    D.chartData.mapSection U hU 0 V (absoluteTwistUnit (A.grading U) V) =
      D.algebra.one.eval (op (((relativeProj A).chart U hU) ''ᵁ V)) :=
  D.isGradedChartIso.2 U hU V

end TwistData

/-- Any two sets of twist data on a relative Proj are carried into each other by a unique
isomorphism of graded algebras commuting with the homogeneous-section maps. -/
public def IsUniqueTwistData : Prop :=
  ∀ D E : TwistData A,
    ∃! e : D.algebra ≅ E.algebra,
      ∀ n : ℕ,
        D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
          (e.hom.app (n : ℤ)) = E.ψ n

/-- An isomorphism of graded algebras commuting with the homogeneous-section maps determines
every chart identification, in every integer degree. -/
public def DeterminesChartIso : Prop :=
  ∀ (D E : TwistData A) (e : D.algebra ≅ E.algebra),
    (∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e.hom.app (n : ℤ)) = E.ψ n) →
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ),
      letI := D.chartData.chart_isOpenImmersion U hU
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
        (e.hom.app n) ≫ (E.chartData.chartIso U hU n).hom =
          (D.chartData.chartIso U hU n).hom

end Relative

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
