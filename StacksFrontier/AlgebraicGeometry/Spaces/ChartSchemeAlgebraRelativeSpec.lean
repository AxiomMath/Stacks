module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebra

/-!
# The relative spectrum of a quasi-coherent algebra on an algebraic space, over a chart

Let `X` be an algebraic space, `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras on its
small étale site, and `V` an étale scheme chart of `X`.
`AlgebraicGeometry.Space.chartSchemeAlgebra` carries `A` to a quasi-coherent sheaf of algebras
on the Zariski site of the scheme `chartScheme V`, so the *scheme-level* relative spectrum of
Stacks 01LP applies to it.  This file forms that spectrum:

`\underline{Spec}_{chartScheme V}(A|_{chartScheme V}) ⟶ chartScheme V`,

an affine morphism of schemes.

This is the object the proof of Stacks 081V names first: the essential surjectivity of
`f ↦ f_* 𝒪_Y` on the algebraic space `X` starts from an étale scheme chart `U ⟶ X` and the
*scheme* `\underline{Spec}_U(A|_U)`, which is available only once `A|_U` is a scheme-level
algebra.  Nothing in this file is Stacks 081V: what it supplies is that first object and its
affineness over the chart, not the étale equivalence relation on the relation scheme nor the
quotient.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpec`: the relative spectrum over a chart's scheme of
  the chart restriction of a quasi-coherent `𝒪_X`-algebra.
* `AlgebraicGeometry.Space.chartRelativeSpecToChart`: its structure morphism to the chart's
  scheme.
* `AlgebraicGeometry.Space.chartRelativeSpecAffineOver`: the same, as an object of the schemes
  affine over the chart's scheme.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_chartRelativeSpecToChart`: the structure morphism is an
  affine morphism of schemes.
* `AlgebraicGeometry.Space.isAffineOpen_preimage_chartRelativeSpecToChart`: Stacks 01LX (1) for
  it — the preimage of an affine open of the chart's scheme is affine.

## Implementation notes

Quasi-coherence of the restricted algebra is an instance argument of
`Stacks.AffineAlgebraEquivalence.relativeSpec`, and
`AlgebraicGeometry.Space.isQuasicoherent_chartSchemeAlgebra` is a theorem, so it is supplied by
`haveI` inside each declaration rather than as an instance argument; the hypothesis that `A` is
quasi-coherent is likewise a plain argument.  This keeps instance search out of the two
definitionally-equal-but-not-syntactically-equal spellings of the module category over the small
étale site, which it cannot resolve.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (V : SmallEtale B S hS X.1)

/-- **The relative spectrum over a chart's scheme of the chart restriction of a quasi-coherent
sheaf of `𝒪_X`-algebras.**

`AlgebraicGeometry.Space.chartSchemeAlgebra` makes `A|_{chartScheme V}` a quasi-coherent sheaf
of algebras on the Zariski site of the scheme `chartScheme V`, which is what the scheme-level
relative spectrum of Stacks 01LP takes. -/
def chartRelativeSpec : Scheme.{u} :=
  haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  Stacks.AffineAlgebraEquivalence.relativeSpec (chartSchemeAlgebra B S hS X A V)

/-- The structure morphism of `AlgebraicGeometry.Space.chartRelativeSpec` to the chart's
scheme. -/
def chartRelativeSpecToChart : chartRelativeSpec B S hS X A hA V ⟶ chartScheme V :=
  haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  Stacks.AffineAlgebraEquivalence.relativeSpecToBase (chartSchemeAlgebra B S hS X A V)

/-- **Stacks 01LX (1) for the relative spectrum over a chart:** the preimage of an affine open of
the chart's scheme is affine. -/
theorem isAffineOpen_preimage_chartRelativeSpecToChart (O : (chartScheme V).affineOpens) :
    IsAffineOpen (chartRelativeSpecToChart B S hS X A hA V ⁻¹ᵁ (O : (chartScheme V).Opens)) :=
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  Stacks.AffineAlgebraEquivalence.isAffineOpen_preimage_relativeSpecToBase
    (chartSchemeAlgebra B S hS X A V) O

/-- **The relative spectrum over a chart is affine over the chart's scheme.** -/
instance isAffineHom_chartRelativeSpecToChart :
    _root_.AlgebraicGeometry.IsAffineHom (chartRelativeSpecToChart B S hS X A hA V) :=
  haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase
    (chartSchemeAlgebra B S hS X A V)

/-- The relative spectrum over a chart, as an object of the category of schemes affine over the
chart's scheme. -/
def chartRelativeSpecAffineOver : _root_.AlgebraicGeometry.AffineOver (chartScheme V) :=
  ⟨Over.mk (chartRelativeSpecToChart B S hS X A hA V),
    isAffineHom_chartRelativeSpecToChart B S hS X A hA V⟩

/-- The object of `AlgebraicGeometry.Space.chartRelativeSpecAffineOver` is the structure
morphism of the relative spectrum. -/
@[simp]
theorem chartRelativeSpecAffineOver_obj_hom :
    (chartRelativeSpecAffineOver B S hS X A hA V).obj.hom =
      chartRelativeSpecToChart B S hS X A hA V :=
  rfl

end AlgebraicGeometry.Space

end
