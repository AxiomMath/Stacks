module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# The projective line is normal, and a finite birational morphism onto it is an isomorphism

The projective line `AlgebraicGeometry.projectiveLineProj k = Proj k[T₀, T₁]` over a field `k` is
a normal scheme. Consequently, by [Stacks, Tag 0AB1], an integral (in particular a finite)
birational morphism of integral schemes onto a scheme presented as the projective line is an
isomorphism.

## Main results

* `Stacks.ResolutionOfSurfaces.isNormal_projectiveLineProj` — the projective line
  `Proj k[T₀, T₁]` over a field is a normal scheme.
* `Stacks.ResolutionOfSurfaces.isNormal_of_iso_projectiveLineProj` — so is any scheme presented
  as the projective line.
* `Stacks.ResolutionOfSurfaces.isIso_of_isIntegralHom_of_isBirational_to_projectiveLineProj` —
  an integral birational morphism from an integral scheme to the projective line is an
  isomorphism.
* `Stacks.ResolutionOfSurfaces.isIso_of_isIntegralHom_of_isBirational_of_iso_projectiveLineProj`
  and `Stacks.ResolutionOfSurfaces.isIso_of_isFinite_of_isBirational_of_iso_projectiveLineProj`
  — the same with the target only presented as the projective line, in the integral and in the
  finite form.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Normality of the projective line -/

/-- **The projective line over a field is normal**, in the `Proj` model
`AlgebraicGeometry.projectiveLineProj k = Proj k[T₀, T₁]`. -/
public theorem isNormal_projectiveLineProj (k : Type u) [Field k] :
    IsNormal (projectiveLineProj k) := by
  have hbase : IsNormal (Spec (CommRingCat.of k)) := isNormal_spec_of_isIntegrallyClosed k
  have hproj : IsNormal (projectiveSpaceOverRing 1 (CommRingCat.of k)) :=
    isNormal_of_smooth (projectiveSpaceOver 1 (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k))
  exact isNormal_of_iso
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1).iso.symm

/-- **A scheme isomorphic to the projective line over a field is normal.** -/
public theorem isNormal_of_iso_projectiveLineProj (k : Type u) [Field k] {E : Scheme.{u}}
    (ε : projectiveLineProj k ≅ E) : IsNormal E :=
  have : IsNormal (projectiveLineProj k) := isNormal_projectiveLineProj k
  isNormal_of_iso ε.symm

/-! ### Finite birational morphisms onto the projective line -/

/-- **An integral birational morphism from an integral scheme onto the projective line over a
field is an isomorphism.** -/
public theorem isIso_of_isIntegralHom_of_isBirational_to_projectiveLineProj (k : Type u)
    [Field k] {E : Scheme.{u}} (g : E ⟶ projectiveLineProj k) [IsIntegral E] [IsIntegralHom g]
    (hg : IsBirational g) : IsIso g :=
  have : IsNormal (projectiveLineProj k) := isNormal_projectiveLineProj k
  isIso_of_isIntegralHom_of_isBirational_of_isNormal g hg

/-- **An integral birational morphism of integral schemes onto a scheme presented as the
projective line is an isomorphism:** given `ε : 𝐏¹_k ≅ E'`, an integral birational morphism
`g : E ⟶ E'` of integral schemes is an isomorphism. -/
public theorem isIso_of_isIntegralHom_of_isBirational_of_iso_projectiveLineProj (k : Type u)
    [Field k] {E E' : Scheme.{u}} (g : E ⟶ E') [IsIntegral E] [IsIntegral E'] [IsIntegralHom g]
    (ε : projectiveLineProj k ≅ E') (hg : IsBirational g) : IsIso g :=
  have : IsNormal E' := isNormal_of_iso_projectiveLineProj k ε
  isIso_of_isIntegralHom_of_isBirational_of_isNormal g hg

/-- **A finite birational morphism of integral schemes onto a scheme presented as the projective
line is an isomorphism.** -/
public theorem isIso_of_isFinite_of_isBirational_of_iso_projectiveLineProj (k : Type u) [Field k]
    {E E' : Scheme.{u}} (g : E ⟶ E') [IsIntegral E] [IsIntegral E'] [IsFinite g]
    (ε : projectiveLineProj k ≅ E') (hg : IsBirational g) : IsIso g :=
  isIso_of_isIntegralHom_of_isBirational_of_iso_projectiveLineProj k g ε hg

end Stacks.ResolutionOfSurfaces

end
