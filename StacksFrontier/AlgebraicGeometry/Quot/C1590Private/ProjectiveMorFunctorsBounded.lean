module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism

/-!
# Size-bounded algebraicity statements for the diagonal of `Curves` (towards Stacks 0D53)

The diagonal of the stack of curves is reduced, in
`StacksFrontier/AlgebraicGeometry/Quot/C1590Private/CurvesDiagonalReduction.lean`, to the statement
that the relative morphism functors `Mor_U(F, G)` of families of curves are algebraic spaces.
That statement is proved by gluing along an étale covering of `U`, indexed by the points of `U`,
by affine schemes over which both families are H-projective. Such an index is not bounded by the
cofinality of the cutoff of the site, so the gluing needs the pieces to have atlases of uniformly
bounded size, and this file records the two statements of that shape that the proof passes
through.

* `AlgebraicGeometry.C1590Private.ProjectiveSpaceHilbertModelsBounded`: for every `n`, the Hilbert
  functors of `ℙⁿ_U ⟶ U` over affine objects `U` of the site of bounded size have algebraic models
  with étale atlases of bounded size.
* `AlgebraicGeometry.C1590Private.ProjectiveMorFunctorsBounded`: over affine objects `U` of the
  site of bounded size, the relative morphism functors `Mor_U(Z₁, Z₂)` of H-projective schemes `Z₁`
  (flat, proper and of finite presentation) and `Z₂` (proper and of finite presentation) are
  algebraic spaces with étale atlases of bounded size.

Both are `Prop`s: nothing here is assumed. The first is proved from the construction of the
Hilbert scheme of `ℙⁿ_ℤ`, whose base changes give the models over every `U`; the second follows
from the first by Stacks 0DPF and Stacks 0D1B.

## References

* [Stacks Project, Tag 0D53](https://stacks.math.columbia.edu/tag/0D53)
* [Stacks Project, Tag 0DPF](https://stacks.math.columbia.edu/tag/0DPF)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Hilbert models of projective spaces with atlases of bounded size.** For every `n` and every
cardinal `μ` below the cutoff of the site there is a cardinal `κ` below the cutoff such that for
every affine object `U` of the big fppf site over `Spec ℤ` of size at most `μ`, the Hilbert
presheaf of `ℙⁿ_U ⟶ U` (Stacks 0CZY) has a model in the universe of the site which is an
algebraic space with a surjective étale atlas of size at most `κ`. -/
def ProjectiveSpaceHilbertModelsBounded : Prop :=
  ∀ (n : ℕ) (μ : Cardinal.{u}), μ < B.cutoff → ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
    ∀ (U : BigFppfOver B integerBase hZ),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) →
      ((BigFppfOver.toScheme B integerBase hZ).obj U).size ≤ μ →
      ∃ (M : Space.HilbertPresheafModel
          (schemeSpaceMap (ProjectiveQuot.projectiveSiteStructure B n U)))
        (A : BigFppfOver B integerBase hZ) (a : yoneda.obj A ⟶ M.presheaf),
        IsAlgebraicSpace B integerBase hZ M.presheaf ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B integerBase hZ))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B integerBase hZ))) a ∧
        ((BigFppfOver.toScheme B integerBase hZ).obj A).size ≤ κ

/-- **Relative morphism functors of H-projective schemes with atlases of bounded size.** For
every cardinal `μ` below the cutoff of the site there is a cardinal `κ` below the cutoff with the
following property. Let `U` be an affine object of the big fppf site over `Spec ℤ` of size at most
`μ`, and let `q₁ : Z₁ ⟶ U` and `q₂ : Z₂ ⟶ U` be H-projective, with `q₁` flat, proper and of
finite presentation and `q₂` proper and of finite presentation as morphisms of algebraic spaces.
Then `Mor_U(Z₁, Z₂)` (Stacks 05Y2) is an algebraic space with a surjective étale atlas of size at
most `κ`. -/
def ProjectiveMorFunctorsBounded : Prop :=
  ∀ μ : Cardinal.{u}, μ < B.cutoff → ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
    ∀ (U Z₁ Z₂ : BigFppfOver B integerBase hZ) (q₁ : Z₁ ⟶ U) (q₂ : Z₂ ⟶ U),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) →
      ((BigFppfOver.toScheme B integerBase hZ).obj U).size ≤ μ →
      IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q₁) →
      IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q₂) →
      Space.IsFlat B integerBase hZ (yoneda.map q₁) →
      Space.IsProper B integerBase hZ (yoneda.map q₁) →
      Space.IsFinitePresentation B integerBase hZ (yoneda.map q₁) →
      Space.IsProper B integerBase hZ (yoneda.map q₂) →
      Space.IsFinitePresentation B integerBase hZ (yoneda.map q₂) →
      IsAlgebraicSpace B integerBase hZ
          (Space.relativeHom B integerBase hZ (yoneda.obj Z₁) (yoneda.obj Z₂) (yoneda.obj U)
            (yoneda.map q₁) (yoneda.map q₂) (isAlgebraicSpace_yoneda B integerBase hZ Z₁)
            (isAlgebraicSpace_yoneda B integerBase hZ Z₂)
            (isAlgebraicSpace_yoneda B integerBase hZ U)) ∧
        ∃ (A : BigFppfOver B integerBase hZ)
          (a : yoneda.obj A ⟶ Space.relativeHom B integerBase hZ (yoneda.obj Z₁) (yoneda.obj Z₂)
            (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
            (isAlgebraicSpace_yoneda B integerBase hZ Z₁)
            (isAlgebraicSpace_yoneda B integerBase hZ Z₂)
            (isAlgebraicSpace_yoneda B integerBase hZ U)),
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B integerBase hZ))) a ∧
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B integerBase hZ))) a ∧
          ((BigFppfOver.toScheme B integerBase hZ).obj A).size ≤ κ

end AlgebraicGeometry.C1590Private

end
