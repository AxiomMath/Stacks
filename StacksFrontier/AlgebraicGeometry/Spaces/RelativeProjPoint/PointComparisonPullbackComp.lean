module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonQuasicoherent

/-!
# The scheme restriction maps of Stacks 084A are the composition comparisons of Stacks 03LU

For a morphism `τ : T' ⟶ T` of the site and scheme points `f`, `f' = f ∘ τ` of an algebraic space
`X`, the comparison `τ^*(f^*𝒜)_n ⟶ (f'^*𝒜)_n` of restricted algebras
(`AlgebraicGeometry.Space.pointComparison`), carried to the modules attached by Stacks 03DX (2), is
the composition comparison `φ^*(f^*𝒜_n) ≅ (φ ≫ f)^*𝒜_n` of inverse images of Stacks 03LU followed
by the transport along `φ ≫ f = f'`.

This is `modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_of_compat`
with the compatibility of the comparisons of direct images supplied by
`AlgebraicGeometry.Space.zariskiReadingDirectImageCompat`.

## Main results

* `modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison`:
  **the comparison of restricted algebras, carried to the attached modules, is the composition
  comparison of Stacks 03LU.**

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (τ : T' ⟶ T)

/-- **Bridge K: the scheme restriction maps of Stacks 084A are the Zariski readings of the
comparisons of Stacks 03LU.**  For `τ : T' ⟶ T` of the site and scheme points `f`, `f' = f ∘ τ` of
`X`, the comparison `τ^*(f^*𝒜)_n ⟶ (f'^*𝒜)_n` of restricted algebras
(`AlgebraicGeometry.Space.pointComparison`), carried to the attached modules of Stacks 03DX (2)
and read through `N ≅ (N_Zar)^a` at both ends and through `φ^*(M^a) ≅ (τ^*M)^a`, is the
composition comparison `φ^*(f^*𝒜_n) ≅ (φ ≫ f)^*𝒜_n` of Stacks 03LU followed by the transport along
`φ ≫ f = f'`. -/
theorem modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison
    {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    (modulePullback B S hS (representedSpaceMap B S hS τ)).map
        (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS τ
          (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map
          (ObjectProperty.homMk ((pointComparison A τ f f' hf).app n) :
            quasicoherentPullbackObj B S hS τ
              (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)) ⟶
            zariskiReadingQcoh T' ((etalePointAlgebra A T' f').piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n))).hom =
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
          (A.piece n) ≫ pullbackTransport (A.piece n) (pointHom_comp τ hf)) ≫
        (zariskiReadingQuasicoherentIso T' ((etalePointAlgebra A T' f').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n)).hom :=
  modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_of_compat τ
    (zariskiReadingDirectImageCompat τ) A hA f f' hf n

end AlgebraicGeometry.Space

end
