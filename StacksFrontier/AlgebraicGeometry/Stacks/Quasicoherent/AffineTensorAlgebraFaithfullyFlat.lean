module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineTensorPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineTensorAlgebraUniversallyInjective
public import StacksFrontier.RingTheory.Flat.FaithfullyFlatOfSelfTensorBaseChange

/-!
# The algebra `C = F(g_{QCoh,*}𝒪_U)` is faithfully flat over `R`

Let `𝒳` be a Noetherian algebraic stack with affine diagonal, `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right
exact tensor functor commuting with direct sums and `g : U ⟶ 𝒳` a flat surjective morphism from an
affine scheme. The proof of Stacks 0GRQ shows that `R ⟶ C = F(g_{QCoh,*}𝒪_U)` is faithfully flat:
it is universally injective (Stacks 0GRL), and `C ⊗_R C ≅ C ⊗_A Γ(U ×_𝒳 U)` is flat over `C`
(`AlgebraicGeometry.Stack.AlgebraicStacks.selfTensorEquivBaseChange`), so Stacks 0GRM applies.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.faithfullyFlat_affineTensorAlgebra`: `R ⟶ C` is
  faithfully flat.

## References

* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
* [Stacks Project, Tag 0GRL](https://stacks.math.columbia.edu/tag/0GRL)
* [Stacks Project, Tag 0GRM](https://stacks.math.columbia.edu/tag/0GRM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u w w'

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : IsAffineHom B S hS g)
  {R : Type u} [CommRing R]
  (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Braided] [F.Additive]
  [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]

/-- **`R ⟶ C = F(g_{QCoh,*}𝒪_U)` is faithfully flat** (Stacks 0GRQ, proof). Here `𝒳` is a
Noetherian algebraic stack with affine (absolute) diagonal, `F` a right exact tensor functor
commuting with direct sums and `g : U ⟶ 𝒳` flat, surjective and affine with `U` affine. The map
is universally injective by Stacks 0GRL (`universallyInjective_affineTensorAlgebra`), and
`C ⊗_R C ≅ C ⊗_A Γ(U ×_𝒳 U)` with `Γ(U ×_𝒳 U)` flat over `A`, so Stacks 0GRM applies. -/
theorem faithfullyFlat_affineTensorAlgebra
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳) (hU : IsAffineOver B S hS U)
    (hflat : IsFlat B S hS g) (hsurj : IsSurjective B S hS g) :
    (algebraMap R (affineTensorAlgebra g hg F)).FaithfullyFlat := by
  let := (affineTensorRingHom g hg F).toAlgebra
  have := flat_globalSections_pullback_structureSheaf g hg hflat hU
  exact Algebra.faithfullyFlat_of_universallyInjective_of_selfTensorEquivBaseChange
    (universallyInjective_affineTensorAlgebra hΔ h𝒳 hU F g hflat hsurj).2
    (selfTensorEquivBaseChange g hg F hU)

end AlgebraicGeometry.Stack.AlgebraicStacks
