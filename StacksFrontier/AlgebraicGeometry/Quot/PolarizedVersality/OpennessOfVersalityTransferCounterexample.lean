module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.OpennessOfVersalityTransferCounterexampleFibre
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.OpennessOfVersalityTransferCounterexampleVersality

/-!
# Openness of versality does not transfer along algebraic 1-morphisms

Remark 0D4W of the Stacks project proposes, as route (b) to Lemma 0D4V, to deduce openness of
versality of `Polarized` from two facts: the forgetful 1-morphism
`Polarized ⟶ Spaces′_{fp,flat,proper}` is algebraic (Lemma 0D41), and the target satisfies
openness of versality (Lemma 0D3X, Remark 0D1P). This file shows that the inference those two
facts are used for is false in general: an algebraic 1-morphism `F : 𝒳 ⟶ 𝒴` of stacks in
groupoids, with `𝒴` satisfying openness of versality, can have a source `𝒳` which does not.

The counterexample, over `S = Spec k[s,t]` for any field `k`:

* `𝒳′` is the category of Stacks 07XR (`Deformation.Artin.artinAxiomsCategory`); it fails
  openness of versality (`Deformation.Artin.not_isOpenVersality_artinAxiomsCategory`): the slice
  `Spec k[s,t]/(s)` is versal at the origin and at no other point.
* `𝒲` is the sheaf of locally nilpotent functions and `𝒴 = 𝒳′ × 𝒲`
  (`AlgebraicGeometry.PolarizedVersality.OpennessTransfer.targetStack`). No object of `𝒴` is
  versal at any point
  (`AlgebraicGeometry.PolarizedVersality.OpennessTransfer.not_isVersalAt_targetBased`), so `𝒴`
  satisfies openness of versality vacuously.
* `F = (id, 0) : 𝒳′ ⟶ 𝒴` (`AlgebraicGeometry.PolarizedVersality.OpennessTransfer.zeroSection`) is
  algebraic, its base change along a point `(T₀, g)` of `𝒴` being the closed subscheme `V(g)` of
  `T₀` (`AlgebraicGeometry.PolarizedVersality.OpennessTransfer.isAlgebraicMorphism_zeroSection`).

## Main results

* `not_forall_hasOpenVersality_of_algebraic_of_hasOpenVersality` (in
  `AlgebraicGeometry.PolarizedVersality.OpennessTransfer`): the inference "`F` algebraic and `𝒴`
  has openness of versality, hence `𝒳` has openness of versality" fails for stacks in groupoids
  over the big fppf site of `Spec k[s,t]`.

## Implementation notes

The predicates are the library's: algebraicity is `AlgebraicGeometry.Stack.IsAlgebraicMorphism`
(Stacks 06CF), and openness of versality is `Deformation.Artin.HasOpenVersality` of the structure
functor composed with `Over.post B.inclusion`, exactly as in the registration of Stacks 0D4V
(`AlgebraicGeometry.hasOpenVersality_polarizedStackUnconditional`). The result refutes a proof
route, not the statement of the remark.

## References

* [Stacks Project, Tag 0D4W](https://stacks.math.columbia.edu/tag/0D4W)
* [Stacks Project, Tag 07XR](https://stacks.math.columbia.edu/tag/07XR)
* [Stacks Project, Tag 06CF](https://stacks.math.columbia.edu/tag/06CF)
-/

@[expose] public noncomputable section

universe u w wX wY

open CategoryTheory Deformation.Artin

namespace AlgebraicGeometry.PolarizedVersality.OpennessTransfer

/-- **Openness of versality does not transfer to the source of an algebraic 1-morphism** (the
second route of Stacks 0D4W). Over the big fppf site of `S = Spec k[s,t]`, for any field `k`, it
is not true that for every algebraic 1-morphism `F : 𝒳 ⟶ 𝒴` of stacks in groupoids, openness of
versality of `𝒴` implies openness of versality of `𝒳`. -/
theorem not_forall_hasOpenVersality_of_algebraic_of_hasOpenVersality
    {k : Type u} [Field k] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))) :
    ¬ ∀ (𝒳 : StackInGroupoids.{wX, u, u, u + 1, u + 1}
          (BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)
          (BigFppfOver.topology B _ hS))
        (𝒴 : StackInGroupoids.{wY, u, u, u + 1, u + 1}
          (BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)
          (BigFppfOver.topology B _ hS))
        (F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory),
        Stack.IsAlgebraicMorphism.{u, wX, wY, w} B _ hS F →
        HasOpenVersality (𝒴.toBasedCategory.p ⋙ Over.post B.inclusion) →
        HasOpenVersality (𝒳.toBasedCategory.p ⋙ Over.post B.inclusion) := fun h =>
  not_isOpenVersality_artinAxiomsCategory B hS
    (h (sourceStack B hS) (targetStack B hS) (zeroSection B hS)
      (isAlgebraicMorphism_zeroSection B hS) (hasOpenVersality_targetBased B hS))

end AlgebraicGeometry.PolarizedVersality.OpennessTransfer
