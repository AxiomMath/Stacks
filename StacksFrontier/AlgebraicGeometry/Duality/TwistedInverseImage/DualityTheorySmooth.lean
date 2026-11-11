module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheoryProperDuality
public import StacksFrontier.AlgebraicGeometry.Duality.SmoothProper.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekEtale
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonical
public import StacksCore.Tactic.StacksAttribute

/-!
# A duality theory: the upper shriek of a smooth proper morphism

Clause (9) of [Stacks, Section 0AU3]: for a smooth proper morphism `f : X ⟶ Y` of relative
dimension `d` of `FTS S`,

`f^!(-) ≅ Lf^*(-) ⊗ᴸ_{𝒪_X} Ω^d_{X/Y}[d]`

on `D⁺_QCoh(𝒪_Y)`. A smooth morphism is flat and of finite presentation, hence perfect, so
`μ_{f,-} : Lf^*(-) ⊗ᴸ f^!𝒪_Y ⟶ f^!(-)` is an isomorphism of functors on `D⁺_QCoh(𝒪_Y)`
([Stacks, Tag 0B6U] (e), `Stacks.Duality.upperShriekCompareWithPullbackPlusIso`); `f` being
proper, `f^!𝒪_Y = a(𝒪_Y)` (clause (2)), and `a(𝒪_Y) ≅ ∧^d Ω_{X/Y}[d]` is [Stacks, Tag 0BRT]
(`Stacks.Duality.singleFunctorExteriorPowerIsoRelativeDualizingComplex`), `Y` being Noetherian.

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left] [IsProper f.left]
  (j : CompactificationOf (Over.mk f.left))

/-- **`f^!𝒪_Y ≅ Ω^d_{X/Y}[d]`** for a smooth proper morphism `f` of relative dimension `d` of
`FTS S`, at any compactification: clause (2) and [Stacks, Tag 0BRT]. -/
def upperShriekStructureSheafIsoOfSmoothOfIsProper :
    ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)).obj ≅
      (DerivedCategory.singleFunctor X.left.Modules (-(d : ℤ))).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) d) :=
  (ObjectProperty.ι _).mapIso ((upperShriekPlusIsoRightAdjointOfIsProper f j _
      (twistedInverseImageAdjunction f.left
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f.left))).app
      (derivedStructureSheafPlus Y.left)) ≪≫
    (singleFunctorExteriorPowerIsoRelativeDualizingComplex f.left d).symm

/-- **`f^!(-) ≅ Lf^*(-) ⊗ᴸ Ω^d_{X/Y}[d]`** on `D⁺_QCoh(𝒪_Y)`, naturally, for a smooth proper
morphism `f` of relative dimension `d` of `FTS S` and any compactification. -/
def upperShriekIsoPullbackTensorOfSmoothOfIsProper :
    ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left ⋙ ObjectProperty.ι _) ⋙
      (derivedTensor X.left).flip.obj
        ((DerivedCategory.singleFunctor X.left.Modules (-(d : ℤ))).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) d)) ≅
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        upperShriek f j ⋙ ObjectProperty.ι _ :=
  haveI : Smooth f.left := SmoothOfRelativeDimension.smooth d f.left
  Functor.isoWhiskerLeft _
      ((derivedTensor X.left).flip.mapIso
        (upperShriekStructureSheafIsoOfSmoothOfIsProper f d j).symm) ≪≫
    Functor.isoWhiskerLeft
      ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left)
      (quasiCoherentDerivedTensorFlipCompιIso X.left
        ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left))).symm ≪≫
    Functor.isoWhiskerRight (upperShriekCompareWithPullbackPlusIso f j) (ObjectProperty.ι _)

/-- **Stacks Project, Section 0AU3, clause (9).** Let `S` be a Noetherian scheme and let
`f : X ⟶ Y` be a smooth proper morphism of relative dimension `d` of `FTS S`, with `f^!`
computed at any compactification. Then `f^!(-) ≅ Lf^*(-) ⊗ᴸ_{𝒪_X} Ω^d_{X/Y}[d]` as functors on
`D⁺_QCoh(𝒪_Y)`, where `Ω^d_{X/Y} = ∧^d Ω_{X/Y}` and `[d]` places it in degree `-d`. -/
@[stacks 0AU3 "clause (9): for a smooth proper morphism f of relative dimension d of FTS S and \
  any compactification, f^!(-) = Lf^*(-) tensor Omega^d_{X/Y}[d] as functors on D^+_QCoh(O_Y); \
  from Tag 0B6U (e) (f is perfect), clause (2) and Tag 0BRT"]
theorem nonempty_upperShriekIsoPullbackTensorOfSmoothOfIsProper :
    Nonempty (((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left ⋙ ObjectProperty.ι _) ⋙
      (derivedTensor X.left).flip.obj
        ((DerivedCategory.singleFunctor X.left.Modules (-(d : ℤ))).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) d)) ≅
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        upperShriek f j ⋙ ObjectProperty.ι _) :=
  ⟨upperShriekIsoPullbackTensorOfSmoothOfIsProper f d j⟩

end Stacks.Duality

end
