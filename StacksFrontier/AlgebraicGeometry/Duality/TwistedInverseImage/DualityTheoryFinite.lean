module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheoryProperDuality
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.FiniteTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FiniteOverNoetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# A duality theory: the upper shriek of a finite morphism

Clause (6) of [Stacks, Section 0AU3]: for a finite morphism `f : Y ⟶ X` of `FTS S`,

`f_* f^!(-) = R𝓗om_{𝒪_X}(f_*𝒪_Y, -)`

as functors `D⁺_QCoh(𝒪_X) ⥤ D(f_*𝒪_Y)`. A finite morphism is proper, so `f^!` is the right
adjoint `a` of `Rf_*` on `D⁺_QCoh(𝒪_X)` (clause (2),
`Stacks.Duality.upperShriekPlusIsoRightAdjointOfIsProper`), and `Φ ∘ a = R𝓗om(f_*𝒪_Y, -)` on
`D⁺_QCoh(𝒪_X)` is [Stacks, Tag 0AX2],
`AlgebraicGeometry.derivedPushforwardOverRingCompTwistedInverseImageIso`, where
`Φ : D_QCoh(𝒪_Y) ≌ D_QCoh(f_*𝒪_Y)` is the equivalence of [Stacks, Tag 0AVW] through which `f_*`
of an `𝒪_Y`-module is read as an `f_*𝒪_Y`-module. A finite morphism to a Noetherian scheme is
pseudo-coherent (`AlgebraicGeometry.pseudoCoherent_of_isFinite_of_isLocallyNoetherian`).

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0AX2](https://stacks.math.columbia.edu/tag/0AX2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : Y ⟶ X) [IsFinite f.left]
  (j : CompactificationOf (Over.mk f.left))

/-- **`f_* f^! ≅ R𝓗om(f_*𝒪_Y, -)`** on `D⁺_QCoh(𝒪_X)`, for a finite morphism `f : Y ⟶ X` of
`FTS S` and any compactification `j`. Here `f_*` lands in `D(f_*𝒪_Y)` through the equivalence
`Φ` of [Stacks, Tag 0AVW], and `R𝓗om(f_*𝒪_Y, -)` is read at the standard model and compared along
the identity-on-objects comparison of the two models. -/
def upperShriekFiniteIsoDerivedHomSheaf :
    haveI := pseudoCoherent_of_isFinite_of_isLocallyNoetherian f.left
    upperShriekPlus f j ⋙ ObjectProperty.ι _ ⋙
        (derivedQuasicoherentPushforwardOverRingEquivalence f.left).functor ⋙
          ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (structureSheafModelEquiv X.left).inverse ⋙
        derivedHomSheaf f.left ⋙ (pushforwardRingModelEquiv f.left).functor :=
  haveI := pseudoCoherent_of_isFinite_of_isLocallyNoetherian f.left
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (upperShriekPlusIsoRightAdjointOfIsProper f j _
      (twistedInverseImageAdjunction f.left
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f.left))) _ ≪≫
    Functor.associator _ _ _ ≪≫ derivedPushforwardOverRingCompTwistedInverseImageIso f.left

/-- **Stacks Project, Section 0AU3, clause (6).** Let `S` be a Noetherian scheme and let
`f : Y ⟶ X` be a finite morphism of `FTS S`, with `f^!` computed at any compactification. Then
`f_* f^!(-) = R𝓗om_{𝒪_X}(f_*𝒪_Y, -)` as functors `D⁺_QCoh(𝒪_X) ⥤ D(f_*𝒪_Y)`. -/
@[stacks 0AU3 "clause (6): for a finite morphism f : Y to X of FTS S and any compactification, \
  f_* f^! = RHom(f_* O_Y, -) as functors from D^+_QCoh(O_X) to D(f_* O_Y), f_* read as an \
  f_* O_Y-module through the equivalence of Tag 0AVW; from clause (2) and Tag 0AX2"]
theorem nonempty_upperShriekFiniteIsoDerivedHomSheaf :
    haveI := pseudoCoherent_of_isFinite_of_isLocallyNoetherian f.left
    Nonempty (upperShriekPlus f j ⋙ ObjectProperty.ι _ ⋙
        (derivedQuasicoherentPushforwardOverRingEquivalence f.left).functor ⋙
          ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (structureSheafModelEquiv X.left).inverse ⋙
        derivedHomSheaf f.left ⋙ (pushforwardRingModelEquiv f.left).functor) :=
  ⟨upperShriekFiniteIsoDerivedHomSheaf f j⟩

end Stacks.Duality

end
