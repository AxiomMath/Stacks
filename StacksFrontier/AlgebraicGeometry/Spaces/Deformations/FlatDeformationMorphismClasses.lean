module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatDeformationOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleUniversallyInjectiveOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# Further properties of morphisms invariant under a flat deformation of algebraic spaces

Let `(f, f') : (X ⊂ X') ⟶ (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over a
thickening `B ⊂ B'`, with `Y'` locally of finite type over `B'`, `X'` flat and locally of finite
presentation over `B'`, `X = B ×_{B'} X'` and `Y = B ×_{B'} Y'`; this is
`AlgebraicGeometry.Space.FlatDeformationDiagram`. Each of the following properties holds for `f`
if and only if it holds for `f'`: representability, quasi-compactness, universal closedness,
(quasi-)separatedness, being a monomorphism, affineness, integrality, being locally of finite
type of relative dimension `d`, universal openness, properness and finiteness.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `relativelyRepresentable_iff_of_flatDeformationDiagram`: representability of `f` and of `f'`
  are equivalent.
* `isQuasiCompact_iff_of_flatDeformationDiagram`: quasi-compactness.
* `universallyClosed_iff_of_flatDeformationDiagram`: universal closedness.
* `isSeparated_iff_and_isQuasiSeparated_iff_of_flatDeformationDiagram`: separatedness and
  quasi-separatedness.
* `mono_iff_of_flatDeformationDiagram`: being a monomorphism.
* `isAffineHom_iff_of_flatDeformationDiagram`: affineness.
* `isIntegralHom_iff_of_flatDeformationDiagram`: integrality.
* `isLocallyOfFiniteType_and_hasRelativeDimension_iff_of_flatDeformationDiagram`: being
  locally of finite type of relative dimension `d`.
* `universallyOpen_iff_of_flatDeformationDiagram`: universal openness.
* `isProper_iff_of_flatDeformationDiagram`: properness.
* `isFinite_iff_of_flatDeformationDiagram`: finiteness.

## References

* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 0414](https://stacks.math.columbia.edu/tag/0414)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace FlatDeformationDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FlatDeformationDiagram B S hS)

/-- The source inclusion of a flat deformation diagram is a thickening morphism. -/
theorem isThickeningHom_iX : IsThickeningHom B S hS D.iX :=
  have := D.iX_mono
  (isThickeningHom_iff_of_mono D.iX).2 D.iX_thickening

/-- The target inclusion of a flat deformation diagram is a thickening morphism. -/
theorem isThickeningHom_iY : IsThickeningHom B S hS D.iY :=
  have := D.iY_mono
  (isThickeningHom_iff_of_mono D.iY).2 D.iY_thickening

/-- The horizontal square of a flat deformation diagram, as a commutative square of presheaves
with the morphism under study on top. -/
theorem f_comp_iY : D.f.hom ≫ D.iY.hom = D.iX.hom ≫ D.f'.hom :=
  (congrArg (fun k ↦ k.hom) D.comm_f).symm

/-- The morphism under study is the base change of its ambient deformation along the target
inclusion. -/
theorem isPullback_f : IsPullback D.iX.hom D.f.hom D.f'.hom D.iY.hom :=
  AlgebraicSpaces.isPullback_hom B S hS (D.isPullback_X.of_bot D.comm_f D.isPullback_Y)

/-- The ambient morphism `f'` of a flat deformation diagram is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_f' : IsLocallyOfFinitePresentation B S hS D.f'.hom :=
  isLocallyOfFinitePresentation_of_comp B S hS D.X'.2 D.Y'.2 D.B'.2 D.f'.hom D.g'.hom
    D.finitePresentation_X' D.finiteType_Y'

/-- The ambient morphism `f'` of a flat deformation diagram is locally of finite type. -/
theorem isLocallyOfFiniteType_f' : IsLocallyOfFiniteType B S hS D.f'.hom :=
  isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS D.isLocallyOfFinitePresentation_f'

/-- The morphism `f` of a flat deformation diagram is locally of finite type. -/
theorem isLocallyOfFiniteType_f : IsLocallyOfFiniteType B S hS D.f.hom :=
  IsLocallyOfFiniteType.of_isPullback B S hS D.isPullback_f.flip D.X'.2 D.Y'.2
    D.isLocallyOfFiniteType_f'

end FlatDeformationDiagram

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Representability of a morphism of algebraic spaces is invariant under a flat deformation. -/
@[stacks 0CGX "part (1): representable"]
theorem relativelyRepresentable_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    yoneda.relativelyRepresentable D.f.hom ↔ yoneda.relativelyRepresentable D.f'.hom :=
  relativelyRepresentable_iff_relativelyRepresentable_of_isClosedImmersion_square_unconditional
    B S hS D.X.2 D.X'.2 D.Y'.2 D.f.hom D.f'.hom D.isThickeningHom_iX.isClosedImmersion
    D.isThickeningHom_iX.surjective_pointsMap D.isThickeningHom_iY.isClosedImmersion D.f_comp_iY

/-- Quasi-compactness of a morphism of algebraic spaces is invariant under a flat deformation. -/
@[stacks 0CGX "part (5): quasi-compact"]
theorem isQuasiCompact_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsQuasiCompact B S hS D.f.hom ↔ IsQuasiCompact B S hS D.f'.hom :=
  isQuasiCompact_iff_isQuasiCompact_of_isClosedImmersion_square B S hS D.X.2 D.X'.2 D.Y.2 D.Y'.2
    D.f.hom D.f'.hom D.isThickeningHom_iX.isClosedImmersion
    D.isThickeningHom_iX.surjective_pointsMap D.isThickeningHom_iY.isClosedImmersion D.f_comp_iY

/-- Universal closedness of a morphism of algebraic spaces is invariant under a flat
deformation. -/
@[stacks 0CGX "part (6): universally closed"]
theorem universallyClosed_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    UniversallyClosed B S hS D.f.hom ↔ UniversallyClosed B S hS D.f'.hom :=
  universallyClosed_iff_universallyClosed_of_isClosedImmersion_square B S hS D.X.2 D.X'.2 D.Y.2
    D.Y'.2 D.f.hom D.f'.hom D.isThickeningHom_iX.isClosedImmersion
    D.isThickeningHom_iX.surjective_pointsMap D.isThickeningHom_iY.isClosedImmersion D.f_comp_iY

/-- Separatedness, and quasi-separatedness, of a morphism of algebraic spaces are each invariant
under a flat deformation. -/
@[stacks 0CGX "part (7): separated, and quasi-separated"]
theorem isSeparated_iff_and_isQuasiSeparated_iff_of_flatDeformationDiagram
    (D : FlatDeformationDiagram B S hS) :
    (IsSeparated B S hS D.f.hom ↔ IsSeparated B S hS D.f'.hom) ∧
      (IsQuasiSeparated B S hS D.f.hom ↔ IsQuasiSeparated B S hS D.f'.hom) :=
  ⟨isSeparated_iff_isSeparated_of_isClosedImmersion_square B S hS D.X.2 D.X'.2 D.Y.2 D.Y'.2
      D.f.hom D.f'.hom D.isThickeningHom_iX.isClosedImmersion
      D.isThickeningHom_iX.surjective_pointsMap D.isThickeningHom_iY.isClosedImmersion
      D.f_comp_iY,
    isQuasiSeparated_iff_isQuasiSeparated_of_isClosedImmersion_square B S hS D.X.2 D.X'.2 D.Y.2
      D.Y'.2 D.f.hom D.f'.hom D.isThickeningHom_iX.isClosedImmersion
      D.isThickeningHom_iX.surjective_pointsMap D.isThickeningHom_iY.isClosedImmersion
      D.f_comp_iY⟩

/-- Affineness of a morphism of algebraic spaces is invariant under a flat deformation. -/
@[stacks 0CGX "part (11): affine"]
theorem isAffineHom_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsAffineHom B S hS D.f.hom ↔ IsAffineHom B S hS D.f'.hom :=
  isAffineHom_iff_isAffineHom_of_isClosedImmersion_square_unconditional B S hS D.X'.2 D.Y'.2
    D.f.hom D.f'.hom D.isThickeningHom_iX.isClosedImmersion
    D.isThickeningHom_iX.surjective_pointsMap D.isThickeningHom_iY.isClosedImmersion D.f_comp_iY

/-- Universal openness of a morphism of algebraic spaces is invariant under a flat deformation. -/
@[stacks 0CGX "part (14): universally open"]
theorem universallyOpen_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    UniversallyOpen B S hS D.f.hom ↔ UniversallyOpen B S hS D.f'.hom :=
  universallyOpen_iff_universallyOpen_of_isClosedImmersion_square B S hS D.X.2 D.X'.2 D.Y.2
    D.Y'.2 D.f.hom D.f'.hom D.isThickeningHom_iX.isClosedImmersion
    D.isThickeningHom_iX.surjective_pointsMap D.isThickeningHom_iY.isClosedImmersion
    D.isThickeningHom_iY.surjective_pointsMap D.f_comp_iY

/-- Integrality of a morphism of algebraic spaces is invariant under a flat deformation. -/
theorem isIntegralHom_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsIntegralHom B S hS D.f.hom ↔ IsIntegralHom B S hS D.f'.hom :=
  isIntegralHom_iff_isIntegralHom_of_isClosedImmersion_square_unconditional
    B S hS D.X.2 D.X'.2 D.Y.2 D.Y'.2
    D.f.hom D.f'.hom D.isThickeningHom_iX.isClosedImmersion
    D.isThickeningHom_iX.surjective_pointsMap D.isThickeningHom_iY.isClosedImmersion D.f_comp_iY

/-- Being a monomorphism is invariant under a flat deformation of algebraic spaces. -/
@[stacks 0CGX "part (8): monomorphism"]
theorem mono_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    Mono D.f.hom ↔ Mono D.f'.hom := by
  refine ⟨fun hf ↦ ?_, fun hf' ↦ D.isPullback_f.flip.mono_fst_of_mono hf'⟩
  have hu : IsUnramified B S hS D.f.hom :=
    isUnramified_of_isLocallyOfFiniteType_of_mono B S hS D.f.hom D.isLocallyOfFiniteType_f hf
  have hu' : IsUnramified B S hS D.f'.hom :=
    (isUnramified_iff_isUnramified_deformation B S hS D).mp hu
  exact ((isUnramified_mono_iff_isUnramified_universallyInjective B S hS D.X'.2 D.Y'.2
    D.f'.hom).mpr ⟨hu', (universallyInjective_iff_of_flatDeformationDiagram B S hS D).mp
      (universallyInjective_of_mono B S hS D.f.hom hf)⟩).2

/-- Being locally of finite type of relative dimension `d` is invariant under a flat deformation of
algebraic spaces: the morphism under study is locally of finite type of relative dimension `d`
exactly when its ambient deformation is. -/
@[stacks 0CGX "part (13): locally of finite type of relative dimension d"]
theorem isLocallyOfFiniteType_and_hasRelativeDimension_iff_of_flatDeformationDiagram
    (D : FlatDeformationDiagram B S hS) (d : ℕ) :
    (IsLocallyOfFiniteType B S hS D.f.hom ∧ HasRelativeDimension d B S hS D.f.hom) ↔
      (IsLocallyOfFiniteType B S hS D.f'.hom ∧ HasRelativeDimension d B S hS D.f'.hom) := by
  have key (x : points B S hS D.X.1) :
      HasRelativeDimensionAt (d : ℕ∞) B S hS D.f'.hom (pointsMap B S hS D.X.1 D.iX.hom x) ↔
        HasRelativeDimensionAt (d : ℕ∞) B S hS D.f.hom x :=
    hasRelativeDimensionAt_iff_of_isPullback B S hS D.isPullback_f D.X'.2 D.Y.2 D.Y'.2
      D.isLocallyOfFiniteType_f' x (d : ℕ∞)
  refine ⟨fun ⟨_, h⟩ ↦ ⟨D.isLocallyOfFiniteType_f', fun y ↦ ?_⟩,
    fun ⟨_, h⟩ ↦ ⟨D.isLocallyOfFiniteType_f, fun x ↦ (key x).mp (h _)⟩⟩
  obtain ⟨x, rfl⟩ := D.isThickeningHom_iX.surjective_pointsMap y
  exact (key x).mpr (h x)

/-- Properness of a morphism of algebraic spaces is invariant under a flat deformation. -/
@[stacks 0CGX "part (19): proper"]
theorem isProper_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsProper B S hS D.f.hom ↔ IsProper B S hS D.f'.hom := by
  exact and_congr (isSeparated_iff_and_isQuasiSeparated_iff_of_flatDeformationDiagram B S hS D).1
    (and_congr (and_congr (iff_of_true D.isLocallyOfFiniteType_f D.isLocallyOfFiniteType_f')
      (isQuasiCompact_iff_of_flatDeformationDiagram B S hS D))
      (universallyClosed_iff_of_flatDeformationDiagram B S hS D))

/-- Finiteness of a morphism of algebraic spaces is invariant under a flat deformation. -/
@[stacks 0CGX "part (20): finite"]
theorem isFinite_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsFinite B S hS D.f.hom ↔ IsFinite B S hS D.f'.hom := by
  have hint := isIntegralHom_iff_of_flatDeformationDiagram B S hS D
  exact ⟨fun h ↦ isFinite_of_isIntegralHom_of_isLocallyOfFiniteType B S hS D.f'.hom D.X'.2
      D.Y'.2 (hint.mp h.isIntegralHom) D.isLocallyOfFiniteType_f',
    fun h ↦ isFinite_of_isIntegralHom_of_isLocallyOfFiniteType B S hS D.f.hom D.X.2 D.Y.2
      (hint.mpr h.isIntegralHom) D.isLocallyOfFiniteType_f⟩

end AlgebraicGeometry.Space

end
