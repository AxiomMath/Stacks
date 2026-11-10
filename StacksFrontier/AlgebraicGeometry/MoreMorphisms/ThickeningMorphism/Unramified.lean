module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Extension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.FiberCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Fibers
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SchemeModels
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Unramifiedness extends over a cartesian thickening

Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a commutative square of schemes identifying `X` with `Y ×_{Y'} X'`, in which the target
inclusion `j` is a thickening. Then `f` is unramified exactly when `f'` is, provided `f'` is
locally of finite type. The same equivalence holds for a cartesian morphism of thickenings of
algebraic spaces whose two component maps are locally of finite type.

## Main results

* `Stacks.Thickenings.IsThickening.unramified_of_isPullback`: unramifiedness passes from `f` to
  its deformation `f'`.
* `Stacks.Thickenings.IsThickening.unramified_iff_of_isPullback`: the resulting equivalence.
* `Stacks.Thickenings.CartesianFiniteTypeMorphism.unramified_iff`: **Stacks 0BPG**, part (5),
  the equivalence for a cartesian morphism of thickenings whose two component morphisms are
  locally of finite type.
* `AlgebraicGeometry.Space.isUnramified_iff_of_cartesianMorphismOfThickenings`:
  **Stacks 0BPJ**, part (5), the algebraic-space form of the equivalence.

## Implementation notes

No finiteness or flatness condition on the thickenings themselves is assumed, and `f` is not
assumed locally of finite type.

## References

* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
* [Stacks Project, Tag 02G7](https://stacks.math.columbia.edu/tag/02G7)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

variable {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}

/-- If the square `(i, f, f', j)` is cartesian, `j` is a thickening, `f'` is locally of finite
type and `f` is unramified, then `f'` is unramified. -/
theorem IsThickening.unramified_of_isPullback (hj : IsThickening j)
    (h : IsPullback i f f' j) [LocallyOfFiniteType f'] [Unramified f] : Unramified f' := by
  have : IsClosedImmersion j := hj.1
  refine AlgebraicGeometry.unramified_of_fibres f' fun y' ↦ ?_
  obtain ⟨y, rfl⟩ := hj.2 y'
  have : IsIso (j.residueFieldMap y) :=
    isIso_residueFieldMap_of_surjective_stalkMap j y (j.stalkMap_surjective y)
  have hcomm : Y.fromSpecResidueField y ≫ j =
      Spec.map (j.residueFieldMap y) ≫ Y'.fromSpecResidueField (j y) := by simp
  have hfib : Unramified (f.fiberToSpecResidueField y) := by
    change Unramified (pullback.snd f (Y.fromSpecResidueField y))
    exact unramified_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) inferInstance
  have hfiberMap : IsIso (pullback.map f (Y.fromSpecResidueField y) f'
      (Y'.fromSpecResidueField (j y)) i (Spec.map (j.residueFieldMap y)) j h.w.symm hcomm) :=
    (isPullback_fiberToSpecResidueField_of_isPullback h y).isIso_fst_of_isIso
  have hiso : Arrow.mk (f.fiberToSpecResidueField y) ≅
      Arrow.mk (f'.fiberToSpecResidueField (j y)) :=
    Arrow.isoMk (@asIso _ _ _ _ _ hfiberMap)
      (asIso (Spec.map (j.residueFieldMap y))) (pullback.lift_snd _ _ _)
  have : MorphismProperty.RespectsIso (@Unramified.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (unramified_iff_iso_coproduct_spectra_finite_separable (Y'.residueField (j y))
    (f'.fiberToSpecResidueField (j y))).mp
    ((MorphismProperty.arrow_mk_iso_iff (P := @Unramified.{u}) hiso).1 hfib)

/-- If the square `(i, f, f', j)` is cartesian, `j` is a thickening and `f'` is locally of
finite type, then `f` is unramified exactly when `f'` is. -/
theorem IsThickening.unramified_iff_of_isPullback (hj : IsThickening j)
    (h : IsPullback i f f' j) [LocallyOfFiniteType f'] : Unramified f ↔ Unramified f' :=
  ⟨fun _ ↦ hj.unramified_of_isPullback h,
    fun hf' ↦ AlgebraicGeometry.unramified_isStableUnderBaseChange.of_isPullback h hf'⟩

/-- Being unramified is invariant under a cartesian, locally finite type morphism of
thickenings. -/
@[stacks 0BPG "unramified"]
theorem CartesianFiniteTypeMorphism.unramified_iff (S : CartesianFiniteTypeMorphism.{u}) :
    Unramified S.f ↔ Unramified S.f' :=
  S.targetThickening.unramified_iff_of_isPullback S.cartesian.flip

end Stacks.Thickenings

/-! ### Algebraic spaces -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being unramified is invariant under a cartesian morphism of thickenings of algebraic spaces
whose two component maps are locally of finite type. -/
@[stacks 0BPJ "unramified"]
theorem isUnramified_iff_of_cartesianMorphismOfThickenings
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    IsUnramified B S hS T.f ↔ IsUnramified B S hS T.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianMorphismOfThickenings B S hS T _
    unramified_isEtaleLocalOnSourceAndTarget fun E => E.unramified_iff

end AlgebraicGeometry.Space

end
