module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# Reducing the direct image of coherent sheaves along a quasi-finite morphism to the finite case

Let `π : X ⟶ Y` and `pY : Y ⟶ Z` be morphisms of algebraic spaces such that `π ≫ pY` is proper
and `pY` is separated. Then `π` is finite as soon as it is locally quasi-finite, and of finite
presentation as soon as `π ≫ pY` is locally of finite presentation and `pY` is locally of finite
type.

## Main results

* `AlgebraicGeometry.Space.isFinite_of_comp_isProper_of_isSeparated_of_isLocallyQuasiFinite`:
  a locally quasi-finite morphism `π : X ⟶ Y` of algebraic spaces over an algebraic space `Z`
  whose source is proper over `Z` and whose target is separated over `Z` is finite.
* `AlgebraicGeometry.Space.isFinitePresentation_of_comp_isProper_of_isSeparated`: a morphism
  `π : X ⟶ Y` of algebraic spaces over `Z` whose source is locally of finite presentation and
  proper over `Z` and whose target is locally of finite type and separated over `Z` is of finite
  presentation.
* `AlgebraicGeometry.Space.isFinite_comp_of_isLocallyQuasiFinite_of_comp_isProper_of_isSeparated`:
  the composite of two locally quasi-finite morphisms whose source is proper over `Z` and whose
  final target is separated over `Z` is finite.

## References

* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `π : X ⟶ Y` and `pY : Y ⟶ Z` be morphisms of algebraic spaces over `S`. If the composite
`X ⟶ Z` is proper, `pY` is separated and `π` is locally quasi-finite, then `π` is finite. -/
@[stacks 0DN9 "the reduction of the proof to the finite case: a locally quasi-finite morphism \
whose source is proper and whose target is separated over the base is finite"]
theorem isFinite_of_comp_isProper_of_isSeparated_of_isLocallyQuasiFinite
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (π : X ⟶ Y) (pY : Y ⟶ Z)
    (hXZ : IsProper B S hS (π ≫ pY)) (hpY : IsSeparated B S hS pY)
    (hπ : IsLocallyQuasiFinite B S hS π) :
    IsFinite B S hS π :=
  isFinite_of_isProper_of_isLocallyQuasiFinite B S hS hX hY π
    (isProper_of_comp_of_isSeparated B S hS hX hY hZ π pY hXZ hpY) hπ

/-- Let `π : X ⟶ Y` and `pY : Y ⟶ Z` be morphisms of algebraic spaces over `S`. If the composite
`X ⟶ Z` is locally of finite presentation and proper and `pY` is locally of finite type and
separated, then `π` is of finite presentation. -/
@[stacks 0DN9 "the finite presentation of π in the reduction to the finite case"]
theorem isFinitePresentation_of_comp_isProper_of_isSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (π : X ⟶ Y) (pY : Y ⟶ Z)
    (hXZfp : IsLocallyOfFinitePresentation B S hS (π ≫ pY))
    (hXZ : IsProper B S hS (π ≫ pY)) (hpYft : IsLocallyOfFiniteType B S hS pY)
    (hpY : IsSeparated B S hS pY) :
    IsFinitePresentation B S hS π :=
  have hproper := isProper_of_comp_of_isSeparated B S hS hX hY hZ π pY hXZ hpY
  ⟨isLocallyOfFinitePresentation_of_comp B S hS hX hY hZ π pY hXZfp hpYft, hproper.2.1.2,
    isQuasiSeparated_of_isSeparated B S hS hproper.1⟩

/-- Let `i : W ⟶ X`, `π : X ⟶ Y` and `pY : Y ⟶ Z` be morphisms of algebraic spaces over `S`. If
`i` and `π` are locally quasi-finite, the composite `W ⟶ Z` is proper and `pY` is separated, then
`i ≫ π` is finite. -/
@[stacks 0DN9 "the finiteness of the composite Z ⟶ X_T ⟶ Y_T in the first paragraph of the \
proof, the composite being locally quasi-finite"]
theorem isFinite_comp_of_isLocallyQuasiFinite_of_comp_isProper_of_isSeparated
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (i : W ⟶ X) (π : X ⟶ Y) (pY : Y ⟶ Z)
    (hi : IsLocallyQuasiFinite B S hS i) (hπ : IsLocallyQuasiFinite B S hS π)
    (hWZ : IsProper B S hS (i ≫ π ≫ pY)) (hpY : IsSeparated B S hS pY) :
    IsFinite B S hS (i ≫ π) :=
  isFinite_of_comp_isProper_of_isSeparated_of_isLocallyQuasiFinite B S hS hW hY hZ (i ≫ π) pY
    (by rwa [Category.assoc]) hpY
    (isLocallyQuasiFinite_comp B S hS hW hX hY i π hi hπ)

end AlgebraicGeometry.Space

end
