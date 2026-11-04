module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness

/-!
# Generic flatness of a finite type morphism

A finite type morphism to a reduced scheme is flat and of finite presentation over a dense open
subset of its target. This is generic flatness, `AlgebraicGeometry.exists_dense_open_flat_`
`finitePresentation`, read off for the structure sheaf of the source in place of an arbitrary
quasi-coherent module of finite type; it is the form in which the spreading-out arguments about
fibres consume generic flatness, since they shrink the base until the morphism itself is flat and
of finite presentation and have no module to carry along.

## Main results

* `AlgebraicGeometry.exists_dense_open_flat_finitePresentation_structureSheaf`: the dense open
  subset of the target over which the morphism becomes flat and of finite presentation.

## Implementation notes

The restriction of `f` over an open subset `U` of the target is `f.resLE U (f ⁻¹ᵁ U) le_rfl`.
The structure sheaf of a scheme, viewed as a module over itself, is quasi-coherent and of finite
type, so generic flatness applies to it; only the two conclusions about the morphism are kept,
the two about the module being automatic for the structure sheaf.

## References

* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A finite type morphism to a reduced scheme is flat and of finite presentation over a dense
open subset of the target. -/
theorem exists_dense_open_flat_finitePresentation_structureSheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced Y]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : Y.Opens,
      Dense (U : Set Y) ∧
        Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∧
        FinitePresentation (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  let F : X.Modules := SheafOfModules.unit.{u} X.ringCatSheaf
  have : F.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have : F.IsFiniteType := structureSheaf_isFiniteType X
  obtain ⟨U, hU, hflat, hfp, -, -⟩ := exists_dense_open_flat_finitePresentation f F
  exact ⟨U, hU, hflat, hfp⟩

/-- Generic flatness applied simultaneously to `f` and to the reduced closed subscheme cut out by
a closed subset `Z` of its source: dense opens `U` and `V` of the base over which each of the two
morphisms to the base is flat and of finite presentation. -/
theorem exists_dense_opens_flat_source_and_closed {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (Z : Set X) (hZ : IsClosed Z) :
    ∃ U V : Y.Opens, Dense (U : Set Y) ∧ Dense (V : Set Y) ∧
      Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∧
      FinitePresentation (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∧
      Flat (((Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subschemeι ≫ f).resLE
        V (((Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subschemeι ≫ f) ⁻¹ᵁ V) le_rfl) ∧
      FinitePresentation (((Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subschemeι ≫ f).resLE
        V (((Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subschemeι ≫ f) ⁻¹ᵁ V) le_rfl) := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩
  let g : I.subscheme ⟶ Y := I.subschemeι ≫ f
  have : LocallyOfFiniteType g := inferInstance
  have : QuasiCompact g := inferInstance
  obtain ⟨U, hU, hflat, hfp⟩ := exists_dense_open_flat_finitePresentation_structureSheaf f
  obtain ⟨V, hV, hflatZ, hfpZ⟩ := exists_dense_open_flat_finitePresentation_structureSheaf g
  exact ⟨U, V, hU, hV, hflat, hfp, hflatZ, hfpZ⟩

end AlgebraicGeometry

end
