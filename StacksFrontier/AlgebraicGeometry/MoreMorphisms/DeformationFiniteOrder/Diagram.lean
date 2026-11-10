module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Flat deformation diagrams

A *flat deformation diagram* is a morphism of thickenings from `X ⊂ X'` to `Y ⊂ Y'` over a
thickening `S ⊂ S'` of the base, in which the ambient target `Y'` is locally of finite type over
`S'`, the ambient source `X'` is flat and locally of finite presentation over `S'`, and both
unprimed schemes are the base changes of their primed counterparts along `S ⟶ S'`. This is the
standing situation in which the properties of `X ⟶ Y` and of its deformation `X' ⟶ Y'` are
compared.

The first thing one wants about such a diagram is that it does not change the fibres: the fibre
of `X' ⟶ Y'` over a point of `Y'` is canonically the fibre of `X ⟶ Y` over the corresponding
point of `Y`, because the source square is cartesian and the target thickening is a bijection on
points with isomorphisms on residue fields.

## Main definitions

* `Stacks.Thickenings.FlatDeformationDiagram` packages the six schemes, the three thickenings,
  the two horizontal morphisms, the two structure morphisms, and all the hypotheses.

## Main results

* `Stacks.Thickenings.isIso_residueFieldMap_of_surjective_stalkMap`: a morphism of schemes whose
  stalk map at a point is surjective induces an isomorphism on residue fields there.
* `Stacks.Thickenings.FlatDeformationDiagram.isIso_fiberMap`: the canonical map between
  corresponding scheme-theoretic fibres in a flat deformation diagram is an isomorphism.

## Implementation notes

The morphisms from `X` and `X'` to the bases are the composites through `Y` and `Y'`. The two
base-change identifications are recorded as cartesian squares by `CategoryTheory.IsPullback`,
so that no isomorphism to a particular pullback object has to be chosen.

The identification of fibres is likewise formulated as `IsIso` for the canonical pullback
comparison map rather than by exhibiting an inverse. Every point of the thickened target is the
image of a unique point of the original target, since the target thickening is a closed immersion
and surjective on points.

## References

* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- A morphism of thickenings over a base thickening, with flat, locally finitely presented
ambient source, locally finite type ambient target, and cartesian special fibres. -/
structure FlatDeformationDiagram where
  /-- The closed subscheme of the source thickening. -/
  X : Scheme.{u}
  /-- The ambient scheme of the source thickening. -/
  X' : Scheme.{u}
  /-- The closed subscheme of the target thickening. -/
  Y : Scheme.{u}
  /-- The ambient scheme of the target thickening. -/
  Y' : Scheme.{u}
  /-- The closed subscheme of the base thickening. -/
  S : Scheme.{u}
  /-- The ambient scheme of the base thickening. -/
  S' : Scheme.{u}
  /-- The source thickening. -/
  iX : X ⟶ X'
  /-- The target thickening. -/
  iY : Y ⟶ Y'
  /-- The base thickening. -/
  iS : S ⟶ S'
  /-- The morphism of interest. -/
  f : X ⟶ Y
  /-- The ambient deformation of the morphism of interest. -/
  f' : X' ⟶ Y'
  /-- The structure morphism of the target over the base. -/
  g : Y ⟶ S
  /-- The structure morphism of the ambient target over the ambient base. -/
  g' : Y' ⟶ S'
  /-- The source inclusion is a thickening. -/
  iX_thickening : IsThickening iX
  /-- The target inclusion is a thickening. -/
  iY_thickening : IsThickening iY
  /-- The base inclusion is a thickening. -/
  iS_thickening : IsThickening iS
  /-- The morphism of source and target thickenings commutes. -/
  comm_f : iX ≫ f' = f ≫ iY
  /-- The morphism to the base thickening commutes. -/
  comm_g : iY ≫ g' = g ≫ iS
  /-- `X` is the special fibre of `X'` over `S`. -/
  isPullback_X : IsPullback iX (f ≫ g) (f' ≫ g') iS
  /-- `Y` is the special fibre of `Y'` over `S`. -/
  isPullback_Y : IsPullback iY g g' iS
  /-- `Y' ⟶ S'` is locally of finite type. -/
  finiteType_Y' : LocallyOfFiniteType g'
  /-- `X' ⟶ S'` is flat. -/
  flat_X' : Flat (f' ≫ g')
  /-- `X' ⟶ S'` is locally of finite presentation. -/
  finitePresentation_X' : LocallyOfFinitePresentation (f' ≫ g')

/-- A morphism of schemes which is surjective on the stalk at a point induces an isomorphism of
residue fields at that point: the induced map of residue fields is a map of fields, hence
injective, and it is surjective because the residue maps are. -/
theorem isIso_residueFieldMap_of_surjective_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : Function.Surjective (f.stalkMap x)) : IsIso (f.residueFieldMap x) :=
  (ConcreteCategory.isIso_iff_bijective (f.residueFieldMap x)).2 ⟨
    RingHom.injective (f.residueFieldMap x).hom, by
      intro a
      obtain ⟨r, hr⟩ := X.residue_surjective x a
      obtain ⟨s, hs⟩ := h r
      refine ⟨Y.residue (f x) s, ?_⟩
      change (f.residueFieldMap x).hom ((Y.residue (f x)).hom s) = a
      rw [← RingHom.comp_apply]
      change (Y.residue (f x) ≫ f.residueFieldMap x) s = a
      rw [Scheme.residue_residueFieldMap]
      change (X.residue x).hom ((f.stalkMap x).hom s) = a
      rw [hs, hr]⟩

/-- The canonical map from a fibre of `f` to the corresponding fibre of `f'` in a flat
deformation diagram is an isomorphism. -/
theorem FlatDeformationDiagram.isIso_fiberMap (D : FlatDeformationDiagram.{u}) (y : D.Y) :
    IsIso (pullback.map D.f (D.Y.fromSpecResidueField y) D.f'
      (D.Y'.fromSpecResidueField (D.iY y)) D.iX
      (Spec.map (D.iY.residueFieldMap y)) D.iY
      D.comm_f.symm (by simp)) := by
  let : IsClosedImmersion D.iY := D.iY_thickening.1
  let : IsIso (D.iY.residueFieldMap y) :=
    isIso_residueFieldMap_of_surjective_stalkMap D.iY y (D.iY.stalkMap_surjective y)
  let : IsIso (Spec.map (D.iY.residueFieldMap y)) := by infer_instance
  have h : IsPullback D.iX D.f D.f' D.iY :=
    D.isPullback_X.of_bot D.comm_f D.isPullback_Y
  exact (AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback h y).isIso_fst_of_isIso

end Stacks.Thickenings

end
