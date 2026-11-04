module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Diagram
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram

/-!
# Fibres along a cartesian thickening

A cartesian square

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

of schemes whose target inclusion `j` is a thickening does not change fibres: for every point
`y` of the smaller target the fibre of `f` over `y` and the fibre of `f'` over the image of `y`
are isomorphic, compatibly with their structure morphisms to the spectra of the residue fields,
which are themselves identified because a thickening induces an isomorphism of residue fields.

Consequently any property of morphisms of schemes which is invariant under isomorphism of arrows
holds for one of these two fibre morphisms exactly when it holds for the other. That is the form
in which the fibrewise criteria for flatness, smoothness, syntomicity and étaleness consume the
statement. Both standing situations of this directory give such a square: in a flat deformation
diagram and in a cartesian finite-order deformation diagram the morphism of special fibres is the
base change of its ambient deformation along the target thickening.

## Main definitions

* `Stacks.Thickenings.fiberMapOfIsPullback`: the canonical comparison morphism of fibres.
* `Stacks.Thickenings.fiberArrowIsoOfIsPullback`: the resulting isomorphism in the arrow
  category.

## Main results

* `Stacks.Thickenings.prop_fiberToSpecResidueField_iff_of_isPullback`: transfer of an
  isomorphism-invariant property of morphisms between corresponding fibres.
* `Stacks.Thickenings.FlatDeformationDiagram.prop_fiberToSpecResidueField_iff` and
  `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.prop_fiberToSpecResidueField_iff`:
  the same transfer for the two deformation diagrams.

## Implementation notes

That the comparison morphism of fibres is an isomorphism is Mathlib's
`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`, which exhibits it as the
base change of `Spec` of the residue-field map of `j` along the structure morphism of the fibre;
that residue-field map is an isomorphism because a closed immersion is surjective on stalks. The
commutativity of the resulting square of arrows is the
`CategoryTheory.Limits.pullback.lift_snd` component of the defining property of
`CategoryTheory.Limits.pullback.map`, since the structure morphism of a fibre is the second
projection of the defining fibre square.

In both deformation diagrams the cartesian square comparing `f` with `f'` is obtained by pasting:
the source square is cartesian over the base thickening, and factoring it through the target
square exhibits `f` as the base change of `f'` along the target thickening.

## References

* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-! ### A cartesian square with thickened target -/

section Cartesian

variable {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}

/-- A thickening induces an isomorphism on the residue field at every point: a closed immersion
is surjective on stalks, and a surjective map of local rings induces an isomorphism of residue
fields. -/
theorem IsThickening.isIso_residueFieldMap (hj : IsThickening j) (y : Y) :
    IsIso (j.residueFieldMap y) :=
  have : IsClosedImmersion j := hj.1
  isIso_residueFieldMap_of_surjective_stalkMap j y (j.stalkMap_surjective y)

/-- The canonical morphism from the fibre of `f` over `y` to the fibre of `f'` over the image of
`y`, for a commuting square `(i, f, f', j)`. -/
noncomputable def fiberMapOfIsPullback (h : IsPullback i f f' j) (y : Y) :
    f.fiber y ⟶ f'.fiber (j y) :=
  pullback.map f (Y.fromSpecResidueField y) f' (Y'.fromSpecResidueField (j y)) i
    (Spec.map (j.residueFieldMap y)) j h.w.symm (by simp)

/-- The comparison morphism of fibres of a cartesian square with thickened target is an
isomorphism. -/
theorem isIso_fiberMapOfIsPullback (hj : IsThickening j) (h : IsPullback i f f' j) (y : Y) :
    IsIso (fiberMapOfIsPullback h y) :=
  have := hj.isIso_residueFieldMap y
  have : IsIso (Spec.map (j.residueFieldMap y)) := inferInstance
  (AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback h y).isIso_fst_of_isIso

/-- The comparison morphism of fibres is compatible with the structure morphisms of the two
fibres to the spectra of the residue fields. -/
theorem fiberMapOfIsPullback_comp_fiberToSpecResidueField (h : IsPullback i f f' j) (y : Y) :
    fiberMapOfIsPullback h y ≫ f'.fiberToSpecResidueField (j y) =
      f.fiberToSpecResidueField y ≫ Spec.map (j.residueFieldMap y) :=
  pullback.lift_snd _ _ _

/-- The fibre of `f` over `y` and the fibre of `f'` over the image of `y`, viewed as schemes over
the spectra of the respective residue fields, are isomorphic as arrows. -/
noncomputable def fiberArrowIsoOfIsPullback (hj : IsThickening j) (h : IsPullback i f f' j)
    (y : Y) :
    Arrow.mk (f.fiberToSpecResidueField y) ≅ Arrow.mk (f'.fiberToSpecResidueField (j y)) :=
  haveI := hj.isIso_residueFieldMap y
  haveI := isIso_fiberMapOfIsPullback hj h y
  Arrow.isoMk (asIso (fiberMapOfIsPullback h y)) (asIso (Spec.map (j.residueFieldMap y)))
    (fiberMapOfIsPullback_comp_fiberToSpecResidueField h y)

/-- A property of morphisms of schemes invariant under isomorphism of arrows holds for the fibre
of `f` over `y` exactly when it holds for the fibre of `f'` over the image of `y`. -/
theorem prop_fiberToSpecResidueField_iff_of_isPullback (hj : IsThickening j)
    (h : IsPullback i f f' j) (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (y : Y) :
    P (f.fiberToSpecResidueField y) ↔ P (f'.fiberToSpecResidueField (j y)) :=
  P.arrow_mk_iso_iff (fiberArrowIsoOfIsPullback hj h y)

end Cartesian

/-! ### Flat deformation diagrams -/

namespace FlatDeformationDiagram

variable (D : FlatDeformationDiagram.{u})

/-- In a flat deformation diagram the morphism of special fibres is the base change of its
ambient deformation along the target thickening. -/
theorem isPullback_f : IsPullback D.iX D.f D.f' D.iY :=
  D.isPullback_X.of_bot D.comm_f D.isPullback_Y

/-- The target thickening of a flat deformation diagram induces an isomorphism on the residue
field at every point. -/
theorem isIso_residueFieldMap_iY (y : D.Y) : IsIso (D.iY.residueFieldMap y) :=
  D.iY_thickening.isIso_residueFieldMap y

/-- The canonical morphism from the fibre of `f` over `y` to the fibre of `f'` over the image of
`y` under the target thickening. -/
noncomputable def fiberMap (y : D.Y) : D.f.fiber y ⟶ D.f'.fiber (D.iY y) :=
  fiberMapOfIsPullback D.isPullback_f y

/-- The comparison morphism of fibres `D.fiberMap y` is an isomorphism. -/
instance isIso_fiberMap' (y : D.Y) : IsIso (D.fiberMap y) :=
  isIso_fiberMapOfIsPullback D.iY_thickening D.isPullback_f y

/-- The comparison morphism of fibres is compatible with the structure morphisms of the two
fibres to the spectra of the residue fields. -/
theorem fiberMap_comp_fiberToSpecResidueField (y : D.Y) :
    D.fiberMap y ≫ D.f'.fiberToSpecResidueField (D.iY y) =
      D.f.fiberToSpecResidueField y ≫ Spec.map (D.iY.residueFieldMap y) :=
  fiberMapOfIsPullback_comp_fiberToSpecResidueField D.isPullback_f y

/-- The fibre of `f` over `y` and the fibre of `f'` over the image of `y`, viewed as schemes over
the spectra of the respective residue fields, are isomorphic as arrows. -/
noncomputable def fiberArrowIso (y : D.Y) :
    Arrow.mk (D.f.fiberToSpecResidueField y) ≅
      Arrow.mk (D.f'.fiberToSpecResidueField (D.iY y)) :=
  fiberArrowIsoOfIsPullback D.iY_thickening D.isPullback_f y

/-- A property of morphisms of schemes invariant under isomorphism of arrows holds for the fibre
of `f` over `y` exactly when it holds for the fibre of `f'` over the image of `y`. -/
theorem prop_fiberToSpecResidueField_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (y : D.Y) :
    P (D.f.fiberToSpecResidueField y) ↔ P (D.f'.fiberToSpecResidueField (D.iY y)) :=
  prop_fiberToSpecResidueField_iff_of_isPullback D.iY_thickening D.isPullback_f P y

end FlatDeformationDiagram

/-! ### Cartesian finite-order deformation diagrams -/

namespace CartesianFiniteOrderDeformationDiagram

variable (D : CartesianFiniteOrderDeformationDiagram.{u})

/-- In a cartesian finite-order deformation diagram the morphism of special fibres is the base
change of its ambient deformation along the target thickening. -/
theorem isPullback_f : IsPullback D.iX D.f D.f' D.iY :=
  IsPullback.of_bot (by simpa only [D.f_over_S, D.f'_over_S'] using D.X_cartesian)
    D.f_thickening_comm.symm D.Y_cartesian

/-- A property of morphisms of schemes invariant under isomorphism of arrows holds for the fibre
of `f` over `y` exactly when it holds for the fibre of `f'` over the image of `y`. -/
theorem prop_fiberToSpecResidueField_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (y : D.Y) :
    P (D.f.fiberToSpecResidueField y) ↔ P (D.f'.fiberToSpecResidueField (D.iY y)) :=
  prop_fiberToSpecResidueField_iff_of_isPullback D.iY_thickening D.isPullback_f P y

end CartesianFiniteOrderDeformationDiagram

end Stacks.Thickenings

end
