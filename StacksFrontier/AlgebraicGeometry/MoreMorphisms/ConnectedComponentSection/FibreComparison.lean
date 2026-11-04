module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BaseChangeFiberMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre

/-!
# Comparing the fibres of a base change

`AlgebraicGeometry.baseChangeFiberMap` compares the fibre of a base change
`pullback.snd f a : pullback f a ⟶ T` at a point `t : T` with the fibre of `f` at `a t`. It is
exhibited here as a base change of that second fibre, so it is an isomorphism as soon as `a`
induces an isomorphism of residue fields at `t` (`AlgebraicGeometry.isIso_baseChangeFiberMap`),
which is the case for an elementary étale neighbourhood.

## Main definitions

* `AlgebraicGeometry.ConnectedComponentSection.elementaryFiberIso`: the resulting isomorphism for
  an elementary étale neighbourhood.

## Main results

* `AlgebraicGeometry.ConnectedComponentSection.baseChangeFiberMap_isPullback`: the comparison
  morphism exhibits the fibre of a base change as a base change of the fibre.
* `AlgebraicGeometry.ConnectedComponentSection.elementaryFiberIso_hom_fiberι` and
  `AlgebraicGeometry.ConnectedComponentSection.elementaryFiberIso_hom_fiberToSpecResidueField`
  express the compatibility of the isomorphism with the inclusion of the fibre into the total
  space and with the structure morphism to the spectrum of the residue field.

## References

* [Stacks Project, Tag 055W](https://stacks.math.columbia.edu/tag/055W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ConnectedComponentSection

/-! ### The fibre of a base change -/

/-- The comparison morphism `AlgebraicGeometry.baseChangeFiberMap` exhibits the fibre of a base
change as a base change of the fibre. -/
theorem baseChangeFiberMap_isPullback {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ S) (t : T) :
    IsPullback (baseChangeFiberMap f a t) ((pullback.snd f a).fiberToSpecResidueField t)
      (f.fiberToSpecResidueField (a t)) (Spec.map (a.residueFieldMap t)) :=
  isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f a) t

/-- The comparison morphism `AlgebraicGeometry.baseChangeFiberMap` is compatible with the two
maps to the spectra of the residue fields. -/
theorem baseChangeFiberMap_fiberToSpecResidueField {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ S)
    (t : T) : baseChangeFiberMap f a t ≫ f.fiberToSpecResidueField (a t) =
      (pullback.snd f a).fiberToSpecResidueField t ≫ Spec.map (a.residueFieldMap t) :=
  (baseChangeFiberMap_isPullback f a t).w

/-! ### Transport of a fibre along an equality of points -/

/-- Transporting a fibre along an equality of base points is compatible with the maps to the
spectra of the residue fields. -/
theorem fiberIsoOfEq_hom_fiberToSpecResidueField {X S : Scheme.{u}} (f : X ⟶ S) {a b : S}
    (h : a = b) : (fiberIsoOfEq f h).hom ≫ f.fiberToSpecResidueField b =
      f.fiberToSpecResidueField a ≫ Spec.map (S.residueFieldCongr h).inv := by
  cases h
  simp [fiberIsoOfEq]

/-! ### The fibre over the distinguished point of an elementary étale neighbourhood -/

/-- Base change along an elementary étale neighbourhood does not change the fibre over the
distinguished point. -/
def elementaryFiberIso {X S : Scheme.{u}} (f : X ⟶ S) {s : S} (U : EtaleNeighborhood S s)
    [IsIso U.residueFieldMap] : (pullback.snd f U.toBase).fiber U.point ≅ f.fiber s := by
  haveI : IsIso (U.toBase.residueFieldMap U.point) := (U.isElementary_iff).mp ‹_›
  haveI : IsIso (baseChangeFiberMap f U.toBase U.point) :=
    isIso_baseChangeFiberMap f U.toBase U.point
  exact asIso (baseChangeFiberMap f U.toBase U.point ≫ (fiberIsoOfEq f U.map_point).hom)

/-- The isomorphism `AlgebraicGeometry.ConnectedComponentSection.elementaryFiberIso` is compatible
with the inclusions of the two fibres into the two total spaces. -/
theorem elementaryFiberIso_hom_fiberι {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) [IsIso U.residueFieldMap] :
    (elementaryFiberIso f U).hom ≫ f.fiberι s =
      (pullback.snd f U.toBase).fiberι U.point ≫ pullback.fst f U.toBase := by
  dsimp [elementaryFiberIso]
  rw [Category.assoc, fiberIsoOfEq_hom_fiberι, baseChangeFiberMap_comp_fiberι]

/-- The isomorphism `AlgebraicGeometry.ConnectedComponentSection.elementaryFiberIso` is compatible
with the two maps to the spectra of the residue fields, up to the residue field isomorphism of the
neighbourhood. -/
theorem elementaryFiberIso_hom_fiberToSpecResidueField {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) [IsIso U.residueFieldMap] :
    (elementaryFiberIso f U).hom ≫ f.fiberToSpecResidueField s =
      (pullback.snd f U.toBase).fiberToSpecResidueField U.point ≫
        Spec.map U.residueFieldMap := by
  dsimp [elementaryFiberIso]
  rw [Category.assoc, fiberIsoOfEq_hom_fiberToSpecResidueField, ← Category.assoc,
    baseChangeFiberMap_fiberToSpecResidueField, Category.assoc, ← Spec.map_comp]
  rfl

end AlgebraicGeometry.ConnectedComponentSection

end
