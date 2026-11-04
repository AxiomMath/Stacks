module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularMorphism.FppfLocalTarget
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth morphisms are regular

Every smooth morphism of schemes is regular, and its fibres are locally Noetherian.

## Main results

* `AlgebraicGeometry.Scheme.Hom.smooth_fiberToSpecResidueField`: each fibre of a smooth morphism
  is smooth over the residue field of its point.
* `AlgebraicGeometry.Scheme.Hom.isRegular_of_smooth`: a smooth morphism of schemes is regular.
* `AlgebraicGeometry.regularWithLocallyNoetherianFibers_of_smooth`: a smooth morphism has
  locally Noetherian fibres and is regular.

## References

* [Stacks Project, Tag 07R9](https://stacks.math.columbia.edu/tag/07R9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Each fibre of a smooth morphism is smooth over the residue field of its point. -/
@[ega "IV 17.5.1" "a)"]
public theorem Scheme.Hom.smooth_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] (y : Y) : Smooth (f.fiberToSpecResidueField y) :=
  inferInstanceAs (Smooth (pullback.snd f (Y.fromSpecResidueField y)))

/-- A smooth morphism of schemes is regular. -/
@[stacks 07R9, ega "IV 17.5.2" "Necessity", ega "IV 6.8.6" "Implication a) ⇒ b)"]
public theorem Scheme.Hom.isRegular_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    f.IsRegular :=
  (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers f).mpr
    ⟨inferInstance, fun y => @isGeometricallyRegular_of_smooth (Y.residueField y) inferInstance
      (f.fiber y) (f.fiberToSpecResidueField y) (f.smooth_fiberToSpecResidueField y)⟩

/-- A smooth morphism of schemes has locally Noetherian fibres and is regular. -/
public theorem regularWithLocallyNoetherianFibers_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] : regularWithLocallyNoetherianFibers f :=
  ⟨fun y =>
    have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y)))
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y),
    Scheme.Hom.isRegular_of_smooth f⟩

end AlgebraicGeometry
