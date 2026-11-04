module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus

/-!
# Openness of the flat locus of a morphism locally of finite type

Let `f : X ⟶ Y` be locally of finite type with `Y` locally Noetherian. The relative flat locus
of a coherent `O_X`-module is open, and in particular so is the locus where `f` itself is flat.

## Main results

* `AlgebraicGeometry.isOpen_setOf_isFlatAt_of_isLocallyNoetherian`: the flat locus of a morphism
  locally of finite type over a locally Noetherian scheme is open.

## Implementation notes

Openness for a coherent module is `AlgebraicGeometry.isOpen_setOf_coherent_flatOverAt`, to which
the first half of the source statement is attached here. The locus where the morphism is flat is
the locus where the structure sheaf of the source, regarded as a module over itself, is flat
over the target: this is `AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`. Over a locally
Noetherian scheme that module is coherent, so the second half follows from the first.

The hypotheses here are incomparable with those of
`AlgebraicGeometry.isOpen_setOf_isFlatAt`, which asks for local finite presentation and no
Noetherian condition.

## References

* [Stacks Project, Tag 0255](https://stacks.math.columbia.edu/tag/0255)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

add_to_stacks 0255 "relative flat locus of a coherent module"
  AlgebraicGeometry.isOpen_setOf_coherent_flatOverAt

/-- **Stacks Project, Tag 0255.** The flat locus of a morphism locally of finite type to a
locally Noetherian scheme is open. -/
@[stacks 0255 "flat locus of the morphism",
  ega "IV 11.1.1" "F = O_X case",
  sga "1 IV 6.10" "F = O_X case",
  ega "IV 11.1.6" "M = C = B case",
  ega "IV 11.3.1" "Noetherian, F = O_X"]
theorem isOpen_setOf_isFlatAt_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    IsOpen {x : X | IsFlatAt f.toLRSHom.toShHom x} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.structureSheaf_isCoherent X
  have hset : {x : X | IsFlatAt f.toLRSHom.toShHom x} =
      {x : X | IsFlatOverAt f.toLRSHom.toShHom (SheafOfModules.unit X.ringCatSheaf) x} :=
    Set.ext fun x => (isFlatOverAt_unit_iff_isFlatAt f x).symm
  rw [hset]
  exact isOpen_setOf_coherent_flatOverAt f (SheafOfModules.unit X.ringCatSheaf)

end AlgebraicGeometry
