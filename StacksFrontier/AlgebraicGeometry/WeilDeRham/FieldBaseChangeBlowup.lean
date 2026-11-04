module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Open.OverField
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeData

/-!
# Base change along a field extension: flatness and closed immersions

For an extension `k'/k` and a smooth projective `X` over `k`, the projection `X_{k'} ⟶ X` is flat,
being a base change of `Spec(k') → Spec(k)`, and the base change `i_{k'}` of a closed immersion
`i : Z ⟶ X` of smooth projective schemes is a closed immersion.

## Main results

* `Stacks.WeilDeRham.flat_fieldBaseChangeProj`: `X_{k'} ⟶ X` is flat.
* `Stacks.WeilDeRham.isClosedImmersion_fieldBaseChange_map`: `i_{k'}` is a closed immersion.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.WeilCohomology

universe u w w'

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- The projection `X_{k'} ⟶ X` is flat, as a base change of `Spec(k') → Spec(k)`. -/
instance flat_fieldBaseChangeProj (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Flat (fieldBaseChangeProj (k' := k') X) := by
  have : Flat (specStructure k k') :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k k'))
  exact MorphismProperty.of_isPullback (isPullback_fieldBaseChangeProj (k' := k') X).flip
    inferInstance

/-- The base change `i_{k'} : Z_{k'} ⟶ X_{k'}` of a closed immersion is a closed immersion. -/
instance isClosedImmersion_fieldBaseChange_map {Z X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : Z ⟶ X) [IsClosedImmersion i.hom.left] :
    IsClosedImmersion ((fieldBaseChange k k').map i).hom.left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_fieldBaseChange_map (k' := k') i).flip
    (inferInstanceAs (IsClosedImmersion i.hom.left))

variable {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

end Stacks.WeilDeRham

end
