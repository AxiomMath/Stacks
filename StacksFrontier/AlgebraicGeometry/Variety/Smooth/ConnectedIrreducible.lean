module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible

/-!
# A connected scheme smooth over a field is irreducible

A scheme smooth over a field is normal ([Stacks, Tag 056S]), and a connected Noetherian normal
scheme is irreducible ([Stacks, Tag 033M]), so a connected Noetherian scheme smooth over a field
is irreducible.

## Main results

* `AlgebraicGeometry.irreducibleSpace_of_smooth_of_connectedSpace`: a connected Noetherian
  scheme smooth over a field is irreducible.
* `AlgebraicGeometry.irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace`: a connected
  quasi-compact scheme smooth over a field is irreducible.

## References

* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 033M](https://stacks.math.columbia.edu/tag/033M)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A connected Noetherian scheme smooth over a field is irreducible. -/
theorem irreducibleSpace_of_smooth_of_connectedSpace {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [IsNoetherian X] [ConnectedSpace X] :
    IrreducibleSpace X :=
  irreducibleSpace_of_isNormal_of_connectedSpace X (isNormal_of_smooth_over_field f)

/-- A connected quasi-compact scheme smooth over a field is irreducible. -/
theorem irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [CompactSpace X] [ConnectedSpace X] :
    IrreducibleSpace X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  irreducibleSpace_of_smooth_of_connectedSpace f

end AlgebraicGeometry

end
