module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian
import StacksCore.Tactic.StacksAttribute

/-!
# A finite morphism to a locally Noetherian scheme is pseudo-coherent

A finite morphism is locally of finite type, and over a locally Noetherian base a morphism is
pseudo-coherent exactly when it is locally of finite type. In particular a finite morphism of
Noetherian schemes is pseudo-coherent.

## Main results

* `AlgebraicGeometry.pseudoCoherent_of_isFinite_of_isLocallyNoetherian`: a finite morphism to a
  locally Noetherian scheme is pseudo-coherent.

## References

* [Stacks Project, Tag 0AX2](https://stacks.math.columbia.edu/tag/0AX2)
* [Stacks Project, Tag 0684](https://stacks.math.columbia.edu/tag/0684)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- A finite morphism `f : Y ⟶ X` to a locally
Noetherian scheme is pseudo-coherent; in particular a finite morphism of Noetherian schemes is
pseudo-coherent. -/
@[stacks 0AX2 "parenthetical remark: a finite morphism of Noetherian schemes is pseudo-coherent"]
theorem pseudoCoherent_of_isFinite_of_isLocallyNoetherian {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (f : Y ⟶ X) [IsFinite f] : PseudoCoherent f :=
  (pseudoCoherent_iff_locallyOfFiniteType f).2 inferInstance

end AlgebraicGeometry

end
