module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension

/-!
# Images of morphisms out of a coherent module

On a locally Noetherian scheme the image of a morphism from a coherent module to a
quasi-coherent module is coherent.

## Main results

* `Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_image_of_isCoherent_of_isQuasicoherent`:
  the image of a morphism from a coherent module to a quasi-coherent module is coherent.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherenceCriteria

/-- **The image of a morphism from a coherent module into a quasi-coherent module is coherent**,
on a locally Noetherian scheme. -/
theorem isCoherent_image_of_isCoherent_of_isQuasicoherent {X : Scheme.{u}}
    [IsLocallyNoetherian X] {M N : X.Modules} [M.IsCoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (image f).IsCoherent := by
  obtain ⟨hqcM, hftM⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M
  have := hqcM
  have : (image f).IsQuasicoherent := Stacks.Algebraization.isQuasicoherent_image f
  have : (image f).IsFiniteType := Stacks.SheafOfModules.isFiniteType_image f hftM
  exact isCoherent_of_isQuasicoherent_of_isFiniteType _

end Stacks.AlgebraicGeometry.CoherenceCriteria

end
