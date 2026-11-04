module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import StacksFrontier.Homology.KFlat.Flat

/-!
# The cochain complex of a projective resolution is K-flat

A projective resolution of an `R`-module is, read as a cochain complex concentrated in
nonpositive degrees, a bounded above complex of projective — hence flat — modules, so
`CochainComplex.KFlat.kFlat_of_flat` (Stacks 064K) applies to it.

This is the statement every computation of `Tor` through a projective resolution needs in order
to use a K-flat model, and it is kept here, next to Stacks 064K itself, rather than restated in
each such file.

## Main results

* `CochainComplex.KFlat.kFlat_projectiveResolution`: the cochain complex of a projective
  resolution of a module is K-flat.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

open CategoryTheory

@[expose] public section

namespace CochainComplex.KFlat

universe u v

/-- **The cochain complex of a projective resolution is K-flat.** Its terms are projective,
hence flat, and it is concentrated in nonpositive degrees, so Stacks 064K applies. -/
public theorem kFlat_projectiveResolution {R : Type u} [CommRing R]
    {X : ModuleCat.{max u v} R} (Q : ProjectiveResolution X) : Q.cochainComplex.KFlat := by
  have : ∀ n : ℤ, Module.Flat R (Q.cochainComplex.X n) := fun n ↦ by
    have : Module.Projective R (Q.cochainComplex.X n) :=
      ModuleCat.projective_of_module_projective _
    infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat Q.cochainComplex 0

end CochainComplex.KFlat

end
