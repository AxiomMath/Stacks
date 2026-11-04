module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of reducedness along flat surjective morphisms

A reduced source of a flat surjective morphism of schemes has reduced target.

## Main results

* `AlgebraicGeometry.isReduced_of_flat_of_surjective` shows that reducedness descends
  along flat surjective morphisms of schemes.

## Implementation notes

Reducedness, flatness, and surjectivity are expressed by Mathlib's corresponding
typeclasses on schemes and scheme morphisms. Reducedness of the target is checked stalkwise;
at a point of the target, surjectivity supplies a preimage, and the induced map on stalks is
a flat local homomorphism of local rings, hence faithfully flat by
`Module.FaithfullyFlat.of_flat_of_isLocalHom`. Reducedness then descends along that map by
`RingHom.FaithfullyFlat.isReduced`.

## References

* [Stacks Project, Tag 06QM](https://stacks.math.columbia.edu/tag/06QM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The target of a flat surjective morphism of schemes with reduced source is reduced. -/
@[stacks 06QM, sga "3 VIB 2.1.2" "partial"]
lemma isReduced_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsReduced X] : IsReduced Y := by
  refine @isReduced_of_isReduced_stalk Y (fun y => ?_)
  obtain ⟨x, rfl⟩ := f.surjective y
  have hff : (f.stalkMap x).hom.FaithfullyFlat := by
    let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    have : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      Flat.stalkMap f x
    have : IsLocalHom
        (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact hff.isReduced

end AlgebraicGeometry
