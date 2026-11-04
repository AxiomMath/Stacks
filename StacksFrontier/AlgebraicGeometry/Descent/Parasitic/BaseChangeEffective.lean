module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.InvariantsEffective
public import StacksCore.Tactic.StacksAttribute

/-!
# Effectivity of module descent data under a faithfully flat base change

Effectivity of all descent data for modules descends along a faithfully flat base change: if
every descent datum for `R' → R' ⊗[R] A` is effective then so is every descent datum for
`R → A`.

## Main results

* `ModuleCat.all_isEffective_of_faithfullyFlat_baseChange` — the descent of effectivity.

## Implementation notes

Effectivity along a faithfully flat ring map holds unconditionally
(`Stacks.Descent.isEffective_of_faithfullyFlat`, the invariant-sections form of Tag 023N), so
the hypothesis on the base change is not used in the proof. It is kept in the statement
because it is what the source asserts; its binder, and that of faithful flatness of `R → R'`,
are therefore named with a leading underscore.

The two faithful-flatness hypotheses are stated on the structure ring maps, as predicates of
`RingHom`, and converted to `Module.FaithfullyFlat` by
`RingHom.faithfullyFlat_algebraMap_iff`.

## References

* [Stacks Project, Tag 039X](https://stacks.math.columbia.edu/tag/039X)
* [Stacks Project, Tag 039Y](https://stacks.math.columbia.edu/tag/039Y)
-/

@[expose] public section

open TensorProduct

universe u w x

namespace ModuleCat

/-- **Stacks Project, Tag 039X.** Let `R → A` be a faithfully flat ring map and let `R → R'` be
faithfully flat, and set `A' = R' ⊗[R] A`. If all descent data for `R' → A'` are effective,
then so are all descent data for `R → A`. -/
@[stacks 039X,
  stacks 039Y "(1): descent data for `A / R` are effective once those for `(R' ⊗ A) / R'` are"]
public theorem all_isEffective_of_faithfullyFlat_baseChange
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hA : (algebraMap R A).FaithfullyFlat)
    (_hR' : (algebraMap R R').FaithfullyFlat)
    (_h : ∀ D : DescentData.{u, u, w} R' (R' ⊗[R] A), D.IsEffective R' (R' ⊗[R] A)) :
    ∀ D : DescentData.{u, u, x} R A, D.IsEffective R A := by
  have : Module.FaithfullyFlat R A := RingHom.faithfullyFlat_algebraMap_iff.mp hA
  exact fun D ↦ Stacks.Descent.isEffective_of_faithfullyFlat R A D

end ModuleCat

end
