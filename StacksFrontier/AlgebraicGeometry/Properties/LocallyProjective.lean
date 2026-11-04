module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Locally projective quasi-coherent modules

A quasi-coherent sheaf of modules on a scheme is locally projective when its module of sections
on every affine open is projective over the ring of functions on that open.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsLocallyProjective` is the predicate that the sections of a
  sheaf of modules on every affine open are projective.

## Implementation notes

The universe of the module sections is independent of the universe of the scheme, so the
predicate also applies to modules obtained by restriction from a site whose sections live in
another universe.

The predicate is defined for every sheaf of modules, although the Stacks Project applies it to
quasi-coherent sheaves. This harmless generalization lets quasi-coherence remain an independent
hypothesis in results using the definition. It is an abbreviation so clients can use its
affine-open characterization directly.

## References

* [Stacks Project, Tag 05JP](https://stacks.math.columbia.edu/tag/05JP)
-/

@[expose] public section

open AlgebraicGeometry

universe u m

namespace AlgebraicGeometry.Scheme.Modules

/-- A sheaf of modules on a scheme is locally projective if its sections on every affine open
are projective over the ring of functions on that open. -/
@[stacks 05JP]
public abbrev IsLocallyProjective {X : Scheme.{u}}
    (M : SheafOfModules.{m} X.ringCatSheaf) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    @Module.Projective Γ(X, U) _ (M.val.obj (.op U)) _ (M.val.obj (.op U)).isModule

end AlgebraicGeometry.Scheme.Modules

end
