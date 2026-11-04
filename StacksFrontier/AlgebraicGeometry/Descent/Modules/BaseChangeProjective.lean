module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.BaseChangeFiniteness
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.BaseChangeFlat
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective

/-!
# Descent of finite projectivity along universally injective ring maps

Let `R → S` be a universally injective map of commutative rings. An `R`-module is finite and
projective exactly when its scalar extension to `S` is.

## Main results

* `Module.finite_projective_iff_baseChange_of_universallyInjective`: finite projectivity
  descends and ascends along a universally injective ring map.

## Implementation notes

Finite projectivity is expressed as finite generation together with projectivity. The scalar
extension is written `S ⊗[R] M`, with `S` as the left tensor factor, so that it carries its
canonical `S`-module structure. The proof passes through the equivalent description of a
finite projective module as a finitely presented flat one, where the two halves descend
separately.

## References

* [Stacks Project, Tag 08XD](https://stacks.math.columbia.edu/tag/08XD)
-/

@[expose] public section

universe u v

namespace Module

/-- Finite projectivity descends and ascends along a universally injective ring map. -/
@[stacks 08XD "finite_projective"]
theorem finite_projective_iff_baseChange_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (Module.Finite R M ∧ Module.Projective R M) ↔
      (Module.Finite S (TensorProduct R S M) ∧
        Module.Projective S (TensorProduct R S M)) :=
  ((Module.finite_projective_tfae R M).out 1 2).symm.trans <|
    (and_congr (finitePresentation_iff_baseChange_of_universallyInjective hRS M)
        (flat_iff_baseChange_of_universallyInjective hRS M)).trans
      ((Module.finite_projective_tfae S (TensorProduct R S M)).out 1 2)

end Module

end
