module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Unramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# The descent ingredients for unramifiedness

Three properties of unramifiedness of morphisms of schemes, the hypotheses of the generic fpqc
criterion of **Stacks 02KP**, `AlgebraicGeometry.Stacks.Descent.isLocalAtTarget_fpqcPrecoverage`:
Zariski locality on the base, the identification of unramifiedness with the conjunction of local
finite type and formal unramifiedness (**Stacks 02HE**), and fpqc descent.

## Main results

* `AlgebraicGeometry.unramified_eq_locallyOfFiniteType_inf_formallyUnramified`: unramifiedness
  is the conjunction of local finite type and formal unramifiedness.
* `AlgebraicGeometry.unramified_descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  unramifiedness satisfies fpqc descent.
* `AlgebraicGeometry.unramified_isZariskiLocalAtTarget`: unramifiedness is Zariski local on the
  target.

## Implementation notes

The Zariski locality instance is supplied by name rather than by synthesis, because the
ring-homomorphism property indexing `AlgebraicGeometry.HasRingHomProperty` is not an output
parameter and so cannot be inferred from `AlgebraicGeometry.Unramified` alone; for
unramifiedness that property is the conjunction of formal unramifiedness and finite type.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 02GA](https://stacks.math.columbia.edu/tag/02GA)
* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 02VM](https://stacks.math.columbia.edu/tag/02VM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02HE** read as an identity of morphism properties: unramifiedness is
the conjunction of local finite type and formal unramifiedness. -/
theorem unramified_eq_locallyOfFiniteType_inf_formallyUnramified :
    (@Unramified : MorphismProperty Scheme.{u})
      = (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) :=
  MorphismProperty.ext _ _ fun _ _ f =>
    unramified_iff_locallyOfFiniteType_and_formallyUnramified f

/-- Unramifiedness satisfies fpqc descent: if the base change of a morphism along a surjective
flat quasi-compact morphism is unramified, then so is the morphism. -/
@[ega "IV 17.7.3" "(i), (ii)"]
instance unramified_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@Unramified : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [unramified_eq_locallyOfFiniteType_inf_formallyUnramified]
  exact MorphismProperty.DescendsAlong.inf

/-- Unramifiedness of morphisms of schemes is Zariski local on the target. -/
instance unramified_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@Unramified.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Unramified.{u})
    (Q := fun {R T : Type u} [CommRing R] [CommRing T] (g : R →+* T) =>
      g.FormallyUnramified ∧ g.FiniteType)

end AlgebraicGeometry

end
