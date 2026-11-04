module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite presentation of finite flat modules over a local ring

Over a local ring, finiteness and flatness together already give finite presentation: a finite
flat module over a local ring is free (Stacks Tag 00NZ, `Module.free_of_flat_of_isLocalRing`),
hence projective, and a finite projective module over any ring is finitely presented.

This is the step which turns the flatness hypothesis of the Stacks Project's "after an elementary
étale neighbourhood" statements into the finite-presentation half of their conclusion once the
base has been replaced by `Spec 𝒪_{S, s}`: the base case of the induction in the first proof of
Tag 05I5 is exactly a finite flat module over a local ring.

Note that no Noetherian hypothesis appears, and none is needed — freeness over a local ring
(Tag 00NZ) holds for finite flat modules over an arbitrary local ring.

## Main results

* `Module.finitePresentation_of_flat_of_isLocalRing`: a finite flat module over a local ring is
  finitely presented.

## References

* [Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
-/

@[expose] public section

universe u v

/-- **A finite flat module over a local ring is finitely presented.** It is free by Stacks Tag
00NZ, hence projective, and a finite projective module is finitely presented. -/
theorem Module.finitePresentation_of_flat_of_isLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Flat R M] : Module.FinitePresentation R M :=
  have : Module.Free R M := Module.free_of_flat_of_isLocalRing
  Module.finitePresentation_of_projective R M

end
