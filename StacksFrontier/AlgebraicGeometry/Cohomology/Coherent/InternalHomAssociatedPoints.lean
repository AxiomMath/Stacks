module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.InternalHomDepth
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.RingTheory.Depth.AssociatedPrime
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Associated points of an internal hom

For coherent modules `F`, `G` on a locally Noetherian scheme, every associated point of
`SheafHom(F, G)` is an associated point of `G`. This is the consequence of [Stacks, Tag 0EBC],
part (1), that the proof of [Stacks, Tag 0EIV] uses: at a point where `G` has no associated
point, `G_x` has depth at least one, hence so does `SheafHom(F, G)_x`, so the maximal ideal of
`𝒪_{X,x}` is not an associated prime of it.

## Main results

* `AlgebraicGeometry.associatedPoints_internalHomOf_subset` — `Ass(SheafHom(F, G)) ⊆ Ass(G)`.

## References

* [Stacks Project, Tag 0EBC](https://stacks.math.columbia.edu/tag/0EBC)
* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **The associated points of an internal hom are associated points of the target.** For
coherent modules `F`, `G` on a locally Noetherian scheme and any representative `H` of
`SheafHom(F, G)` in the sense of [Stacks, Tag 01CO], `Ass(SheafHom(F, G)) ⊆ Ass(G)`: off
`Ass(G)` the stalk `G_x` has depth at least one, which [Stacks, Tag 0EBC] part (1) passes to the
stalk of the internal hom, and depth at least one excludes the maximal ideal from its
associated primes. -/
public theorem associatedPoints_internalHomOf_subset [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (H : SheafHom X.sheaf F G) [_root_.SheafOfModules.IsCoherent (internalHomOf H)] :
    Stacks.Divisors.associatedPoints (internalHomOf H) ⊆ Stacks.Divisors.associatedPoints G := by
  intro x hx
  by_contra hxG
  have : Module.Finite (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent G x
  have : Module.Finite (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent G x
  have hG : (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (G.presheaf.stalk x) := by
    refine Order.one_le_iff_ne_zero.2 fun h0 => hxG ?_
    exact (isAssociatedPrimeStacks_iff_mem_associatedPrimes _).2
      ((Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes).1 h0)
  have hH := one_le_depth_stalk_internalHom F G H x hG
  have : Module.Finite (X.presheaf.stalk x) ((internalHomOf H).presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent (internalHomOf H) x
  exact maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth hH hx

end AlgebraicGeometry
