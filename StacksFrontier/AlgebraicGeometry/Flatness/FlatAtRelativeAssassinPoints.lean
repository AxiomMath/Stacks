module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatAtAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus

/-!
# Flatness at a point from flatness at the relative-assassin points specializing to it

Let `f : X → S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type and let `x ∈ X`. The implication (2) ⟹ (1) of Stacks 05UA,
`AlgebraicGeometry.isFlatOverAt_of_forall_isAssociatedPoint_specializes`, is stated with the
associated points of the fibre module. This file restates it with clause (2) read on the
relative assassin `Ass_{X/S}(F)` of Stacks 05AT, the shape in which the algebraic-space case
Stacks 0CWL consumes it.

## Main results

* `AlgebraicGeometry.isFlatOverAt_of_forall_mem_relativeAssassin_specializes`: the implication
  (2) ⟹ (1) of Stacks 05UA with clause (2) read on the relative assassin `Ass_{X/S}(F)` of
  Stacks 05AT instead of the associated points of the fibre.

## References

* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 05UA, the implication (2) ⟹ (1), in relative-assassin form.** Let `f : X ⟶ S` be
locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite type and let `x ∈ X`.
If `F` is flat over `S` at every point of the relative assassin `Ass_{X/S}(F)` of Stacks 05AT
which lies over `f x` and specializes to `x`, then `F` is flat over `S` at `x`.

The source states clause (2) with the associated points of the fibre module; intersecting the
relative assassin with the fibre of `f` through `x` is that same set, because a point of the
fibre over `f x` lies in `Ass_{X/S}(F)` exactly when it is associated to the restriction of `F`
to that fibre, `Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin`. This is
the shape in which the algebraic-space case Stacks 0CWL consumes the theorem. -/
theorem isFlatOverAt_of_forall_mem_relativeAssassin_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (h : ∀ x' : X, f.base x' = f.base x → x' ∈ Stacks.Divisors.relativeAssassin f F →
      x' ⤳ x → IsFlatOverAt f.toLRSHom.toShHom F x') :
    IsFlatOverAt f.toLRSHom.toShHom F x :=
  isFlatOverAt_of_forall_isAssociatedPoint_specializes f F x fun x' hass hsp =>
    h _ (f.apply_fiberι (f.base x) x')
      ((Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin f F _ x').mp hass) hsp

end AlgebraicGeometry

end

end
