module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# The rank of the kernel of an invertible quotient

Let `q : ℳ ⟶ ℒ` be an epimorphism of modules on a scheme onto an invertible one, with `ℳ`
finite locally free of rank `n`. If its kernel is finite locally free of rank `r` at all, then
`n = r + 1`: the rank is forced, and `r` cannot be anything but `n - 1`.

This is the field `sub_rank` of `Stacks.Divisors.BundleSplittingDatum` reduced to its
rank-free half. What it leaves is local freeness of the kernel with *some* constant rank; the
value of that rank is then not a further assumption.

## Main results

* `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible`: an
  invertible module on a scheme is finite locally free of rank one, at the spelling of Tag 01CS
  that `Stacks.Divisors.BundleSplittingDatum` uses.
* `Stacks.ProjectiveBundleSplitting.rank_eq_succ_of_epi_isInvertible`: the rank of the middle
  term is one more than the rank of the kernel.
* `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_succ`: the kernel of an
  epimorphism from a module of rank `m + 2` onto an invertible one is finite locally free of
  rank `m + 1`, given that it is finite locally free of some constant rank.

## Implementation notes

**A point of the scheme is an argument.** Rank additivity is read at a stalk, so the statements
inherit the point from
`AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`. On the projective bundle of a module
of positive rank over a nonempty base the point is available; it is not produced here.

**The two invertibility predicates.** The hypothesis is stated with
`AlgebraicGeometry.SheafOfModules.IsInvertible`, which is what the splitting datum records,
and crossed once to `Stacks.SheafOfModules.IsInvertible`, in which Tag 0B8M's
characterisation of invertibility as finite local freeness of rank one is stated.

## References

* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveBundleSplitting

/-- **An invertible module on a scheme is finite locally free of rank one.** This is clause 2 of
Tag 0B8M, with the Tag 01CS twin crossed once by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible {P : Scheme.{u}} (L : P.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
  (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one P L).mp
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL)

/-- **The rank of the middle term is one more than the rank of the kernel.** The kernel sequence
of an epimorphism onto an invertible module is short exact, its third term has rank one, and
rank is additive along a short exact sequence of finite locally free modules. -/
theorem rank_eq_succ_of_epi_isInvertible {P : Scheme.{u}} {M L : P.Modules} (q : M ⟶ L)
    (hq : Epi q)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (n r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M n)
    (hker : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel q) r)
    (x : P) : n = r + 1 := by
  have := hq
  exact @AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact _
    (ShortComplex.mk (kernel.ι q) q (kernel.condition q))
    { exact := ShortComplex.exact_kernel q } r n 1 hker hM
    (isFiniteLocallyFreeOfRank_one_of_isInvertible L hL) x

/-- **The kernel of an epimorphism from a module of rank `m + 2` onto an invertible one is
finite locally free of rank `m + 1`**, as soon as it is finite locally free of some constant
rank: that rank is forced by additivity. This is the field `sub_rank` of
`Stacks.Divisors.BundleSplittingDatum`, with the value of the rank no longer assumed. -/
theorem isFiniteLocallyFreeOfRank_kernel_succ {P : Scheme.{u}} {M L : P.Modules} (q : M ⟶ L)
    (hq : Epi q)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (m r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (m + 2))
    (hker : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel q) r)
    (x : P) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel q) (m + 1) := by
  have h := rank_eq_succ_of_epi_isInvertible q hq hL (m + 2) r hM hker x
  have hr : r = m + 1 := by omega
  exact hr ▸ hker

end Stacks.ProjectiveBundleSplitting

end
