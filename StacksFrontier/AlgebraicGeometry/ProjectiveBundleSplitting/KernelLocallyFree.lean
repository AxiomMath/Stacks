module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingKernel
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.TwoTermResolution
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelRank
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel of an invertible quotient of a finite locally free module is finite locally free

Let `q : ℳ ⟶ ℒ` be an epimorphism of modules on a scheme with `ℳ` finite locally free and `ℒ`
invertible. Then `ker q` is finite locally free, and — once `ℳ` has rank `m + 2` — of rank
`m + 1`.

This is the field `sub_rank` of `Stacks.Divisors.BundleSplittingDatum`, with nothing left of it
an argument. `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_succ` already
pins the *value* of the rank as soon as the kernel is finite locally free of some constant rank;
what this file supplies is that local freeness.

## Main results

* `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi`: the kernel of an
  epimorphism of finite locally free modules is finite locally free.
* `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi_isInvertible`: the kernel
  of an epimorphism from a finite locally free module onto an invertible one is finite locally
  free.
* `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible`: the
  same with the rank read off, for a middle term of rank `m + 1`.

## Implementation notes

**The route is Tag 05P2, flat plus finitely presented.** An invertible module is finite locally
free of rank one, hence flat, hence of Tor amplitude in `[0, 0]` and a fortiori in `[-1, 0]`;
`AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude` then makes the kernel of a
surjection onto it from a finite locally free module finite locally free, provided the kernel is
finitely presented. That last point is
`AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree`, whose proof is the local
splitting of the surjection.

**Two spellings of finite local freeness.** The hypothesis and the conclusion are stated with
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, the class of Tag 01C6 part (2) that
`Stacks.Divisors.BundleSplittingDatum` reads; the Tor-amplitude lemma is stated with
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, a reducible abbreviation of the first, so the
hypotheses pass between them unchanged.

**The rank statement keeps its point of the scheme.** Rank additivity is read at a stalk, so
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible` inherits
the point from `AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`, exactly as
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_succ` does.

## References

* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveBundleSplitting

attribute [local instance] HasDerivedCategory.standard

/-- **The kernel of an epimorphism of finite locally free modules is finite locally free.** The
target is finite locally free, hence flat, hence of Tor amplitude in `[-1, 0]`; the kernel is
finitely presented because the surjection splits locally; and flat plus finitely presented is
finite locally free, which is Tag 05P2. -/
@[sga "6 I 1.3" "special case"]
theorem isFiniteLocallyFree_kernel_of_epi {P : Scheme.{u}} {M L : P.Modules}
    (q : M ⟶ L) (hq : Epi q)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (kernel q) := by
  have := hq
  have := hM
  have := hL
  have : M.IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree M hM
  have : M.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M
  have hfp : (kernel q).IsFinitePresentation :=
    AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree q
  set S : ShortComplex P.Modules := ShortComplex.mk (kernel.ι q) q (kernel.condition q) with hS'
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  have h₃ : Stacks.Cohomology.TorAmplitude.HasTorAmplitude P.toRingedSpace
      ((DerivedCategory.singleFunctor P.Modules 0).obj S.X₃) (-1) 0 :=
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (AlgebraicGeometry.hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree P S.X₃
        ‹_›)
      (show (-1 : ℤ) ≤ 0 by omega) (le_refl (0 : ℤ))
  exact AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude S hS
      hM h₃ hfp

/-- **The kernel of an epimorphism from a finite locally free module onto an invertible one is
finite locally free.** The invertible target is finite locally free of rank one, so this is
`isFiniteLocallyFree_kernel_of_epi`. -/
theorem isFiniteLocallyFree_kernel_of_epi_isInvertible {P : Scheme.{u}} {M L : P.Modules}
    (q : M ⟶ L) (hq : Epi q)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (kernel q) :=
  have hL1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible L hL
  isFiniteLocallyFree_kernel_of_epi q hq hM hL1.isFiniteLocallyFree

end Stacks.ProjectiveBundleSplitting

end
