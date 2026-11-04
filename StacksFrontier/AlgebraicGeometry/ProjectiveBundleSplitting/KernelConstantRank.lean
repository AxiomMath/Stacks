module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelLocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel of an invertible quotient has constant rank, with no point assumed

Let `q : ℳ ⟶ ℒ` be an epimorphism of modules on a scheme with `ℳ` finite locally free of rank
`m + 1` and `ℒ` invertible. Then `ker q` is finite locally free of rank `m`. This includes the
rank-one source `m = 0`, where the kernel is of rank zero.

`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_succ` already draws this
conclusion, but only from two further inputs: that the kernel is finite locally free of *some*
constant rank, and that the scheme has a point.
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi_isInvertible` removes the
first. What this file removes is the second: the point at which rank additivity is read is produced
inside the proof, from a trivialising open of the kernel, so the statement is unconditional. This
is the field `sub_rank` of `Stacks.Divisors.BundleSplittingDatum` with nothing left of it an
argument.

## Main results

* `Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict`: a finite locally
  free module is, near each point, of some constant rank after restriction.
* `Stacks.ProjectiveBundleSplitting.rank_restrict_kernel_eq_pred`: on a trivialising open the
  rank of the restricted kernel is forced to be `m`.
* `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred`:
  the kernel of an epimorphism from a module of rank `m + 1` onto an invertible one is finite
  locally free of rank `m`, with no point of the scheme assumed.
* `Stacks.ProjectiveBundleSplitting.rank_restrict_kernel_eq`,
  `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible`: the
  two statements at a source of rank `m + 2`, which is the shape the splitting tower reads them
  at above its base case.

## Implementation notes

**Why no point is needed.** Rank additivity
(`AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`) is read at a stalk and so needs a
point. The point is not needed *globally*, though: the conclusion is local on the base, and the
open over which it is checked already contains a point, namely the one it was chosen around.
Restricting the whole kernel sequence to that open therefore supplies the missing argument for
free. The restriction functor is a left adjoint
(`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`), so it preserves the epimorphism, and it
preserves finite limits, so `CategoryTheory.Limits.PreservesKernel.iso` identifies the kernel of
the restricted map with the restricted kernel.

**Two spellings of finite local freeness of rank `r`.** The hypotheses and the conclusion use
the class `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, which asks for a single
cover of the whole space; the gluing step uses the pointwise
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank`, which asks for a neighbourhood of
each point. `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff` crosses between
them, and `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top` is the
gluing statement.

**The local rank is read off as a cardinality.** The trivialisation produced by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff` has an arbitrary finite index type
`I`; its rank is `Nat.card I`, and `Finite.equivFin` turns that into the equivalence with
`Fin (Nat.card I)` that
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv` wants.

## References

* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveBundleSplitting

/-- **A finite locally free module is of some constant rank near each point.** The pointwise
form of finite local freeness gives, around a point, a trivialisation with a finite index type
`I`; the rank is then the cardinality of `I`, and the free module on `I` is finite locally free
of that rank. -/
theorem exists_isFiniteLocallyFreeOfRank_restrict {P : Scheme.{u}} (F : P.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) (x : P) :
    ∃ (U : P.Opens) (_ : x ∈ U) (r : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.restrict U.ι) r := by
  obtain ⟨U, hx, I, hI, ⟨ε⟩⟩ := (Scheme.Modules.isFiniteLocallyFree_iff F).mpr hF x
  have := hI
  exact ⟨U, hx, Nat.card I,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} ε.symm
      (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv I (Nat.card I)
        (Finite.equivFin I))⟩

/-- **On an open over which the kernel has a constant rank, that rank is `m`.** Restriction
along the inclusion of the open preserves the epimorphism and the kernel, so the restricted
kernel sequence is a short exact sequence of modules of constant ranks `r`, `m + 1` and `1` on a
scheme with the point `x`; additivity of the rank then reads `m + 1 = r + 1`.

The rank of the kernel is the predecessor of the rank of the source, which is assumed only to be
positive; hence the name, and hence the rank-one source `m = 0`, where the kernel has rank zero,
is included. The form at a source of rank `m + 2` is
`Stacks.ProjectiveBundleSplitting.rank_restrict_kernel_eq`. -/
theorem rank_restrict_kernel_eq_pred {P : Scheme.{u}} {M L : P.Modules} (q : M ⟶ L) (hq : Epi q)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (m r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (m + 1))
    (U : P.Opens) (x : P) (hx : x ∈ U)
    (hker : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((kernel q).restrict U.ι) r) :
    r = m := by
  have := hq
  set q' : (M.restrict U.ι) ⟶ (L.restrict U.ι) := (Scheme.Modules.restrictFunctor U.ι).map q
    with hq'
  have : Epi q' := by rw [hq']; infer_instance
  have hS : (ShortComplex.mk (kernel.ι q') q' (kernel.condition q')).ShortExact :=
    { exact := ShortComplex.exact_kernel q' }
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (ShortComplex.mk (kernel.ι q') q' (kernel.condition q')).X₁ r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor U.ι) q) hker
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (ShortComplex.mk (kernel.ι q') q' (kernel.condition q')).X₂ (m + 1) :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
      (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff M (m + 1)).mpr hM).restrict U.ι)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (ShortComplex.mk (kernel.ι q') q' (kernel.condition q')).X₃ 1 :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
      (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff L 1).mpr
        (isFiniteLocallyFreeOfRank_one_of_isInvertible L hL)).restrict U.ι)
  have h := AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact
    (ShortComplex.mk (kernel.ι q') q' (kernel.condition q')) hS r (m + 1) 1
    (⟨x, hx⟩ : U.toScheme)
  omega

/-- **The kernel of an epimorphism from a module of rank `m + 1` onto an invertible one is
finite locally free of rank `m`.** The kernel is finite locally free by
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi_isInvertible`, hence of some
constant rank near each point; on such an open rank additivity forces that rank to be `m`,
and constant rank glues over an open cover. Unlike
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_succ` this assumes no point of
the scheme: the point is the one the trivialising open was chosen around.

The rank of the kernel is the predecessor of the rank of the source, which is assumed only to be
positive; hence the name. The rank-one source `m = 0`, where the kernel is of rank zero, is the
base case of the splitting tower of [Stacks, Tag 02UL] and is proved by the same rank additivity
as every other rank. The form at a source of rank `m + 2`, which is the shape the tower reads
above its base case, is
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible`. -/
@[sga "6 I 1.3" "special case"]
theorem isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred {P : Scheme.{u}}
    {M L : P.Modules} (q : M ⟶ L) (hq : Epi q)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (m : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (m + 1)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel q) m := by
  have hfl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (kernel q) :=
    isFiniteLocallyFree_kernel_of_epi_isInvertible q hq hM.isFiniteLocallyFree hL
  choose U hx r hr using fun x : P ↦ exists_isFiniteLocallyFreeOfRank_restrict (kernel q) hfl x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff (kernel q) m).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x ↦ ?_
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y, hx y⟩
  · have hrx : r x = m :=
      rank_restrict_kernel_eq_pred q hq hL m (r x) hM (U x) x (hx x) (hr x)
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hrx ▸ hr x)

/-- **On an open over which the kernel has a constant rank, that rank is `m + 1`.** Restriction
along the inclusion of the open preserves the epimorphism and the kernel, so the restricted
kernel sequence is a short exact sequence of modules of constant ranks `r`, `m + 2` and `1` on a
scheme with the point `x`; additivity of the rank then reads `m + 2 = r + 1`.

This is `Stacks.ProjectiveBundleSplitting.rank_restrict_kernel_eq_pred` at a source of rank at
least two. -/
theorem rank_restrict_kernel_eq {P : Scheme.{u}} {M L : P.Modules} (q : M ⟶ L) (hq : Epi q)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (m r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (m + 2))
    (U : P.Opens) (x : P) (hx : x ∈ U)
    (hker : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((kernel q).restrict U.ι) r) :
    r = m + 1 :=
  rank_restrict_kernel_eq_pred q hq hL (m + 1) r hM U x hx hker

/-- **The kernel of an epimorphism from a module of rank `m + 2` onto an invertible one is
finite locally free of rank `m + 1`.** The kernel is finite locally free by
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi_isInvertible`, hence of some
constant rank near each point; on such an open rank additivity forces that rank to be `m + 1`,
and constant rank glues over an open cover. Unlike
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_succ` this assumes no point of
the scheme: the point is the one the trivialising open was chosen around.

This is
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred`
at a source of rank at least two. -/
@[sga "6 I 1.3" "special case"]
theorem isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible {P : Scheme.{u}} {M L : P.Modules}
    (q : M ⟶ L) (hq : Epi q)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (m : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (m + 2)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel q) (m + 1) :=
  isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred q hq hL (m + 1) hM

end Stacks.ProjectiveBundleSplitting

end
