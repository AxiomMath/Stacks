module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel of a locally free quotient has constant rank

Let `q : ℳ ⟶ ℒ` be an epimorphism of modules on a scheme with `ℳ` finite locally free of rank
`m` and `ℒ` finite locally free of rank `r`. Then `ker q` is finite locally free of rank `m - r`,
with no point of the scheme assumed. The case of an invertible `ℒ` and a source of rank `m + 2`
is `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible`.

## Main results

* `Stacks.ProjectiveBundleSplitting.rank_restrict_kernel_add_eq`: on a trivialising open of the
  kernel of an epimorphism of modules of constant ranks `m` and `r`, the rank `e` of the
  restricted kernel satisfies `m = e + r`.
* `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi`: the kernel of an
  epimorphism of finite locally free modules of constant ranks `m` and `r` is finite locally free
  of rank `m - r`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveBundleSplitting

/-- **On an open over which the kernel of an epimorphism of modules of constant ranks `m` and `r`
has a constant rank `e`, one has `m = e + r`.** Restriction along the inclusion of the open
preserves the epimorphism and the kernel, so the restricted kernel sequence is a short exact
sequence of modules of constant ranks `e`, `m` and `r` on a scheme with the point `x`; this is
additivity of the rank. -/
theorem rank_restrict_kernel_add_eq {P : Scheme.{u}} {M L : P.Modules} (q : M ⟶ L) (hq : Epi q)
    (m r e : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M m)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L r)
    (U : P.Opens) (x : P) (hx : x ∈ U)
    (hker : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((kernel q).restrict U.ι) e) :
    m = e + r := by
  have := hq
  have restrict_rank : ∀ (N : P.Modules) (n : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N n →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (N.restrict U.ι) n :=
    fun N n h ↦ (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
      (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff N n).mpr h).restrict U.ι)
  set q' : (M.restrict U.ι) ⟶ (L.restrict U.ι) := (Scheme.Modules.restrictFunctor U.ι).map q
    with hq'
  have : Epi q' := by rw [hq']; infer_instance
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (PreservesKernel.iso (Scheme.Modules.restrictFunctor U.ι) q) hker
  have := restrict_rank M m hM
  have := restrict_rank L r hL
  exact AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact
    (ShortComplex.mk (kernel.ι q') q' (kernel.condition q'))
    { exact := ShortComplex.exact_kernel q' } e m r (⟨x, hx⟩ : U.toScheme)

/-- **The kernel of an epimorphism of finite locally free modules of constant ranks `m` and `r`
is finite locally free of rank `m - r`**, with no point of the scheme assumed. The kernel is
finite locally free by `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi`,
hence of some constant rank `e` near each point, and there `m = e + r` by additivity of the rank;
constant rank glues over an open cover. -/
@[sga "6 I 1.3" "special case"]
theorem isFiniteLocallyFreeOfRank_kernel_of_epi {P : Scheme.{u}} {M L : P.Modules}
    (q : M ⟶ L) (hq : Epi q) (m r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M m)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel q) (m - r) := by
  have hfl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (kernel q) :=
    isFiniteLocallyFree_kernel_of_epi q hq hM.isFiniteLocallyFree hL.isFiniteLocallyFree
  choose U hx e he using fun x : P ↦ exists_isFiniteLocallyFreeOfRank_restrict (kernel q) hfl x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff (kernel q) (m - r)).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x ↦ ?_
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y, hx y⟩
  · have hex : e x = m - r := by
      have := rank_restrict_kernel_add_eq q hq m r (e x) hM hL (U x) x (hx x) (he x)
      omega
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hex ▸ he x)

end Stacks.ProjectiveBundleSplitting

end
