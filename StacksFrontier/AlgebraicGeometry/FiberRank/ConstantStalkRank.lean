module

public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf

/-!
# A finite locally free module of constant fibre rank has that rank

A finite locally free sheaf of modules on a scheme whose fibre rank is the same natural number
`r` at every point of the scheme is finite locally free of rank `r`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq`: constant
  fibre rank `r` upgrades finite local freeness to finite local freeness of rank `r`.

## References

* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free sheaf of modules whose fibre rank is `r` at every point of the scheme
is finite locally free of rank `r`. -/
public theorem isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq {X : Scheme.{u}}
    (F : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (r : ℕ)
    (hr : ∀ x : X, fiberRank F x = r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r := by
  have hres : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.restrict (⊤ : X.Opens).ι) r :=
    isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq F ⊤ r fun x _ => hr x
  have htop : IsFiniteLocallyFreeOfRank F r :=
    isFiniteLocallyFreeOfRank_of_iSup_eq_top (ι := PUnit.{u + 1}) (fun _ => (⊤ : X.Opens))
      (by simp) fun _ => (isFiniteLocallyFreeOfRank_iff _ r).2 hres
  exact (isFiniteLocallyFreeOfRank_iff F r).1 htop

end AlgebraicGeometry.Scheme.Modules

end
