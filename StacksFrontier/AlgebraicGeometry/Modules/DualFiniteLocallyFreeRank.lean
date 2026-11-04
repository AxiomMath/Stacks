module

public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation

/-!
# Finite local freeness of constant rank from local trivialisations

Let `X` be a scheme and `ℱ` an `𝒪_X`-module which near every point is free on an index set
equivalent to `Fin r`. Then `ℱ` is finite locally free of rank `r`. That the dual of a finite
locally free module of rank `r` has rank `r` is
`Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf` of
`StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree`.

## Main results

* `isFiniteLocallyFreeOfRank_of_forall_exists_iso_free_over`: finite local freeness of rank `r`
  from local isomorphisms with free modules on index sets of cardinality `r`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **Finite local freeness of constant rank from local trivialisations.** A module which near
every point is free on an index set in bijection with `Fin r` is finite locally free of rank
`r`. -/
theorem isFiniteLocallyFreeOfRank_of_forall_exists_iso_free_over {X : Scheme.{u}}
    (F : X.Modules) (r : ℕ)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (I : Type u) (_ : Nonempty (I ≃ Fin r)),
      Nonempty (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
        (F : _root_.SheafOfModules.{u} X.ringCatSheaf).over U)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) F r := by
  choose U hU I hI e using h
  have hfin : ∀ x, Finite (I x) := fun x => Finite.of_equiv _ (hI x).some.symm
  constructor
  exact ⟨{
    I := (X : Type u)
    X := U
    coversTop := by
      rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, eq_top_iff]
      exact fun x _ => Opens.mem_iSup.2 ⟨x, hU x⟩
    generators := fun x => (_root_.SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U x)) (I x)).ofEpi (e x).some.hom },
    ⟨fun x => SheafOfModules.isIso_free_generatingSections_ofEpi_π (I x) (e x).some⟩, hI⟩

end Stacks.AlgebraicGeometry.ReflexiveModules

end
