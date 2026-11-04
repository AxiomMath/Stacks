module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPoints
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# The stalk basis at a point where a module is finite locally free of a fixed rank

If a sheaf of modules on a scheme is finite locally free of rank `r` on a neighbourhood of a
point — `AlgebraicGeometry.FreeAtPointOfRank` — then its stalk at that point is free with a basis
indexed by `Fin r`.

## Main results

* `AlgebraicGeometry.exists_restrict_iso_free_le_of_freeAtPointOfRank`: the trivialisation can
  be taken inside any prescribed open containing the point.
* `AlgebraicGeometry.nonempty_basis_stalk_of_freeAtPointOfRank`: the statement above.

## Implementation notes

The rank datum on the neighbourhood is turned into an actual trivialisation over a possibly
smaller open *of the ambient scheme* by
`Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion`; that detour is what avoids the
missing `𝒪`-linear comparison between the stalk of a restriction and the stalk of the module
(Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` compares them only as abelian
groups). The trivialisation becomes a free presentation of rank `r` by
`AlgebraicGeometry.Scheme.Modules.exists_generatingSections_of_restrict_iso_of_rank`, and
`Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv` reads off the stalk as a finitely supported
function space, whose associated basis is reindexed to `Fin r`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Finite local freeness of rank `r` of a pullback along an open immersion gives it for the
restriction. -/
private theorem isFiniteLocallyFreeOfRank_restrict_of_invertible {X : Scheme.{u}}
    (F : X.Modules) (r : ℕ) (U : X.Opens)
    (h : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank (F.restrict U.ι) r :=
  Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ r).mpr
      { exists_isFiniteLocallyFreeOfRankData := h.exists_isFiniteLocallyFreeOfRankData })

/-- **A module finite locally free of rank `r` near a point is free of rank `r` on an open
neighbourhood inside any prescribed open containing the point.** -/
theorem exists_restrict_iso_free_le_of_freeAtPointOfRank {X : Scheme.{u}} (F : X.Modules)
    (x : X) (r : ℕ) (V : X.Opens) (hxV : x ∈ V) (h : FreeAtPointOfRank F x r) :
    ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      Nonempty (F.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  obtain ⟨U, hxU, hdata⟩ := h
  have hdata' := invertibleRank_pullback_of_le F r (inf_le_left : U ⊓ V ≤ U) hdata
  have hres := isFiniteLocallyFreeOfRank_restrict_of_invertible F r (U ⊓ V) hdata'
  obtain ⟨W, hxW, hWle, hiso⟩ := Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion
    (U ⊓ V).ι F r ⟨x, ⟨hxU, hxV⟩⟩ hres
  refine ⟨W, hxW, ?_, hiso⟩
  refine hWle.trans ?_
  rw [Scheme.Opens.opensRange_ι]
  exact inf_le_right

/-- **The stalk of a module which is finite locally free of rank `r` near a point has a basis
indexed by `Fin r`.** -/
theorem nonempty_basis_stalk_of_freeAtPointOfRank {X : Scheme.{u}} (F : X.Modules) (x : X)
    (r : ℕ) (h : FreeAtPointOfRank F x r) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x)) := by
  obtain ⟨U, hxU, hdata⟩ := h
  have hres := isFiniteLocallyFreeOfRank_restrict_of_invertible F r U hdata
  obtain ⟨W, hxW, -, ⟨e⟩⟩ :=
    Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion U.ι F r ⟨x, hxU⟩ hres
  obtain ⟨σ, hσ, ⟨eI⟩⟩ :=
    Scheme.Modules.exists_generatingSections_of_restrict_iso_of_rank F W r e
  have := hσ
  obtain ⟨erep⟩ := Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv W F σ hxW
  exact ⟨(Module.Basis.ofRepr erep).reindex eI⟩

end AlgebraicGeometry

end
