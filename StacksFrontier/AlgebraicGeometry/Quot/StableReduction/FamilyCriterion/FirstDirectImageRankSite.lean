module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# Finite local freeness of rank `r` on a scheme and on its small Zariski ringed site

A sheaf of modules `M` on a scheme `X` which is free of rank `r` on an open neighbourhood of
every point, `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank M r`, is finite locally
free of rank `r` on the small Zariski ringed site of `X` in the sense of Stacks 0409,
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank X.zariskiRingedSite M r`: the chosen
neighbourhoods cover the final object of the site, and over each of them the trivialization
gives a presentation of `M` as a coproduct of `r` copies of the structure sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank.
  isFiniteLocallyFreeOfRank_zariskiRingedSite`: the pointwise form implies the site form.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Pointwise rank `r` gives rank `r` on the small Zariski ringed site.** A sheaf of modules on
a scheme which is free of rank `r` on an open neighbourhood of every point is finite locally free
of rank `r` on the small Zariski ringed site of the scheme. -/
theorem IsFiniteLocallyFreeOfRank.isFiniteLocallyFreeOfRank_zariskiRingedSite {X : Scheme.{u}}
    {M : X.Modules} {r : ℕ} (h : IsFiniteLocallyFreeOfRank M r) :
    RingedSite.IsFiniteLocallyFreeOfRank X.zariskiRingedSite M r := by
  classical
  choose U hU hiso using h
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit
    X.zariskiRingedSite M r).2 ⟨X, U, ?_, fun x => ?_⟩
  · refine (Opens.coversTop_iff (X : Type u) U).mpr (eq_top_iff.mpr fun x _ => ?_)
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨x, hU x⟩
  · obtain ⟨σ, hσ, ⟨eσ⟩⟩ :=
      exists_generatingSections_of_restrict_iso_of_rank M (U x) r (hiso x).some
    have hc : IsColimit (Cofan.mk (M.over (U x))
        (fun j : σ.I => SheafOfModules.ιFree j ≫ σ.π)) :=
      IsColimit.ofIsoColimit (SheafOfModules.isColimitFreeCofan σ.I)
        (Cocone.ext (@asIso _ _ _ _ _ hσ) (by rintro ⟨j⟩; rfl))
    exact ⟨fun j => SheafOfModules.ιFree (eσ.symm j) ≫ σ.π,
      ⟨(Cofan.isColimitEquivOfEquiv eσ.symm
        (Cofan.mk (M.over (U x)) (fun j : σ.I => SheafOfModules.ιFree j ≫ σ.π))) hc⟩⟩

end AlgebraicGeometry.Scheme.Modules

end
