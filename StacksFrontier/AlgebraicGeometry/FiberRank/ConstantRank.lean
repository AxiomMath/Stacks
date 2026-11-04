module

public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constant fibre rank and finite local freeness of a fixed rank

A finite locally free module has locally constant fibre rank, and on a member of any of its
local free bases the fibre rank is the cardinality of that basis. Conversely, an open subset on
which the fibre rank is constantly `r` is one over which the module becomes finite locally free
of rank `r`: the members of a local free basis meeting that open are bases of exactly `r`
sections there, and they restrict to a local free basis of rank `r` of the restricted module.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank`: a module which
  is finite locally free of rank `r` has fibre rank constantly `r`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq` and
  `isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq`: a finite locally free module whose
  fibre rank is constantly `r` on an open set is finite locally free of rank `r` there.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_unique`: on a nonempty scheme the
  rank of a finite locally free module is determined.

## Implementation notes

The rank is read off the fibre rank rather than off a cardinal-valued rank function, so the
constant-rank locus of a finite locally free module is a fibre of a locally constant
`ℕ`-valued function and is therefore open.

## References

* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Stacks Project, Tag 01C9.** A module which is finite locally free of rank `r` has fibre
rank constantly `r`: every point lies in a member of a local free basis of `r` sections, where
the fibre rank is the cardinality of that basis. -/
public theorem fiberRank_eq_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} (F : X.Modules)
    (r : ℕ) [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (x : X) :
    fiberRank F x = r := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  have : Finite (q.generators i).I := Finite.of_equiv _ (hr i).some.symm
  rw [Stacks.FiniteLocallyFree.ModuleTFAE.fiberRank_eq_card_of_trivialization F q hq i x hxi,
    Nat.card_eq_of_equiv_fin (hr i).some]

/-- **Stacks Project, Tag 01C9.** A finite locally free module whose fibre rank is constantly
`r` on an open set `U` restricts to a module which is finite locally free of rank `r` on `U`.

A point of `U` lies in a member `W` of a local free basis of the module, and there the fibre
rank is the cardinality of that basis; the hypothesis pins that cardinality to `r`. The
trivialization over `W` restricts to one over `U ∩ W`, so the restriction to `U` has a local
free basis of `r` sections near every point. -/
public theorem isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq {X : Scheme.{u}}
    (F : X.Modules) [h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (U : X.Opens) (r : ℕ)
    (hr : ∀ x : X, x ∈ U → fiberRank F x = r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.restrict U.ι) r := by
  classical
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  have hpt : ∀ z : U.toScheme, ∃ (W : U.toScheme.Opens) (_ : z ∈ W) (I : Type u),
      Nonempty (I ≃ Fin r) ∧
      Nonempty ((F.restrict U.ι).restrict W.ι ≅ _root_.SheafOfModules.free.{u} I) := by
    intro z
    obtain ⟨i, hzi⟩ := ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem (U.ι.base z)
    have : Finite (q.generators i).I := (hfin.isFiniteType i).finite
    have hcard : Nat.card (q.generators i).I = r :=
      (Stacks.FiniteLocallyFree.ModuleTFAE.fiberRank_eq_card_of_trivialization
          F q hq i _ hzi).symm.trans (hr _ z.2)
    obtain ⟨e⟩ := nonempty_restrict_iso_free_of_isLocallyFreeData F q hq i
    have hrange : Set.range ((U.ι ⁻¹ᵁ q.X i).ι ≫ U.ι).base ⊆
        Set.range (Scheme.Opens.ι (q.X i)).base := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨y.1.1, y.2⟩, rfl⟩
    obtain ⟨e'⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset
      (Scheme.Opens.ι (q.X i)) ((U.ι ⁻¹ᵁ q.X i).ι ≫ U.ι) F (q.generators i).I hrange e
    exact ⟨U.ι ⁻¹ᵁ q.X i, hzi, (q.generators i).I, ⟨Finite.equivFinOfCardEq hcard⟩,
      ⟨((Scheme.Modules.restrictFunctorComp (U.ι ⁻¹ᵁ q.X i).ι U.ι).app F).symm ≪≫ e'⟩⟩
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
    (exists_isFiniteLocallyFreeOfRankData_of_pointwise (F.restrict U.ι) r hpt)

/-- **Stacks Project, Tag 01C9.** The pullback form of
`isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq`: a finite locally free module whose fibre
rank is constantly `r` on an open set pulls back to a module which is finite locally free of
rank `r` there. -/
public theorem isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq {X : Scheme.{u}}
    (F : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (U : X.Opens) (r : ℕ)
    (hr : ∀ x : X, x ∈ U → fiberRank F x = r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F)
    (isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq F U r hr)

/-- The rank of a finite locally free module on a nonempty scheme is determined: both candidate
ranks are the fibre rank at any point. -/
@[sga "6 I 6.10" "special case"]
public theorem isFiniteLocallyFreeOfRank_unique {X : Scheme.{u}} (F : X.Modules) {r s : ℕ}
    (hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r)
    (hs : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s) (x : X) : r = s :=
  (fiberRank_eq_of_isFiniteLocallyFreeOfRank F r x).symm.trans
    (fiberRank_eq_of_isFiniteLocallyFreeOfRank F s x)

end AlgebraicGeometry.Scheme.Modules

end
