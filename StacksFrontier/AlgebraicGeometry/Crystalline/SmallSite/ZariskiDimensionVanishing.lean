module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImage
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpacesCoefficientUniverse

/-!
# The Zariski-side dimension bound of [Stacks, Tag 07MR], clause (1)

Let `X` be the scheme of a global crystalline situation, with `S₀` having at most one point and
`X → S₀` quasi-compact and quasi-separated. Then the space of `X` is spectral, and if it has
topological Krull dimension at most `d`, every abelian sheaf on the small Zariski site `X_Zar`,
with coefficients in `AddCommGrpCat.{u + 1}`, has vanishing cohomology in every degree above `d`.
This is clause (1) of [Stacks, Tag 0A3G] at the site and the universes of the crystalline chapter,
where the coefficient universe `u + 1` differs from the universe `u` of the space.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.compactSpace_of_subsingleton_closedFiber` and
  `...quasiSeparatedSpace_of_subsingleton_closedFiber`: under the hypotheses of [Stacks, Tag 07MR]
  — `S₀` with at most one point and `X → S₀` quasi-compact and quasi-separated — the space of `X`
  is quasi-compact and quasi-separated.
* `...spectralSpace_of_subsingleton_closedFiber`: hence spectral, by [Stacks, Tag 094L].
* `...subsingleton_zariskiSheafH_of_topologicalKrullDim_le`: on the small Zariski site of such an
  `X`, of Krull dimension at most `d`, every abelian sheaf in `AddCommGrpCat.{u + 1}` has vanishing
  cohomology in every degree above `d`.
* `...isZero_rightDerivedZariskiGlobalSections_of_topologicalKrullDim_le`: the same, as the
  vanishing of `R^q Γ(X_Zar, -)` for `q > d`.

## References

* [Stacks Project, Tag 07MR](https://stacks.math.columbia.edu/tag/07MR)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 094L](https://stacks.math.columbia.edu/tag/094L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The space of `X` is spectral under the hypotheses of [Stacks, Tag 07MR] -/

/-- If `S₀` has at most one point and `X → S₀` is quasi-compact, then `X` is quasi-compact. -/
theorem compactSpace_of_subsingleton_closedFiber
    (hsub : Subsingleton ↥(DividedPowerScheme.closedFiber S.S))
    (hqc : QuasiCompact S.toClosedFiber) : CompactSpace ↥S.X :=
  QuasiCompact.compactSpace_of_compactSpace S.toClosedFiber

/-- If `S₀` has at most one point and `X → S₀` is quasi-separated, then `X` is quasi-separated. -/
theorem quasiSeparatedSpace_of_subsingleton_closedFiber
    (hsub : Subsingleton ↥(DividedPowerScheme.closedFiber S.S))
    (hqs : QuasiSeparated S.toClosedFiber) : QuasiSeparatedSpace ↥S.X :=
  have : QuasiSeparatedSpace ↥(DividedPowerScheme.closedFiber S.S) :=
    ⟨fun U V _ _ _ _ => (Set.toFinite (U ∩ V)).isCompact⟩
  quasiSeparatedSpace_of_quasiSeparated S.toClosedFiber

/-- If `S₀` has at most one point and `X → S₀` is quasi-compact and quasi-separated, then the space
of `X` is spectral. -/
theorem spectralSpace_of_subsingleton_closedFiber
    (hsub : Subsingleton ↥(DividedPowerScheme.closedFiber S.S))
    (hqc : QuasiCompact S.toClosedFiber) (hqs : QuasiSeparated S.toClosedFiber) :
    SpectralSpace ↥S.X :=
  have := compactSpace_of_subsingleton_closedFiber S hsub hqc
  have := quasiSeparatedSpace_of_subsingleton_closedFiber S hsub hqs
  spectralSpace_of_compactSpace_of_quasiSeparatedSpace S.X

/-! ### The Zariski-side dimension bound -/

/-- Abelian sheaves on the small Zariski site of `X` have `Ext`-groups in the universe `u + 1`. -/
instance instHasExtOpens :
    HasExt.{u + 1} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-- Let `X` be the scheme of a global crystalline situation, quasi-compact and quasi-separated as a
space, of topological Krull dimension at most `d`. Then every abelian sheaf on the small Zariski
site `X_Zar`, with coefficients in `AddCommGrpCat.{u + 1}`, has vanishing cohomology in every
degree above `d`. -/
theorem subsingleton_zariskiSheafH_of_topologicalKrullDim_le
    [CompactSpace ↥S.X] [QuasiSeparatedSpace ↥S.X]
    (G : Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) (d q : ℕ)
    (hdim : topologicalKrullDim ↥S.X ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1, u, u} G q) :=
  have : SpectralSpace ↥S.X := spectralSpace_of_compactSpace_of_quasiSeparatedSpace S.X
  Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le_succ
    d ↥S.X G q hdim hq

/-- Let `X` be the scheme of a global crystalline situation, quasi-compact and quasi-separated as a
space, of topological Krull dimension at most `d`. Then the right derived functors
`R^q Γ(X_Zar, -)` vanish on every abelian sheaf for `q > d`. -/
theorem isZero_rightDerivedZariskiGlobalSections_of_topologicalKrullDim_le
    [CompactSpace ↥S.X] [QuasiSeparatedSpace ↥S.X]
    (G : Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) (d q : ℕ)
    (hdim : topologicalKrullDim ↥S.X ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    IsZero (((zariskiGlobalSections S).rightDerived q).obj G) :=
  (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1, u, u}
    (opensTopology S) G q).1
      (subsingleton_zariskiSheafH_of_topologicalKrullDim_le S G d q hdim hq)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
