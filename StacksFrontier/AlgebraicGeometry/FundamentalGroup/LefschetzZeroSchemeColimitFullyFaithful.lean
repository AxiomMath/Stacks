module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzNeighbourhoodSectionsComplete
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NeighbourhoodCompletionConditions
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SectionsExtendFromCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.LefschetzZeroSchemeSectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsAtFactor

/-!
# Full faithfulness of `colim_𝒱 FÉt_V ⟶ FÉt_Y` for the zero scheme of an ample section

Let `k` be a field, `X` a proper scheme over `k`, `L` an ample invertible `𝒪_X`-module, `s` a
global section of `L`, `Y = Z(s)` its zero scheme and `𝒱` the open neighbourhoods of `Y`. If

`depth(𝒪_{X, x}) + dim({x}‾) > 2`

at every point `x ∉ Y`, then the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful.
This is the full faithfulness half of [Stacks, Tag 0ELD], which the source derives as a formal
consequence of [Stacks, Tag 0EL7] and [Stacks, Tag 0EK1].

## The proof

* [Stacks, Tag 0EL2]
  (`Stacks.Algebraization.SectionRingCone.sectionsCompleteAmplePowers_zeroScheme_of_depth`)
  gives an ample invertible module `L₀` (a power of `L`) whose large powers `L₀^{⊗ m}` have
  `Γ(X, L₀^{⊗ m}) → lim Γ(Y_n, L₀^{⊗ m}|_{Y_n})` bijective, and
  `Stacks.Algebraization.SectionRingCone.bijective_restrict_of_depthAddDimGtOne` makes
  `Γ(X, L₀^{⊗ m}) → Γ(V, L₀^{⊗ m})` bijective for every open `V ⊇ Y`. Together these are the
  completeness of the colimit of the sections over the neighbourhoods of `Y`
  (`Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_isInfinitesimalSectionsComplete`),
  which is condition (2) of [Stacks, Tag 0EK0].
* `(2) ⇒ (4)` of [Stacks, Tag 0EK2]
  (`completionFullyFaithfulComplete_of_neighbourhoodSectionsCompleteAmplePowers`)
  makes completion `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` fully faithful on finite locally free objects.
* [Stacks, Tag 0ELA]
  (`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete`)
  concludes.

The bound `> 2` of [Stacks, Tag 0ELD] is only used through the weaker bound `> 1` of
[Stacks, Tag 0EL2].

## Main results

* `Stacks.FundamentalGroup.neighbourhoodSectionsCompleteAmplePowers_zeroScheme_of_depth`
* `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_zeroScheme_of_depth` — the full
  faithfulness half of [Stacks, Tag 0ELD].

## References

* [Stacks Project, Tag 0ELD](https://stacks.math.columbia.edu/tag/0ELD)
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
* [Stacks Project, Tag 0EK0](https://stacks.math.columbia.edu/tag/0EK0)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.FundamentalGroup

/-- **Condition (2) of [Stacks, Tag 0EK0] for the zero scheme of an ample section**, from the
depth bound `> 1` of [Stacks, Tag 0EL2]. -/
public theorem neighbourhoodSectionsCompleteAmplePowers_zeroScheme_of_depth
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : Γ(L, ⊤))
    (hdepth : DepthAddDimGtOneOutsideSupport X (zeroScheme X L s)) :
    NeighbourhoodSectionsCompleteAmplePowers (zeroScheme X L s) := by
  have hLs : Stacks.Ample.IsAmple X L :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mp hL
  obtain ⟨L₀, hL₀, hample, N, hN⟩ :=
    Stacks.Algebraization.SectionRingCone.sectionsCompleteAmplePowers_zeroScheme_of_depth k g L hL
      s hdepth
  have := hL₀
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAmple k g L hL
  have : Stacks.Ample.IsInvertibleModule X L₀ :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  refine ⟨L₀, hL₀, hample, N, fun m hm => ?_⟩
  set G := Stacks.Ample.tensorPowModule X L₀ (m : ℤ)
  have : G.IsCoherent :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_tensorPowModule L₀ _
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G :=
    Stacks.Algebraization.isFiniteLocallyFree_tensorPowModule L₀ _
  have hGX :
      Stacks.Algebraization.IsInfinitesimalSectionsComplete (zeroScheme X L s).subschemeι G :=
    Stacks.Algebraization.isInfinitesimalSectionsComplete_of_iso _
      (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X L₀ (m : ℤ)) (hN m hm)
  have hG :=
    Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_isInfinitesimalSectionsComplete _ G hGX
      fun V hV => Stacks.Algebraization.SectionRingCone.bijective_restrict_of_depthAddDimGtOne
        L k g hLs s hdepth V (by rwa [Scheme.IdealSheafData.range_subschemeι] at hV) G
  exact Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_iso _
    (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X L₀ (m : ℤ)).symm hG

/-- **The full faithfulness half of [Stacks, Tag 0ELD].** Let `k` be a field, `X` a proper scheme
over `k`, `L` an ample invertible `𝒪_X`-module, `s ∈ Γ(X, L)` and `Y = Z(s)`. If
`depth(𝒪_{X, x}) + dim({x}‾) > 2` at every point `x ∉ Y`, then the restriction functor
`colim_𝒱 FÉt_V ⟶ FÉt_Y` from the finite étale covers of the open neighbourhoods `V` of `Y` is
fully faithful: every morphism of restrictions to `Y` comes from a morphism over a smaller
neighbourhood, and two morphisms with the same restriction agree on a smaller neighbourhood. -/
public theorem finiteEtaleColimitFullyFaithful_zeroScheme_of_depth
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : Γ(L, ⊤))
    (hdepth : DepthAddDimGtTwoOutsideSupport X (zeroScheme X L s)) :
    FiniteEtaleColimitFullyFaithful X (zeroScheme X L s) := by
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAmple k g L hL
  exact finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete X _
    (completionFullyFaithfulComplete_of_neighbourhoodSectionsCompleteAmplePowers _
      (neighbourhoodSectionsCompleteAmplePowers_zeroScheme_of_depth k g L hL s
        (depthAddDimGtOneOutsideSupport_of_gtTwo hdepth)))

end Stacks.FundamentalGroup

end
