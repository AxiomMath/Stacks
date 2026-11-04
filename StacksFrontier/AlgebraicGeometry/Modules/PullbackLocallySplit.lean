module

public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Stalk

/-!
# An arbitrary pullback keeps a short exact sequence with finite locally free quotient exact

Let `g : T ⟶ Y` be a morphism of schemes and let `0 → ℰ → ℱ → 𝒢 → 0` be a short exact sequence
of `𝒪_Y`-modules whose quotient `𝒢` is finite locally free. Then

  `0 → g^*ℰ → g^*ℱ → g^*𝒢 → 0`

is short exact, with no flatness hypothesis on `g`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree`: **a short
  exact sequence of `𝒪_Y`-modules whose quotient is finite locally free stays short exact after
  pullback along an arbitrary morphism of schemes.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **A short exact sequence of `𝒪_Y`-modules whose quotient is finite locally free stays short
exact after pullback along an arbitrary morphism of schemes**, with no flatness hypothesis. -/
theorem shortExact_map_pullback_of_isFiniteLocallyFree {T Y : Scheme.{u}} (g : T ⟶ Y)
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) S.X₃] :
    (S.map (Scheme.Modules.pullback g)).ShortExact := by
  choose U hU hsp using fun y : Y ↦
    exists_nonempty_splitting_restrict_of_isFiniteLocallyFree S hS y
  refine Stacks.SheafOfModules.shortExact_of_forall_restrict
    (fun t : T ↦ (g ⁻¹ᵁ U (g t)).ι) _ (fun t ↦ ⟨t, ⟨t, hU (g t)⟩, rfl⟩) fun t ↦ ?_
  obtain ⟨sp⟩ := hsp (g t)
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.mapNatIso S
      (Stacks.Modules.restrictPullbackIso g (le_refl (g ⁻¹ᵁ U (g t))))).symm
    (sp.map (Scheme.Modules.pullback (g.resLE (U (g t)) (g ⁻¹ᵁ U (g t)) le_rfl))).shortExact

end AlgebraicGeometry.Scheme.Modules

end
