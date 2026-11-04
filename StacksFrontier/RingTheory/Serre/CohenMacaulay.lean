module

public import StacksFrontier.RingTheory.CohenMacaulay.Defs
import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohen–Macaulay rings satisfy Serre's condition `(Sₖ)`

Property `(Sₖ)` asks that `depth R_𝔭 ≥ min(k, dim R_𝔭)` at every prime `𝔭`. A Cohen–Macaulay
ring has `depth R_𝔭 = dim R_𝔭` at every prime, so the minimum is bounded by its second argument
and the condition holds for every `k`.

The only work is bookkeeping between the three depths the library carries for a Noetherian local
ring: `localRingDepth`, used in the definition of Cohen–Macaulayness; `ringDepth`, used in the
definition of `(Sₖ)`; and `Module.depth R 𝔪 R`, through which the two are compared. All three
agree because the maximal ideal of a local ring does not satisfy `𝔪 • ⊤ = ⊤`.

## Main results

* `Stacks.propertySkRing_of_isCohenMacaulayRing` — a Cohen–Macaulay Noetherian ring satisfies
  `(Sₖ)` for every `k`.

## References

* [Stacks Project, Tag 00NC](https://stacks.math.columbia.edu/tag/00NC)
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P)
-/

@[expose] public section

namespace Stacks

/-- For a Noetherian local ring the depth used in the definition of Cohen–Macaulayness agrees
with the depth of the ring as a module over itself along its maximal ideal. -/
private theorem localRingDepth_eq_moduleDepth (A : Type*) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    (localRingDepth A : WithBot ℕ∞) =
      (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) := by
  have hne : IsLocalRing.maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  exact_mod_cast (show localRingDepth A = Module.depth A (IsLocalRing.maximalIdeal A) A by
    rw [localRingDepth, Module.depth, ite_eq_right hne]
    simp only [iSup_subtype, Set.mem_ofPred_eq])

/-- **A Cohen–Macaulay Noetherian ring satisfies Serre's condition `(Sₖ)` for every `k`.** At
each prime the depth of the localization equals its dimension, so it dominates
`min(k, dim R_𝔭)`. -/
theorem propertySkRing_of_isCohenMacaulayRing (R : Type*) [CommRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayRing R) (k : ℕ) : PropertySkRing R k := by
  intro p hp
  have : p.IsPrime := hp
  have hcm := hR p
  rw [IsCohenMacaulayLocalRingPropForm, localRingDepth_eq_moduleDepth] at hcm
  rw [ringDepth_eq_depth_maximalIdeal]
  have hdim : (ringKrullDim (Localization.AtPrime p)).unbotD 0 =
      Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) := by
    simpa using (congrArg (WithBot.unbotD 0) hcm).symm
  rw [hdim]
  exact min_le_right _ _

end Stacks
