module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Datum
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Segre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The first Chern class of Stacks 02U6 is the Segre pushforward

For a finite locally free module `ℰ` of rank `n + 1` with projective bundle
`(π : 𝐏(ℰ) ⟶ X, 𝒪(1))`, the member `c₁(ℰ) ∩ α` of the family of Chern class cap products of
[Stacks, Tag 02U6] (`Stacks.Chow.bundleChernCapFamily`) is `π_*(c₁(𝒪(1))^{n+1} ∩ π^*α)`, the
operation `Stacks.Chow.GenuineChern.segre`; so `Stacks.Chow.GenuineChern.firstChern` is the first
Chern class of [Stacks, Tag 02U0] and [Stacks, Tag 02U6] in every rank.

## Main results

* `Stacks.Chow.segre_eq_bundleChernCapFamily_one` — `π_*(ξ^{n+1} ∩ π^*α) = c₁(ℰ) ∩ α`.
* `Stacks.Chow.firstChern_eq_bundleChernCapFamily_one` — the same for `firstChern` in rank `n + 1`.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The first Chern class is the Segre pushforward.** For `ℰ` of rank `n + 1` and
`α ∈ A_k(X)`, `π_*(c₁(𝒪(1))^{n+1} ∩ π^*α) = c₁(ℰ) ∩ α`, the member `j = 1` of the family of
Stacks 02U6. -/
@[sga "7 XVII 5.3" "partial"]
theorem segre_eq_bundleChernCapFamily_one
    (k : ℤ) (α : chowGroup C sX k) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    GenuineChern.segre E n C sX k α =
      chowGroupCast C sX (by simp) (bundleChernCapFamily E n C sX k α ⟨1, by omega⟩) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  have h := chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily C sX
    (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1) (relativeDimension_bundleProj E n)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
    (bundleTwistCap E C sX) (by omega)
    (projectiveBundleProjection_bundle_self E n C sX) k α _
    (isChernCapFamily_bundleChernCapFamily E n C sX k α)
  simp only [GenuineChern.segre, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [← h, chowGroupCast_chowGroupCast]

/-- **`Stacks.Chow.GenuineChern.firstChern` is the first Chern class of Stacks 02U6** in every
positive rank. -/
theorem firstChern_eq_bundleChernCapFamily_one
    (k : ℤ) (α : chowGroup C sX k) :
    GenuineChern.firstChern E C sX (n + 1) k α =
      chowGroupCast C sX (by simp) (bundleChernCapFamily E n C sX k α ⟨1, by omega⟩) :=
  segre_eq_bundleChernCapFamily_one E n C sX k α

end Stacks.Chow

end
