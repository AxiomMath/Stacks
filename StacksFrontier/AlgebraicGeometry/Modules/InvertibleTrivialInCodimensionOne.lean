module

public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree

/-!
# An invertible module trivial in codimension one on a normal scheme is trivial

Let `X` be a normal locally Noetherian scheme, let `U ⊆ X` be an open containing every point `x`
with `dim 𝒪_{X,x} ≤ 1`, and let `ℒ` be a coherent invertible `𝒪_X`-module. If `ℒ|_U ≅ 𝒪_U`, then
`ℒ ≅ 𝒪_X`.

At a point `x ∉ U` the local ring is normal of dimension at least two, so it has depth at least
two (Serre's criterion), and so does the stalk `ℒ_x ≅ 𝒪_{X,x}`. By [Stacks, Tag 0E9I] both `ℒ`
and `𝒪_X` are the direct images of their restrictions to `U`, so the isomorphism over `U` extends.

## Main results

* `AlgebraicGeometry.nonempty_iso_unit_of_pullback_iso`: the statement above.

## References

* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- On a normal locally Noetherian scheme the stalks of an invertible module have depth at least
two at every point whose local ring has dimension at least two. -/
theorem two_le_depth_stalk_of_isInvertible {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X)
    (hx : (2 : ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)) :
    let M := TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x
    letI : Module (X.presheaf.stalk x) M :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier L.val x
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      M := by
  intro M
  obtain ⟨e⟩ := Stacks.InvertibleStalk.nonempty_linearEquiv_stalk L x
  have key := VectorBundleCodimensionOne.two_le_depth_stalk_of_isNormal x hx
  rwa [← Module.depth_eq_depth_of_linearEquiv _ e] at key

/-- **An invertible module on a normal scheme that is trivial over an open containing all points
of codimension at most one is trivial**, by [Stacks, Tag 0E9I]. -/
theorem nonempty_iso_unit_of_pullback_iso {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] [L.IsCoherent]
    (U : X.Opens) (hU : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅
      (Scheme.Modules.pullback U.ι).obj (SheafOfModules.unit X.ringCatSheaf)) :
    Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf) := by
  have h2 : ∀ x : X, x ∉ (U : Set X) → (2 : ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
    intro x hx
    by_contra h
    refine hx (hU x ?_)
    rcases hd : ringKrullDim (X.presheaf.stalk x) with _ | n
    · exact bot_le
    · rw [hd] at h
      have hn : ¬ (2 : ℕ∞) ≤ n := fun h' => h (WithBot.coe_le_coe.2 h')
      have : n ≤ 1 := Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using not_le.1 hn)
      exact WithBot.coe_le_coe.2 this
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_unit X
  have hL := isIso_unit_restrict_pushforward_of_depth_ge_two
    X L U fun x hx => two_le_depth_stalk_of_isInvertible L x (h2 x hx)
  have hO := isIso_unit_restrict_pushforward_of_depth_ge_two
    X (SheafOfModules.unit X.ringCatSheaf) U fun x hx =>
      two_le_depth_stalk_of_isInvertible _ x (h2 x hx)
  exact ⟨asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L) ≪≫
    (Scheme.Modules.pushforward U.ι).mapIso e ≪≫
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app _)).symm⟩

end AlgebraicGeometry

end
