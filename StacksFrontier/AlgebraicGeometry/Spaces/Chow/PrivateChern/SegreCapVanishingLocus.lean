module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.RelativeEffectiveCartierChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreCapDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# The Segre operations along the vanishing locus of a section of a projective bundle

Let `(π : P ⟶ X, 𝒪_P(1))` be a projective bundle datum of fibre dimension `d + 1` over a good
space `X`, `ℒ` an invertible `𝒪_X`-module and `𝒩` an invertible `𝒪_P`-module with a global
section `σ` whose vanishing locus `i : Q = Z(σ) → P` is a relative effective Cartier divisor over
`X`. Then `Q` with `π|_Q` and `𝒪_P(1)|_Q` is a projective bundle datum of fibre dimension `d`
(`AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.vanishingLocusDatum`), and if
`c₁(𝒪_P(1)) = c₁(𝒩) + c₁(π^*ℒ)` on `CH_*(P)`, then

  `t_{n+1}(P) = t_{n+1}(Q) + t_n(P) ∘ (c₁(ℒ) ∩ -)`:

`c₁(𝒪_P(1)) ∩ π^*α = c₁(𝒩) ∩ π^*α + π^*(c₁(ℒ) ∩ α) = i_*((π|_Q)^*α) + π^*(c₁(ℒ) ∩ α)` by Stacks
0ERE and Stacks 0EQR, the projection formula along `i` is Stacks 0EQT for a closed immersion and
`π_* i_* = (π|_Q)_*` is Stacks 0EP2.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.vanishingLocusDatum`

## Main results

* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.segreCap_succ_eq_vanishingLocusDatum`

## References

* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

namespace ProjectiveBundleDatum

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} {d : ℕ} (P : ProjectiveBundleDatum D sX hX (d + 1))
  (N : Modules.{u, u} D.site D.base D.base_mem P.space P.isGood.1)
  (σ : N.sections)
  (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
    (ObjectProperty.homMk P.proj : (⟨P.space, P.isGood.1⟩ : AlgebraicSpaces D.site D.base
      D.base_mem) ⟶ ⟨X, hX.1⟩) (vanishingLocus D P.toBase P.isGood N σ))

/-- **The vanishing locus of a section as a projective bundle datum** of one dimension less: the
closed subspace `Q = Z(σ) ⊆ P` with the restriction of the projection and of the twist, when `Q`
is a relative effective Cartier divisor over `X`. -/
def vanishingLocusDatum : ProjectiveBundleDatum D sX hX d where
  space := (vanishingLocus D P.toBase P.isGood N σ).1.toFunctor
  toBase := (vanishingLocus D P.toBase P.isGood N σ).1.ι ≫ P.toBase
  isGood := isGood_closedSubspace D P.toBase P.isGood _
  proj := (vanishingLocus D P.toBase P.isGood N σ).1.ι ≫ P.proj
  proj_comp := by rw [Category.assoc, P.proj_comp]
  isProper := isProper_comp' D.site D.base D.base_mem _ _ P.isGood.1 hX.1
    (isProper_closedSubspace_ι D P.toBase P.isGood _) P.isProper
  isFlat := hE.2
  hasRelativeDimension :=
    hasRelativeDimension_ι_comp D P.toBase P.isGood sX hX P.proj P.proj_comp d
      P.hasRelativeDimension _ hE
  twist := closedSubspaceModuleRestrict D P.toBase P.isGood P.twist _
  isInvertible_twist := modulePullbackInvertible
    (closedSubspaceHom D.site D.base D.base_mem P.isGood.1 _ _) P.twist P.isInvertible_twist

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
  (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
  (hN : IsInvertibleSheaf D P.toBase P.isGood N)

/-- **The Segre operations along the vanishing locus**: if `c₁(𝒪_P(1)) = c₁(𝒩) + c₁(π^*ℒ)` and
`Z(σ)` is a relative effective Cartier divisor over `X`, then
`t_{n+1}(P) = t_{n+1}(Z(σ)) + t_n(P) ∘ (c₁(ℒ) ∩ -)`. -/
theorem segreCap_succ_eq_vanishingLocusDatum
    (htensor : ∀ β, P.twistCap β = firstChernCapChow.{u, u + 1} D P.toBase P.isGood N
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN) β +
      firstChernCapChow.{u, u + 1} D P.toBase P.isGood
        (pullbackLine D P.toBase P.isGood sX hX P.proj L)
        (isInvertibleModule_pullbackLine D P.toBase P.isGood sX hX P.proj L hL) β) (n : ℕ)
    (α : chowHomology.{u, u + 1} D sX hX) :
    P.segreCap (n + 1) α = (P.vanishingLocusDatum N σ hE).segreCap (n + 1) α +
      P.segreCap n (firstChernCapChow.{u, u + 1} D sX hX L hL α) := by
  refine DFunLike.congr_fun (segreCap_succ_eq_of_divisor P (P.vanishingLocusDatum N σ hE)
    (closedSubspacePushforwardChow D P.toBase P.isGood (vanishingLocus D P.toBase P.isGood N σ))
    (firstChernCapChow.{u, u + 1} D sX hX L hL) (fun α => ?_) (fun β => ?_) (fun β => ?_) n) α
  · rw [htensor]
    congr 1
    · exact firstChernCapChow_flatPullbackChow_of_vanishingLocus D P.toBase P.isGood sX hX P.proj
        P.proj_comp d P.isFlat P.hasRelativeDimension N hN σ hE α
    · exact (flatPullbackChow_firstChernCapChow D P.toBase P.isGood sX hX P.proj P.proj_comp
        (d + 1) P.isFlat P.hasRelativeDimension L hL α).symm
  · exact firstChernCapChow_closedSubspacePushforwardChow D P.toBase P.isGood _ P.twist
      P.isInvertible_twist β
  · exact properPushforwardChow_comp D _ (isGood_closedSubspace D P.toBase P.isGood _) P.toBase
      P.isGood sX hX rfl P.proj_comp (isProper_closedSubspace_ι D P.toBase P.isGood _)
      P.isProper β

end ProjectiveBundleDatum

end AlgebraicGeometry.Space.PrivateChern

end
