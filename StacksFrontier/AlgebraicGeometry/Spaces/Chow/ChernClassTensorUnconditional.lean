module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapPropertiesAssembly

/-!
# Chern classes of a tensor product (Stacks 0ESE)

In Situation 0EDT let `X/B` be good and let `ℰ`, `ℱ` be finite locally free `𝒪_X`-modules of
ranks `r` and `s`. Then `c₁(ℰ ⊗ ℱ) = r c₁(ℱ) + s c₁(ℰ)`, `c₂(ℰ ⊗ ℱ)` is given by the degree two
part of the splitting formula, and on a splitting the total Chern classes are the products of the
splitting principle.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_tensorObj`: Stacks 0ESE, the formulas for
  `c₁(ℰ ⊗ ℱ)` and `c₂(ℰ ⊗ ℱ)`, and the total Chern classes of `ℰ`, `ℱ` and `ℰ ⊗ ℱ` on a
  splitting.

## Implementation notes

The source prints `c₂(ℰ ⊗ ℱ) = r² c₂(ℱ) + r s c₁(ℱ) c₁(ℰ) + s² c₂(ℰ)`, which is false (see the
docstring of `AlgebraicGeometry.Space.PrivateChern.chernCap_tensorObj`); the identity proved is the
degree two part of the source's own product formula, as in Stacks 0FA6 and Fulton, *Intersection
theory*, Example 3.2.2.

## References

* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
* W. Fulton, *Intersection theory*, Example 3.2.2.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **Stacks 0ESE.** For finite locally free `ℰ`, `ℱ` of ranks `r`, `s` on a good algebraic space
`X/B`:

* on every good `f : Y ⟶ X`, as operations on `CH_*(Y)`,
  `c₁(f^*(ℰ ⊗ ℱ)) = r c₁(f^*ℱ) + s c₁(f^*ℰ)` and
  `c₂(f^*(ℰ ⊗ ℱ)) = r c₂(f^*ℱ) + s c₂(f^*ℰ) + C(r,2) c₁(f^*ℱ)² + (r s - 1) c₁(f^*ℱ) c₁(f^*ℰ) +
  C(s,2) c₁(f^*ℰ)²`;
* "and so on (see proof)": on a splitting `π : P ⟶ X` (flat, with injective flat pullback after
  every base change) with invertible `ℒ_i`, `𝒩_j` and `x_i = c₁(ℒ_i)`, `y_j = c₁(𝒩_j)`,
  `c(π^*ℰ) = ∏ (1 + x_i)`, `c(π^*ℱ) = ∏ (1 + y_j)` and `c(π^*(ℰ ⊗ ℱ)) = ∏_{i,j} (1 + x_i + y_j)`.

The source prints `c₂(ℰ ⊗ ℱ) = r² c₂(ℱ) + r s c₁(ℱ) c₁(ℰ) + s² c₂(ℰ)`, which is false: for
`r = s = 1`, `ℰ = 𝒪(1, 0)` and `ℱ = 𝒪(0, 1)` on `𝐏¹ × 𝐏¹`, `ℰ ⊗ ℱ` is invertible so
`c₂(ℰ ⊗ ℱ) = 0`, while `c₁(ℱ) c₁(ℰ) ∩ [𝐏¹ × 𝐏¹]` is the class of a point, which is not zero. The
identity stated here is the degree two part of the source's own product formula
`∏_{i,j} (1 + x_i + y_j)` (Stacks 0FA6; Fulton, *Intersection theory*, Example 3.2.2). -/
@[stacks 0ESE "c₂ corrected to the degree-two part of ∏ (1 + x_i + y_j); the printed c₂ is false"]
theorem chernCap_tensorObj
    (E F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r s : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D sX hX E r) (hs : IsFiniteLocallyFreeOfRank D sX hX F s) :
    (∀ {Y : D.Ambient} (f : Y ⟶ X) (hY : D.IsGood (f ≫ sX)),
      let hrY := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨X, hX.1⟩) hr
      let hsY := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨X, hX.1⟩) hs
      let hrsY := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨X, hX.1⟩) (isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem X hX.1 hr hs)
      chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj (E ⊗ F)) (r * s)
          hrsY 1 =
          (r : ℤ) • chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj F) s
              hsY 1 +
            (s : ℤ) • chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r
              hrY 1 ∧
        chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj (E ⊗ F)) (r * s)
            hrsY 2 =
          (r : ℤ) • chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj F) s
              hsY 2 +
            (s : ℤ) • chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r
              hrY 2 +
            (r.choose 2 : ℤ) • chernCap.{u, u + 1} (hX := hY)
              ((spaceModulePullback D hX.1 hY.1 f).obj F) s hsY 1 ^ 2 +
            ((r : ℤ) * s - 1) •
              (chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj F) s hsY 1 *
                chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r
                  hrY 1) +
            (s.choose 2 : ℤ) • chernCap.{u, u + 1} (hX := hY)
              ((spaceModulePullback D hX.1 hY.1 f).obj E) r hrY 1 ^ 2) ∧
    ∃ (P : D.Ambient) (π : P ⟶ X) (hP : D.IsGood (π ≫ sX))
      (d : ℕ) (_ : IsFlat D.site D.base D.base_mem π)
      (_ : HasRelativeDimension d D.site D.base D.base_mem π),
      HasInjectiveChowBaseChange.{u + 1} D sX π d ∧
      ∃ (L : Fin r → Modules.{u, u} D.site D.base D.base_mem P hP.1)
        (N : Fin s → Modules.{u, u} D.site D.base D.base_mem P hP.1)
        (hL : ∀ i, IsFiniteLocallyFreeOfRank D (π ≫ sX) hP (L i) 1)
        (hN : ∀ j, IsFiniteLocallyFreeOfRank D (π ≫ sX) hP (N j) 1),
        (∀ i, IsInvertibleModule ⟨P, hP.1⟩ (L i)) ∧ (∀ j, IsInvertibleModule ⟨P, hP.1⟩ (N j)) ∧
        totalChernCap.{u, u + 1} ((spaceModulePullback D hX.1 hP.1 π).obj E) r
            (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
              (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
                ⟨X, hX.1⟩) hr) =
          ((List.finRange r).map fun i => 1 + chernCap.{u, u + 1} (L i) 1 (hL i) 1).prod ∧
        totalChernCap.{u, u + 1} ((spaceModulePullback D hX.1 hP.1 π).obj F) s
            (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
              (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
                ⟨X, hX.1⟩) hs) =
          ((List.finRange s).map fun j => 1 + chernCap.{u, u + 1} (N j) 1 (hN j) 1).prod ∧
        totalChernCap.{u, u + 1} ((spaceModulePullback D hX.1 hP.1 π).obj (E ⊗ F)) (r * s)
            (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
              (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
                ⟨X, hX.1⟩) (isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem X hX.1
                  hr hs)) =
          ((List.finRange r).flatMap fun i => (List.finRange s).map fun j =>
            1 + (chernCap.{u, u + 1} (L i) 1 (hL i) 1 +
              chernCap.{u, u + 1} (N j) 1 (hN j) 1)).prod :=
  chernCap_tensorObj_of_flatPullbackChow (chernCapProperties D)
    (fun hZ hP π hπ d hflat hd M r hM hM' n α =>
      chernCap_spaceModulePullback_flatPullbackChow hZ hP π hπ d hflat hd M r hM hM' n α)
    E F r s hr hs

end AlgebraicGeometry.Space.PrivateChern

end
