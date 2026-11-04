module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassDualTensorOfProperties

/-!
# Chern classes of a tensor product

In Situation 0EDT let `X/B` be good and let `ℰ`, `ℱ` be finite locally free `𝒪_X`-modules of
ranks `r` and `s`. Stacks 0ESE computes the Chern classes of `ℰ ⊗ ℱ` from those of `ℰ` and `ℱ`:

  `c₁(ℰ ⊗ ℱ) = r c₁(ℱ) + s c₁(ℰ)`,
  `c₂(ℰ ⊗ ℱ) = r c₂(ℱ) + s c₂(ℰ) + C(r,2) c₁(ℱ)² + (r s - 1) c₁(ℱ) c₁(ℰ) + C(s,2) c₁(ℰ)²`,

"and so on": after pulling back along a splitting `π : P ⟶ X` (Stacks 0ESC), along which `ℰ` and
`ℱ` acquire filtrations with invertible successive quotients `ℒ_1, …, ℒ_r` and `𝒩_1, …, 𝒩_s`,
one has, with `x_i = c₁(ℒ_i)` and `y_j = c₁(𝒩_j)`,

  `c(π^*ℰ) = ∏ (1 + x_i)`,   `c(π^*ℱ) = ∏ (1 + y_j)`,   `c(π^*(ℰ ⊗ ℱ)) = ∏_{i,j} (1 + x_i + y_j)`,

and `π^*` is injective on Chow homology after every base change, so that these determine every
`c_n(ℰ ⊗ ℱ)`. As in Section 0ES3 an identity in `A^*(X)` is read as the identity of the
operations on `CH_*(Y)` for every good `Y ⟶ X`, applied to the inverse images of the modules.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_tensorObj_of_flatPullbackChow`: the identities
  for `c₁` and `c₂` on every good `Y ⟶ X` and the product formula on a splitting, from the
  properties of the Chern classes and their compatibility with flat pullback.

## Implementation notes

The source prints the second identity as
`c₂(ℰ ⊗ ℱ) = r² c₂(ℱ) + r s c₁(ℱ) c₁(ℰ) + s² c₂(ℰ)`, which is not correct: for `r = s = 1`,
`ℰ = 𝒪(1, 0)` and `ℱ = 𝒪(0, 1)` on `𝐏¹ × 𝐏¹` the module `ℰ ⊗ ℱ` is invertible, so
`c₂(ℰ ⊗ ℱ) = 0`, while the right hand side is `c₁(ℱ) c₁(ℰ) ∩ [𝐏¹ × 𝐏¹]`, the class of a point,
which is not zero. The formal computation omitted in the source's proof, expanding the degree two
part of `∏_{i,j} (1 + x_i + y_j)`, gives the identity stated here, which is the one of Stacks 0FA6
and of Fulton, *Intersection theory*, Example 3.2.2.

The Chow groups are those whose rational equivalences are indexed in the universe `u + 1`, the
universe at which the splitting principle provides the injectivity of flat pullback.

## References

* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
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

/-- **Stacks 0ESE, from the properties of the Chern classes and their compatibility with flat
pullback.** For finite locally free `ℰ`, `ℱ` of ranks `r`, `s` on a good `X`:

* on every good `f : Y ⟶ X`, as operations on `CH_*(Y)`,
  `c₁(f^*(ℰ ⊗ ℱ)) = r c₁(f^*ℱ) + s c₁(f^*ℰ)` and
  `c₂(f^*(ℰ ⊗ ℱ)) = r c₂(f^*ℱ) + s c₂(f^*ℰ) + C(r,2) c₁(f^*ℱ)² + (r s - 1) c₁(f^*ℱ) c₁(f^*ℰ) +
  C(s,2) c₁(f^*ℰ)²`;
* there are a good `P` with a flat `π : P ⟶ X` of some relative dimension along which flat
  pullback is injective on Chow homology after every base change, and invertible `ℒ_1, …, ℒ_r`,
  `𝒩_1, …, 𝒩_s` on `P` with, for `x_i = c₁(ℒ_i)` and `y_j = c₁(𝒩_j)`,
  `c(π^*ℰ) = ∏ (1 + x_i)`, `c(π^*ℱ) = ∏ (1 + y_j)` and `c(π^*(ℰ ⊗ ℱ)) = ∏_{i,j} (1 + x_i + y_j)`.

The hypotheses are the properties of the Chern classes of
`AlgebraicGeometry.Space.PrivateChern.ChernCapProperties` and the compatibility of the Chern
classes with flat pullback. -/
theorem chernCap_tensorObj_of_flatPullbackChow (hC : ChernCapProperties.{u, u + 1} D)
    (hnat : ∀ {Z P : D.Ambient} {sZ : Z ⟶ D.space} {sP : P ⟶ D.space} (hZ : D.IsGood sZ)
      (hP : D.IsGood sP) (π : P ⟶ Z) (hπ : π ≫ sZ = sP) (d : ℕ)
      (hflat : IsFlat D.site D.base D.base_mem π)
      (hd : HasRelativeDimension d D.site D.base D.base_mem π)
      (M : Modules.{u, u} D.site D.base D.base_mem Z hZ.1) (r : ℕ) hM hM' (n : ℕ)
      (α : chowHomology.{u, u + 1} D sZ hZ),
      chernCap.{u, u + 1} (hX := hP) ((spaceModulePullback D hZ.1 hP.1 π).obj M) r hM' n
          (flatPullbackChow.{u, u + 1} D sP hP sZ hZ π hπ d hflat hd α) =
        flatPullbackChow.{u, u + 1} D sP hP sZ hZ π hπ d hflat hd
          (chernCap.{u, u + 1} (hX := hZ) M r hM n α))
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
  ⟨fun f hY => chernCap_tensorObj_of_chernCapProperties hC
      (hasIntertwiningSplittings_of_flatPullbackChow hnat) E F r s hr hs f hY,
    exists_totalChernCap_tensorObj_eq_prod_of_chernCapProperties hC IsProjectiveBundleTower E F r s
      hr hs (isSplitting_projectiveBundleTower hX ![E, F] ![r, s]
        (fun i => by fin_cases i <;> assumption))⟩

end AlgebraicGeometry.Space.PrivateChern

end
