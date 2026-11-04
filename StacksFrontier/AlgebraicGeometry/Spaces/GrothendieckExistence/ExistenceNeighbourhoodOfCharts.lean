module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The neighbourhood of [Stacks, Tag 0CX9] glued from étale charts

The proof of [Stacks, Tag 0CX9] finds, for every point `x ∈ X₀`, an étale neighbourhood of `x` on
which the three conclusions hold, and takes for `W` the union of their images. This file is that
last step: for a family of étale charts `cⱼ` of `X` whose images cover `X₀`, on each of which

1. the sections of `Hⁱ(K)`, `i ≠ 0`, over every chart over `cⱼ` vanish,
2. the sections of `H⁰(K)` over every affine chart over `cⱼ` are finitely presented, and
3. the comparison `iₙ^* H⁰(K) ⟶ Fₙ` is an isomorphism over every chart of `Xₙ` over `cⱼ ×_X Xₙ`,

the open subspace `W` of `X` cut out by the union of the images is an existence neighbourhood.

## Main results

* `FlatSheafExistenceSituation.chartsNeighbourhood`: the open subspace `W`.
* `FlatSheafExistenceSituation.isExistenceNeighbourhood_chartsNeighbourhood`: `W` is an existence
  neighbourhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) {ι : Type v}
  (c : ι → SmallEtale D.B D.S D.containsLimitBase D.X.left.1)

/-- The open subspace of `X` cut out by the union of the images of the charts `cⱼ`. -/
abbrev chartsNeighbourhood : Subfunctor D.X.left.1 :=
  openSubspaceOfPoints D.B D.S D.containsLimitBase D.X.left.1 (⋃ j, chartPointsRange (c j))

/-- The subfunctor `chartsNeighbourhood c` is an open subspace of `X`. -/
theorem isOpenSubspace_chartsNeighbourhood :
    IsOpenSubspace D.B D.S D.containsLimitBase (D.chartsNeighbourhood c) :=
  let := pointTopology D.B D.S D.containsLimitBase D.X.left.1
  isOpenSubspace_openSubspaceOfPoints D.B D.S D.containsLimitBase D.X.left.2 _
    (isOpen_iUnion fun j =>
      isOpen_range_pointsMap_of_isEtale D.B D.S D.containsLimitBase _
        (chartSpace D.B D.S D.containsLimitBase D.X.left (c j)).2 D.X.left.2
        (isEtale_chartToSpace D.B D.S D.containsLimitBase D.X.left (c j)))

/-- The points of `chartsNeighbourhood c` are the union of the images of the charts `cⱼ`. -/
theorem range_chartsNeighbourhood :
    Set.range (pointsMap D.B D.S D.containsLimitBase (D.chartsNeighbourhood c).toFunctor
      (D.chartsNeighbourhood c).ι) = ⋃ j, chartPointsRange (c j) :=
  range_pointsMap_ι_openSubspaceOfPoints D.B D.S D.containsLimitBase _

/-- **Gluing the local conclusions of [Stacks, Tag 0CX9].** For charts `cⱼ` of `X` whose images
cover `X₀` and on which the three local conditions hold, the union of their images is an
existence neighbourhood. -/
theorem isExistenceNeighbourhood_chartsNeighbourhood
    (K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hK : spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left K)
    (π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n))
    (h0 : D.pointsOverFirstStage ⊆ ⋃ j, chartPointsRange (c j))
    (h1 : ∀ i : ℤ, i ≠ 0 → ∀ (j : ι) (T : SmallEtale D.B D.S D.containsLimitBase D.X.left.1),
      (T ⟶ c j) → IsZero (((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left i).obj
        K).val.obj (op T)))
    (h2 : ∀ (j : ι) (T : SmallEtale D.B D.S D.containsLimitBase D.X.left.1),
      IsAffine ((SmallEtale.toOver D.B D.S D.containsLimitBase D.X.left.1 ⋙
        BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj T) → (T ⟶ c j) →
      Module.FinitePresentation (chartRing D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 T)
        (((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K).val.obj (op T)))
    (h3 : ∀ (n : ℕ) (j : ι) (T : SmallEtale D.B D.S D.containsLimitBase (D.stage n).1),
      (T ⟶ (smallBaseChange D.B D.S D.containsLimitBase (D.closedImmersion n)
        (D.isClosedImmersion_closedImmersion n).rep).obj (c j)) →
      IsIso ((D.stageComparison K π n).val.app (op T))) :
    D.IsExistenceNeighbourhood K π (D.chartsNeighbourhood c)
      (D.isOpenSubspace_chartsNeighbourhood c) := by
  have hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap D.B D.S D.containsLimitBase
      (D.chartsNeighbourhood c).toFunctor (D.chartsNeighbourhood c).ι) := fun j => by
    rw [range_chartsNeighbourhood]; exact Set.subset_iUnion (fun j => chartPointsRange (c j)) j
  have hUc : Set.range (pointsMap D.B D.S D.containsLimitBase
      (D.chartsNeighbourhood c).toFunctor (D.chartsNeighbourhood c).ι) ⊆
      ⋃ j, chartPointsRange (c j) :=
    (range_chartsNeighbourhood D c).le
  have hq : ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj
      K).IsQuasicoherentOnSite := hK 0
  refine ⟨?_, fun i hi => ?_, ?_, fun n => ?_⟩
  · rw [range_chartsNeighbourhood]; exact h0
  · exact isZero_modulePullback_obj_openSubspaceHom_of_forall _ hcU hUc _ (h1 i hi)
  · exact isFinitePresentationOnSite_modulePullback_openSubspaceHom_of_forall _ hcU hUc _
      hq h2
  · have key := isIso_modulePullback_map_preimage_of_forall
      (D.closedImmersion n) (D.isClosedImmersion_closedImmersion n).rep
      (D.isOpenSubspace_stagePreimage (D.isOpenSubspace_chartsNeighbourhood c) n) hcU hUc
      (D.stageComparison K π n) (h3 n)
    convert key using 4

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
