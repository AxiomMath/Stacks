module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspacePushforwardReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinClosedSubspaceIntersectionAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceComposition

/-!
# The cap product of Stacks 0EQJ commutes with pushforward along a closed immersion

In Situation 0EDT let `X/B` be good, let `i : Y ⟶ X` be the inclusion of a closed subspace and
let `β ∈ Z_{k+1}(Y)`. An integral closed subspace `T ⊆ Y` and its image `i(T) ⊆ X` are
canonically isomorphic, so a component rule of Stacks 0EQJ on `X` transports to one on `Y`. For
the transported rule the projection formula of Stacks 0EQT,

`i_*(c₁ ∩ β) = c₁ ∩ i_*β`,

holds at the level of cycles, with no further hypotheses.

## Main definitions

* `closedSubspaceChernRule`: the component rule of Stacks 0EQJ on a closed subspace `Y ⊆ X`
  transported from one on `X`, by pushforward of cycles along the identification of an integral
  closed subspace of `Y` with its image in `X`.

## Main results

* `cycleClosedPushforward_firstChernComponentCycle_closedSubspaceChernRule`: the component cycle
  of the transported rule at `T ⊆ Y` pushes forward to the component cycle of the original rule
  at the image `i(T) ⊆ X`.
* `cycleGroupClosedPushforward_firstChernCapCycleMap`: the projection formula
  `i_*(c₁ ∩ β) = c₁ ∩ i_*β` in `Z_k(X)` for the transported rule.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)

/-- The δ-dimension of an integral closed subspace of a closed subspace `Y ⊆ X`, computed along
`Y → B`, is the δ-dimension of its image in `X`. -/
theorem deltaDimension_pushforward_eq_iff
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    deltaDimension D sX (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T) = k + 1 ↔
      deltaDimension D (Y.ι ≫ sX) T = k + 1 := by
  rw [IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
    (D.isDecentSpace_of_isGood sX hX) hY.2 T]

/-- The identification of an integral closed subspace of `Y` with its image in `X` is one over
the base: it carries the structure morphism of `T` over `Y` to that of the image over `X`. -/
theorem pushforwardIso_symm_hom_comp
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 T).symm.hom ≫ (T.subspace.ι ≫ Y.ι ≫ sX) =
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T).subspace.ι ≫ sX := by
  rw [Iso.symm_hom, show T.subspace.ι ≫ Y.ι ≫ sX = (T.subspace.ι ≫ Y.ι) ≫ sX from
      (Category.assoc _ _ _).symm, ← Category.assoc,
    IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp]

include hY in
/-- The component rule of Stacks 0EQJ on a closed subspace `Y ⊆ X` of a good algebraic space
transported from a component rule `chern` on `X`: its value at an integral closed subspace
`T ⊆ Y` of δ-dimension `k + 1` is the cycle `chern` assigns to the image `i(T) ⊆ X`, read on `T`
through the identification `IntegralClosedSubspace.pushforwardIso` of `T` with that image. -/
def closedSubspaceChernRule (chern : FirstChernComponentCycleRule D sX k) :
    FirstChernComponentCycleRule D (Y.ι ≫ sX) k := fun T hT =>
  cycleGroupClosedPushforward D
    (isGood_integralClosedSubspace D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) T).1
    (isGood_integralClosedSubspace D sX hX
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T)).1
    (D.isDecentSpace_of_isGood (T.subspace.ι ≫ Y.ι ≫ sX)
      (isGood_integralClosedSubspace D (Y.ι ≫ sX)
        (isGood_ι_of_isClosedSubspace D sX hX Y hY) T))
    (isClosedImmersion_of_isIso D.site D.base D.base_mem
      (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T).symm.hom)
    _ (isGood_integralClosedSubspace D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) T).2.2
    _ (pushforwardIso_symm_hom_comp D sX hX Y hY T) k
    (chern _ ((deltaDimension_pushforward_eq_iff D sX hX Y hY k T).2 hT))

include hY in
/-- For `T ⊆ Y` an integral closed subspace, the component cycle on `Y` of
`closedSubspaceChernRule` at `T`, pushed forward to `X` along `i : Y ⟶ X`, is the component cycle
on `X` of the original rule at the image `i(T)`. -/
theorem cycleClosedPushforward_firstChernComponentCycle_closedSubspaceChernRule
    (chern : FirstChernComponentCycleRule D sX k)
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
        (firstChernComponentCycle D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) k
          (closedSubspaceChernRule D sX hX Y hY k chern) T).1 =
      (firstChernComponentCycle D sX hX k chern
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 T)).1 := by
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  by_cases hT : deltaDimension D (Y.ι ≫ sX) T = k + 1
  · rw [firstChernComponentCycle_of_deltaDimension_eq D (Y.ι ≫ sX) hYgood k _ hT,
      firstChernComponentCycle_of_deltaDimension_eq D sX hX k chern
        ((deltaDimension_pushforward_eq_iff D sX hX Y hY k T).2 hT)]
    refine Eq.trans (cycleClosedPushforward_comp D hX.1 hY.1 T.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood (Y.ι ≫ sX) hYgood)
      T.isClosedSubspace.2 hY.2 _).symm ?_
    refine Eq.trans (cycleClosedPushforward_comp D hX.1 T.isClosedSubspace.1
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T).isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX)
      (D.isDecentSpace_of_isGood (T.subspace.ι ≫ Y.ι ≫ sX)
        (isGood_integralClosedSubspace D (Y.ι ≫ sX) hYgood T))
      (isClosedImmersion_of_isIso D.site D.base D.base_mem
        (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 T).symm.hom)
      (isClosedImmersion_comp D.site D.base D.base_mem T.subspace.ι Y.ι
        T.isClosedSubspace.2 hY.2) _).symm ?_
    exact cycleClosedPushforward_congr D hX.1
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T).isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) _ _
      (IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T) _
  · rw [firstChernComponentCycle_of_deltaDimension_ne D (Y.ι ≫ sX) hYgood k _ hT,
      firstChernComponentCycle_of_deltaDimension_ne D sX hX k chern
        fun h => hT ((deltaDimension_pushforward_eq_iff D sX hX Y hY k T).1 h)]
    exact cycleClosedPushforward_zero D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2

include hY in
/-- For `i : Y ⟶ X` the inclusion of a closed subspace of a good algebraic space and
`β ∈ Z_{k+1}(Y)`,

`i_*(c₁ ∩ β) = c₁ ∩ i_*β`  in  `Z_k(X)`,

the cap product of Stacks 0EQJ being formed on `Y` with the transported component rule
`closedSubspaceChernRule` and on `X` with the given one. -/
theorem cycleGroupClosedPushforward_firstChernCapCycleMap
    (chern : FirstChernComponentCycleRule D sX k)
    (β : CycleGroup D (Y.ι ≫ sX) (k + 1)) :
    cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k
        (firstChernCapCycleMap D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) k
          (closedSubspaceChernRule D sX hX Y hY k chern) β) =
      firstChernCapCycleMap D sX hX k chern
        (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX
          hX.2.2 (Y.ι ≫ sX) rfl (k + 1) β) := by
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  refine Subtype.ext (funext fun V => ?_)
  rw [firstChernCapCycleMap_cycleGroupClosedPushforward_apply D sX hX hY.1 hY.2 (Y.ι ≫ sX) rfl
    k chern β V]
  change cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
      (firstChernCapCycleMap D (Y.ι ≫ sX) hYgood k
        (closedSubspaceChernRule D sX hX Y hY k chern) β).1 V = _
  rw [show (firstChernCapCycleMap D (Y.ι ≫ sX) hYgood k
        (closedSubspaceChernRule D sX hX Y hY k chern) β).1 =
      fun T₀ => ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
        β.1 T * (firstChernComponentCycle D (Y.ι ≫ sX) hYgood k
          (closedSubspaceChernRule D sX hX Y hY k chern) T).1 T₀ from rfl,
    cycleClosedPushforward_finsum_mul D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
      (fun T : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor => β.1 T)
      (fun T T₀ => (firstChernComponentCycle D (Y.ι ≫ sX) hYgood k
        (closedSubspaceChernRule D sX hX Y hY k chern) T).1 T₀) V]
  exact finsum_congr fun T => by
    rw [cycleClosedPushforward_firstChernComponentCycle_closedSubspaceChernRule D sX hX Y hY k
      chern T]

end AlgebraicGeometry.Space

end
