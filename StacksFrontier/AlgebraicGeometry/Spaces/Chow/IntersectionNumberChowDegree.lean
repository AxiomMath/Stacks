module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.IntersectionNumberIteratedCap

/-!
# Intersection numbers on a proper algebraic space are degrees of iterated first Chern classes

Let `k` be a field, `X` a proper algebraic space over `k`, `Z ⊆ X` a closed subspace of dimension
`d` and `ℒ₁, …, ℒ_d` invertible `𝒪_X`-modules. The intersection number of Spaces over Fields,
Definition 0EDF, is a degree:

`(ℒ₁ ⋯ ℒ_d · Z) = deg(c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒ_d) ∩ [Z]_d)`.

The right hand side is formed in Situation 0EDT over `Spec k` with the zero dimension function:
`[Z]_d` is the `d`-cycle of `Z` (Stacks 0EE9), each cap product is that of Stacks 0EQJ at its
canonical choices, and `deg : CH_0(X) → ℤ` is the degree of Stacks 0ESG.

## Main results

* `AlgebraicGeometry.Space.intersectionNumber_eq_chowGroupZeroDegree_iteratedFirstChernCapCycle`:
  `(ℒ₁ ⋯ ℒ_d · Z) = deg(c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒ_d) ∩ [Z]_d)` (Stacks 0ESI).

## Implementation notes

The source's displayed formula repeats `c₁(ℒ₁)`; the last factor is `c₁(ℒ_d)`, as the count of
`d` factors on a `d`-cycle requires. The iterated cap product is formed on cycles, the cap with
`c₁(ℒ_d)` applied first, and the degree is applied to its class in `CH_0(X)`.

## References

* [Stacks Project, Tag 0ESI](https://stacks.math.columbia.edu/tag/0ESI)
* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
* [Stacks Project, Tag 0EDE](https://stacks.math.columbia.edu/tag/0EDE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0ESG](https://stacks.math.columbia.edu/tag/0ESG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- **Stacks 0ESI.** Let `k` be a field, `X` a proper algebraic space over `k`, `Z ⊆ X` a closed
subspace of dimension `d` and `ℒ₁, …, ℒ_d` invertible `𝒪_X`-modules. Then

`(ℒ₁ ⋯ ℒ_d · Z) = deg(c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒ_d) ∩ [Z]_d)`,

the left hand side the intersection number of Stacks 0EDF, `[Z]_d` the `d`-cycle of `Z`
(Stacks 0EE9), the cap products those of Stacks 0EQJ and `deg : CH_0(X) → ℤ` the degree of
Stacks 0ESG, in Situation 0EDT over `Spec k` with the zero dimension function. -/
@[stacks 0ESI]
theorem intersectionNumber_eq_chowGroupZeroDegree_iteratedFirstChernCapCycle
    (X : AlgebraicSpaces B (Spec (.of k)) hk) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (Z : ClosedSubspaces B (Spec (.of k)) hk X.1) (d : ℕ)
    (hd : dimension B (Spec (.of k)) hk Z.1.toFunctor Z.2.1 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    intersectionNumber.{u, w} k B hk X (closedSubspaceToSpace B (Spec (.of k)) hk X Z) d f hf
        (closedSubspaceInclusion B (Spec (.of k)) hk X Z) Z.2.2 hd L =
      chowGroupZeroDegree.{v} (fieldSpaceSituation k B hk) f
        (isGood_fieldSpaceSituation_of_isProper k B hk X hf) (𝟙 _)
        (isGood_fieldSpaceSituation_id k B hk) (Category.comp_id f) hf inferInstance
        (fieldSpaceSituation_deltaValue_id k B hk) (fieldSpacePoint k B hk)
        (chowClass.{v} (fieldSpaceSituation k B hk) f
          (isGood_fieldSpaceSituation_of_isProper k B hk X hf) 0
          (iteratedFirstChernCapCycle (fieldSpaceSituation k B hk) f
            (isGood_fieldSpaceSituation_of_isProper k B hk X hf) d L hL 0
            (cycleGroupCast (fieldSpaceSituation k B hk) f (zero_add _).symm
              (closedSubspaceCycle (fieldSpaceSituation k B hk) f
                (isGood_fieldSpaceSituation_of_isProper k B hk X hf) Z.1 Z.2 d
                (deltaDimensionSubspace_le_of_dimension_eq k B hk X hf Z hd))))) := by
  rw [chowGroupZeroDegree_chowClass]
  exact (intersectionNumber_eq_iteratedFirstChernCapDegree_closedSubspaceCycle.{u, w} k B hk X f hf
    Z d hd L).trans (iteratedFirstChernCapDegree_apply k B hk X f hf d L hL _)

end AlgebraicGeometry.Space

end
