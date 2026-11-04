module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChernComponentAmbient
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowDevissage
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.SupComapSubscheme

/-!
# `i₁^*[W₁] = c₁(p₁^*ℒ₁) ∩ [W₁]` for the branch over a component of the divisor

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be an integral closed subscheme of
δ-dimension `k+1` contained in the divisor `D = Z(s)`. The case `W ⊆ D` of
[Stacks, Tag 0F98] computes `i₁^*p^*[W]` by splitting `[p^{-1}W] = [W₁] + [W₂]` and evaluating the
Gysin rule of `i₁` on each branch. On the first branch, which *is* contained in `D₁`, the source
takes the step

  "`i₁^*([W₁] + [W₂]) = c₁(p₁^*ℒ₁) ∩ [W₁] + [W₁ ∩ W₂]_k`"

whose first summand this file produces. Two readings of `c₁ ∩ [W₁]` have to be reconciled, and
neither is avoidable:

* the Gysin rule of `i₁` is a rule on integral closed subschemes of `L`, so it computes
  `c₁(p^*ℒ₁|_{W₁}) ∩ [W₁]` with `W₁` spelled as the join `D₁ ⊔ p^{-1}(W)` **in `L`** — that is the
  spelling the cycle split hands it;
* the localized form of Stacks 02SS,
  `firstChernCapRule_extendCycleGroup_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_base`,
  is the cap product of `p₁^*(ℒ₁|_D)` **on `D₁`**, so it computes the same class with `W₁` spelled
  as the inverse image `p^{-1}(W)|_{D₁}`.

The reconciliation is
`Stacks.Chow.firstChernComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin` at
the closed immersion `i₁`, whose scheme-theoretic image hypothesis is discharged by
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_subschemeι`, together with
`Stacks.Chow.firstChernComponentCycle_sub_isRationallyEquivalentToZeroWithin_of_iso` at the
isomorphism `p₁^*(ℒ₁|_D) ≅ i₁^*p^*ℒ₁` of `Stacks.Chow.pullbackCompIso`, both read against the
square `i₁ ≫ p = p₁ ≫ i` of the diagram.

## Main results

* `gysinRuleBranch₁_cycle_sub_firstChernComponentCycle_isRationallyEquivalentToZeroWithin`
  — **the first summand of the step above**: the Gysin cycle of the branch `W₁` and the component
  cycle of `c₁(p₁^*(ℒ₁|_D))` at `p^{-1}(W)|_{D₁}` differ by a cycle rationally equivalent to zero
  on `D₁`, witnessed inside the preimage of `W`.

## Implementation notes

### Why the four proof arguments are parameters

`IsIntegral` and the δ-dimension of the two presentations of the branch are propositions, so
passing them in costs nothing and spares the consumer having to produce them in the exact spelling
this statement would otherwise fix. The consumer has them from
`Stacks.Chow.TensorZeroScheme.isIntegral_sup_comap_proj_of_le` and
`…schemeDeltaDimension_sup_comap_proj_of_le`, at the degree `k+2`, which is the same integer as
the `k+1+1` the Gysin rule of `i₁` asks for but not the same term.

### The carrier

All three comparisons are confined to the branch, and the branch lies over `W`: the support of a
join is the intersection of the supports (`AlgebraicGeometry.Scheme.IdealSheafData.support_sup`),
so `W₁` lies inside `p^{-1}(W)`, and the support of an inverse image is a preimage, so
`p^{-1}(W)|_{D₁}` is exactly `i₁^{-1}p^{-1}(W)`. Both land in the carrier
`(i₁ ≫ p)^{-1}(W)` that
`Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj_of_primeCycle` prescribes.

### No `@[stacks]` attribute here

This is one summand of one case of the proof of [Stacks, Tag 0F98], which is a single identity of
maps; see the convention note in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme


variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (k : ℤ) (W : Y.IdealSheafData)

include h₁ h₂ in
/-- **The two readings of `c₁ ∩ [W₁]` agree, up to rational equivalence over `W`.** The Gysin
cycle of the branch `W₁ = D₁ ⊔ p^{-1}(W)` under the Gysin rule of `i₁ : D₁ ⟶ L`, and the first
Chern component cycle of `p₁^*(ℒ₁|_D)` on `D₁` at the inverse image `p^{-1}(W)|_{D₁}`, differ by a
cycle rationally equivalent to zero on `D₁` witnessed inside the preimage of `W`.

The component `V` of `D₁` is a parameter satisfying `p^{-1}(W)|_{D₁} = V` rather than that
inverse image itself: the localized 02SS reaches it as `p₁^{-1}(W|_D)`, which is the same ideal
sheaf by `AlgebraicGeometry.Scheme.IdealSheafData.comap_comp` and the square `i₁ ≫ p = p₁ ≫ i`
but not the same term, and rewriting an ideal sheaf under the morphism whose type it determines
would transport a cycle group along a concrete equality. -/
theorem gysinRuleBranch₁_cycle_sub_firstChernComponentCycle_isRationallyEquivalentToZeroWithin
    (hW₁int : IsIntegral (R.normalize.D₁ ⊔ W.comap R.normalize.p).subscheme)
    (hW₁dim : Stacks.Chow.schemeDeltaDimension C
      ((R.normalize.D₁ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) =
        ((k + 1 + 1 : ℤ) : EInt))
    (V : R.normalize.D₁.subscheme.IdealSheafData)
    (hV : (W.comap R.normalize.p).comap R.normalize.D₁.subschemeι = V)
    (hW₁'int : IsIntegral V.subscheme)
    (hW₁'dim : Stacks.Chow.schemeDeltaDimension C
      (V.subschemeι ≫ R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) =
        ((k + 1 + 1 : ℤ) : EInt)) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      ((gysinRuleBranch₁ C Y L₁ L₂ s R sY k).cycle
          (R.normalize.D₁ ⊔ W.comap R.normalize.p) hW₁int hW₁dim -
        Stacks.Chow.firstChernComponentCycle C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
          (Stacks.Chow.firstChernComponentCycleRule C
            (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
            ((Scheme.Modules.pullback R.normalize.p₁).obj
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁)))
          V hW₁'int hW₁'dim)
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
  subst hV
  let : AlgebraicGeometry.SheafOfModules.IsInvertible
      R.normalize.total.sheaf.obj
      R.normalize.total.ringCatSheaf.property
      ((Scheme.Modules.pullback R.normalize.p).obj L₁) :=
    Stacks.Divisors.pullback_isInvertible _ _
  have hsupW₁ : ((R.normalize.D₁ ⊔ W.comap R.normalize.p).support :
        Set R.normalize.total) ⊆
      R.normalize.p.base ⁻¹' (W.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
      Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    exact Set.inter_subset_right
  have hsupW₁' : (((W.comap R.normalize.p).comap R.normalize.D₁.subschemeι).support :
        Set R.normalize.D₁.subscheme) ⊆
      (R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y) := by
    rw [preimage_branch₁_comp, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage]
  have hA : Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      ((gysinRuleBranch₁ C Y L₁ L₂ s R sY k).cycle
          (R.normalize.D₁ ⊔ W.comap R.normalize.p) hW₁int hW₁dim -
        Stacks.Chow.properPushforward C
          ((R.normalize.D₁ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY)
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          (Scheme.IdealSheafData.inclusion
            (le_sup_left : R.normalize.D₁ ≤
              R.normalize.D₁ ⊔ W.comap R.normalize.p)) (by simp) (k + 1)
          (Stacks.Chow.firstChernComponentCycleRule C (R.normalize.p ≫ sY) (k + 1)
            ((Scheme.Modules.pullback R.normalize.p).obj L₁)
            (R.normalize.D₁ ⊔ W.comap R.normalize.p) hW₁int hW₁dim))
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
    refine (gysinComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin_of_le
      C (R.normalize.p ≫ sY) (k + 1) ((Scheme.Modules.pullback R.normalize.p).obj L₁)
      R.normalize.s₁
      (Stacks.Chow.firstChernComponentClass C (R.normalize.p ≫ sY) (k + 1)
        ((Scheme.Modules.pullback R.normalize.p).obj L₁))
      (R.normalize.D₁ ⊔ W.comap R.normalize.p) hW₁int hW₁dim le_sup_left _
      (Stacks.Chow.firstChernComponentClass_eq_mk _ _ _ _ _ _ _)).mono ?_
    rw [preimage_branch₁_comp]
    exact Set.preimage_mono hsupW₁
  have hB :=
    (Stacks.Chow.firstChernComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin
      C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (R.normalize.p ≫ sY)
      R.normalize.D₁.subschemeι rfl (k + 1)
      ((Scheme.Modules.pullback R.normalize.p).obj L₁)
      ((W.comap R.normalize.p).comap R.normalize.D₁.subschemeι) hW₁'int hW₁'dim
      (R.normalize.D₁ ⊔ W.comap R.normalize.p)
      (Scheme.IdealSheafData.map_comap_subschemeι R.normalize.D₁
        (W.comap R.normalize.p))
      (Scheme.IdealSheafData.inclusion le_sup_left)
      (Scheme.IdealSheafData.inclusion_subschemeι _) hW₁int hW₁dim).mono hsupW₁'
  have hC :=
    (Stacks.Chow.firstChernComponentCycle_sub_isRationallyEquivalentToZeroWithin_of_iso C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1) _ _
      (Stacks.Chow.pullbackCompIso R.normalize.p₁ (zeroIdeal Y L₁ L₂ s).subschemeι
        R.normalize.D₁.subschemeι R.normalize.p
        R.normalize.comm₁.symm L₁)
      ((W.comap R.normalize.p).comap R.normalize.D₁.subschemeι) hW₁'int
      hW₁'dim).mono hsupW₁'
  convert isRationallyEquivalentToZeroWithin_add _ _ _
    (isRationallyEquivalentToZeroWithin_add _ _ _ hA
      (isRationallyEquivalentToZeroWithin_neg _ _ _ hB))
    (isRationallyEquivalentToZeroWithin_neg _ _ _ hC) using 1
  abel

end Stacks.Chow.TensorZeroScheme

end
