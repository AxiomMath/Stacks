module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionGysinCap

/-!
# The Gysin map of a regular immersion on one part, for a subscheme of varying dimension

Let `X` be a scheme smooth over a field `k` and `i : Y ⟶ X` a regular closed immersion. The Gysin
map `i^!` on the part `X_d` of `X` of dimension `d`
(`Stacks.Chow.regularImmersionPartGysin`) is computed on `c_q ∩ [X_d]` by Stacks 0FF6 and 0FF7:

  `i^!(c_q ∩ [X_d]) = c_q|_{Y_d} ∩ [Y_d]_e`   for `Y_d = Y ×_X X_d`,

as soon as the piece `Y_d` has pure dimension `e`. Unlike
`Stacks.Chow.regularImmersionGysin_totalChowClassCapFundamental`, `Y` itself need not be
equidimensional: only the piece over `X_d` is.

## Main results

* `Stacks.Chow.cap_lciGysinClass_dimPart_fundamentalChowClass_of_piece`: the degree `d - e` term
  of `i^!`, capped at `X_d ⟶ X`, carries `[X_d]_d` to `[Y ×_X X_d]_e`.
* `Stacks.Chow.regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass_of_piece`: `i^!`
  on the part `X_d` carries `[X_d]_d` to `[Y ×_X X_d]_e`.
* `Stacks.Chow.regularImmersionPartGysin_totalChowClassCapFundamental`:
  `i^!(c_q ∩ [X_d]) = c_q|_{Y_d} ∩ [Y_d]_e` on the part `X_d`.

## References

* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase isClopenDecomposition_dimPart
  relativeDimension_partBase)

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (i : Y ⟶ X) [IsClosedImmersion i]
  (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

/-- **Stacks 0FF7 for the Gysin map of `i` on a part, the piece being equidimensional.** If the
piece `Y ×_X X_d` of `Y` has pure dimension `e`, the degree `d - e` term of `i^!`, capped at the
test scheme `X_d ⟶ X`, carries `[X_d]_d` to `[Y ×_X X_d]_e`. -/
theorem cap_lciGysinClass_dimPart_fundamentalChowClass_of_piece (e d : ℕ)
    (hP : RelativeDimension (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e) :
    (lciGysinMapComponent (fieldChowSituation k) (i ≫ sX) sX rfl
        (isLocalCompleteIntersectionMorphism_of_isRegularImmersion i hreg)
        (GysinMapExists.of_isImmersion i) ((d : ℤ) - e)).cap (dimPart sX d).ι d
        (fundamentalChowClass (fieldChowSituation k) (partBase sX d) d) =
      fundamentalChowClass (fieldChowSituation k) (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX)
        ((d : ℤ) - ((d : ℤ) - e)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have hlci := isLocalCompleteIntersectionMorphism_of_isRegularImmersion i hreg
  have hex := GysinMapExists.of_isImmersion i
  set π := pullback.fst i (dimPart sX d).ι
  have hXd := relativeDimension_partBase sX d
  have hT := WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k
    (partBase sX d) d hXd
  have hPδ := WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k
    (π ≫ i ≫ sX) e hP
  have hdimV : schemeDeltaDimension (fieldChowSituation k) (π ≫ i ≫ sX) ≤
      (((d : ℤ) - ((d : ℤ) - e) : ℤ) : EInt) := by
    rw [sub_sub_cancel]
    exact WeilCohomology.schemeDeltaDimension_le_of_forall_irreducibleComponent _ hPδ
  obtain ⟨dd, hd, hdeg⟩ := (Classical.choice ((gysinMapExists_iff_nonempty i).1 hex) :
    SmoothFactorization i).exists_hasCapFundamentalFormula_gysinMap (fieldChowSituation k)
      (i ≫ sX) sX rfl hlci
  refine chowGroup_eq_of_chowGroupRestrict_preimage_connectedComponent_eq
    (C := fieldChowSituation k) _ π _ fun w ↦ ?_
  rw [chowGroupRestrict_fundamentalChowClass (fieldChowSituation k) _ _ _ rfl _ hdimV]
  rcases isEmpty_or_nonempty (π ⁻¹ᵁ Y.connectedComponentOpens w).toScheme with hw | ⟨⟨x, hx⟩⟩
  · have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      ((π ⁻¹ᵁ Y.connectedComponentOpens w).ι ≫ π ≫ i ≫ sX) ((d : ℤ) - ((d : ℤ) - e))
    exact Subsingleton.elim _ _
  have hXdc : IsClopen ((dimPart sX d : X.Opens) : Set X) :=
    (isClopenDecomposition_dimPart sX).isClopen d
  have hUc : IsClopen (((i ⁻¹ᵁ dimPart sX d : Y.Opens)) : Set Y) := hXdc.preimage i.continuous
  have hrange : ∀ y, y ∈ i ⁻¹ᵁ dimPart sX d ↔ y ∈ Set.range π := by
    intro y
    have h : (π.opensRange : Set Y) = (i ⁻¹ᵁ dimPart sX d : Y.Opens) := by
      rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι]
    rw [← SetLike.mem_coe, ← h]
    rfl
  have hxd : π x ∈ i ⁻¹ᵁ dimPart sX d := (hrange _).2 ⟨x, rfl⟩
  have hsub : ∀ y ∈ Y.connectedComponentOpens w, y ∈ i ⁻¹ᵁ dimPart sX d := fun y hy ↦
    hUc.connectedComponent_subset hxd (ConnectedComponents.coe_eq_coe'.1 (hy.trans hx.symm))
  have hdw : dd w = (d : ℤ) - e := by
    obtain ⟨ξ, hξ, hξw⟩ := exists_mem_genericPoints_mk_eq w
    have hξd : i ξ ∈ dimPart sX d := hsub ξ hξw
    have hV : X.connectedComponentOpens (i.continuous.connectedComponentsMap
        (ConnectedComponents.mk ξ)) ≤ dimPart sX d := fun y hy ↦
      hXdc.connectedComponent_subset hξd (ConnectedComponents.coe_eq_coe'.1 hy)
    have hδ : relativeDimension (fieldChowSituation k).dimensionFunction (i ≫ sX) ξ = e := by
      obtain ⟨ξ', hξ'⟩ := (hrange ξ).1 hξd
      have hgen : ξ' ∈ genericPoints (pullback i (dimPart sX d).ι : Scheme.{u}) :=
        (mem_genericPoints_iff_of_isOpenEmbedding π.isOpenEmbedding ξ').2 (hξ' ▸ hξ)
      rw [← hξ', ← relativeDimension_comp_isOpenImmersion]
      exact WeilCohomology.relativeDimension_of_mem_irreducibleComponents_of_relativeDimension k
        (π ≫ i ≫ sX) e hP ξ' hgen
    rw [← hξw, hdeg ξ hξ d fun W ↦ ?_, hδ]
    rw [← WeilCohomology.deltaDimension_congr (X.homOfLE_ι_assoc hV sX)]
    exact deltaDimension_irreducibleComponents_of_isOpenImmersion (fieldChowSituation k)
      (partBase sX d) hT _ W
  have hca := (hd w).2 d
  rw [hdw] at hca
  exact chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula
    (fieldChowSituation k) (i ≫ sX) sX i rfl (completedBivariantSequenceOfInvertible _ (i ≫ sX)
      sX i rfl (lciGysinMap (fieldChowSituation k) (i ≫ sX) sX rfl hlci hex) ((d : ℤ) - e)) w
    ((restriction_completedBivariantSequence (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) (i ≫ sX) sX i rfl
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion (fieldChowSituation k))
      (gysinSystemOfInvertible_isNaturalUnderOpensRestriction (fieldChowSituation k))
      (gysinSystemOfInvertible_isNaturalUnderPullbackComp (fieldChowSituation k))
      (lciGysinMap (fieldChowSituation k) (i ≫ sX) sX rfl hlci hex) ((d : ℤ) - e) w) ▸ hca)
    (dimPart sX d).ι hT (fun ξ _ ↦ relativeDimension_le_of_schemeDeltaDimension_le' _ _ hdimV ξ)
    (fun ξ _ _ ↦ WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth k (partBase sX d) _)
    _ _ _ (π.resLE (Y.connectedComponentOpens w) (π ⁻¹ᵁ Y.connectedComponentOpens w) le_rfl)
    (Scheme.Hom.resLE_comp_ι _ _)

/-- **`i^!` on the part `X_d` carries `[X_d]_d` to `[Y ×_X X_d]_e`** when the piece `Y ×_X X_d`
has pure dimension `e`. -/
theorem regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass_of_piece (e d : ℕ)
    (hP : RelativeDimension (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e) :
    (regularImmersionPartGysinClass sX i hreg e d).capTargetHom _ _ _ _ _ _ ((d : ℤ) - e) d
        (fundamentalChowClass (fieldChowSituation k) (partBase sX d) d) =
      fundamentalChowClass (fieldChowSituation k) (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX)
        ((d : ℤ) - ((d : ℤ) - e)) := by
  rw [BivariantClass.capTargetHom_apply, regularImmersionPartGysinClass,
    bivariantRestriction_capTarget (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _)]
  exact cap_lciGysinClass_dimPart_fundamentalChowClass_of_piece sX i hreg e d hP

/-- **`i^!(c_q ∩ [X_d]) = c_q|_{Y_d} ∩ [Y_d]_e`** on the part `X_d` of `X`, for the piece
`Y_d = Y ×_X X_d` of pure dimension `e`: Stacks 0FF6 and 0FF7 for the Gysin map of `i` on
`X_d`. -/
theorem regularImmersionPartGysin_totalChowClassCapFundamental (e d : ℕ)
    (hP : RelativeDimension (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e)
    (c : TotalChowClass (fieldChowSituation k) sX) (q : ℕ) :
    regularImmersionPartGysin sX i hreg e d q (totalChowClassCapFundamental sX c q d) =
      chowCohomologyCapFundamentalClass (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k))
        (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e q
        (TotalChowClass.res (pullback.fst i (dimPart sX d).ι ≫ i) (Category.assoc _ _ _) c q) := by
  have hgys : (gysinSystemOfInvertible (fieldChowSituation k)).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _
  have hq : pullback.snd i (dimPart sX d).ι ≫ partBase sX d =
      pullback.fst i (dimPart sX d).ι ≫ i ≫ sX :=
    pullbackSnd_comp_structureMorphism_eq _ (i ≫ sX) sX i rfl (dimPart sX d).ι
  have hβ : regularImmersionPartGysin sX i hreg e d q (totalChowClassCapFundamental sX c q d) =
      chowCohomologyCapFundamentalClass (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k))
        (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e q
        (chowCohomologyRestrictionOfEq (fieldChowSituation k)
          (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (partBase sX d) hq
          (gysinSystemOfInvertible (fieldChowSituation k)) hgys q
          (TotalChowClass.res (dimPart sX d).ι rfl c q)) :=
    eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      (BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq _ _ hgys _ _ q hq
        ((d : ℤ) - e) (regularImmersionPartGysinClass sX i hreg e d) _
        (regularImmersionPartGysinClass_commutesWithEveryClass sX i hreg e d (𝟙 _) q _) d
        (regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass_of_piece sX i hreg e d
          hP)
        (by ring)))
  rw [hβ, ← TotalChowClass.res_apply_eq_restrictionOfEq, TotalChowClass.res_res]
  exact congrArg (fun c' ↦ chowCohomologyCapFundamentalClass (fieldChowSituation k)
    (gysinSystemOfInvertible (fieldChowSituation k))
    (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e q (c' q))
    (TotalChowClass.res_congr pullback.condition.symm _ _ c)

end Stacks.Chow

end
