module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CodimensionClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter

/-!
# The codimension-graded Gysin map and the rational Gysin map

Let `k` be a field and let `f : X ⟶ Y` be a morphism of schemes smooth and quasi-compact over `k`.
The Gysin map `f^!` of Stacks 0FF3 is constructed in two forms: on Chow groups graded by
codimension, `Stacks.Chow.codimensionGysin : CH^i(Y) ⟶ CH^i(X)`, `CH^i(-) = ∏_d CH_{d-i}((-)_d)`,
assembled from the restrictions of `f^!` to the pieces `X_{d,e} = X_d ∩ f⁻¹(Y_e)`; and on
`CH_*(-) ⊗ 𝐐`, `Stacks.Chow.lciGysinRational`, the sum over all degrees of the cap products with
the parts of `f^!`. This file shows that they agree through the maps
`Stacks.Chow.codimensionToRationalChow : CH^i(-) ⟶ CH_*(-) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.codimensionToRationalChow_codimensionGysin`: the two Gysin maps agree.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart includePart)

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sY] [Smooth sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] in
/-- The inclusion `X_{d,e'} ⟶ X_d ⟶ X` is a morphism over `k`. -/
theorem dimPartPiece_ι_comp_ι_comp (d e : ℕ) :
    ((dimPartPiece sX sY f d e).ι ≫ (dimPart sX d).ι) ≫ sX = dimPartPieceBase sX sY f d e :=
  Category.assoc _ _ _

/-- The cap product of `f^!` with a class of `Y`, restricted to a piece `X_{d,e}`, is the
restriction of the cap product at the test scheme `Y_e` with the restriction of the class to
`Y_e`. -/
theorem chowGroupRestrict_dimPartPiece_smoothGysinChow (d e : ℕ) (q n : ℤ)
    (z : chowGroup (fieldChowSituation k) sY n) :
    chowGroupRestrict (fieldChowSituation k) sX (dimPartPieceBase sX sY f d e)
        ((dimPartPiece sX sY f d e).ι ≫ (dimPart sX d).ι) (dimPartPiece_ι_comp_ι_comp sX sY d e)
        (n - q) (smoothGysinChow (fieldChowSituation k) sX sY hf q n z) =
      chowGroupRestrict (fieldChowSituation k) (pullback.fst f (dimPart sY e).ι ≫ sX)
        (dimPartPieceBase sX sY f d e) (dimPartPieceToPullback sX sY f d e)
        (dimPartPieceToPullback_comp_base sX sY f d e) (n - q)
        ((smoothGysinClass (fieldChowSituation k) sX sY hf q).cap (dimPart sY e).ι n
          (chowGroupRestrict (fieldChowSituation k) sY (partBase sY e) (dimPart sY e).ι rfl n
            z)) := by
  set F := smoothGysinClass (fieldChowSituation k) sX sY hf q
  set V := dimPart sY e
  have he : (pullbackIdIso f).hom ≫ (pullback.fst f (𝟙 Y) ≫ sX) = sX := by
    rw [pullbackIdIso_hom_fst_assoc]
  have hm : V.ι ≫ 𝟙 Y = V.ι := Category.comp_id _
  set v' := baseChangeMapOfEq f (𝟙 Y) V.ι V.ι hm
  have sq := isPullback_baseChangeMapOfEq f (𝟙 Y) V.ι V.ι hm
  have : IsOpenImmersion v' := MorphismProperty.of_isPullback sq (P := @IsOpenImmersion)
    inferInstance
  have hvY : V.ι ≫ (𝟙 Y ≫ sY) = V.ι ≫ sY := by rw [Category.id_comp]
  have hcap := BivariantClass.cap_chowGroupRestrict (fieldChowSituation k)
    (gysinSystemOfInvertible (fieldChowSituation k)) sX sY f hf q F
    (𝟙 Y) V.ι V.ι hm v' sq (baseChangeMapOfEq_fst f (𝟙 Y) V.ι V.ι hm) n hvY
    (baseChangeMapOfEq_comp_structure sX f (𝟙 Y) V.ι V.ι hm)
    (chowGroupCongr (fieldChowSituation k) (Category.id_comp sY).symm n z)
  rw [chowGroupRestrict_chowGroupCongr (fieldChowSituation k) sY (𝟙 Y ≫ sY) (V.ι ≫ sY) V.ι rfl
    hvY (Category.id_comp sY).symm] at hcap
  rw [← hcap, chowGroupRestrict_comp, smoothGysinChow, lciGysinChow,
    BivariantClass.capTargetHom_apply, BivariantClass.capTarget,
    ← chowGroupRestrict_eq_chowPushforwardOfIso_inv (fieldChowSituation k) _ sX (pullbackIdIso f)
      he,
    chowGroupRestrict_comp]
  refine DFunLike.congr_fun (chowGroupRestrict_congr (fieldChowSituation k) _ _ _ _ _ _ ?_ _) _
  refine pullback.hom_ext ?_ ?_
  · simp only [v', Category.assoc, pullbackIdIso_hom_fst, Category.comp_id,
      baseChangeMapOfEq_fst]
    exact (dimPartPieceToPullback_fst sX sY f d e).symm
  · have h2 : dimPartPieceHom sX sY f d e ≫ V.ι =
        (dimPartPiece sX sY f d e).ι ≫ (dimPart sX d).ι ≫ f := by
      simp only [V, dimPartPieceHom, dimPartPieceToPreimage, Category.assoc, morphismRestrict_ι,
        morphismRestrict_ι_assoc]
    simp only [v', Category.assoc, pullbackIdIso_hom_snd, baseChangeMapOfEq_snd]
    exact ((dimPartPieceToPullback_snd_assoc sX sY f d e V.ι).trans h2).symm

/-- On a piece `X_{d,e}` the Gysin map is homogeneous of degree `e - d`: for `q ≠ e - d` the
part `f^!_q`, capped at the test scheme `Y_e` with any class, restricts to zero on `X_{d,e}`. -/
theorem chowGroupRestrict_cap_smoothGysinClass_eq_zero (d e : ℕ) {q : ℤ} (hq : q ≠ (e : ℤ) - d)
    (n : ℤ) (β : chowGroup (fieldChowSituation k) (partBase sY e) n) :
    chowGroupRestrict (fieldChowSituation k) (pullback.fst f (dimPart sY e).ι ≫ sX)
        (dimPartPieceBase sX sY f d e) (dimPartPieceToPullback sX sY f d e)
        (dimPartPieceToPullback_comp_base sX sY f d e) (n - q)
        ((smoothGysinClass (fieldChowSituation k) sX sY hf q).cap (dimPart sY e).ι n β) = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hlci := isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf
  have hex := GysinMapExists.of_smooth_source f sY sX hf
  set π := (dimPartPiece sX sY f d e).ι ≫ (dimPart sX d).ι
  have hYe := relativeDimension_partBase sY e
  have hXd := relativeDimension_partBase sX d
  have hT := WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k
    (partBase sY e) e hYe
  obtain ⟨dd, hd, hdeg⟩ := (Classical.choice ((gysinMapExists_iff_nonempty f).1 hex) :
    SmoothFactorization f).exists_hasCapFundamentalFormula_gysinMap (fieldChowSituation k) sX sY
      hf hlci
  refine chowGroup_eq_of_chowGroupRestrict_preimage_connectedComponent_eq
    (C := fieldChowSituation k) _ π _ fun w ↦ ?_
  rw [map_zero, chowGroupRestrict_comp]
  rcases isEmpty_or_nonempty (π ⁻¹ᵁ X.connectedComponentOpens w).toScheme with hw | ⟨⟨x, hx⟩⟩
  · have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      ((π ⁻¹ᵁ X.connectedComponentOpens w).ι ≫ dimPartPieceBase sX sY f d e) (n - q)
    exact Subsingleton.elim _ _
  have hsub : ∀ U : X.Opens, IsClopen (U : Set X) → π x ∈ U →
      ∀ y ∈ X.connectedComponentOpens w, y ∈ U := by
    intro U hU hxU y hy
    refine hU.connectedComponent_subset hxU ?_
    rw [← ConnectedComponents.coe_eq_coe']
    exact hy.trans hx.symm
  have hXdc : IsClopen ((dimPart sX d : X.Opens) : Set X) :=
    (isClopenDecomposition_dimPart sX).isClopen d
  have hYec : IsClopen ((dimPart sY e : Y.Opens) : Set Y) :=
    (isClopenDecomposition_dimPart sY).isClopen e
  have hxd : π x ∈ dimPart sX d := ((dimPartPiece sX sY f d e).ι x).2
  have hxe : π x ∈ f ⁻¹ᵁ dimPart sY e := x.2
  have hdw : dd w = (e : ℤ) - d := by
    obtain ⟨ξ, hξ, hξw⟩ := exists_mem_genericPoints_mk_eq w
    have hξd : ξ ∈ dimPart sX d := hsub _ hXdc hxd ξ hξw
    have hξe : f ξ ∈ dimPart sY e :=
      hsub (f ⁻¹ᵁ dimPart sY e) (hYec.preimage f.continuous) hxe ξ hξw
    have hV : Y.connectedComponentOpens (f.continuous.connectedComponentsMap
        (ConnectedComponents.mk ξ)) ≤ dimPart sY e := by
      intro y hy
      refine hYec.connectedComponent_subset hξe ?_
      rw [← ConnectedComponents.coe_eq_coe']
      exact hy
    have hgen : (⟨ξ, hξd⟩ : (dimPart sX d).toScheme) ∈ genericPoints (dimPart sX d).toScheme :=
      (dimPart sX d).ι.isOpenEmbedding.mem_genericPoints_of_image hξ
    have hδ : relativeDimension (fieldChowSituation k).dimensionFunction sX ξ = d := by
      have h := WeilCohomology.relativeDimension_of_mem_irreducibleComponents_of_relativeDimension
        k (partBase sX d) d hXd _ hgen
      exact (relativeDimension_comp_isOpenImmersion _ (dimPart sX d).ι sX
        (⟨ξ, hξd⟩ : (dimPart sX d).toScheme)).symm.trans h
    rw [← hξw, hdeg ξ hξ e fun W ↦ ?_, hδ]
    rw [← WeilCohomology.deltaDimension_congr (Y.homOfLE_ι_assoc hV sY)]
    exact deltaDimension_irreducibleComponents_of_isOpenImmersion (fieldChowSituation k)
      (partBase sY e) hT _ W
  have hres := restriction_completedBivariantSequence (fieldChowSituation k)
    (gysinSystemOfInvertible (fieldChowSituation k)) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion (fieldChowSituation k))
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction (fieldChowSituation k))
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp (fieldChowSituation k))
    (lciGysinMap (fieldChowSituation k) sX sY hf hlci hex) q w
  have h0 : lciGysinMap (fieldChowSituation k) sX sY hf hlci hex w q = 0 := by
    have hca : lciGysinMap (fieldChowSituation k) sX sY hf hlci hex w =
        DirectSum.of _ (dd w) (lciGysinMap (fieldChowSituation k) sX sY hf hlci hex w (dd w)) :=
      (hd w).1
    rw [hca, hdw]
    exact DirectSum.of_eq_of_ne _ _ _ hq
  exact chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero
    (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) sX sY f hf q
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion (fieldChowSituation k))
    (smoothGysinClass (fieldChowSituation k) sX sY hf q) w (hres.trans h0) (dimPart sY e).ι n β
    _ ((π ⁻¹ᵁ X.connectedComponentOpens w).ι ≫ dimPartPieceToPullback sX sY f d e)
    (by rw [Category.assoc, dimPartPieceToPullback_comp_base])
    (π.resLE (X.connectedComponentOpens w) (π ⁻¹ᵁ X.connectedComponentOpens w) le_rfl)
    (by rw [Scheme.Hom.resLE_comp_ι, Category.assoc, dimPartPieceToPullback_fst])

/-- The pushforward from the part `Y_e` of `Y`. -/
abbrev partPushforward (e : ℕ) (n : ℤ) :
    chowGroup (fieldChowSituation k) (partBase sY e) n →+ chowGroup (fieldChowSituation k) sY n :=
  haveI := (isClopenDecomposition_dimPart sY).isProper_ι e
  properChowPushforward (fieldChowSituation k) (partBase sY e) sY (dimPart sY e).ι rfl n
    (properPushforwardDescends _ _ _ _ _ _)

/-- The class `f^!_q (ι_{e*} β)` restricted to the part `X_d`. -/
abbrev partGysinTerm (d e : ℕ) (q n : ℤ) (β : chowGroup (fieldChowSituation k) (partBase sY e) n) :
    chowGroup (fieldChowSituation k) (partBase sX d) (n - q) :=
  chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl (n - q)
    (smoothGysinChow (fieldChowSituation k) sX sY hf q n (partPushforward sY e n β))

/-- **The piece `X_{d,e'}` of `f^!_q (ι_{e*} β)`.** -/
theorem chowGroupRestrict_partGysinTerm (d e e' : ℕ) (q n : ℤ)
    (β : chowGroup (fieldChowSituation k) (partBase sY e) n) :
    chowGroupRestrict (fieldChowSituation k) (partBase sX d) (dimPartPieceBase sX sY f d e')
        (dimPartPiece sX sY f d e').ι rfl (n - q) (partGysinTerm sX sY hf d e q n β) =
      chowGroupRestrict (fieldChowSituation k) (pullback.fst f (dimPart sY e').ι ≫ sX)
        (dimPartPieceBase sX sY f d e') (dimPartPieceToPullback sX sY f d e')
        (dimPartPieceToPullback_comp_base sX sY f d e') (n - q)
        ((smoothGysinClass (fieldChowSituation k) sX sY hf q).cap (dimPart sY e').ι n
          (chowGroupRestrict (fieldChowSituation k) sY (partBase sY e') (dimPart sY e').ι rfl n
            (partPushforward sY e n β))) := by
  rw [chowGroupRestrict_comp]
  exact chowGroupRestrict_dimPartPiece_smoothGysinChow sX sY hf d e' q n _

/-- Off the pieces over `Y_e`, `f^!_q (ι_{e*} β)` vanishes: for `e' ≠ e` its restriction to
`X_{d,e'}` is zero. -/
theorem chowGroupRestrict_partGysinTerm_of_ne (d : ℕ) {e e' : ℕ} (he : e' ≠ e) (q n : ℤ)
    (β : chowGroup (fieldChowSituation k) (partBase sY e) n) :
    chowGroupRestrict (fieldChowSituation k) (partBase sX d) (dimPartPieceBase sX sY f d e')
        (dimPartPiece sX sY f d e').ι rfl (n - q) (partGysinTerm sX sY hf d e q n β) = 0 := by
  have := (isClopenDecomposition_dimPart sY).isProper_ι e
  rw [chowGroupRestrict_partGysinTerm, chowGroupRestrict_properChowPushforward_opens_of_disjoint
    _ _ _ _ ((isClopenDecomposition_dimPart sY).disjoint e e' (Ne.symm he)), map_zero, map_zero]

/-- On the pieces over `Y_e`, `f^!_q (ι_{e*} β)` restricts to `f^!_q ∩_{Y_e} β`. -/
theorem chowGroupRestrict_partGysinTerm_self (d e : ℕ) (q n : ℤ)
    (β : chowGroup (fieldChowSituation k) (partBase sY e) n) :
    chowGroupRestrict (fieldChowSituation k) (partBase sX d) (dimPartPieceBase sX sY f d e)
        (dimPartPiece sX sY f d e).ι rfl (n - q) (partGysinTerm sX sY hf d e q n β) =
      chowGroupRestrict (fieldChowSituation k) (pullback.fst f (dimPart sY e).ι ≫ sX)
        (dimPartPieceBase sX sY f d e) (dimPartPieceToPullback sX sY f d e)
        (dimPartPieceToPullback_comp_base sX sY f d e) (n - q)
        ((smoothGysinClass (fieldChowSituation k) sX sY hf q).cap (dimPart sY e).ι n β) := by
  have := (isClopenDecomposition_dimPart sY).isProper_ι e
  rw [chowGroupRestrict_partGysinTerm, chowGroupRestrict_properChowPushforward_opens_self]

/-- **`f^!_q (ι_{e*} β)` vanishes on `X_d` unless `q = e - d`.** -/
theorem partGysinTerm_eq_zero (d e : ℕ) {q : ℤ} (hq : q ≠ (e : ℤ) - d) (n : ℤ)
    (β : chowGroup (fieldChowSituation k) (partBase sY e) n) :
    partGysinTerm sX sY hf d e q n β = 0 := by
  refine (chowGroupDimPartPieceEquiv sX sY (f := f) d (n - q)).injective (funext fun e' => ?_)
  rw [chowGroupDimPartPieceEquiv_apply, map_zero, Pi.zero_apply]
  rcases eq_or_ne e'.down e with h | h
  · obtain ⟨e'⟩ := e'
    subst h
    rw [chowGroupRestrict_partGysinTerm_self]
    exact chowGroupRestrict_cap_smoothGysinClass_eq_zero sX sY hf d e' hq n β
  · exact chowGroupRestrict_partGysinTerm_of_ne sX sY hf d h q n β

/-- The component of `f^! b` on `X_d` is the sum over the nonempty parts `Y_e` of the parts
`f^!_{e-d} (ι_{e*} b_e)` restricted to `X_d`. -/
theorem sum_partGysinTerm_eq_codimensionGysin [CompactSpace Y] (i : ℤ)
    (b : codimensionChowGroup k sY i) (d : ℕ) :
    ∑ e ∈ nonemptyDimParts k sY, chowGroupDegreeEquiv (fieldChowSituation k) (partBase sX d)
        (by ring : (e : ℤ) - i - ((e : ℤ) - d) = d - i)
        (partGysinTerm sX sY hf d e ((e : ℤ) - d) ((e : ℤ) - i) (b e)) =
      codimensionGysin sX sY hf i b d := by
  classical
  refine (chowGroupDimPartPieceEquiv sX sY (f := f) d (d - i)).injective (funext fun e' => ?_)
  obtain ⟨e'⟩ := e'
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply, map_sum,
    chowGroupRestrict_codimensionGysin]
  simp_rw [chowGroupRestrict_chowGroupDegreeEquiv]
  by_cases he' : e' ∈ nonemptyDimParts k sY
  · rw [Finset.sum_eq_single_of_mem e' he' fun e _ he => by
      rw [chowGroupRestrict_partGysinTerm_of_ne sX sY hf d (Ne.symm he), map_zero],
      chowGroupRestrict_partGysinTerm_self, dimPartPieceGysin, AddMonoidHom.comp_apply]
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
    refine HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm
    rw [BivariantClass.capTargetHom_apply]
    exact (dimPartPieceGysinClass_capTarget_heq sX sY hf d e' _ _).symm
  · have : IsEmpty (dimPartPiece sX sY f d e').toScheme := ⟨fun x => he'
      ((mem_nonemptyDimParts k sY).2 ⟨_, (x.2 : _ ∈ f ⁻¹ᵁ dimPart sY e')⟩)⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (dimPartPieceBase sX sY f d e') (d - i)
    exact Subsingleton.elim _ _

/-- **The codimension-graded Gysin map agrees with the rational Gysin map.** For a morphism
`f : X ⟶ Y` of schemes smooth and quasi-compact over `k` and `b ∈ CH^i(Y)`, the image in
`CH_*(X) ⊗ 𝐐` of `f^! b ∈ CH^i(X)` (`Stacks.Chow.codimensionGysin`) is the rational Gysin map
`Stacks.Chow.lciGysinRational` of the image of `b` in `CH_*(Y) ⊗ 𝐐`. -/
theorem codimensionToRationalChow_codimensionGysin [CompactSpace X] [CompactSpace Y] (i : ℤ)
    (b : codimensionChowGroup k sY i) :
    codimensionToRationalChow k sX i (codimensionGysin sX sY hf i b) =
      lciGysinRational (fieldChowSituation k) sX sY hf
        (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf)
        (GysinMapExists.of_smooth_source f sY sX hf) (codimensionToRationalChow k sY i b) := by
  classical
  have := isNoetherian_of_compactSpace sX
  have : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  set S := (finite_lciGysinSupport (fieldChowSituation k) sX sY hf
    (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf)
    (GysinMapExists.of_smooth_source f sY sX hf)).toFinset
  rw [codimensionToRationalChow_apply, ← sum_rationalIncludePart_rationalRestrictPart k sX
    (lciGysinRational _ _ _ _ _ _ _)]
  refine Finset.sum_congr rfl fun d _ => congrArg _ ?_
  rw [codimensionToRationalChow_apply, map_sum, map_sum]
  have hterm : ∀ e ∈ nonemptyDimParts k sY,
      rationalRestrictPart k sX d (lciGysinRational (fieldChowSituation k) sX sY hf
        (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf)
        (GysinMapExists.of_smooth_source f sY sX hf) (rationalIncludePart k sY e
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sY e) j)
            ((e : ℤ) - i) ((1 : ℚ) ⊗ₜ[ℤ] b e)))) =
        DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j)
          ((d : ℤ) - i) ((1 : ℚ) ⊗ₜ[ℤ] chowGroupDegreeEquiv (fieldChowSituation k) (partBase sX d)
            (by ring : (e : ℤ) - i - ((e : ℤ) - d) = d - i)
            (partGysinTerm sX sY hf d e ((e : ℤ) - d) ((e : ℤ) - i) (b e))) := by
    intro e _
    rw [← DirectSum.lof_eq_of ℚ, rationalIncludePart_lof, includePart, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap, DirectSum.lof_eq_of, lciGysinRational_of_tmul, map_sum]
    simp only [rationalChowMap_of_tmul]
    show ∑ q ∈ S, DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k)
        (partBase sX d) j) ((e : ℤ) - i - q)
        ((1 : ℚ) ⊗ₜ[ℤ] partGysinTerm sX sY hf d e q ((e : ℤ) - i) (b e)) = _
    rw [directSum_of_one_tmul_chowGroupDegreeEquiv]
    refine Finset.sum_eq_single _ (fun q _ hq => ?_) fun hS => ?_
    · rw [partGysinTerm_eq_zero sX sY hf d e hq, TensorProduct.tmul_zero, map_zero]
    · rw [partGysinTerm, smoothGysinChow, lciGysinChow_eq_zero _ _ _ _ _ _
        (fun h => hS ((Set.Finite.mem_toFinset _).2 h)), AddMonoidHom.zero_apply, map_zero,
        TensorProduct.tmul_zero, map_zero]
  rw [Finset.sum_congr rfl hterm, ← map_sum, ← TensorProduct.tmul_sum,
    sum_partGysinTerm_eq_codimensionGysin]

end Stacks.Chow

end
