module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreCartesianOfGood
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteNearCodimensionOnePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective

/-!
# The generic fibre of a proper dominant morphism of integral good algebraic spaces

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

omit sX hX in
/-- **The only point of codimension zero of an integral algebraic space is its generic point.** -/
theorem eq_genericPoint_of_localRingDimension_eq_zero
    (hXa : IsAlgebraicSpace D.site D.base D.base_mem X) {x : points D.site D.base D.base_mem X}
    (hx : localRingDimension D.site D.base D.base_mem x = 0) :
    x = genericPoint D.site D.base D.base_mem hXa hintX := by
  have hmem := (mem_genericPoints_iff_localRingDimension_eq_zero D.site D.base D.base_mem hXa
    hintX.2.1 x).mpr hx
  have : IrreducibleSpace (points D.site D.base D.base_mem X) := hintX.2.2
  have := t0Space_points_of_isDecentSpace D.site D.base D.base_mem hXa hintX.2.1
  have hcl : closure {x} = (Set.univ : Set (points D.site D.base D.base_mem X)) :=
    Set.Subset.antisymm (Set.subset_univ _)
      (hmem.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
  exact IsGenericPoint.eq (show IsGenericPoint x Set.univ from hcl)
    (isGenericPoint_genericPoint D.site D.base D.base_mem hXa hintX)

include hintY in
/-- **A point of `X` over the generic point of `Y` is the generic point of `X`**, for a morphism
over the base between good integral spaces of the same δ-dimension. -/
theorem eq_genericPoint_of_pointsMap_eq_genericPoint_of_deltaDimension {p : X ⟶ Y}
    (hpB : p ≫ sY = sX)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ)
    {x : points D.site D.base D.base_mem X}
    (hx : pointsMap D.site D.base D.base_mem X p x =
      genericPoint D.site D.base D.base_mem hY.1 hintY) :
    x = genericPoint D.site D.base D.base_mem hX.1 hintX := by
  obtain ⟨dX, hdX⟩ := exists_dimensionFunction_deltaValue_of_isGood D sX hX
  have hle := inducedDimensionValue_pointsMap_le D sX hX sY hY p hpB x
  rw [hx] at hle
  have hgen : inducedDimensionValue D.site D.base D.base_mem D.delta sX
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      inducedDimensionValue D.site D.base D.base_mem D.delta sY
        (genericPoint D.site D.base D.base_mem hY.1 hintY) :=
    WithBotTop.coe_injective
      ((deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint D sX hX hintX).symm.trans
        (hdim.trans (deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint D sY hY
          hintY)))
  by_contra hne
  have hspec : genericPoint D.site D.base D.base_mem hX.1 hintX ⤳ x :=
    (isGenericPoint_genericPoint D.site D.base D.base_mem hX.1 hintX).specializes
      (Set.mem_univ x)
  have hlt := dX.strictAnti_specializes hspec (Ne.symm hne)
  rw [hdX, hdX] at hlt
  change inducedDimensionValue D.site D.base D.base_mem D.delta sX x <
    inducedDimensionValue D.site D.base D.base_mem D.delta sX _ at hlt
  omega

/-- The image of the chosen residue-field point of `x` along a monomorphism `α : F ⟶ G` has a
monomorphic field morphism factoring through `α`, and represents `α x`. -/
private theorem mono_fieldMorphism_map_residueFieldRepresentative {F G : _ ⥤ Type u} (α : F ⟶ G)
    [Mono α] (hdec : IsDecentSpace D.site D.base D.base_mem F)
    (x : points D.site D.base D.base_mem F) :
    Mono (fieldMorphism D.site D.base D.base_mem G (FieldValuedPoint.map D.site D.base D.base_mem
      F α (residueFieldRepresentative D.site D.base D.base_mem F hdec x).1)) ∧
    fieldMorphism D.site D.base D.base_mem G (FieldValuedPoint.map D.site D.base D.base_mem
      F α (residueFieldRepresentative D.site D.base D.base_mem F hdec x).1) =
      fieldMorphism D.site D.base D.base_mem F
        (residueFieldRepresentative D.site D.base D.base_mem F hdec x).1 ≫ α ∧
    (FieldValuedPoint.map D.site D.base D.base_mem F α
      (residueFieldRepresentative D.site D.base D.base_mem F hdec x).1).class D.site D.base
        D.base_mem G = pointsMap D.site D.base D.base_mem F α x := by
  have hf := fieldMorphism_map D.site D.base D.base_mem F α
    (residueFieldRepresentative D.site D.base D.base_mem F hdec x).1
  refine ⟨?_, hf, ?_⟩
  · rw [hf]
    exact @mono_comp _ _ _ _ _ _ (residueFieldRepresentative D.site D.base D.base_mem F hdec
      x).2.2 _ inferInstance
  · rw [← pointsMap_class, (residueFieldRepresentative D.site D.base D.base_mem F hdec x).2.1]

include hintY in
/-- **The generic fibre of a proper dominant morphism of integral good algebraic spaces of the same
δ-dimension is `Spec R(X)`.** The square

```
Spec κ(ξ_X) ⟶ X
    ↓          ↓ p
Spec κ(p ξ_X) ⟶ Y
```

of the chosen residue-field points of Stacks 0EMW is cartesian. -/
theorem exists_isPullback_residueFieldMorphism_genericPoint_of_isProper {p : X ⟶ Y}
    (hpB : p ≫ sY = sX) (hproper : IsProper D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ) :
    ∃ g : (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX)).1.siteObject
          D.site D.base D.base_mem X ⟶
        (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX))).1.siteObject
          D.site D.base D.base_mem Y,
      IsPullback
        (residueFieldMorphism D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX))
        (yoneda.map g) p
        (residueFieldMorphism D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX))) := by
  have hYLN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  have hld : localRingDimension D.site D.base D.base_mem (pointsMap D.site D.base D.base_mem X p
      (genericPoint D.site D.base D.base_mem hX.1 hintX)) = 0 := by
    rw [hgen]
    exact localRingDimension_genericPoint_eq_zero D.site D.base D.base_mem hY.1 hintY
  -- Step 1: `p` is finite over an open neighbourhood `W` of `ηY` (Stacks 0AD2).
  obtain ⟨W, hWopen, ⟨w, hw⟩, hfin⟩ :=
    exists_isOpenSubspace_isFinite_pullback_snd_of_localRingDimension_le_one D.site D.base
      D.base_mem hX.1 hY.1 p hproper hYLN _ (by rw [hld]; exact zero_le_one) (Or.inl
        fun x hx => by
          have hxgen : x = genericPoint D.site D.base D.base_mem hX.1 hintX :=
            eq_genericPoint_of_localRingDimension_eq_zero D hintX hX.1 hx
          rw [hxgen]
          exact hasTranscendenceDegreeAt_genericPoint_eq_zero D sX sY hX hY hintX hintY p hpB
            hgen hdim)
  -- Step 2: the restriction `pW : X ×_Y W ⟶ W` and its properties.
  have hsq : IsPullback (pullback.fst p W.ι) (pullback.snd p W.ι) p W.ι :=
    IsPullback.of_hasPullback p W.ι
  have hXW : IsAlgebraicSpace D.site D.base D.base_mem (pullback p W.ι) :=
    isAlgebraicSpace_pullback D.site D.base D.base_mem p W.ι hX.1 hWopen.1 hY.1
  have hrep : yoneda.relativelyRepresentable (pullback.snd p W.ι) :=
    relativelyRepresentable_of_isFinite D.site D.base D.base_mem hXW.isSheaf hWopen.1.isSheaf
      hfin
  have hetW : IsEtale D.site D.base D.base_mem W.ι := isEtale_ι_of_isOpenSubspace hWopen
  have hetfst : IsEtale D.site D.base D.base_mem (pullback.fst p W.ι) :=
    isEtale_pullback_fst D.site D.base D.base_mem hX.1 hY.1 hWopen.1 p W.ι hetW
  have hdecW : IsDecentSpace D.site D.base D.base_mem W.toFunctor :=
    isDecentSpace_of_isOpenSubspace D.site D.base D.base_mem hY.1 hintY.2.1 hWopen
  have hdecXW : IsDecentSpace D.site D.base D.base_mem (pullback p W.ι) :=
    isDecentSpace_of_isEtale D.site D.base D.base_mem (pullback.fst p W.ι) hXW hX.1 hetfst
      hintX.2.1
  have hredXW : HasEtaleLocalProperty D.site D.base D.base_mem (pullback p W.ι)
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_of_isEtale D.site D.base D.base_mem hXW hX.1 hetfst hintX.1
  have hredW : HasEtaleLocalProperty D.site D.base D.base_mem W.toFunctor
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_of_isEtale D.site D.base D.base_mem hWopen.1 hY.1 hetW hintY.1
  -- Step 3: the point of `X ×_Y W` over the generic points.
  obtain ⟨xW, hxW1, hxW2⟩ := exists_points_of_isPullback D.site D.base D.base_mem hsq
    (genericPoint D.site D.base D.base_mem hX.1 hintX) w hw.symm
  have hdimW : localRingDimension D.site D.base D.base_mem
      (pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) xW) = 0 := by
    rw [hxW2, ← localRingDimension_pointsMap_of_etale D.site D.base D.base_mem hWopen.1 hY.1
      W.ι hetW w, hw, hld]
  have hfib : ∀ y y' : points D.site D.base D.base_mem (pullback p W.ι),
      pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) y =
          pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) xW →
        pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) y' =
          pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) xW → y = y' := by
    have hfst : ∀ y : points D.site D.base D.base_mem (pullback p W.ι),
        pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) y =
          pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) xW →
        pointsMap D.site D.base D.base_mem _ (pullback.fst p W.ι) y =
          genericPoint D.site D.base D.base_mem hX.1 hintX := by
      intro y hy
      refine eq_genericPoint_of_pointsMap_eq_genericPoint_of_deltaDimension D sX hX sY hY hintX
        hintY hpB hdim ?_
      rw [pointsMap_apply_comm D.site D.base D.base_mem hsq.w y, hy, ← hgen,
        ← pointsMap_apply_comm D.site D.base D.base_mem hsq.w xW, hxW1]
    intro y y' hy hy'
    exact pointsMap_injective_of_mono D.site D.base D.base_mem (pullback.fst p W.ι)
      ((hfst y hy).trans (hfst y' hy').symm)
  -- Step 4: the generic fibre of the finite `pW`.
  obtain ⟨gW, hgW⟩ := exists_isPullback_residueFieldMorphism D.site D.base D.base_mem hrep hfin
    hXW hWopen.1 hdecXW hdecW hredXW hredW xW hdimW hfib
  have hpaste := hgW.paste_horiz hsq
  -- Step 5: transport to the chosen residue-field points of `X` and `Y`.
  let rX := (residueFieldRepresentative D.site D.base D.base_mem (pullback p W.ι) hdecXW xW).1
  let rY := (residueFieldRepresentative D.site D.base D.base_mem W.toFunctor hdecW
    (pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) xW)).1
  let qX := FieldValuedPoint.map D.site D.base D.base_mem _ (pullback.fst p W.ι) rX
  let qY := FieldValuedPoint.map D.site D.base D.base_mem _ W.ι rY
  obtain ⟨hqXm, hqXf, hqXc⟩ := mono_fieldMorphism_map_residueFieldRepresentative D
    (pullback.fst p W.ι) hdecXW xW
  obtain ⟨hqYm, hqYf, hqYc⟩ := mono_fieldMorphism_map_residueFieldRepresentative D W.ι hdecW
    (pointsMap D.site D.base D.base_mem _ (pullback.snd p W.ι) xW)
  replace hqXc := hqXc.trans hxW1
  replace hqYc := hqYc.trans (by rw [hxW2, hw])
  have hpaste' : IsPullback (fieldMorphism D.site D.base D.base_mem X qX) (yoneda.map gW) p
      (fieldMorphism D.site D.base D.base_mem Y qY) := by
    rw [hqXf, hqYf]
    exact hpaste
  obtain ⟨eX, heX, -⟩ := residueFieldRepresentative_unique D.site D.base D.base_mem X hX.1
    hintX.2.1 _ qX hqXc hqXm
  obtain ⟨eY, heY, -⟩ := residueFieldRepresentative_unique D.site D.base D.base_mem Y hY.1
    hintY.2.1 _ qY hqYc hqYm
  refine ⟨yoneda.preimage (eX.hom ≫ yoneda.map gW ≫ eY.inv), ?_⟩
  rw [Functor.map_preimage]
  refine hpaste'.of_iso eX.symm (Iso.refl _) eY.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← heX]
    simp
  · simp
  · simp
  · rw [← heY]
    simp only [Iso.symm_hom, Iso.refl_hom]
    exact (Category.comp_id (fieldMorphism D.site D.base D.base_mem Y qY)).trans
      (Iso.inv_hom_id_assoc eY _).symm

end AlgebraicGeometry.Space

end
