module

public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessTransport
public import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionModule
public import StacksFrontier.AlgebraicGeometry.StrictTransform.OpenRestriction

/-!
# The strict transform along a blowup, over an open of the base

Let `f : X ⟶ S`, let `K` be a quasi-coherent ideal sheaf on `S` and let `V ⊆ S` be an open. By
flat base change for blowups ([Stacks, Tag 0805]) the blowup of `V` in `K|_V` is the part of the
blowup of `S` in `K` lying over `V`, and this file upgrades that to the strict transforms: the
strict transform of `X_V/V` along the blowup of `V` in `K|_V`, together with the strict transform
of a module on it, is the part of the strict transform of `X/S` along the blowup of `S` in `K`
lying over `V`.

That statement is the input to the local-global reduction of [Stacks, Tag 080Y]: it is what makes
the strict-transform problem on the blown-up base local on the original base.

## Main results

* `AlgebraicGeometry.exists_strictTransformBlowUp_iso_restrict`: the comparison over an open of
  the base, with the identification of the base, of the scheme and of the module.

## Implementation notes

The open immersion of ambient base changes along which
`Stacks.StrictTransform.schemeRestrictIso` and `Stacks.StrictTransform.moduleRestrictIso` are
applied is `CategoryTheory.Limits.pullback.map` of the two open immersions `X_V ⟶ X` and
`Bl_{K|_V}(V) ⟶ Bl_K(S)`, the latter coming from tag 0805. Its image is the inverse image of `V`
in the ambient base change, which identifies the restricted strict transform with a cartesian
square over the open `Bl_K(S)|_V`; the two squares are pasted by
`CategoryTheory.IsPullback.paste_vert`.

The support of a composite centre, which is the hypothesis `hK` of [Stacks, Tag 080I] at the
composite centre of [Stacks, Tag 080A], is
`AlgebraicGeometry.supportSet_mul_eq_union_image_comap` in
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/StrictTransformFlatnessTransport.lean`; it is
imported rather than restated here.

The matching of the exceptional preimages, which is the hypothesis of the two comparison
isomorphisms, is purely formal: the exceptional ideal of the blowup of `V` in `K|_V` is the
inverse image of the exceptional ideal of the blowup of `S` in `K`, because both are inverse
images of `K` along the two routes of the cartesian square of tag 0805.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The underlying map of an isomorphism of schemes is surjective. -/
public lemma surjective_base_of_isIso {A B : Scheme.{u}} (e : A ⟶ B) [IsIso e] :
    Function.Surjective e.base := by
  have : Surjective e := inferInstance
  exact e.surjective

/-! ### The comparison over an open of the base -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (K : S.IdealSheafData) (V : S.Opens)

/-- **The strict transform along a blowup is computed over an open of the base.** The blowup of
`V` in `K|_V` is the part of the blowup of `S` in `K` over `V` (tag 0805), the strict transform
of `X_V` is the part of the strict transform of `X` over it, and the strict transform of the
restricted module is the restriction of the strict transform of the module. The three
identifications are returned in the shape in which a property of a morphism-and-module pair
invariant under isomorphism consumes them. -/
public theorem exists_strictTransformBlowUp_iso_restrict (F : X.Modules) :
    ∃ (eT : blowUp (K.comap V.ι) ≅ (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).toScheme)
      (eY : Stacks.StrictTransform.scheme (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι))
          (exceptionalIdeal (K.comap V.ι)) ≅
        Limits.pullback (strictTransformToBlowUp f K)
          (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι),
      strictTransformToBlowUp (pullback.snd f V.ι) (K.comap V.ι) ≫ eT.hom =
          eY.hom ≫ pullback.snd (strictTransformToBlowUp f K)
            (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι ∧
        Nonempty (strictTransformBlowUpModule (pullback.snd f V.ι) (K.comap V.ι)
            ((Scheme.Modules.pullback (pullback.fst f V.ι)).obj F) ≅
          (Scheme.Modules.pullback eY.hom).obj
            ((Scheme.Modules.pullback (pullback.fst (strictTransformToBlowUp f K)
              (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι)).obj
              (strictTransformBlowUpModule f K F))) := by
  obtain ⟨hBl, hBlPB⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap V.ι K
  have : IsOpenImmersion hBl := MorphismProperty.of_isPullback hBlPB inferInstance
  -- The image of the comparison morphism of tag 0805 is the inverse image of `V`.
  have hBlRange : Set.range hBl.base =
      Set.range (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι.base := by
    have hcan := IsPullback.of_hasPullback V.ι (blowUpToBase K)
    have hsnd := hBlPB.isoIsPullback_hom_snd _ _ hcan
    have h1 : Set.range hBl.base = Set.range (pullback.snd V.ι (blowUpToBase K)).base := by
      rw [← hsnd]
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
        Set.range_comp]
      rw [(surjective_base_of_isIso (hBlPB.isoIsPullback _ _ hcan).hom).range_eq,
        Set.image_univ]
    rw [h1, Scheme.Pullback.range_snd, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  let eT := IsOpenImmersion.isoOfRangeEq hBl
    (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι hBlRange
  have heT : eT.hom ≫ (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι = hBl :=
    IsOpenImmersion.isoOfRangeEq_hom_fac hBl _ hBlRange
  -- The open immersion of ambient base changes.
  have hXopen : pullback.snd f V.ι ≫ V.ι = pullback.fst f V.ι ≫ f := pullback.condition.symm
  have hBopen : blowUpToBase (K.comap V.ι) ≫ V.ι = hBl ≫ blowUpToBase K := hBlPB.w
  let j := pullback.map (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι)) f (blowUpToBase K)
    (pullback.fst f V.ι) hBl V.ι hXopen hBopen
  have : IsOpenImmersion j :=
    Scheme.pullback_map_isOpenImmersion (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι))
      f (blowUpToBase K) (pullback.fst f V.ι) hBl V.ι hXopen hBopen
  have hjFirst : j ≫ pullback.fst f (blowUpToBase K) =
      pullback.fst (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι)) ≫ pullback.fst f V.ι :=
    pullback.lift_fst _ _ _
  have hjSecond : j ≫ pullback.snd f (blowUpToBase K) =
      pullback.snd (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι)) ≫ hBl :=
    pullback.lift_snd _ _ _
  -- The exceptional preimages correspond.
  have hExcIdeal : exceptionalIdeal (K.comap V.ι) = (exceptionalIdeal K).comap hBl := by
    rw [exceptionalIdeal, exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, ← hBopen]
  have hExceptional : Stacks.StrictTransform.exceptionalPreimage (pullback.snd f V.ι)
        (blowUpToBase (K.comap V.ι)) (exceptionalIdeal (K.comap V.ι)) =
      j.base ⁻¹' Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase K)
        (exceptionalIdeal K) := by
    have hset : ((exceptionalIdeal (K.comap V.ι)).support :
          Set (blowUp (K.comap V.ι))) =
        hBl.base ⁻¹' ((exceptionalIdeal K).support : Set (blowUp K)) := by
      rw [hExcIdeal, Scheme.IdealSheafData.support_comap]
      rfl
    ext x
    have hx : (pullback.snd f (blowUpToBase K)).base (j.base x) =
        hBl.base ((pullback.snd (pullback.snd f V.ι)
          (blowUpToBase (K.comap V.ι))).base x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjSecond]
    show (pullback.snd (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι))).base x ∈
        ((exceptionalIdeal (K.comap V.ι)).support : Set (blowUp (K.comap V.ι))) ↔
      (pullback.snd f (blowUpToBase K)).base (j.base x) ∈
        ((exceptionalIdeal K).support : Set (blowUp K))
    rw [hx, hset]
    exact Iff.rfl
  -- The restricted strict transform as a base change along `j`.
  let eStrict := Stacks.StrictTransform.schemeRestrictIso f (blowUpToBase K) (exceptionalIdeal K)
    (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι)) (exceptionalIdeal (K.comap V.ι)) j
    hExceptional
  have hStrictSnd : eStrict.hom ≫ pullback.snd
        (Stacks.StrictTransform.ideal f (blowUpToBase K) (exceptionalIdeal K)).subschemeι j =
      (Stacks.StrictTransform.ideal (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι))
        (exceptionalIdeal (K.comap V.ι))).subschemeι :=
    Stacks.StrictTransform.schemeRestrictIso_hom_snd f (blowUpToBase K)
      (exceptionalIdeal K) (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι))
      (exceptionalIdeal (K.comap V.ι)) j hExceptional
  -- The square over the open `Bl_K(S)|_V`.
  have hRangeJ : Set.range j.base =
      (pullback.snd f (blowUpToBase K)).base ⁻¹'
        ((blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens) : Set (blowUp K)) := by
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_fst, Scheme.Opens.range_ι, hBlRange,
      Scheme.Opens.range_ι]
    refine Set.inter_eq_right.mpr ?_
    intro x hx
    have hpull : f.base ((pullback.fst f (blowUpToBase K)).base x) =
        (blowUpToBase K).base ((pullback.snd f (blowUpToBase K)).base x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    simp only [Set.mem_preimage] at hx ⊢
    rw [hpull]
    exact hx
  have hRangeOpen : pullback.snd f (blowUpToBase K) ⁻¹ᵁ
      (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι.opensRange = j.opensRange := by
    refine Opens.ext ?_
    rw [Scheme.Opens.opensRange_ι, Scheme.Hom.coe_opensRange]
    exact hRangeJ.symm
  have hjOver : j ≫ pullback.snd f (blowUpToBase K) =
      (pullback.snd (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι)) ≫ eT.hom) ≫
        (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι := by
    rw [Category.assoc, heT]
    exact hjSecond
  have hBasePB : IsPullback (pullback.snd (pullback.snd f V.ι)
      (blowUpToBase (K.comap V.ι)) ≫ eT.hom) j
      (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι (pullback.snd f (blowUpToBase K)) :=
    IsOpenImmersion.isPullback _ j _ _ hjOver hRangeOpen
  have hOuter := (IsPullback.of_hasPullback
    (Stacks.StrictTransform.ideal f (blowUpToBase K) (exceptionalIdeal K)).subschemeι j).paste_vert
      hBasePB.flip
  have hcanOuter := IsPullback.of_hasPullback (strictTransformToBlowUp f K)
    (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι
  let eOuter := hOuter.isoIsPullback _ _ hcanOuter
  have hOuterFst := hOuter.isoIsPullback_hom_fst _ _ hcanOuter
  have hOuterSnd := hOuter.isoIsPullback_hom_snd _ _ hcanOuter
  refine ⟨eT, eStrict ≪≫ eOuter, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc]
    rw [hOuterSnd, ← hStrictSnd]
    simp only [Category.assoc]
  · refine ⟨?_⟩
    have eF := Scheme.Modules.pullbackModuleIsoOfSquare (pullback.fst f (blowUpToBase K))
      (pullback.fst (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι))) j (pullback.fst f V.ι)
      hjFirst F ((Scheme.Modules.pullback (pullback.fst f V.ι)).obj F) (Iso.refl _)
    have eModule := Stacks.StrictTransform.moduleRestrictIso f (blowUpToBase K)
      (exceptionalIdeal K) (pullback.snd f V.ι) (blowUpToBase (K.comap V.ι))
      (exceptionalIdeal (K.comap V.ι)) j hExceptional F
      ((Scheme.Modules.pullback (pullback.fst f V.ι)).obj F) eF
    have eAmbient := (Scheme.Modules.pullbackComp eOuter.hom
          (pullback.fst (strictTransformToBlowUp f K)
            (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι)).app
          (strictTransformBlowUpModule f K F) ≪≫
        (Scheme.Modules.pullbackCongr hOuterFst).app (strictTransformBlowUpModule f K F)
    exact eModule ≪≫ (Scheme.Modules.pullback eStrict.hom).mapIso eAmbient.symm ≪≫
      (Scheme.Modules.pullbackComp eStrict.hom eOuter.hom).app _

end AlgebraicGeometry

end
