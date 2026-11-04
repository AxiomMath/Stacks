module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeAllPoints

/-!
# The two directions of Stacks 0ANW, each on its own

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0ANW** compares `f` being locally of finite type with
the condition that every affine representable étale square over `f` carry a taut, topologically
of finite type morphism of `WAdm^{count}`. This file proves the two implications between those
two conditions as separate statements:

* `hasPropertyOnEveryAffineEtaleDiagram_tautTopologicallyOfFiniteType_of_isLocallyOfFiniteType`:
  locally of finite type implies the chart condition, for any morphism of formal algebraic
  spaces (the implication (4) ⟹ (1));
* `isLocallyOfFiniteType_of_hasPropertyOnEveryAffineEtaleDiagram_tautTopologicallyOfFiniteType`:
  the chart condition implies locally of finite type, for locally countably indexed `X` and `Y`
  (the implication (1) ⟹ (4)).

On a chart the comparison is Stacks 0ANV. Its forward half is
`hasPropertyOnAffineChartMap_tautTopologicallyOfFiniteType_of_isLocallyOfFiniteType`,
which needs no countability; its backward half,
`isLocallyOfFiniteType_of_hasPropertyOnAffineChartMap_tautTopologicallyOfFiniteType`,
rests on the implication (2) ⟹ (1) of Stacks 0ANT stated with condition (a) of Stacks 0ANU as
its hypothesis, `isFiniteType_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal`.

## Implementation notes

The library's equivalence of the four conditions of Stacks 0ANW,
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae'`, and its chart form of Stacks 0ANV,
`AlgebraicGeometry.FormalSpace.chartPropertyIsLocallyOfFiniteType`, are built on
`AlgebraicGeometry.FormalSpace.isFiniteType_formalSpectrumMap_of_isTaut`. The compiled module
of that declaration currently served by the build cache records `sorryAx` for it, although its
source contains none and recompiling the same source gives the three standard axioms. The
statements here reach the same mathematics without that compiled declaration: the 0ANT step
takes condition (a) of Stacks 0ANU as its hypothesis, which on a chart presented by rings of
`WAdm^{count}` Stacks 0ANU (`TopologicalRing.finiteType_tfae`) supplies, and the rest is
assembled from the pieces the library's equivalence uses.

## References

* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0ANV](https://stacks.math.columbia.edu/tag/0ANV)
* [Stacks Project, Tag 0ANW](https://stacks.math.columbia.edu/tag/0ANW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section FormalSpectrum

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **Stacks 0ANT, the implication (2) ⟹ (1), from condition (a) of Stacks 0ANU.** Let
`φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over `S` which
is taut and of finite type modulo every weak ideal of definition. Then
`Spf (φ) : Spf C ⟶ Spf A` is of finite type.

The base change of `Spf (φ)` along a point of `Spf A` out of an affine object of the site is an
affine morphism of finite type of the site
(`AlgebraicGeometry.FormalSpace.exists_isPullback_affineFiniteType_formalSpectrumMap_of_isAffine`),
and those two properties are Zariski local at the target, so the charts over the affine opens of
an arbitrary test object glue. -/
theorem isFiniteType_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hE : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E))
    (hmod : TopologicalRing.FiniteTypeModuloEveryWeakIdeal f.toRingHom) :
    IsFiniteType B S hS (formalSpectrumMap hA f) := by
  classical
  let L := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  have _ : FunctorToTypes.Small.{u} (formalSpectrum E).obj :=
    CartesianColimit.small_of_setTheoreticCondition B S hS _ hE.1
  have _ : MorphismProperty.RespectsIso
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u}) :=
    MorphismProperty.RespectsIso.inf _ _
  have _ : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hzlA : IsZariskiLocalAtTarget (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  have hzlT : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  -- The affine charts glue, being affine and of finite type over an affine open.
  have hrel : (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (formalSpectrumMap hA f) := by
    refine CartesianColimit.relative_of_affineBaseChanges B S hS _
      (MorphismProperty.IsLocalAtTarget.inf _ _) _ (κ := 0)
      (lt_of_lt_of_le Cardinal.aleph0_pos B.aleph0_lt_cutoff.le) fun U hU ξ => ?_
    obtain ⟨V, p, q, hq, hqa, hqt⟩ :=
      exists_isPullback_affineFiniteType_formalSpectrumMap_of_isAffine B S hS hA hC D E f
        hmod U hU ξ
    refine ⟨V, p, q, hq, ⟨hqa, hqt⟩, ?_⟩
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    have _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map q) := hqa
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
      isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map q)
    have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) := hqt
    exact (Scheme.size_le_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map q)).trans (le_max_right _ _)
  have hrel' := relative_ulift_of_relative_sheaf B S hS
    (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)) (formalSpectrumMap hA f) hrel
  refine ⟨isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable B S hS hrel'.rep,
    fun U ξ => ?_⟩
  obtain ⟨hqa, hqt⟩ := hrel'.property_snd ξ
  have hfst : (hrel'.rep.isPullback ξ).flip.isoPullback.hom ≫
      pullback.fst ξ (formalSpectrumMap hA f).hom = L.map (hrel'.rep.snd ξ) :=
    (hrel'.rep.isPullback ξ).flip.isoPullback_hom_fst
  have hinv : (hrel'.rep.isPullback ξ).flip.isoPullback.inv ≫ L.map (hrel'.rep.snd ξ) =
      pullback.fst ξ (formalSpectrumMap hA f).hom := (Iso.inv_comp_eq _).mpr hfst.symm
  refine ⟨?_, ?_⟩
  · have hlft : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
        (L.map (hrel'.rep.snd ξ)) :=
      Space.isLocallyOfFiniteTypeULift_uliftYoneda_map B S hS (hrel'.rep.snd ξ) hqt
    have h2 := Space.holdsOnEveryEtaleChartULift_precomp B S hS
      (@LocallyOfFiniteType.{u}) (hrel'.rep.isPullback ξ).flip.isoPullback.inv
      (L.map (hrel'.rep.snd ξ)) hlft
    rwa [hinv] at h2
  · have _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map (hrel'.rep.snd ξ)) := hqa
    have hqc : Space.IsQuasiCompactULift.{u + 1} B S hS (L.map (hrel'.rep.snd ξ)) :=
      Space.isQuasiCompactULift_uliftYoneda_map B S hS (hrel'.rep.snd ξ) inferInstance
    have h2 : Space.IsQuasiCompactULift.{u + 1} B S hS
        ((hrel'.rep.isPullback ξ).flip.isoPullback.inv ≫ L.map (hrel'.rep.snd ξ)) :=
      Space.isQuasiCompactULift_precomp B S hS
        (hrel'.rep.isPullback ξ).flip.isoPullback.symm (L.map (hrel'.rep.snd ξ)) hqc
    rwa [hinv] at h2

end FormalSpectrum

/-! ### Stacks 0ANV on affine charts, one direction at a time -/

/-- Composing a locally finite type map with isomorphisms on both sides keeps it locally of
finite type. -/
private theorem isLocallyOfFiniteType_iso_comp_comp {U U' V V' : FppfSheaf B S hS}
    (e : U ≅ U') (t : U' ⟶ V') (e' : V' ≅ V) (h : IsLocallyOfFiniteType B S hS t) :
    IsLocallyOfFiniteType B S hS (e.hom ≫ t ≫ e'.hom) :=
  IsLocallyOfFiniteType.comp B S hS e.hom (t ≫ e'.hom)
    (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS e.hom
      (isRepresentableEtale_of_isIso B S hS e.hom))
    (IsLocallyOfFiniteType.comp B S hS t e'.hom h
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS e'.hom
        (isRepresentableEtale_of_isIso B S hS e'.hom)))

/-- **Stacks 0ANV on affine charts, forward.** A map of affine formal algebraic spaces over `S`
which is locally of finite type has every morphism of `WAdm^{count}` presenting it taut and
topologically of finite type: the presenting formal spectrum map is locally of finite type,
hence of finite type (Stacks 0AKN), and Stacks 0AN5 with Stacks 0ANT reads off the ring
condition. -/
theorem hasPropertyOnAffineChartMap_tautTopologicallyOfFiniteType_of_isLocallyOfFiniteType
    {U V : FppfSheaf B S hS} (t : U ⟶ V) (hUaff : IsAffineFormalAlgebraicSpace B S hS U)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V) (hlft : IsLocallyOfFiniteType B S hS t) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.IsTautTopologicallyOfFiniteTypeHom t := by
  intro A R _ _ _ _ _ _ _ _ _ hCR hA D E eU eV g heq
  have hsrc : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) :=
    isAffineFormalAlgebraicSpace_of_iso B S hS eU hUaff
  have htgt : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
    isAffineFormalAlgebraicSpace_of_iso B S hS eV hVaff
  have hmap : IsLocallyOfFiniteType B S hS (formalSpectrumMap hA g) := by
    have hrw : formalSpectrumMap hA g = eU.inv ≫ t ≫ eV.hom := by
      rw [heq]; simp
    rw [hrw]
    exact isLocallyOfFiniteType_iso_comp_comp B S hS eU.symm t eV hlft
  exact isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap B S hS
    hA hCR.1 D E g htgt hsrc
    (IsLocallyOfFiniteType.isFiniteType_of_isAffineFormal B S hS _ hsrc htgt hmap)

/-- **Stacks 0ANV on countably indexed affine charts, backward.** A map of countably indexed
affine formal algebraic spaces over `S` whose presenting morphisms of `WAdm^{count}` are taut
and topologically of finite type is locally of finite type.

Both charts are formal spectra of rings of `WAdm^{count}` (Stacks 0AIK) and the map comes from
a continuous homomorphism (Stacks 0AN0); that homomorphism is of finite type modulo every weak
ideal of definition by Stacks 0ANU, and Stacks 0ANT makes its formal spectrum map of finite
type. -/
theorem isLocallyOfFiniteType_of_hasPropertyOnAffineChartMap_tautTopologicallyOfFiniteType
    {U V : FppfSheaf B S hS} (t : U ⟶ V) (hUaff : IsAffineFormalAlgebraicSpace B S hS U)
    (_hVaff : IsAffineFormalAlgebraicSpace B S hS V) (hUc : IsCountablyIndexed B S hS U)
    (hVc : IsCountablyIndexed B S hS V)
    (hchart : HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.IsTautTopologicallyOfFiniteTypeHom t) :
    IsLocallyOfFiniteType B S hS t := by
  obtain ⟨R, _, _, _, _, E, hR, hRc, ⟨eU⟩⟩ :=
    exists_quotientSystem_of_isCountablyIndexed B S hS hUc
  obtain ⟨A, _, _, _, _, D, hA, hAc, ⟨eV⟩⟩ :=
    exists_quotientSystem_of_isCountablyIndexed B S hS hVc
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hR
    (eU.inv ≫ t ≫ eV.hom)
  have hsrc : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) :=
    isAffineFormalAlgebraicSpace_of_iso B S hS eU hUaff
  have heq : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv := by
    rw [hg]; simp
  have hmod : TopologicalRing.FiniteTypeModuloEveryWeakIdeal g.toRingHom :=
    ((TopologicalRing.finiteType_tfae g.toRingHom g.continuous hA hR hAc hRc).out 3 1).mp
      (hchart A R ⟨hA, hAc⟩ ⟨hR, hRc⟩ hA D E eU eV g heq)
  have hft := isFiniteType_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal B S hS hA hR
    D E g hsrc hmod
  rw [heq]
  exact isLocallyOfFiniteType_iso_comp_comp B S hS eU (formalSpectrumMap hA g) eV.symm
    hft.isLocallyOfFiniteType

/-! ### Stacks 0ANW, one direction at a time -/

variable {B S hS}

/-- **Stacks 0ANW, the implication (4) ⟹ (1).** If a morphism `f : X ⟶ Y` of fppf sheaves over
`S` is locally of finite type, then every affine representable étale square over `f` has its
upper map given by taut, topologically of finite type morphisms of `WAdm^{count}`.

The upper map of such a square is locally of finite type by the implication (1) ⟹ (3) of
Stacks 0ANL, and Stacks 0ANV on charts reads off the ring condition. Neither step uses that `X`
and `Y` are locally countably indexed, which the source assumes throughout Stacks 0ANW. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_tautTopologicallyOfFiniteType_of_isLocallyOfFiniteType
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f := by
  intro U V a b t hU hV ha hb hsq
  exact hasPropertyOnAffineChartMap_tautTopologicallyOfFiniteType_of_isLocallyOfFiniteType
    B S hS t hU hV
    (isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType B S hS f hf U V a b t
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU)
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) ha hb hsq)

/-- **Stacks 0ANW, the implication (1) ⟹ (4).** Let `f : X ⟶ Y` be a morphism of locally
countably indexed formal algebraic spaces over `S`. If every affine representable étale square
over `f` has its upper map given by taut, topologically of finite type morphisms of
`WAdm^{count}`, then `f` is locally of finite type.

The chart condition holds in particular on the affine étale coverings of the fibre products of
the members of an affine étale covering of `Y` with `X` (condition (2), through Stacks 0AJ3);
those members are countably indexed by Stacks 0AKX, so Stacks 0ANV makes their maps locally of
finite type, and the implications (4) ⟹ (5) ⟹ (1) of Stacks 0ANL conclude. -/
theorem isLocallyOfFiniteType_of_hasPropertyOnEveryAffineEtaleDiagram_tautTopologicallyOfFiniteType
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (h : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f) :
    IsLocallyOfFiniteType B S hS f := by
  have h0AKX := isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS
  obtain ⟨J, V, v, hVcover, hinner⟩ := hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S
    hS TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f hY.1
    (fun _V v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v' f hY.1 hV' hX.1) h
  have h4 : IsLocallyOfFiniteTypeAfterTargetCover B S hS f := by
    refine ⟨J, V, v, hVcover, fun j ↦ ?_⟩
    obtain ⟨I, U, w, hUcover, hUproperty⟩ := hinner j
    refine ⟨I, U, w, hUcover, fun i ↦ ?_⟩
    have hsnd : IsRepresentableEtale B S hS (w i ≫ pullback.snd (v j) f) :=
      IsRepresentableEtale.comp B S hS (hUcover.2.1 i)
        (isRepresentableEtale_pullback_snd B S hS (v j) f (hVcover.2.1 j))
    exact isLocallyOfFiniteType_of_hasPropertyOnAffineChartMap_tautTopologicallyOfFiniteType B S
      hS (w i ≫ pullback.fst (v j) f) (hUcover.1 i) (hVcover.1 j)
      (h0AKX X hX (U i) (w i ≫ pullback.snd (v j) f) (hUcover.1 i) hsnd)
      (h0AKX Y hY (V j) (v j) (hVcover.1 j) (hVcover.2.1 j)) (hUproperty i)
  exact isLocallyOfFiniteType_of_onFactoredAtlas B S hS f hX.1 hY.1
    (isLocallyOfFiniteTypeOnFactoredAtlas_of_afterTargetCover' B S hS f h4)

end AlgebraicGeometry.FormalSpace

end
