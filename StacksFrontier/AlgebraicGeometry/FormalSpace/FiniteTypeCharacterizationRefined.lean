module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeAllPoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentabilityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertyClassClosure
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocalRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagram

/-!
# Finite type morphisms of formal algebraic spaces on affine charts

A morphism of locally countably indexed formal algebraic spaces is locally of finite type
exactly when the continuous homomorphisms of countably indexed weakly admissible topological
rings presenting it on affine étale charts are taut and topologically of finite type.

## Main results

* `chartPropertyAscendsAlongAffineEtale_tautTopologicallyOfFiniteType`: being taut and
  topologically of finite type ascends along affine étale maps of charts.
* `chartPropertyDescendsAlongFiniteAffineEtaleCover_tautTopologicallyOfFiniteType`: being taut
  and topologically of finite type descends along finite affine étale coverings of charts.
* `chartPropertyIsLocallyOfFiniteType`: a map of countably indexed affine formal algebraic
  spaces is locally of finite type exactly when every presenting morphism of `WAdm^{count}` is
  taut and topologically of finite type.
* The equivalent characterisations of finite type for a morphism of affine formal algebraic
  spaces, Stacks 0ANV, are
  `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae_of_isAffineFormalAlgebraicSpace`.
* `isLocallyOfFiniteType_tfae'`: the equivalent characterisations of being locally of finite
  type for a morphism of locally countably indexed formal algebraic spaces.

## Implementation notes

These are the strengthened and newly added declarations belonging with
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterization`. A declaration of that
module whose statement was strengthened keeps its original statement there; its strengthened
form lives here under a primed name.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The locality axioms of Situation 0CBA for tautness and topological finite type -/

/-- **Axiom (1) of Situation 0CBA for tautness together with being topologically of finite
type, read on affine formal algebraic spaces.** The property ascends along affine étale maps of
charts.

The property is local on `WAdm^{count}` by Stacks 0ANU, and `WAdm^{count}` is closed under the
completion of Stacks 0AN6 by Stacks 0ANB; those are the two inputs of
`hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap`. -/
theorem chartPropertyAscendsAlongAffineEtale_tautTopologicallyOfFiniteType :
    ChartPropertyAscendsAlongAffineEtale' B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.IsTautTopologicallyOfFiniteTypeHom :=
  fun _ _ _ _ _ _ _ _ _ _ _ hloc ht ↦
    hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap B S hS _ _
      TopologicalRing.topologicallyFiniteType_propertyIsLocal'.{u}.toPropertyIsLocal
      TopologicalRing.topologicallyFiniteType_propertyIsLocal'.{u}.isomorphismInvariant
      (fun φ _ _ hC ↦ TopologicalRing.isCountablyWeaklyAdmissible_completionOver φ hC) hloc ht

/-- **Axioms (2) and (3) of Situation 0CBA for tautness together with being topologically of
finite type, read on affine formal algebraic spaces.** The property descends along finite
affine étale coverings of charts.

The three inputs of `hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap` are
the locality of Stacks 0ANU, membership of `WAdm^{count}` — which for this class is its own
definition — and the closure of `WAdm^{count}` under the completion of Stacks 0AN6 by Stacks
0ANB. -/
theorem chartPropertyDescendsAlongFiniteAffineEtaleCover_tautTopologicallyOfFiniteType :
    ChartPropertyDescendsAlongFiniteAffineEtaleCover' B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.IsTautTopologicallyOfFiniteTypeHom :=
  fun t _ _ _ _ W Z _ m _ _ _ _ _ hcover hPm ↦
    hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap B S hS _ _
      TopologicalRing.topologicallyFiniteType_propertyIsLocal'.{u}.toPropertyIsLocal
      TopologicalRing.topologicallyFiniteType_propertyIsLocal'.{u}.isomorphismInvariant
      (fun _ _ _ _ _ hC ↦ hC)
      (fun φ _ _ hC ↦ TopologicalRing.isCountablyWeaklyAdmissible_completionOver φ hC)
      t W Z m hcover hPm

/-! ### Stacks 0ANV on countably indexed affine charts -/

/-- A map of countably indexed affine formal algebraic spaces over `S` is locally of finite
type exactly when every morphism of `WAdm^{count}` presenting it is taut and topologically of
finite type.

A countably indexed affine formal algebraic space is the formal spectrum of a weakly admissible
topological ring with a countable fundamental system of neighbourhoods of zero — item (6) of
Stacks 0AIK — and a map of formal spectra comes from a unique continuous homomorphism by Stacks
0AN0, so the chart condition is never vacuous here and both directions are the corresponding
implications of Stacks 0ANV for that homomorphism. The implication out of being locally of
finite type is Stacks 0AN5 (1) ⟹ (3) for tautness together with the implication (1) ⟹ (2) of
Stacks 0ANT, the two being combined in
`isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap` once Stacks 0AKN has
upgraded locally of finite type to of finite type; the implication back is the implication
(2) ⟹ (1) of Stacks 0ANT, `isFiniteType_formalSpectrumMap_of_isTaut`. Being locally of finite
type is carried across the two comparison isomorphisms by Stacks 0AQ4, an isomorphism being
representable étale. -/
@[stacks 0ANV "the equivalence, read on countably indexed affine charts rather than on formal \
spectra: a map of countably indexed affine formal algebraic spaces over `S` is locally of \
finite type exactly when every morphism of `WAdm^{count}` presenting it is taut and \
topologically of finite type"]
theorem chartPropertyIsLocallyOfFiniteType :
    ChartPropertyIsLocallyOfFiniteType B S hS := by
  intro U V t hUaff hVaff hUc hVc
  constructor
  · intro hlft A R _ _ _ _ _ _ _ _ _ hCR hA D E eU eV g heq
    have hsrc : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) :=
      isAffineFormalAlgebraicSpace_of_iso B S hS eU hUaff
    have htgt : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
      isAffineFormalAlgebraicSpace_of_iso B S hS eV hVaff
    have hmap : IsLocallyOfFiniteType B S hS (formalSpectrumMap hA g) := by
      have hrw : formalSpectrumMap hA g = eU.inv ≫ t ≫ eV.hom := by
        rw [heq]
        simp
      rw [hrw]
      exact IsLocallyOfFiniteType.comp B S hS eU.inv (t ≫ eV.hom)
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eU.inv
          (isRepresentableEtale_of_isIso B S hS eU.inv))
        (IsLocallyOfFiniteType.comp B S hS t eV.hom hlft
          (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eV.hom
            (isRepresentableEtale_of_isIso B S hS eV.hom)))
    exact isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap B S hS
      hA hCR.1 D E g htgt hsrc
      (IsLocallyOfFiniteType.isFiniteType_of_isAffineFormal B S hS _ hsrc htgt hmap)
  · intro hchart
    obtain ⟨R, _, _, _, _, E, hR, hRc, ⟨eU⟩⟩ :=
      exists_quotientSystem_of_isCountablyIndexed B S hS hUc
    obtain ⟨A, _, _, _, _, D, hA, hAc, ⟨eV⟩⟩ :=
      exists_quotientSystem_of_isCountablyIndexed B S hS hVc
    obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hR
      (eU.inv ≫ t ≫ eV.hom)
    have heq : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv := by
      rw [hg]
      simp
    obtain ⟨htaut, hfin⟩ := hchart A R ⟨hA, hAc⟩ ⟨hR, hRc⟩ hA D E eU eV g heq
    rw [heq]
    exact IsLocallyOfFiniteType.comp B S hS eU.hom (formalSpectrumMap hA g ≫ eV.inv)
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eU.hom
        (isRepresentableEtale_of_isIso B S hS eU.hom))
      (IsLocallyOfFiniteType.comp B S hS (formalSpectrumMap hA g) eV.inv
        (isFiniteType_formalSpectrumMap_of_isTaut B S hS hA hR D E g
          (isAffineFormalAlgebraicSpace_of_iso B S hS eU hUaff) htaut hfin).isLocallyOfFiniteType
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eV.inv
          (isRepresentableEtale_of_isIso B S hS eV.inv)))

/-! ### Stacks 0ANV -/

variable {B S hS}

/-! ### Stacks 0ANW -/

/-- For a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic spaces over `S`,
the condition that every affine representable étale square over `f` carry a taut, topologically
of finite type morphism of `WAdm^{count}`, the existence of an affine étale covering of `Y`
together with affine étale coverings of the fibre products of its members with `X` on which
that condition holds, the existence of an affine étale covering of `X` whose members factor
through affine representable étale charts of `Y` by such morphisms, and `f` being locally of
finite type, are all equivalent.

The first three are the three conditions of Stacks 0ANG for the class of countably indexed
weakly admissible topological rings and the property of being taut and topologically of finite
type, which Stacks 0ANU makes a local property of such arrows; the comparison with the fourth is
Stacks 0ANV on charts together with the implications (1) ⟹ (3) and (4) ⟹ (5) ⟹ (1) of Stacks
0ANL. -/
@[stacks 0ANW "the equivalence of its four conditions, at the source's own hypotheses. The \
presented refinement of a covering of the source is the library's \
`hasEtaleRefinementOfSourceCover_isCountablyWeaklyAdmissible` (Stacks 0AJ2, \
quasi-compactness of an affine formal algebraic space and Stacks 0AN8) and the implication \
(2) \u27f9 (1) of Stacks 0AKX is the library's \
`isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed`"]
theorem isLocallyOfFiniteType_tfae' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y) :
    List.TFAE
      [HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f,
        IsLocallyOfFiniteType B S hS f] := by
  have h0AKX := isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS
  tfae_have 1 → 2 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f hY.1
    (fun _V v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v' f hY.1 hV' hX.1) h
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f h
  tfae_have 3 → 1 := fun h ↦ hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover' B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f hX hY
    (chartPropertyAscendsAlongAffineEtale_tautTopologicallyOfFiniteType B S hS)
    (chartPropertyDescendsAlongFiniteAffineEtaleCover_tautTopologicallyOfFiniteType B S hS)
    (hasEtaleRefinementOfSourceCover_isCountablyWeaklyAdmissible B S hS f) h
  tfae_have 2 → 4 := by
    rintro ⟨J, V, v, hVcover, hinner⟩
    have h4 : IsLocallyOfFiniteTypeAfterTargetCover B S hS f := by
      refine ⟨J, V, v, hVcover, fun j ↦ ?_⟩
      obtain ⟨I, U, w, hUcover, hUproperty⟩ := hinner j
      refine ⟨I, U, w, hUcover, fun i ↦ ?_⟩
      have hsnd : IsRepresentableEtale B S hS (w i ≫ pullback.snd (v j) f) :=
        IsRepresentableEtale.comp B S hS (hUcover.2.1 i)
          (isRepresentableEtale_pullback_snd B S hS (v j) f (hVcover.2.1 j))
      exact (chartPropertyIsLocallyOfFiniteType B S hS
        (w i ≫ pullback.fst (v j) f) (hUcover.1 i) (hVcover.1 j)
        (h0AKX X hX (U i) (w i ≫ pullback.snd (v j) f) (hUcover.1 i) hsnd)
        (h0AKX Y hY (V j) (v j) (hVcover.1 j) (hVcover.2.1 j))).2 (hUproperty i)
    exact isLocallyOfFiniteType_of_onFactoredAtlas B S hS f hX.1 hY.1
      (isLocallyOfFiniteTypeOnFactoredAtlas_of_afterTargetCover' B S hS f h4)
  tfae_have 4 → 1 := fun hf U V a b t hU hV ha hb hsq ↦
    (chartPropertyIsLocallyOfFiniteType B S hS t hU hV
      (h0AKX X hX U a hU ha) (h0AKX Y hY V b hV hb)).1
      (isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType B S hS f hf U V a b t
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU)
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) ha hb hsq)
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
