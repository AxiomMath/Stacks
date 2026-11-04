module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsChartMaps

/-!
# Finite type on reductions: invariance and the characterisation of Stacks 0GC7

Being locally of finite type on reductions is invariant under conjugation by isomorphisms, can be
checked on any one pair of reductions, and on formal spectra is the property of Stacks 0GC2 of
the ring map. For locally countably indexed formal algebraic spaces it is equivalent to the chart
conditions of Stacks 0ANG for that property, given its ascent and descent along affine étale maps.

## Main results

* `isLocallyOfFiniteTypeOnReductions_conj`: Being locally of finite type on reductions is
  invariant under conjugation by isomorphisms of the source and the target.
* `isLocallyOfFiniteTypeOnReductions_iff_isLocallyOfFiniteTypeULift`: A morphism is locally of
  finite type on reductions iff the morphism of any one pair of reductions is locally of finite
  type.
* `isLocallyOfFiniteTypeOnReductions_formalSpectrumMap_iff_of_hasLargeSite`: `Spf (φ)` is locally
  of finite type on reductions iff `φ` is of finite type on reductions.
* `isLocallyOfFiniteTypeOnReductions_tfae_of_chartAscentDescent`: The four conditions of
  Stacks 0GC7 are equivalent, given the ascent and descent of the chart property.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

universe u

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being locally of finite type on reductions, condition (4) of Stacks 0GC7, is invariant under
conjugating the morphism by isomorphisms of its source and of its target. -/
theorem isLocallyOfFiniteTypeOnReductions_conj {X Y X' Y' : FppfSheaf B S hS}
    (eX : X' ≅ X) (eY : Y' ≅ Y) {f : X ⟶ Y}
    (h : IsLocallyOfFiniteTypeOnReductions B S hS f) :
    IsLocallyOfFiniteTypeOnReductions B S hS (eX.hom ≫ f ≫ eY.inv) := by
  intro Xred Yred iX iY hiX hiY fred hfred
  refine h Xred Yred (iX ≫ eX.hom) (iY ≫ eY.hom)
    (IsReduction.comp_iso B S hS hiX eX) (IsReduction.comp_iso B S hS hiY eY)
    fred ?_
  rw [← Category.assoc, hfred]
  simp

/-- **Condition (4) of Stacks 0GC7 is a condition on any one pair of reductions.** Let
`f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S`, let `iX : Xred ⟶ X` and
`iY : Yred ⟶ Y` be reductions and let `fred : Xred ⟶ Yred` be compatible with `f`. Then `f` is
locally of finite type on reductions exactly when `fred` is a morphism of algebraic spaces
locally of finite type. -/
theorem isLocallyOfFiniteTypeOnReductions_iff_isLocallyOfFiniteTypeULift
    {X Y Xred Yred : FppfSheaf B S hS} {iX : Xred ⟶ X} {iY : Yred ⟶ Y}
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    {f : X ⟶ Y} {fred : Xred ⟶ Yred} (hfred : fred ≫ iY = iX ≫ f) :
    IsLocallyOfFiniteTypeOnReductions B S hS f ↔
      Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS fred.hom := by
  refine ⟨fun h ↦ h Xred Yred iX iY hiX hiY fred hfred,
    fun h Xred' Yred' iX' iY' hiX' hiY' fred' hfred' ↦ ?_⟩
  obtain ⟨a, ha, -⟩ := hiX.universal Xred' hiX'.algebraic hiX'.reduced iX'
  obtain ⟨b, hb, -⟩ := hiY.universal Yred' hiY'.algebraic hiY'.reduced iY'
  have _ : IsIso a := IsReduction.isIso_of_comp_eq B S hS hiX' hiX ha
  have _ : IsIso b := IsReduction.isIso_of_comp_eq B S hS hiY' hiY hb
  have _ : Mono iY := mono_of_isRepresentableThickening B S hS iY hiY.isRepresentableThickening
  have hsq : a ≫ fred = fred' ≫ b := (cancel_mono iY).1 <| by
    rw [Category.assoc, Category.assoc, hfred, hb, hfred', ← Category.assoc, ha]
  obtain rfl : fred' = a ≫ fred ≫ inv b := by
    rw [← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have _ : IsIso a.hom := (sheafToPresheaf _ _).map_isIso a
  have _ : IsIso (inv b).hom := (sheafToPresheaf _ _).map_isIso (inv b)
  exact Space.holdsOnEveryEtaleChartULift_precomp B S hS _ a.hom _
    (Space.holdsOnEveryEtaleChartULift_postcomp B S hS _ (inv b).hom _ h)

section Affine

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **Finite type on reductions for a morphism of formal spectra.** Let `φ : A ⟶ C`
be a continuous homomorphism of weakly admissible topological rings over `S`, with both quotient
systems in a large enough site. Then `Spf (φ) : Spf C ⟶ Spf A` is locally of finite type on
reductions exactly when `φ` has the property of Stacks 0GC2, that the induced map
`A ⧸ 𝔞 ⟶ C ⧸ 𝔠` of the quotients by the ideals of topologically nilpotent elements be of finite
type. -/
theorem isLocallyOfFiniteTypeOnReductions_formalSpectrumMap_iff_of_hasLargeSite
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (hBD : D.HasLargeSite) (hBE : E.HasLargeSite) (g : ContinuousHom D E) :
    IsLocallyOfFiniteTypeOnReductions B S hS (formalSpectrumMap hA g) ↔
      Rig.IsFiniteTypeOnReductions g.toRingHom g.continuous := by
  have hle : (TopologicalRing.nilIdx hA.1).1 ≤
      Ideal.comap g.toRingHom (TopologicalRing.nilIdx hC.1).1 :=
    TopologicalRing.topologicalNilradical_le_comap g.toRingHom g.continuous
  have hsq : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map
          (g.stageMap (TopologicalRing.nilIdx hA.1) (TopologicalRing.nilIdx hC.1) hle)) ≫
        formalSpectrumInclusion D (OrderDual.toDual (TopologicalRing.nilIdx hA.1)) =
      formalSpectrumInclusion E (OrderDual.toDual (TopologicalRing.nilIdx hC.1)) ≫
        formalSpectrumMap hA g :=
    (formalSpectrumMap_spec hA g (TopologicalRing.nilIdx hA.1)
      (TopologicalRing.nilIdx hC.1) hle).symm
  refine (isLocallyOfFiniteTypeOnReductions_iff_isLocallyOfFiniteTypeULift B S hS
      (isReduction_formalSpectrum hC E hBE) (isReduction_formalSpectrum hA D hBD) hsq).trans
    ((isLocallyOfFiniteTypeULift_sheafifiedYoneda_map_iff B S hS
      ((BigAffineFppf.inclusion B S hS).map
        (g.stageMap (TopologicalRing.nilIdx hA.1) (TopologicalRing.nilIdx hC.1) hle))).trans ?_)
  exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)

end Affine

variable {B S hS}

/-- **Stacks 0GC7.** For a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic
spaces over `S`, the condition that every affine representable étale square over `f` carry an
arrow of `WAdm^{count}` with the property of Stacks 0GC2, the existence of an affine étale
covering of `Y` together with affine étale coverings of the fibre products of its members with
`X` on which that condition holds, the existence of an affine étale covering of `X` whose
members factor through affine representable étale charts of `Y` by such arrows, and the morphism
of reductions `f_red` being locally of finite type, are all equivalent. The first three are the
three conditions of Stacks 0ANG for the class of countably indexed weakly admissible topological
rings and the property of Stacks 0GC2. -/
theorem isLocallyOfFiniteTypeOnReductions_tfae_of_chartAscentDescent {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty)
    (href : HasEtaleRefinementOfSourceCover B S hS f)
    (hredsquare : IsLocallyOfFiniteTypeOnReductionsOnEveryAffineEtaleSquare B S hS)
    (hredcover : IsLocallyOfFiniteTypeOnReductionsOfTargetCover B S hS) :
    List.TFAE
      [HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        IsLocallyOfFiniteTypeOnReductions B S hS f] := by
  have h0AKX : ∀ (Z : FppfSheaf B S hS), IsLocallyCountablyIndexed B S hS Z →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U := fun Z hZ ↦
    (hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed B S hS Z
      hZ.1).2 hZ.2
  have hbridge : ChartPropertyIsFiniteTypeOnReductions B S hS :=
    chartPropertyIsFiniteTypeOnReductions B S hS
  tfae_have 1 → 2 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f hY.1 (fun _V v _hV hv ↦
      isFormalAlgebraicSpace_pullback_of_isRepresentableEtale B S hS v f hX.1 hv) h
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f h
  tfae_have 3 → 1 := fun h ↦ hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f hasc hdesc href h
  tfae_have 2 → 4 := by
    rintro ⟨J, V, v, hVcover, hinner⟩
    refine hredcover f ⟨J, V, v, hVcover, fun j ↦ ?_⟩
    obtain ⟨I, U, w, hUcover, hUproperty⟩ := hinner j
    refine ⟨I, U, w, hUcover, fun i ↦ ?_⟩
    have hsnd : IsRepresentableEtale B S hS (w i ≫ pullback.snd (v j) f) :=
      IsRepresentableEtale.comp B S hS (hUcover.2.1 i)
        (isRepresentableEtale_pullback_snd B S hS (v j) f (hVcover.2.1 j))
    exact (hbridge (w i ≫ pullback.fst (v j) f) (hUcover.1 i) (hVcover.1 j)
      (h0AKX X hX (U i) (w i ≫ pullback.snd (v j) f) (hUcover.1 i) hsnd)
      (h0AKX Y hY (V j) (v j) (hVcover.1 j) (hVcover.2.1 j))).2 (hUproperty i)
  tfae_have 4 → 1 := by
    intro hf U V a b t hU hV ha hb hsq
    exact (hbridge t hU hV (h0AKX X hX U a hU ha) (h0AKX Y hY V b hV hb)).1
      (hredsquare f a b t hU hV ha hb hsq hf)
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
