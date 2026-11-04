module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessCompleteSite
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOpenDense
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Nodal
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange

/-!
# A prestable family of curves over a complete local ring is a family of schemes

Let `F` be a prestable family of curves (Stacks 0E6T) and `W = Spec Λ ⟶ S` a morphism from the
spectrum of a complete Noetherian local ring to its base. Then the base change `F ×_S W` is
represented by a scheme of the site ([Stacks, Tag 0AE7]): it is proper over `W`, and its closed
fibre, presented by a scheme as for every family of curves over a field, is a nodal curve, of
dimension one.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isPullback_schemeSpace_of_isAdicComplete`: the base change
  of a prestable family of curves to the spectrum of a complete Noetherian local ring is a scheme.

## References

* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **The fibre of a prestable family of curves over a field-valued point is a curve.** A scheme
presenting it is nonempty, at-worst-nodal over the field, and of dimension one. -/
theorem topologicalKrullDim_eq_one_of_isPullback_fieldValuedPoint {F : CurveFamily B hZ}
    (hF : IsPrestableCurveFamily B hZ F)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : schemeSpace V ⟶ F.total}
    (hsq : IsPullback q (schemeSpaceMap v) F.toBase (schemeSpaceMap p.value)) :
    topologicalKrullDim ((𝒯).obj V) = 1 := by
  have hnod : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ (yoneda.map v) :=
    (Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase hZ
      ).of_isPullback hsq hF.1
  have hnod' : IsAtWorstNodalOfRelativeDimensionOne ((𝒯).map v) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget v).1 hnod
  have hH0 := isIso_appTop_of_isPullback_fieldValuedPoint hF.2 hsq
  have : Nontrivial (CommRingCat.of p.carrier) := inferInstanceAs (Nontrivial p.carrier)
  have : Nonempty ((𝒯).obj V) :=
    Stacks.Models.nonempty_of_isIso_globalSections ((𝒯).map v)
  -- the fibre over the unique point of `Spec k`
  set s : Spec (.of p.carrier) := IsLocalRing.closedPoint p.carrier
  have := isIso_fromSpecResidueField_closedPoint p.carrier
  have hsq' : IsPullback (𝟙 ((𝒯).obj V))
      ((𝒯).map v ≫ inv ((Spec (.of p.carrier)).fromSpecResidueField s)) ((𝒯).map v)
      ((Spec (.of p.carrier)).fromSpecResidueField s) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact (Stacks.Models.hasAtWorstNodalSingularities_of_isPullback_fiber hnod' s hsq').1

/-- **The base change of a stable family of curves to the spectrum of a complete Noetherian
local ring is a scheme** ([Stacks, Tag 0AE7]). Let `F` be a stable family of curves and
`w : Spec Λ ⟶ S` a morphism of the site from the spectrum of a complete Noetherian local ring to
its base. Then there are a scheme `Q` of the site over `Spec Λ` and a cartesian square exhibiting
`Q` as `F ×_S Spec Λ`. -/
theorem exists_isPullback_schemeSpace_of_isAdicComplete (Λ : Type u) [CommRing Λ]
    [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    (hΛ : B.Contains (Spec (.of Λ))) {F : CurveFamily B hZ} (hF : IsStableCurveFamily B hZ F)
    (w : integerSiteObject B hZ hΛ ⟶ F.base) :
    ∃ (Q : BigFppfOver B integerBase hZ) (qQ : Q ⟶ integerSiteObject B hZ hΛ)
      (r : schemeSpace Q ⟶ F.total),
      IsPullback r (schemeSpaceMap qQ) F.toBase (schemeSpaceMap w) := by
  have sqP := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ F.toBase (schemeSpaceMap w)
  let yw : yoneda.obj (integerSiteObject B hZ hΛ) ⟶ (schemeSpace F.base).obj := yoneda.map w
  have sqP' : IsPullback (pullback.fst F.toBase.hom yw) (pullback.snd F.toBase.hom yw)
      F.toBase.hom yw :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ sqP
  have hpP : Space.IsProper B integerBase hZ (pullback.snd F.toBase.hom yw) :=
    (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback sqP F.proper
  -- the closed point of `Spec Λ` and the fibre of `F` there
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue Λ))) :=
    IsClosedImmersion.spec_of_surjective _ residue_surjective
  have hκ : B.Contains (Spec (.of (ResidueField Λ))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
      (Spec.map (CommRingCat.ofHom (residue Λ)))) hΛ
  let k : integerSiteObject B hZ hκ ⟶ integerSiteObject B hZ hΛ :=
    integerSiteMap B hZ hκ hΛ (Spec.map (CommRingCat.ofHom (residue Λ)))
  let pt : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj :=
    { carrier := ResidueField Λ
      contained := hκ
      toBase := specULiftZIsTerminal.from _
      value := k ≫ w }
  let k' : pt.siteObject ⟶ integerSiteObject B hZ hΛ := k
  obtain ⟨V, v, q₀, hq₀, -⟩ := hF.2 pt
  have hval : yonedaEquiv.symm pt.value = yoneda.map pt.value :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm
  rw [hval] at hq₀
  have hsq₀ : IsPullback (ObjectProperty.homMk q₀ : schemeSpace V ⟶ F.total)
      (schemeSpaceMap v) F.toBase (schemeSpaceMap pt.value) :=
    IsPullback.of_map (ObjectProperty.ι _) ((ObjectProperty.ι _).map_injective hq₀.w) hq₀
  have hdim := topologicalKrullDim_eq_one_of_isPullback_fieldValuedPoint hF.1 hsq₀
  have hq₀' : IsPullback q₀ (yoneda.map v) F.toBase.hom (yoneda.map k' ≫ yw) := by
    rw [show yoneda.map k' ≫ yw = yoneda.map pt.value from (Functor.map_comp yoneda k' w).symm]
    exact hq₀
  let i : yoneda.obj V ⟶ pullback F.toBase.hom yw :=
    sqP'.lift q₀ (yoneda.map v ≫ yoneda.map k') hq₀'.w
  have hi : IsPullback i (yoneda.map v) (pullback.snd F.toBase.hom yw) (yoneda.map k') :=
    IsPullback.of_right (by rw [sqP'.lift_fst]; exact hq₀') (sqP'.lift_snd _ _ _) sqP'
  -- Stacks 0AE7
  obtain ⟨Q, qQ, e, he⟩ := Space.exists_iso_yoneda_of_isProper_of_closedFibre B integerBase hZ Λ
    (integerSiteObject B hZ hΛ) (Iso.refl _)
    (AlgebraicSpaces.fiberProduct B integerBase hZ F.toBase (schemeSpaceMap w)).property
    (pullback.snd F.toBase.hom yw) hpP k' (Iso.refl _) (by simp; rfl) v i hi hdim.le
  have hsq : IsPullback (e.hom ≫ pullback.fst F.toBase.hom yw) (yoneda.map qQ)
      F.toBase.hom yw := by
    have h₁ : IsPullback e.hom (yoneda.map qQ) (pullback.snd F.toBase.hom yw)
        (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
    have := h₁.paste_horiz sqP'
    rwa [Category.id_comp] at this
  refine ⟨Q, qQ, ObjectProperty.homMk (e.hom ≫ pullback.fst F.toBase.hom yw), ?_⟩
  exact IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.w) hsq

end AlgebraicGeometry.CurveFamily

end
