module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationDescent
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenCharts
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci

/-!
# Existence of the stabilization from local stabilizations

Let `X ⟶ S` be a prestable family of curves whose fibres have genus `g ≥ 2`. Suppose given an
étale covering `{φᵢ : Wᵢ ⟶ S}` of `S` by schemes of the site such that every field-valued point
of `S` lifts, over the same field, to some `Wᵢ` (as for the covering by the elementary étale
neighbourhoods of Stacks 0E7C), and on each `Wᵢ` a stable family of curves `Yᵢ` with a morphism
`cᵢ : X ×_S Wᵢ ⟶ Yᵢ` over `Wᵢ` satisfying conditions (1) and (2) of Stacks 0E8A. Then there is a
stable family `Y ⟶ S` with a morphism `c : X ⟶ Y` over `S` satisfying (1) and (2).

This is the gluing step in the proof of Stacks 0E8A: the `Yᵢ` glue by the uniqueness of the
stabilization over the overlaps
(`AlgebraicGeometry.CurveFamily.exists_glued_of_hasStableContractionFibres`), the glued space is a
family of curves (`AlgebraicGeometry.CurveFamily.ofIsFppfCovering`), condition (1) is étale local
on the base (`AlgebraicGeometry.CurveFamily.isUniversalStructureContraction_of_etale`), the glued
family is prestable (at-worst-nodal by descent of an open condition, Stacks 0E0E; `f_*𝒪 = 𝒪`
universally along the universal structure contraction), it is stable and condition (2) holds
because every field-valued point lifts to a member of the covering over the same field
(`AlgebraicGeometry.CurveFamily.isStableCurveFamily_of_forall_fieldValuedPoint_eq_map`).

## Main statements

* `AlgebraicGeometry.CurveFamily.exists_stabilization_of_etale`: the stabilization of `X` from
  local stabilizations over an étale covering.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- A field-valued point of `S` which is the image of one of `W` along `φ` is the image of one of
`W'` along `W' = W ⟶ S`. -/
theorem exists_map_eqToHom_comp_eq {W W' S : BigFppfOver B integerBase hZ} (h : W' = W)
    (φ : W ⟶ S) (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace S).obj)
    (p' : Space.FieldValuedPoint B integerBase hZ (schemeSpace W).obj)
    (hp : Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ).hom p' = p) :
    ∃ p'' : Space.FieldValuedPoint B integerBase hZ (schemeSpace W').obj,
      Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap (eqToHom h ≫ φ)).hom p'' =
        p := by
  subst h
  exact ⟨p', by simpa only [eqToHom_refl, Category.id_comp] using hp⟩

/-- **The stabilization from local stabilizations.** Let `X ⟶ S` be a prestable family of curves
with fibres of genus `g ≥ 2`, `{φᵢ : Wᵢ ⟶ S}` an étale covering of `S` by schemes of the site
through which every field-valued point of `S` lifts over the same field, and `cᵢ : X ×_S Wᵢ ⟶ Yᵢ`
morphisms over `Wᵢ` to stable families of curves satisfying conditions (1) and (2) of
Stacks 0E8A. Then there are a stable family of curves `Y` over `S` and a morphism `c : X ⟶ Y`
over `S` satisfying conditions (1) and (2) of Stacks 0E8A. -/
theorem exists_stabilization_of_etale
    {X : CurveFamily B hZ} (hX : IsPrestableCurveFamily B hZ X) {g : ℕ} (hg : 2 ≤ g)
    (hgen : X.HasFibresOfGenus g) {ι : Type u} {W : ι → BigFppfOver B integerBase hZ}
    (φ : ∀ i, W i ⟶ X.base) (hφ : ∀ i, Etale ((𝒯).map (φ i)))
    (hsurj : ∀ x : (𝒯).obj X.base, ∃ i, x ∈ Set.range ((𝒯).map (φ i)))
    (hlift : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      ∃ i, ∃ p' : Space.FieldValuedPoint B integerBase hZ (schemeSpace (W i)).obj,
        Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap (φ i)).hom p' = p)
    {Y : ι → CurveFamily B hZ} (hY : ∀ i, (Y i).base = W i)
    (hYst : ∀ i, IsStableCurveFamily B hZ (Y i))
    (c : ∀ i, AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)) ⟶
      (Y i).total)
    (hc : ∀ i, c i ≫ (Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i)) =
      ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (φ i)).hom))
    (h1 : ∀ i, (X.baseChangeAlong (φ i)).IsUniversalStructureContraction B hZ (Y i) (hY i) (c i))
    (h2 : ∀ i, (X.baseChangeAlong (φ i)).HasStableContractionFibres B hZ (Y i) (hY i) (c i)) :
    ∃ (Y' : CurveFamily B hZ) (hb : Y'.base = X.base) (c' : X.total ⟶ Y'.total),
      IsStableCurveFamily B hZ Y' ∧
      c' ≫ Y'.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase ∧
      X.IsUniversalStructureContraction B hZ Y' hb c' ∧
      X.HasStableContractionFibres B hZ Y' hb c' := by
  have hcov : Space.IsFppfCovering B integerBase hZ (fun i => (schemeSpace (W i)).obj)
      (fun i => (schemeSpaceMap (φ i)).hom) :=
    Space.isFppfCovering_of_isEtaleCovering B integerBase hZ
      (Space.isEtaleCovering_yoneda_of_etale B integerBase hZ W φ hφ fun x => by
        obtain ⟨i, y, hy⟩ := hsurj x
        exact ⟨i, y, hy⟩)
  obtain ⟨Q, q, r, cQ, hsq, hcQq, hcQ⟩ :=
    exists_glued_of_hasStableContractionFibres hX hg hgen φ hcov hY c hc h1 h2
  let Y' := ofIsFppfCovering q φ hcov hY r hsq
  have hsq' : ∀ i, IsPullback (r i) ((Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i)))
      (Y'.toBase ≫ eqToHom (congrArg schemeSpace (rfl : Y'.base = X.base)))
      (schemeSpaceMap (φ i)) := fun i => by
    simpa using hsq i
  have h1' : X.IsUniversalStructureContraction B hZ Y' rfl cQ :=
    isUniversalStructureContraction_of_etale φ hφ hsurj
      fun i T t X' Y'' pX' fX' pY' fY' c' sqX sqY hcY hcf =>
        isStructureContraction_of_isUniversalStructureContraction_baseChangeAlong (X := X)
          (Y := Y') (hb := rfl) (c := cQ) (φ i) (hsq' i) (hc i) (hcQ i) (h1 i) T t X' Y''
          pX' fX' pY' fY' c' sqX sqY hcY hcf
  have hcQ' : cQ ≫ Y'.toBase ≫ eqToHom (congrArg schemeSpace (rfl : Y'.base = X.base)) =
      X.toBase := by
    simpa using hcQq
  -- the glued family is prestable: at-worst-nodal by descent of an open condition, and
  -- `f_*𝒪 = 𝒪` universally from that of `X` along the universal structure contraction `cQ`
  have hnod : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ Y'.toBase.hom :=
    IsOpenCurvesLocus.prop_ofIsFppfCovering (isOpenCurvesLocus_isAtWorstNodal B hZ) q φ hcov hY
      r hsq fun i => (hYst i).1.1
  have hH0 : HasUniversallyBijectiveGlobalFunctions B hZ Y' :=
    hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp_baseChange (X := X) rfl cQ hcQ'
      (fun T t X' Y'' pX' fX' pY' fY' c' a b e₁ e₂ =>
        (h1' T t X' Y'' pX' fX' pY' fY' c' a b e₁ e₂).1) hX.2
  -- it is stable, as every field-valued point of the base lifts to a stable member
  have hst : IsStableCurveFamily B hZ Y' := by
    refine isStableCurveFamily_of_forall_fieldValuedPoint_eq_map ⟨hnod, hH0⟩
      (fun i => (⟨eqToHom (hY i) ≫ φ i, r i,
        (Y i).isPullback_toBase_of_isPullback_comp_eqToHom (hY i) (hsq i)⟩ : Y i ⟶ Y'))
      hYst fun p => ?_
    obtain ⟨i, p', hp'⟩ := hlift p
    exact ⟨i, exists_map_eqToHom_comp_eq (hY i) (φ i) p p' hp'⟩
  exact ⟨Y', rfl, cQ, hst, hcQ', h1',
    hasStableContractionFibres_ofIsFppfCovering q φ hcov hlift hY r hsq c hc h2 cQ hcQ⟩

end CurveFamily

end AlgebraicGeometry

end
