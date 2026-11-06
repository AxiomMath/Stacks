module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.DescendingProperties.SeparatedDescentSiteConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Limits.DescendingMorphismPropertiesSiteConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.BaseChangeLimitsConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionRelocalize
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentBounded

namespace AlgebraicGeometry.BigFppfOver.LimitInSite.C1573
end AlgebraicGeometry.BigFppfOver.LimitInSite.C1573
namespace AlgebraicGeometry.Space.DescentSituation.C1573
end AlgebraicGeometry.Space.DescentSituation.C1573

/-!
# Separatedness descends to a stage, under the chapter's convention

Stacks 084T, 086X and 0851 are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/SeparatedDescent.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/SeparatedMorphismDescent.lean` for
inverse systems small for the site. Here they are proved under the chapter's standing convention
of Section 70.2 (tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, which is what
the systems of Stacks 07SU satisfy.

## Main results

* `AlgebraicGeometry.BigFppfOver.LimitInSite.C1573.comp_prodFunctor_obj`: the convention for a
  diagram passes to its products with a fixed object.
* Stacks 084T, in the namespace `AlgebraicGeometry.Space.DescentSituation.C1573`:
  `exists_isAbsolutelySeparated_system_obj_of_siteContainsBaseChangeLimits`.
* Stacks 086X, in the namespace `AlgebraicGeometry.Space.DescentSituation.C1573`:
  `exists_isSeparated_system_app_of_siteContainsBaseChangeLimits`.
* Stacks 0851, in the namespace `AlgebraicGeometry.Space.MorphismDescentSituation`:
  `exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits`, stated in the imported module
  `StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDiagonalDescent`.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 084T](https://stacks.math.columbia.edu/tag/084T)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_SeparatedDescentConvention
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The convention passes to products with a fixed object.** If the limit of the underlying
schemes of a cofiltered diagram `V` of affine objects of the site lies in the site, so does the
limit of the products `Z × V j`. -/
theorem BigFppfOver.LimitInSite.C1573.comp_prodFunctor_obj {K : Type u} [Category.{u} K]
    [IsCofiltered K] {V : K ⥤ BigFppfOver B S hS}
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hL : BigFppfOver.LimitInSite V) (Z : BigFppfOver B S hS) :
    BigFppfOver.LimitInSite (V ⋙ prod.functor.obj Z) := by
  intro c hc
  have : ∀ j, IsAffine ((underlyingDiagram V).obj j) := hV
  have := CofilteredLimit.hasLimit_of_isAffine (underlyingDiagram V)
  have hLc : B.Contains (limit (underlyingDiagram V)) :=
    hL _ (limit.isLimit (underlyingDiagram V))
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := K)
  have hT : IsTerminal (Over.mk (𝟙 (B.obj hS))) := Over.mkIdTerminal
  have hpb : ∀ j, IsPullback ((BigFppfOver.toScheme B S hS).map (prod.fst : Z ⨯ V.obj j ⟶ Z))
      ((BigFppfOver.toScheme B S hS).map (prod.snd : Z ⨯ V.obj j ⟶ V.obj j))
      ((BigFppfOver.toScheme B S hS).map (hT.from Z))
      ((BigFppfOver.toScheme B S hS).map (hT.from (V.obj j))) := fun j =>
    (IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd Z (V.obj j)) hT).map _
  set F := BigFppfOver.toScheme B S hS
  have hfst : ∀ j, c.π.app j ≫ F.map (prod.fst : Z ⨯ V.obj j ⟶ Z) =
      c.π.app j₀ ≫ F.map (prod.fst : Z ⨯ V.obj j₀ ⟶ Z) := by
    have key : ∀ {j k : K} (f : k ⟶ j), c.π.app j ≫ F.map (prod.fst : Z ⨯ V.obj j ⟶ Z) =
        c.π.app k ≫ F.map (prod.fst : Z ⨯ V.obj k ⟶ Z) := fun {j k} f => by
      have h2 : F.map (prod.map (𝟙 Z) (V.map f)) ≫ F.map (prod.fst : Z ⨯ V.obj j ⟶ Z) =
          F.map (prod.fst : Z ⨯ V.obj k ⟶ Z) := by
        rw [← Functor.map_comp, prod.map_fst, Category.comp_id]
      exact (congrArg (· ≫ F.map (prod.fst : Z ⨯ V.obj j ⟶ Z)) (c.w f).symm).trans
        ((Category.assoc _ _ _).trans (congrArg (c.π.app k ≫ ·) h2))
    intro j
    exact (key (IsCofiltered.minToLeft j j₀)).trans (key (IsCofiltered.minToRight j j₀)).symm
  let d : Cone (underlyingDiagram V) :=
    { pt := c.pt
      π := { app j := c.π.app j ≫ F.map (prod.snd : Z ⨯ V.obj j ⟶ V.obj j)
             naturality {j k} f := by
              have h3 : F.map (prod.map (𝟙 Z) (V.map f)) ≫
                  F.map (prod.snd : Z ⨯ V.obj k ⟶ V.obj k) =
                  F.map (prod.snd : Z ⨯ V.obj j ⟶ V.obj j) ≫ F.map (V.map f) := by
                rw [← Functor.map_comp, ← Functor.map_comp, prod.map_snd]
              exact (Category.id_comp _).trans <|
                (congrArg (· ≫ F.map (prod.snd : Z ⨯ V.obj k ⟶ V.obj k)) (c.w f).symm).trans <|
                (Category.assoc _ _ _).trans <|
                (congrArg (c.π.app j ≫ ·) h3).trans (Category.assoc _ _ _).symm } }
  have hcond : (c.π.app j₀ ≫ F.map (prod.fst : Z ⨯ V.obj j₀ ⟶ Z)) ≫ F.map (hT.from Z) =
      limit.lift _ d ≫ limit.π (underlyingDiagram V) j₀ ≫ F.map (hT.from (V.obj j₀)) := by
    rw [limit.lift_π_assoc]
    exact (Category.assoc _ _ _).trans
      ((congrArg (c.π.app j₀ ≫ ·) (hpb j₀).w).trans (Category.assoc _ _ _).symm)
  let m : c.pt ⟶ pullback (F.map (hT.from Z))
      (limit.π (underlyingDiagram V) j₀ ≫ F.map (hT.from (V.obj j₀))) :=
    pullback.lift _ _ hcond
  have hm₁ : m ≫ pullback.fst _ _ = c.π.app j₀ ≫ F.map (prod.fst : Z ⨯ V.obj j₀ ⟶ Z) :=
    pullback.lift_fst _ _ _
  have hm₂ : ∀ j, m ≫ pullback.snd _ _ ≫ limit.π (underlyingDiagram V) j =
      c.π.app j ≫ F.map (prod.snd : Z ⨯ V.obj j ⟶ V.obj j) := fun j => by
    rw [← Category.assoc, pullback.lift_snd, limit.lift_π]
  have hm : Mono m := by
    have hx₁ : ∀ {T : Scheme.{u}} (x : T ⟶ c.pt) (j : K),
        (x ≫ c.π.app j) ≫ F.map (prod.fst : Z ⨯ V.obj j ⟶ Z) = x ≫ m ≫ pullback.fst _ _ := by
      intro T x j
      rw [Category.assoc, hfst j, hm₁]
    have hx₂ : ∀ {T : Scheme.{u}} (x : T ⟶ c.pt) (j : K),
        (x ≫ c.π.app j) ≫ F.map (prod.snd : Z ⨯ V.obj j ⟶ V.obj j) =
          x ≫ m ≫ pullback.snd _ _ ≫ limit.π (underlyingDiagram V) j := by
      intro T x j
      rw [Category.assoc, hm₂ j]
    refine ⟨fun {T} x y hxy => hc.hom_ext fun j => (hpb j).hom_ext ?_ ?_⟩
    · refine (hx₁ x j).trans (Eq.trans ?_ (hx₁ y j).symm)
      rw [← Category.assoc, hxy, Category.assoc]
    · refine (hx₂ x j).trans (Eq.trans ?_ (hx₂ y j).symm)
      rw [← Category.assoc, hxy, Category.assoc]
  have : B.Contains (pullback (F.map (hT.from Z))
      (limit.π (underlyingDiagram V) j₀ ≫ F.map (hT.from (V.obj j₀)))) :=
    Scheme.size_pullback_lt _ _ Z.left.property hLc
  exact B.contains_of_mono m this

/-- **The convention passes to products with a fixed object on the right.** -/
theorem BigFppfOver.LimitInSite.C1573.comp_prodFunctor_flip_obj {K : Type u} [Category.{u} K]
    [IsCofiltered K] {V : K ⥤ BigFppfOver B S hS}
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    (hL : BigFppfOver.LimitInSite V) (Z : BigFppfOver B S hS) :
    BigFppfOver.LimitInSite (V ⋙ prod.functor.flip.obj Z) := by
  have hiso : prod.functor.flip.obj Z ≅ prod.functor.obj Z :=
    NatIso.ofComponents (fun W => prod.braiding W Z)
      (fun {W W'} f => braid_natural f (𝟙 Z))
  exact BigFppfOver.LimitInSite.of_iso
    (Functor.isoWhiskerRight (Functor.isoWhiskerRight (Functor.isoWhiskerLeft V hiso) _) _)
    ((AlgebraicGeometry.BigFppfOver.LimitInSite.C1573.comp_prodFunctor_obj (hL := hL)) hV Z)

namespace Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))

namespace DescentSituation

open _root_.AlgebraicGeometry.Space.DescentSituation.C1573
/-- **Stacks 084T over an affine base scheme, under the chapter's convention.** In the situation
of Stacks 084R over an affine base scheme, for an inverse system satisfying the convention of
Section 70.2 (tag 07SD), if the limit `X` of the inverse system is separated then some stage
`X_i` is separated. -/
theorem C1573.exists_isAbsolutelySeparated_system_obj_of_isAffine_of_siteContainsBaseChangeLimits
    (hSaff : IsAffine S)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  have : Nonempty I := ⟨D.base⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have e : D.limitCone.pt ≅ limit D.system :=
    D.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  have hlimAS : IsAlgebraicSpace B S hS (limit D.system) := D.limitAlgebraicSpace.of_iso e
  have hlimSep : IsSeparatedOver B S hS (limit D.system) :=
    (isAbsolutelySeparated_iff_isSeparatedOver B S hS hZ hSaff hlimAS).mp
      (isAbsolutelySeparated_of_isSeparated B S hS hZ hX (isSeparated_of_isIso B S hS e.inv))
  obtain ⟨U₀, chart, hU₀, hchartS, hchartE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (D.system.obj (op D.base)) (D.algebraicSpace D.base)).mp (D.quasiCompact D.base)
  have hchartE' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) chart :=
    (isEtale_iff_presheaf_of_yoneda B S hS chart).mp hchartE
  set C := affineChartSystem B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart
    (fun {_ _} g ↦ D.transition_affine g) with hC
  have hLC : BigFppfOver.LimitInSite C.siteDiagram :=
    C.limitInSite_of_siteContainsBaseChangeLimits hconv
  set L : AffineChartSystem.LimitBridge C := C.limitBridgeOfLimitInSite hLC with hL
  set j₀ : Over (op D.base) := Over.mk (𝟙 (op D.base)) with hj₀
  have hq : ∀ j : Over (op D.base), yoneda.relativelyRepresentable (C.stageMap j) := fun j =>
    (D.algebraicSpace j.left.unop).diagonal_representable.of_diag (C.stageMap j)
  have hqE : ∀ j : Over (op D.base), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (C.stageMap j) := fun j =>
    presheaf_of_isPullback B S hS (C.isPullback j).flip hchartE'
  have hqS : ∀ j : Over (op D.base), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (C.stageMap j) := fun j =>
    presheaf_of_isPullback B S hS (C.isPullback j).flip hchartS
  have hqLim : yoneda.relativelyRepresentable L.toLimit :=
    hlimAS.diagonal_representable.of_diag L.toLimit
  have hqLimE : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) L.toLimit :=
    presheaf_of_isPullback B S hS (L.isPullback_stage j₀).flip (hqE j₀)
  have hkpLim : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqLim)) :=
    isClosedImmersion_kernelPairToProd_of_isSeparatedOver B S hS hlimSep hqLim
  have hUaff : ∀ j : Over (op D.base),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) := fun j =>
    C.isAffine_obj j
  have hmono : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ≤
      (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) := by
    intro Vv Ww g hg
    have hgE : Etale ((BigFppfOver.toScheme B S hS).map g) := hg
    exact (inferInstance : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g))
  have hfstLim : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (hqLim.fst' L.toLimit)) := by
    refine property_kernelPair_fst B S hS (@LocallyOfFiniteType.{u}) hqLim ?_
    exact MorphismProperty.relative_monotone hmono _ (presheaf_of_isPullback B S hS
      (IsPullback.of_hasPullback L.toLimit L.toLimit).flip hqLimE)
  have hftLim : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqLim) ≫
        (BigFppfOver.toScheme B S hS).map prod.fst) := by
    rwa [← Functor.map_comp,
      show kernelPairToProd B S hS hqLim ≫ prod.fst = hqLim.fst' L.toLimit from by
        simp [kernelPairToProd]]
  obtain ⟨k₁, hk₁⟩ := exists_isClosedImmersion_comp_prodMap_π_of_preservesLimit B S hS hSaff
    C.siteDiagram hUaff L.isLimit L.isAffine_pt
    (BigFppfOver.preservesLimit_toScheme_of_limitInSite _ (fun j =>
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ L.isAffine_pt (hUaff j))
      ((AlgebraicGeometry.BigFppfOver.LimitInSite.C1573.comp_prodFunctor_obj (hL := hLC))
        hUaff _)) _ hkpLim j₀ hftLim
  obtain ⟨ρ, hρ⟩ := exists_isPullback_kernelPairToProd_prodMap B S hS
    (limit.π D.system k₁.left) (hq k₁) hqLim (L.cone.π.app k₁) (L.isPullback_stage k₁)
  have hlimci : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
        ((BigFppfOver.toScheme B S hS).map
          (prod.map (L.cone.π.app k₁) (𝟙 (C.siteDiagram.obj k₁))))) := by
    refine (prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (hρ.map (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)).mp ?_
    rw [Functor.map_comp]
    exact hk₁ k₁ (𝟙 k₁)
  have hUc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj k₁)) :=
    have := hUaff k₁; Scheme.compactSpace_of_isAffine _
  have hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((hq k₁).pullback (C.stageMap k₁))) :=
    compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ (D.quasiSeparated k₁.left.unop)
      ((hq k₁).isPullback' (C.stageMap k₁)) hUc hUc
  have hmft : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁))) :=
    (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (C.stageMap k₁) (hqE k₁)).1
  have hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj
      ((hq k₁).pullback (C.stageMap k₁))) := by
    have hmm : Mono ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁))) :=
      (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (C.stageMap k₁)
        (hqE k₁)).2
    have hprodaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj k₁ ⨯ C.siteDiagram.obj k₁)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj k₁)
        (C.isAffine_obj k₁)
    exact quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
  obtain ⟨i, hi, hires⟩ := exists_isClosedImmersion_pullback_snd_prodMap_of_preservesLimit B S hS
    hSaff C.siteDiagram hUaff L.isLimit k₁
    (BigFppfOver.preservesLimit_toScheme_of_limitInSite _ (fun j =>
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hUaff j) (hUaff k₁))
      ((AlgebraicGeometry.BigFppfOver.LimitInSite.C1573.comp_prodFunctor_flip_obj (hL := hLC))
        hUaff _))
    (kernelPairToProd B S hS (hq k₁)) hmft hmqc hmqs hlimci
  obtain ⟨ρ', hρ'⟩ := exists_isPullback_kernelPairToProd_prodMap B S hS
    (D.system.map hi.left) (hq k₁) (hq i) (C.siteDiagram.map hi)
    (AffineChartSystem.isPullback_map B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart C hi)
  have hcomp : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i) ≫
        prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) :=
    (prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (hρ'.map (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)).mpr hires
  have hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map
      (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) := by
    have h1 : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj i ⨯ C.siteDiagram.obj i)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj i)
        (C.isAffine_obj i)
    have h2 : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj i ⨯ C.siteDiagram.obj k₁)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj i)
        (C.isAffine_obj k₁)
    have h3 : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) :=
      isAffineHom_of_isAffine _
    exact _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom _
  have hkpi : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i))) := by
    rw [Functor.map_comp] at hcomp
    exact _root_.AlgebraicGeometry.IsClosedImmersion.of_comp
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i)))
      ((BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi)))
  exact ⟨i.left.unop, leOfHom i.hom.unop, (isAbsolutelySeparated_iff_isSeparatedOver B S hS hZ
    hSaff (D.algebraicSpace i.left.unop)).mpr (isSeparatedOver_of_isClosedImmersion_kernelPairToProd
      B S hS (D.algebraicSpace i.left.unop) (hqS i) (hqE i) hkpi)⟩

/-- **Stacks 084T, under the chapter's convention.** In the situation of Stacks 084R, for an
inverse system satisfying the convention of Section 70.2 (tag 07SD), if the limit `X` of the
inverse system is separated then some stage `X_i` is separated. -/
theorem C1573.exists_isAbsolutelySeparated_system_obj_of_siteContainsBaseChangeLimits {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  obtain ⟨i, hi, hres⟩ :=
    exists_isAbsolutelySeparated_system_obj_of_isAffine_of_siteContainsBaseChangeLimits
      B (⊤_ Scheme.{u}) hZ hZ inferInstance (D.viewOverIntegers B S hS hZ)
      (D.siteContainsBaseChangeLimits_viewOverIntegers hZ hconv)
      ((isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ D.limitCone.pt).2 hX)
  exact ⟨i, hi, (isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ
    (D.system.obj (op i))).1 hres⟩

end DescentSituation

/-- **Stacks 086X, under the chapter's convention.** Let `Y` be a quasi-separated algebraic space
and `X = lim X_i` a directed limit over `Y`, with affine transition morphisms, of quasi-compact
quasi-separated algebraic spaces, as in Stacks 084R, whose system satisfies the convention of
Section 70.2 (tag 07SD). If `X ⟶ Y` is separated then so is `X_i ⟶ Y` for all large `i`. -/
theorem DescentSituation.C1573.exists_isSeparated_system_app_of_siteContainsBaseChangeLimits
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : DescentSituation B S hS hZ I) (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (hsep : IsSeparated B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)) := by
  have : Nonempty I := ⟨D.base⟩
  obtain ⟨U₀, q₀, hU₀, hq₀S, hq₀E⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (D.system.obj (op D.base)) (D.algebraicSpace D.base)).mp (D.quasiCompact D.base)
  have hq₀E' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q₀ :=
    (isEtale_iff_presheaf_of_yoneda B S hS q₀).mp hq₀E
  have hlim : IsAbsolutelySeparated B S hS hZ
      (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))).limitCone.pt :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ U₀ hU₀
      (pullback.snd f (q₀ ≫ t.app (op D.base)))
      (isSeparated_pullbackSnd B S hS (q₀ ≫ t.app (op D.base)) hsep)
  obtain ⟨i, hbi₀, hi⟩ :=
    DescentSituation.C1573.exists_isAbsolutelySeparated_system_obj_of_siteContainsBaseChangeLimits
      B S hS hZ (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base)))
      (hconv.baseChangeOverSystem t (q₀ ≫ t.app (op D.base))) hlim
  have hbi : D.base ≤ i := hbi₀
  have hsepi : IsSeparated B S hS (pullback.snd (t.app (op i)) (q₀ ≫ t.app (op D.base))) :=
    (isSeparated_pullbackSnd_iff_isAbsolutelySeparated B S hS hZ (D.algebraicSpace i)
      (t.app (op i)) U₀ hU₀ (q₀ ≫ t.app (op D.base))).mpr hi
  have hτ : D.system.map (homOfLE hbi).op ≫ t.app (op D.base) = t.app (op i) := by simp
  obtain ⟨W, v, wq, hpb⟩ :=
    D.transition_affine (homOfLE hbi).op ⟨U₀, hU₀⟩ q₀
  have hstage : IsSeparated B S hS (t.app (op i)) := by
    refine isSeparated_of_isSeparated_pullbackSnd_of_etaleChart_factorization B S hS
      (D.algebraicSpace i) (t.app (op i))
      (presheaf_of_isPullback B S hS hpb.flip hq₀S)
      (presheaf_of_isPullback B S hS hpb.flip hq₀E') (yoneda.map wq) ?_ hsepi
    rw [← hτ]
    simp only [← Category.assoc, hpb.w]
  refine ⟨i, hbi, fun k hik => ?_⟩
  have hk : D.system.map (homOfLE hik).op ≫ t.app (op i) = t.app (op k) := by simp
  rw [← hk]
  exact isSeparated_comp B S hS _ _
    (isSeparated_of_isAffineHom B S hS (D.system.map (homOfLE hik).op)
      (D.algebraicSpace k) (D.algebraicSpace i) (D.transition_affine _)) hstage

end Space

namespace Space.MorphismDescentSituation

open _root_.AlgebraicGeometry.Space.C1573
variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I)

end Space.MorphismDescentSituation

end AlgebraicGeometry

end
