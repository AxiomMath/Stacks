module

public import StacksFrontier.AlgebraicGeometry.Curves.GeometricallyReducedCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReducedLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
import all StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReducedLocus

/-!
# Families of curves with geometrically reduced fibres are Cohen–Macaulay

A family of curves whose fibres are geometrically reduced is Cohen–Macaulay, so the condition
cutting out `Curves^{geomred}` implies the one cutting out `Curves^{CM}` (Stacks 0E1G).

## Main definitions

* `AlgebraicGeometry.IsGeometricallyReducedCurveFamily`: the fibres of the structure morphism of
  a family of curves are geometrically reduced (the condition of Stacks 0E0G).

## Main results

* `AlgebraicGeometry.CurveFamily.isCohenMacaulayFamily_of_isGeometricallyReducedFamily`: a family
  of curves with geometrically reduced fibres is Cohen–Macaulay.
* `AlgebraicGeometry.curvesGeomred_le_curvesCM`: `Curves^{geomred} ⊂ Curves^{CM}`, as conditions
  on families of curves (Stacks 0E1G).
* `AlgebraicGeometry.openSubstack_le_of_isGeometricallyReducedFamily`: the same inclusion for
  open substacks of an algebraic stack whose objects are identified with families of curves.

## References

* [Stacks Project, Tag 0E1G](https://stacks.math.columbia.edu/tag/0E1G)
* [Stacks Project, Tag 0E0G](https://stacks.math.columbia.edu/tag/0E0G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `integerBase` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_curvesGeometricallyReducedSupplement :
    HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_curvesGeometricallyReducedSupplement
    {X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Geometrically reduced families over an arbitrary base -/

/-- An isomorphism of presheaves on the big fppf site is a surjective chart: it is relatively
representable and every morphism of the site pulled back from it is an isomorphism, hence
surjective. -/
private theorem surjective_presheaf_hom_of_iso
    {F G : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B integerBase hZ)).presheaf e.hom := by
  show yoneda.relativelyRepresentable e.hom ∧
    (∀ ⦃A C⦄ (g : yoneda.obj A ⟶ G) (fst : yoneda.obj C ⟶ F) (snd : C ⟶ A),
      IsPullback fst (yoneda.map snd) e.hom g →
        Surjective ((BigFppfOver.toScheme B integerBase hZ).map snd))
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.hom, ?_⟩
  intro A C g fst snd sq
  have : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
  have : IsIso ((BigFppfOver.toScheme B integerBase hZ).map snd) := inferInstance
  exact inferInstance

/-- **The defining condition of `Curves^{geomred}`** (Stacks 0E0G): the fibres of the structure
morphism of the family of curves are geometrically reduced in the sense of Tag 0E08. -/
abbrev IsGeometricallyReducedCurveFamily (X : CurveFamily B hZ) : Prop :=
  ∀ y : Space.points B integerBase hZ (schemeSpace X.base).obj,
    Space.IsGeometricallyReducedFibreAt B integerBase hZ X.toBase.hom X.total.property
      (schemeSpace X.base).property y

/-- A family of curves whose fibres are geometrically reduced is Cohen–Macaulay. -/
theorem CurveFamily.isCohenMacaulayFamily_of_isGeometricallyReducedFamily
    (X : CurveFamily B hZ) (hX : IsGeometricallyReducedCurveFamily B hZ X) :
    IsCohenMacaulayFamily B hZ X := by
  have hXsp := X.total.property
  have hYsp := (schemeSpace X.base).property
  have hLN : Space.HasLocallyNoetherianFibers B integerBase hZ X.toBase.hom := by
    intro V g hg v hv
    obtain ⟨U, a, h, comm, haS, haE⟩ :=
      Space.exists_surjective_etale_atlas_over_chart B integerBase hZ hXsp hYsp
        X.toBase.hom V g
    have hgE := (Space.isEtale_iff_presheaf_of_yoneda B integerBase hZ g).mp hg
    have hpE := Space.chartSource_property B integerBase hZ (@Etale.{u})
      Etale.etale_isStableUnderBaseChange.{u} etale_isStableUnderComposition.{u}
      X.toBase.hom V g hgE U a haE
    have hpcomm : (a ≫ pullback.fst X.toBase.hom g) ≫ X.toBase.hom = yoneda.map h ≫ g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, comm]
    have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map h) :=
      X.finitePresentation.1 U V (a ≫ pullback.fst X.toBase.hom g) g h hpE hgE hpcomm.symm
    exact (Space.hasEtaleLocalProperty_fiberAt_iff B integerBase hZ hXsp hYsp
      X.toBase.hom V g U a h comm haS haE
      (fun W : Scheme.{u} => IsLocallyNoetherian W) v hv).mpr
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _ v)
  obtain ⟨g, hidS', hidE', hidE, hg1⟩ :
      ∃ g : yoneda.obj X.base ⟶ (schemeSpace X.base).obj,
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B integerBase hZ)).presheaf g ∧
          (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B integerBase hZ)).presheaf g ∧
          Space.IsEtale B integerBase hZ g ∧
          ∀ {W : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (k : W ⟶ yoneda.obj X.base),
            k ≫ g = k :=
    ⟨𝟙 (schemeSpace X.base).obj,
      surjective_presheaf_hom_of_iso B hZ (Iso.refl (schemeSpace X.base).obj),
      Space.presheaf_etale_of_iso B integerBase hZ (Iso.refl (schemeSpace X.base).obj),
      (Space.isEtale_iff_presheaf_of_yoneda B integerBase hZ _).mpr
        (Space.presheaf_etale_of_iso B integerBase hZ (Iso.refl (schemeSpace X.base).obj)),
      fun k => Category.comp_id k⟩
  have key := (Space.isCohenMacaulay_tfae_etaleCharts B integerBase hZ hXsp hYsp
    X.toBase.hom hLN).out 2 1
  refine key.mp ⟨X.flat, X.base, g, hidS', hidE, ?_⟩
  intro v hv
  obtain ⟨U, a, h, comm, haS, haE⟩ :=
    Space.exists_surjective_etale_atlas_over_chart B integerBase hZ hXsp hYsp
      X.toBase.hom X.base g
  have hpE := Space.chartSource_property B integerBase hZ (@Etale.{u})
    Etale.etale_isStableUnderBaseChange.{u} etale_isStableUnderComposition.{u}
    X.toBase.hom X.base g hidE' U a haE
  have hpS := Space.chartSource_property B integerBase hZ (@Surjective.{u}) inferInstance
    surjective_isStableUnderComposition.{u} X.toBase.hom X.base g hidS' U a haS
  have hhh : yoneda.map h = (a ≫ pullback.fst X.toBase.hom g) ≫ X.toBase.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, comm, hg1]
  have hpcomm : yoneda.map h ≫ g = (a ≫ pullback.fst X.toBase.hom g) ≫ X.toBase.hom :=
    (hg1 _).trans hhh
  have hiE : Space.IsEtale B integerBase hZ (a ≫ pullback.fst X.toBase.hom g) :=
    (Space.isEtale_iff_presheaf_of_yoneda B integerBase hZ _).mpr hpE
  have hiS : Space.IsSurjective B integerBase hZ (a ≫ pullback.fst X.toBase.hom g) :=
    (Space.presheafSurjective_iff_isSurjective_yoneda B integerBase hZ X.total.obj hXsp U _).1
      hpS
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map h) :=
    X.finitePresentation.1 U X.base (a ≫ pullback.fst X.toBase.hom g) g h hpE hidE' hpcomm
  have : IsLocallyNoetherian
      (((BigFppfOver.toScheme B integerBase hZ).map h).fiber v) :=
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _ v
  have hgr : GeometricallyReduced
      (((BigFppfOver.toScheme B integerBase hZ).map h).fiberToSpecResidueField v) :=
    (Space.isGeometricallyReducedFibre_iff_geometricallyReduced_fiber B integerBase hZ
      X.toBase.hom hXsp _ h hiE hiS hhh v).mp
      ((Space.isGeometricallyReducedFibreAt_class_iff B integerBase hZ X.toBase.hom hXsp hYsp
        (Space.schemePointRepresentative B integerBase hZ X.base v)).mp (hX _))
  have : IsReduced (((BigFppfOver.toScheme B integerBase hZ).map h).fiber v) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (((BigFppfOver.toScheme B integerBase hZ).map h).fiberToSpecResidueField v)
  have hdim : topologicalKrullDim
      (((BigFppfOver.toScheme B integerBase hZ).map h).fiber v) ≤ 1 := by
    have hfd : ((BigFppfOver.toScheme B integerBase hZ).map h).fiberDimension v ≤
        (1 : WithBot ℕ∞) := by
      refine (Scheme.Hom.fiberDimension_le_iff _ v _).mpr fun u _ => ?_
      obtain ⟨e, hle, he⟩ := X.relativeDimensionLE
        (Space.pointsMap B integerBase hZ (yoneda.obj U)
          (a ≫ pullback.fst X.toBase.hom g)
          ((Space.pointsEquivScheme B integerBase hZ U).symm u))
      rw [(Space.hasRelativeDimensionAt_pointsMap_iff B integerBase hZ (e : ℕ∞)
        X.toBase.hom U X.base (a ≫ pullback.fst X.toBase.hom g) g h hpE hidE' hpcomm u).mp he]
      exact_mod_cast hle
    simpa only [Scheme.Hom.fiberDimension] using hfd
  exact (Space.hasEtaleLocalProperty_fiberAt_iff B integerBase hZ hXsp hYsp X.toBase.hom
    X.base g U a h comm haS haE
    (fun W : Scheme.{u} => _root_.AlgebraicGeometry.IsCohenMacaulay W) v hv).mpr
    (isCohenMacaulay_of_isReduced_of_topologicalKrullDim_le_one _ hdim)

/-- `Curves^{geomred} ⊂ Curves^{CM}`: a family of curves whose fibres are geometrically reduced
is Cohen–Macaulay. -/
@[stacks 0E1G "the inclusion of the conditions cutting the two subcategories out of the \
  category of families of curves"]
theorem curvesGeomred_le_curvesCM :
    (show ObjectProperty (CurveFamily B hZ) from IsGeometricallyReducedCurveFamily B hZ) ≤
      (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ) :=
  fun X hX => CurveFamily.isCohenMacaulayFamily_of_isGeometricallyReducedFamily B hZ X hX

/-- **The inclusion of Stacks 0E1G read on the open substacks themselves.** Let `𝒳` be an
algebraic stack over the big fppf site of the integers whose objects are identified with families
of curves by an equivalence `E`, and let `Ugeomred` and `Ucm` be open substacks of `𝒳` whose
objects are exactly those identified with, respectively, the families of curves with
geometrically reduced fibres and the Cohen–Macaulay families. Then `Ugeomred ⊂ Ucm`. -/
theorem openSubstack_le_of_isGeometricallyReducedFamily
    {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj) (Ugeomred Ucm : Stack.OpenSubstack 𝒳)
    (hUg : ∀ F : CurveFamily B hZ,
      Ugeomred.property (E.functor.obj F) ↔ IsGeometricallyReducedCurveFamily B hZ F)
    (hUc : ∀ F : CurveFamily B hZ,
      Ucm.property (E.functor.obj F) ↔ IsCohenMacaulayFamily B hZ F) :
    Ugeomred.property ≤ Ucm.property := by
  have := Ugeomred.strictlyFull
  have := Ucm.strictlyFull
  intro Z hmem
  have hiso : E.functor.obj (E.inverse.obj Z) ≅ Z := E.counitIso.app Z
  have hg : IsGeometricallyReducedCurveFamily B hZ (E.inverse.obj Z) :=
    (hUg _).mp (ObjectProperty.IsClosedUnderIsomorphisms.of_iso hiso.symm hmem)
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso hiso
    ((hUc _).mpr (curvesGeomred_le_curvesCM B hZ (E.inverse.obj Z) hg))

end AlgebraicGeometry

end
