module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Fibres.ReducedFibreLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# The geometrically reduced fibre locus is étale locally constructible

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S` which is
locally of finite presentation. The set of points of `|Y|` whose fibre is geometrically
reduced is étale locally constructible: its inverse image on every étale scheme chart of `Y`
is locally constructible.

## Main results

* `AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber_of_isAffine_source`:
  the locus of geometrically reduced fibres of a morphism of affine schemes of finite
  presentation is locally constructible, with no Noetherian hypothesis on the base.
* `AlgebraicGeometry.Space.isEtaleLocallyConstructible_geometricallyReducedFibreLocus` is
  Stacks 0E0A.
* `AlgebraicGeometry.Space.geometricallyReducedFibreLocus_eq_preimage_chart`: on a surjective
  étale chart `h_A ⟶ F` of an algebraic space over `h_U`, the locus is the set of points of `U`
  over which the morphism of schemes `A ⟶ U` has geometrically reduced fibre.
* `AlgebraicGeometry.Space.forall_isGeometricallyReducedFibreAt_yoneda_map_iff`: a morphism of
  schemes of the site is geometrically reduced exactly when every fibre of the induced morphism
  of algebraic spaces is geometrically reduced.

## Implementation notes

Constructibility is tested on an affine étale chart `h_V ⟶ Y`, where by Stacks 0E09 the
inverse image of the locus is the locus of the base change `X ×_Y h_V ⟶ h_V`. That base
change is a quasi-compact algebraic space, so it has an affine surjective étale chart
`h_A ⟶ X ×_Y h_V`, and the composite `A ⟶ V` is a morphism of affine schemes of finite
presentation. Over a field-valued point of `h_V` the fibre of `h_A ⟶ h_V` is a surjective
étale chart of the fibre of `X ×_Y h_V ⟶ h_V`, so by Stacks 0DMS the two have the same
geometric reducedness; the chart is the scheme-theoretic fibre, so the locus is read on `V` as
the scheme-level geometrically reduced fibre locus of `A ⟶ V`, which is locally constructible
by Stacks 0579.

Stacks 0579 is available in the library for a morphism of affine schemes of finite
presentation over a *locally Noetherian* base
(`AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber_of_isAffine`). The
Noetherian hypothesis is removed here by Noetherian approximation: such a morphism is the base
change of one over a base of finite type over `ℤ` (Stacks 05FB,
`AlgebraicGeometry.finiteTypeAffineModel`), the locus commutes with base change by Stacks 0576
and local constructibility is inherited by inverse images (Stacks 054I).

The fibre of a morphism of algebraic spaces over a field-valued point `p` of the target is
formed by restricting along the structure morphism of the field spectrum and taking the fibre
product with the tautological section of the restricted target. For a morphism `h_A ⟶ h_V` of
representables the reindexing square
`CategoryTheory.OverShriek.isPullback_restrictReindex` identifies that fibre with the
representable attached to the fibre product `A ×_V Spec κ` *in the site over `S`*, reindexed
over `Spec κ`; its structure morphism is the second projection of that fibre product, which is
the scheme-theoretic fibre because the canonical field-valued representative above a point is
presented by `Scheme.fromSpecResidueField`. Factoring `h_A ⟶ h_V` through `X ×_Y h_V` then
exhibits the chart of the fibre as a base change of the restriction of `h_A ⟶ X ×_Y h_V`,
which is surjective and étale by `CategoryTheory.OverShriek.relative_relocalizeRestrict_map`.

## References

* [Stacks Project, Tag 0E0A](https://stacks.math.columbia.edu/tag/0E0A)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 0E09](https://stacks.math.columbia.edu/tag/0E09)
* [Stacks Project, Tag 0DMS](https://stacks.math.columbia.edu/tag/0DMS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry

/-! ### The scheme-level input: Stacks 0579 for a morphism of affine schemes -/

/-- The base of an affine finite-type model is locally Noetherian, being of finite type over
`ℤ`. -/
private theorem isLocallyNoetherian_base_finiteTypeAffineModel
    {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} {f : X ⟶ S}
    (m : FiniteTypeAffineModel P f) : IsLocallyNoetherian m.S₀ := by
  let _ : IsAffine m.S₀ := m.base_affine
  let _ : LocallyOfFiniteType (terminal.from m.S₀) := m.base_locallyOfFiniteType
  let e : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  let g : m.S₀ ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from m.S₀ ≫ e.inv
  let _ : LocallyOfFiniteType g := by dsimp [g]; infer_instance
  let _ : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  exact LocallyOfFiniteType.isLocallyNoetherian g

/-- **Stacks 0579 for a morphism of affine schemes.** For a morphism `g : X ⟶ S` of finite
presentation between affine schemes the set of points of `S` whose fibre is geometrically
reduced is locally constructible; no Noetherian hypothesis is needed.

By Stacks 05FB the morphism is the base change of a morphism of affine schemes of finite type
over a base of finite type over `ℤ`, hence of finite presentation over a locally Noetherian
base; the locus commutes with base change by Stacks 0576, and the affine Noetherian case of
Stacks 0579 together with Stacks 054I finishes the argument. -/
@[ega "IV 9.7.7" "(iii), special case"]
theorem isLocallyConstructible_geometricallyReduced_fiber_of_isAffine_source {X S : Scheme.{u}}
    (g : X ⟶ S) [IsAffine X] [IsAffine S] (hg : FinitePresentation g) :
    IsLocallyConstructible {y : S | GeometricallyReduced (g.fiberToSpecResidueField y)} := by
  let m := finiteTypeAffineModel g hg
  let _ : IsAffine m.X₀ := m.source_affine
  let _ : IsAffine m.S₀ := m.base_affine
  let _ : LocallyOfFiniteType m.f₀ := m.locallyOfFiniteType
  let _ : QuasiCompact m.f₀ := m.quasiCompact
  let _ : IsLocallyNoetherian m.S₀ := isLocallyNoetherian_base_finiteTypeAffineModel m
  rw [geometricallyReduced_fiber_set_eq_preimage_of_isPullback m.f₀ g m.toSource m.toBase
    m.isPullback]
  exact isLocallyConstructible_preimage _
    (isLocallyConstructible_geometricallyReduced_fiber_of_isAffine m.f₀
      (finitePresentation_of_finiteType m.f₀))

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on a big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_geometricallyReducedLocus
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

private theorem class_schemePointRepresentative (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    (schemePointRepresentative B S hS U x).class B S hS (yoneda.obj U) =
      (schemePointsHomeomorph B S hS U).symm x := by
  apply (schemePointsHomeomorph B S hS U).injective
  rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply]
  exact schemePointRepresentative_point B S hS U x

/-! ### Auxiliary permanence statements -/

/-- A base change of a surjective morphism of algebraic spaces over `S` whose source and the
source of the morphism are representable is surjective. This is the surjectivity companion of
`AlgebraicGeometry.Space.isEtale_of_isPullback_yoneda`. -/
private theorem isSurjective_of_isPullback_yoneda
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G)
    {R V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ G} {f : F ⟶ G}
    {f' : yoneda.obj R ⟶ yoneda.obj V} {g' : yoneda.obj R ⟶ F}
    (sq : IsPullback f' g' g f) (hg : IsSurjective B S hS g) : IsSurjective B S hS g' := by
  have hbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact (surjective_iff_surjective_pointsMap B S hS F hF R g').1
    (hbc.of_isPullback sq ((surjective_iff_surjective_pointsMap B S hS G hG V g).2 hg))

/-! ### The fibre of a morphism of representables over a field-valued point -/

section Fibre

variable {U A : BigFppfOver B S hS} (hAU : A ⟶ U)
  (p : FieldValuedPoint B S hS (yoneda.obj U))

/-- The structure morphism of the field spectrum of a field-valued point of `h_U`, as a
morphism of the big fppf site over `S`. -/
private noncomputable abbrev fieldBase : B.obj p.contained ⟶ B.obj hS := ⟨p.toBase⟩

/-- The final object of the big fppf site over the field spectrum of a field-valued point. -/
private noncomputable abbrev fieldFinal : BigFppfOver B (Spec (.of p.carrier)) p.contained :=
  Over.mk (𝟙 (B.obj p.contained))

/-- The section of `h_U` presenting a field-valued point, read as a morphism out of the image
of the final object of the site over the field spectrum. -/
private noncomputable def fibreBaseHom :
    (Over.map (fieldBase B S hS p)).obj (fieldFinal B S hS p) ⟶ U :=
  Over.homMk p.value.left (by simp [Over.w p.value])

@[simp]
private theorem fibreBaseHom_left : (fibreBaseHom B S hS p).left = p.value.left := rfl

/-- The fibre of `h_A ⟶ h_U` over a field-valued point of `h_U`, as an object of the big fppf
site over the field spectrum: the fibre product `A ×_U Spec κ` formed over `S`, reindexed over
`Spec κ`. -/
private noncomputable def fibreObject :
    BigFppfOver B (Spec (.of p.carrier)) p.contained :=
  OverShriek.restrictReindex (fieldBase B S hS p)
    (pullback.snd hAU (fibreBaseHom B S hS p))

/-- The structure morphism of the fibre object is the second projection of the fibre product
`A ×_U Spec κ`. -/
private theorem map_fibreObject_hom :
    B.inclusion.map (fibreObject B S hS hAU p).hom =
      (BigFppfOver.toScheme B S hS).map (pullback.snd hAU (fibreBaseHom B S hS p)) := by
  have h : (fibreObject B S hS hAU p).hom =
      (pullback.snd hAU (fibreBaseHom B S hS p)).left := Category.comp_id _
  rw [h]
  rfl

/-- The tautological section of the restricted target corresponds, under the identification of
sections of a restriction with sections of the original, to the morphism of the site presenting
the field-valued point. -/
private theorem restrictYonedaEquiv_restrictedSection :
    OverShriek.restrictYonedaEquiv (fieldBase B S hS p) (fieldFinal B S hS p) (yoneda.obj U)
        (restrictedSection B S hS (yoneda.obj U) p.contained (fieldBase B S hS p) p.value) =
      yoneda.map (fibreBaseHom B S hS p) := by
  unfold OverShriek.restrictYonedaEquiv restrictedSection
  rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_eq, yonedaEquiv_yoneda_map]
  exact Over.OverMorphism.ext rfl

/-- **The fibre of a morphism of representables over a field-valued point is representable.**
The fibre product of the restriction of `h_A ⟶ h_U` with the tautological section of the
restriction of `h_U` is represented by the fibre object. -/
private theorem exists_isPullback_fibreObject :
    ∃ (c : yoneda.obj (fibreObject B S hS hAU p) ⟶
        (OverShriek.relocalizeRestrict (fieldBase B S hS p)).obj (yoneda.obj A))
      (d : yoneda.obj (fibreObject B S hS hAU p) ⟶ yoneda.obj (fieldFinal B S hS p)),
      IsPullback c d
        ((OverShriek.relocalizeRestrict (fieldBase B S hS p)).map (yoneda.map hAU))
        (restrictedSection B S hS (yoneda.obj U) p.contained (fieldBase B S hS p) p.value) := by
  refine ⟨_, _, OverShriek.isPullback_restrictReindex (V := fieldFinal B S hS p)
    (fieldBase B S hS p) (pullback.snd hAU (fibreBaseHom B S hS p)) (yoneda.map hAU)
    (restrictedSection B S hS (yoneda.obj U) p.contained (fieldBase B S hS p) p.value)
    (fs := yoneda.map (pullback.fst hAU (fibreBaseHom B S hS p))) ?_⟩
  rw [restrictYonedaEquiv_restrictedSection]
  exact (IsPullback.of_hasPullback hAU (fibreBaseHom B S hS p)).map yoneda

/-- **The fibre object is the scheme-theoretic fibre.** Over the canonical field-valued
representative above a point `x` of the chart, the structure morphism of the fibre object is
the fibre of the morphism of schemes `A ⟶ U` at `x`, so the two are geometrically reduced
together. -/
private theorem geometricallyReduced_fibreObject_iff
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    GeometricallyReduced (B.inclusion.map
        (fibreObject B S hS hAU (schemePointRepresentative B S hS U x)).hom) ↔
      GeometricallyReduced
        (((BigFppfOver.toScheme B S hS).map hAU).fiberToSpecResidueField x) := by
  have _ : MorphismProperty.RespectsIso (@GeometricallyReduced : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    show PreservesLimitsOfShape WalkingCospan ((Over.forget (B.obj hS)) ⋙ B.inclusion)
    apply comp_preservesLimitsOfShape
  have hsq : IsPullback
      ((BigFppfOver.toScheme B S hS).map
        (pullback.fst hAU (fibreBaseHom B S hS (schemePointRepresentative B S hS U x))))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd hAU (fibreBaseHom B S hS (schemePointRepresentative B S hS U x))))
      ((BigFppfOver.toScheme B S hS).map hAU)
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x) := by
    rw [← toScheme_map_siteHom_schemePointRepresentative B S hS U x]
    exact (IsPullback.of_hasPullback hAU
      (fibreBaseHom B S hS (schemePointRepresentative B S hS U x))).map
      (BigFppfOver.toScheme B S hS)
  have hfib : IsPullback (((BigFppfOver.toScheme B S hS).map hAU).fiberι x)
      (((BigFppfOver.toScheme B S hS).map hAU).fiberToSpecResidueField x)
      ((BigFppfOver.toScheme B S hS).map hAU)
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x) :=
    IsPullback.of_hasPullback _ _
  rw [map_fibreObject_hom, ← hsq.isoIsPullback_hom_snd _ _ hfib]
  exact MorphismProperty.cancel_left_of_respectsIso _ _ _

end Fibre

/-! ### A surjective étale chart of the fibre over a field-valued point -/

section Chart

variable {U A : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f' : F ⟶ yoneda.obj U)
  (hF : IsAlgebraicSpace B S hS F) (i : yoneda.obj A ⟶ F) (hAU : A ⟶ U)
  (p : FieldValuedPoint B S hS (yoneda.obj U))

/-- Restriction along the structure morphism of a field spectrum, followed by the identification
of the restricted representable, preserves a relative property of morphisms of presheaves coming
from a property of morphisms of schemes: reindexing leaves the underlying morphism of schemes
untouched. -/
private theorem presheaf_restrictYonedaIso_hom_comp_map (Q : MorphismProperty Scheme.{u})
    (hQ : MorphismProperty.RespectsIso Q) {h : yoneda.obj A ⟶ F}
    (hh : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf h) :
    (MorphismProperty.inverseImage Q
        (BigFppfOver.toScheme B (Spec (.of p.carrier)) p.contained)).presheaf
      ((OverShriek.restrictYonedaIso (fieldBase B S hS p) A).hom ≫
        (OverShriek.relocalizeRestrict (fieldBase B S hS p)).map h) :=
  let _ : (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B (Spec (.of p.carrier)) p.contained)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  MorphismProperty.RespectsIso.precomp _
    (OverShriek.restrictYonedaIso (fieldBase B S hS p) A).hom _
    (OverShriek.relative_relocalizeRestrict_map (fieldBase B S hS p)
      (fun s hs => inverseImage_restrictReindexSnd B (Spec (.of p.carrier)) S p.contained hS
        (fieldBase B S hS p) Q s hs) hh)

/-- The restriction of an étale chart `i` to the fibre over a field-valued point is étale. -/
private theorem isEtale_restrictYonedaIso_hom_comp_map (hiE : IsEtale B S hS i) :
    IsEtale B (Spec (.of p.carrier)) p.contained
      ((OverShriek.restrictYonedaIso (fieldBase B S hS p) A).hom ≫
        (OverShriek.relocalizeRestrict (fieldBase B S hS p)).map i) :=
  (isEtale_iff_presheaf_of_yoneda B (Spec (.of p.carrier)) p.contained _).2 <|
    presheaf_restrictYonedaIso_hom_comp_map B S hS p
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      AlgebraicGeometry.etale_respectsIso
      ((isEtale_iff_presheaf_of_yoneda B S hS i).1 hiE)

include hF

/-- The restriction of a surjective chart `i` to the fibre over a field-valued point is
surjective. -/
private theorem isSurjective_restrictYonedaIso_hom_comp_map (hiS : IsSurjective B S hS i) :
    IsSurjective B (Spec (.of p.carrier)) p.contained
      ((OverShriek.restrictYonedaIso (fieldBase B S hS p) A).hom ≫
        (OverShriek.relocalizeRestrict (fieldBase B S hS p)).map i) :=
  (presheafSurjective_iff_isSurjective_yoneda B (Spec (.of p.carrier)) p.contained _
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of p.carrier)) S p.contained hS
        (fieldBase B S hS p) F hF) _ _).1 <|
    presheaf_restrictYonedaIso_hom_comp_map B S hS p
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) inferInstance
      ((presheafSurjective_iff_isSurjective_yoneda B S hS F hF A i).2 hiS)

/-- **The fibre of a surjective étale chart is a surjective étale chart of the fibre.** If
`i : h_A ⟶ F` is a surjective étale chart of an algebraic space over `h_U` and `A ⟶ U` is the
induced morphism of the site, then the fibre object of `A ⟶ U` over a field-valued point of
`h_U` is a surjective étale chart of the fibre of `F ⟶ h_U` over that point.

The fibre of `h_A ⟶ h_U` is the fibre of `F ⟶ h_U` base changed along the restriction of `i`,
because the fibre of a composite is computed in two steps; and the restriction of `i` is
surjective and étale because reindexing does not change the morphisms of schemes tested. -/
private theorem exists_surjective_etale_chart_fibre
    (hiE : IsEtale B S hS i) (hiS : IsSurjective B S hS i)
    (hh : yoneda.map hAU = i ≫ f') :
    ∃ α : yoneda.obj (fibreObject B S hS hAU p) ⟶ fibreOverFieldValuedPoint B S hS f' p,
      IsSurjective B (Spec (.of p.carrier)) p.contained α ∧
        IsEtale B (Spec (.of p.carrier)) p.contained α := by
  have hRF : IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained
      ((OverShriek.relocalizeRestrict (fieldBase B S hS p)).obj F) :=
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of p.carrier)) S p.contained hS
      (fieldBase B S hS p) F hF
  have hFib : IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained
      (fibreOverFieldValuedPoint B S hS f' p) :=
    isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f' hF (isAlgebraicSpace_yoneda B S hS U) p
  obtain ⟨c, d, hcd⟩ := exists_isPullback_fibreObject B S hS hAU p
  have hs : IsPullback (c ≫ (OverShriek.restrictYonedaIso (fieldBase B S hS p) A).inv) d
      (((OverShriek.restrictYonedaIso (fieldBase B S hS p) A).hom ≫
          (OverShriek.relocalizeRestrict (fieldBase B S hS p)).map i) ≫
        (OverShriek.relocalizeRestrict (fieldBase B S hS p)).map f')
      (restrictedSection B S hS (yoneda.obj U) p.contained (fieldBase B S hS p) p.value) := by
    refine hcd.of_iso' (Iso.refl _) (OverShriek.restrictYonedaIso (fieldBase B S hS p) A)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
    rw [hh, Functor.map_comp]
    simp
  have hbot := IsPullback.of_bot' hs (IsPullback.of_hasPullback
    ((OverShriek.relocalizeRestrict (fieldBase B S hS p)).map f')
    (restrictedSection B S hS (yoneda.obj U) p.contained (fieldBase B S hS p) p.value))
  exact ⟨_, isSurjective_of_isPullback_yoneda B (Spec (.of p.carrier)) p.contained hFib hRF
      hbot (isSurjective_restrictYonedaIso_hom_comp_map B S hS hF i p hiS),
    isEtale_of_isPullback_yoneda B (Spec (.of p.carrier)) p.contained hbot
      (isEtale_restrictYonedaIso_hom_comp_map B S hS i p hiE)⟩

/-- **The fibre condition on the chart.** The fibre of `F ⟶ h_U` over the canonical
field-valued representative above a point `x` of `U` is geometrically reduced exactly when the
scheme-theoretic fibre of `A ⟶ U` at `x` is geometrically reduced over the residue field.

By `AlgebraicGeometry.Space.exists_surjective_etale_chart_fibre` the scheme fibre is a
surjective étale chart of the fibre, so the two conditions agree by the two clauses of
Stacks 0DMS. -/
private theorem isGeometricallyReducedFibre_iff_geometricallyReduced_fiber
    (hiE : IsEtale B S hS i) (hiS : IsSurjective B S hS i) (hh : yoneda.map hAU = i ≫ f')
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    IsGeometricallyReducedFibre B S hS f' hF (isAlgebraicSpace_yoneda B S hS U)
        (schemePointRepresentative B S hS U x) ↔
      GeometricallyReduced
        (((BigFppfOver.toScheme B S hS).map hAU).fiberToSpecResidueField x) := by
  obtain ⟨α, hαS, hαE⟩ := exists_surjective_etale_chart_fibre B S hS f' hF i hAU
    (schemePointRepresentative B S hS U x) hiE hiS hh
  exact ⟨fun h => (geometricallyReduced_fibreObject_iff B S hS hAU x).1
      ((isGeometricallyReduced_iff_forall_etaleChart
        (schemePointRepresentative B S hS U x).carrier B
        (schemePointRepresentative B S hS U x).contained _ _).1 h _ α hαE),
    fun h => (isGeometricallyReduced_iff_exists_surjective_etaleChart
      (schemePointRepresentative B S hS U x).carrier B
      (schemePointRepresentative B S hS U x).contained _ _).2
      ⟨_, α, hαS, hαE, (geometricallyReduced_fibreObject_iff B S hS hAU x).2 h⟩⟩

/-- **The geometrically reduced fibre locus read on a surjective étale chart.** If
`i : h_A ⟶ F` is a surjective étale chart of an algebraic space over `h_U` and `A ⟶ U` is the
induced morphism of the site, then the points of `|h_U|` at which the fibre of `F ⟶ h_U` is
geometrically reduced are exactly those whose image in the scheme `U` has geometrically
reduced fibre for the morphism of schemes `A ⟶ U`.

This is `AlgebraicGeometry.Space.isGeometricallyReducedFibre_iff_geometricallyReduced_fiber`
read through the identification of `|h_U|` with the points of `U`, every point of `U` having
the canonical field-valued representative above it. -/
theorem geometricallyReducedFibreLocus_eq_preimage_chart
    (hiE : IsEtale B S hS i) (hiS : IsSurjective B S hS i) (hh : yoneda.map hAU = i ≫ f') :
    geometricallyReducedFibreLocus B S hS f' hF (isAlgebraicSpace_yoneda B S hS U) =
      schemePointsHomeomorph B S hS U ⁻¹'
        {x | GeometricallyReduced
          (((BigFppfOver.toScheme B S hS).map hAU).fiberToSpecResidueField x)} := by
  ext y
  obtain ⟨x, rfl⟩ := (schemePointsHomeomorph B S hS U).symm.surjective y
  simp only [Set.mem_preimage, Homeomorph.apply_symm_apply, Set.mem_setOf_eq]
  rw [← class_schemePointRepresentative B S hS U x, mem_geometricallyReducedFibreLocus_iff]
  exact isGeometricallyReducedFibre_iff_geometricallyReduced_fiber B S hS f' hF i hAU hiE hiS
    hh x

end Chart

/-! ### Stacks 0E0A -/

/-- **Stacks 0E0A.** For a quasi-compact morphism of algebraic spaces over `S` which is
locally of finite presentation, the set of points of `|Y|` whose fibre is geometrically reduced
is étale locally constructible.

Constructibility is tested on an affine étale chart `h_V ⟶ Y`. There the locus is, by
Stacks 0E09, the locus of the base change `X ×_Y h_V ⟶ h_V`, which is a quasi-compact algebraic
space and so has an affine surjective étale chart `h_A ⟶ X ×_Y h_V`. The induced morphism of
affine schemes `A ⟶ V` is of finite presentation, its scheme-theoretic fibres are surjective
étale charts of the fibres of the base change, and so the locus is the geometrically reduced
fibre locus of `A ⟶ V`; that set is locally constructible by Stacks 0579. -/
@[stacks 0E0A, ega "IV 9.7.7" "more general"]
theorem isEtaleLocallyConstructible_geometricallyReducedFibreLocus
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsQuasiCompact B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f) :
    IsEtaleLocallyConstructible B S hS Y (geometricallyReducedFibreLocus B S hS f hX hY) := by
  refine (forall_etale_iff_forall_affine_etale B S hS Y _).2 fun U hU g hg ↦ ?_
  let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  have hP := isAlgebraicSpace_pullback B S hS f g hX hUalg hY
  have hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompactSpace_yoneda_obj B S hS
      (Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj U))
  have hPqc : IsQuasiCompactSpace B S hS (pullback f g) :=
    isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry g f)
      (hf (yoneda.obj U) hUalg hUqc g)
  obtain ⟨A, i, hA, hiSp, hiE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (pullback f g) hP).1
      hPqc
  let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hA
  have hiS : IsSurjective B S hS i :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS (pullback f g) hP A i).1 hiSp
  obtain ⟨hAU, hh⟩ : ∃ hAU : A ⟶ U, yoneda.map hAU = i ≫ pullback.snd f g :=
    ⟨yoneda.preimage (i ≫ pullback.snd f g), yoneda.map_preimage _⟩
  have hfstE : IsEtale B S hS (pullback.fst f g) :=
    isEtale_of_isPullback B S hS _ _ _ _
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk g : (⟨yoneda.obj U, hUalg⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨Y, hY⟩)).flip hg
  have hcomm : yoneda.map hAU ≫ g = (i ≫ pullback.fst f g) ≫ f := by
    rw [hh, Category.assoc, Category.assoc, pullback.condition]
  have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map hAU) :=
    hfp A U (i ≫ pullback.fst f g) g hAU
      ((isEtale_iff_presheaf_of_yoneda B S hS _).1 (isEtale_comp B S hS hiE hfstE))
      ((isEtale_iff_presheaf_of_yoneda B S hS g).1 hg) hcomm
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map hAU) := by
    have _ : _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map hAU) := inferInstance
    infer_instance
  have hcon := isLocallyConstructible_geometricallyReduced_fiber_of_isAffine_source
    ((BigFppfOver.toScheme B S hS).map hAU) ⟨inferInstance, inferInstance, inferInstance⟩
  rw [← geometricallyReducedFibreLocus_pullback B S hS f g hX hY hUalg]
  refine ((schemePointsHomeomorph B S hS U).symm.isConstructible_preimage_iff _).mp ?_
  rw [geometricallyReducedFibreLocus_eq_preimage_chart B S hS (pullback.snd f g) hP i hAU hiE hiS
    hh, Set.preimage_preimage]
  simpa using hcon.isConstructible

/-! ### The fibre locus of a morphism of representables -/

/-- **The fibre of a morphism of schemes, read as algebraic spaces.** The fibre of
`h_A ⟶ h_U` at the point of `|h_U|` corresponding to a point `x` of `U` is geometrically reduced
exactly when the scheme-theoretic fibre of `A ⟶ U` at `x` is geometrically reduced over the
residue field. The identity of `h_A` is a surjective étale chart of `h_A`. -/
theorem isGeometricallyReducedFibreAt_yoneda_map_iff {U A : BigFppfOver B S hS} (g : A ⟶ U)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    IsGeometricallyReducedFibreAt B S hS (yoneda.map g) (isAlgebraicSpace_yoneda B S hS A)
        (isAlgebraicSpace_yoneda B S hS U) ((schemePointsHomeomorph B S hS U).symm x) ↔
      GeometricallyReduced
        (((BigFppfOver.toScheme B S hS).map g).fiberToSpecResidueField x) := by
  rw [← class_schemePointRepresentative B S hS U x, isGeometricallyReducedFibreAt_class_iff]
  exact isGeometricallyReducedFibre_iff_geometricallyReduced_fiber B S hS (yoneda.map g)
    (isAlgebraicSpace_yoneda B S hS A) (𝟙 _) g (fun _ _ hφ => by simpa using hφ)
    (fun y => ⟨y, congrFun (pointsMap_id B S hS _) y⟩) (Category.id_comp _).symm x

/-- A morphism of schemes `A ⟶ U` of the site is geometrically reduced exactly when every fibre
of the morphism of algebraic spaces `h_A ⟶ h_U` is geometrically reduced (Stacks 0E08). -/
theorem forall_isGeometricallyReducedFibreAt_yoneda_map_iff {U A : BigFppfOver B S hS}
    (g : A ⟶ U) :
    (∀ y, IsGeometricallyReducedFibreAt B S hS (yoneda.map g) (isAlgebraicSpace_yoneda B S hS A)
        (isAlgebraicSpace_yoneda B S hS U) y) ↔
      GeometricallyReduced ((BigFppfOver.toScheme B S hS).map g) := by
  have hfib : GeometricallyReduced ((BigFppfOver.toScheme B S hS).map g) ↔
      ∀ x, GeometricallyReduced
        (((BigFppfOver.toScheme B S hS).map g).fiberToSpecResidueField x) := by
    simp only [GeometricallyReduced.eq_geometrically,
      ← geometrically_iff_forall_fiberToSpecResidueField]
  rw [hfib]
  refine ⟨fun h x => (isGeometricallyReducedFibreAt_yoneda_map_iff B S hS g x).1 (h _),
    fun h y => ?_⟩
  obtain ⟨x, rfl⟩ := (schemePointsHomeomorph B S hS U).symm.surjective y
  exact (isGeometricallyReducedFibreAt_yoneda_map_iff B S hS g x).2 (h x)

end Space

end AlgebraicGeometry

end
