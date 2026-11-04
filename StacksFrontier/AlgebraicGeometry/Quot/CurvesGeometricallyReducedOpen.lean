module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReducedLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReducedOpenLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# Families of curves with geometrically reduced fibres (Stacks 0E0G)

Stacks 0E0G produces the open substack `Curves^{geomred} ⊂ Curves` of families of curves whose
fibres are geometrically reduced (Stacks 0E08). Its proof: the locus of points of the base with
geometrically reduced fibre is open (Stacks 0E0C), its formation commutes with arbitrary base
change (Stacks 0E09), so the method of Section 0E0E applies.

## Main definitions

* `AlgebraicGeometry.IsGeometricallyReducedFamily`: every fibre of the family is geometrically
  reduced, condition (1)(b) of Stacks 0E0G.
* `AlgebraicGeometry.CurveFamily.geometricallyReducedBaseLocus`: the set of points of the base
  with geometrically reduced fibre.

## Main results

* `AlgebraicGeometry.Space.geometricallyReducedFibreLocus_iso_comp`: the locus is unchanged by
  precomposing with an isomorphism of the source.
* `AlgebraicGeometry.CurveFamily.preimage_geometricallyReducedBaseLocus`: for a morphism of
  families of curves, the locus of the source is the inverse image of the locus of the target,
  Stacks 0E09 read on the cartesian square of the morphism.
* `AlgebraicGeometry.isOpenCurvesLocus_isGeometricallyReducedFamily_of_isOpen`: condition (o)
  of Section 0E0E for `Curves^{geomred}`, from the openness of the locus of Stacks 0E0C.
* `AlgebraicGeometry.isGeometricallyReducedFamily_curveFamilyOfSchemeMorphism_iff_over_field`:
  for a proper scheme of dimension at most one over a field, the family has geometrically reduced
  fibres exactly when the scheme is geometrically reduced over the field (Stacks 035V).
* `AlgebraicGeometry.curvesGeometricallyReduced_isOpenSubstack`,
  `AlgebraicGeometry.factors_curvesGeometricallyReduced_iff` and
  `AlgebraicGeometry.factors_curvesGeometricallyReduced_over_field_iff`: the open substack of
  Stacks 0E0G and its parts (1) and (2), for any proof `h0E0C` of the statement of Stacks 0E0C.
* `AlgebraicGeometry.isOpenCurvesLocus_curvesGeomred`: condition (o) of Section 0E0E for
  `Curves^{geomred}`, from `AlgebraicGeometry.Space.isOpen_geometricallyReducedFibreLocus`
  (Stacks 0E0C).
* `AlgebraicGeometry.curvesGeomred_isOpenSubstack`, `AlgebraicGeometry.factors_curvesGeomred_iff`,
  `AlgebraicGeometry.factors_curvesGeomred_over_field_iff` and
  `AlgebraicGeometry.curvesGeomred_isOpenSubstack_and_factors_iff`: **Stacks 0E0G**, the open
  substack, its parts (1) and (2), and the whole statement.
* `AlgebraicGeometry.exists_curvesGeomred_openSubstack`: the open substack of the small model
  `AlgebraicGeometry.curvesAlgebraicStack` of the stack of curves, given that the stack of curves
  is algebraic (the statement of Stacks 0D5A).

## Implementation notes

The results with the argument `h0E0C` are stated for any proof of the statement of Stacks 0E0C;
the library proves it as `AlgebraicGeometry.Space.isOpen_geometricallyReducedFibreLocus`, and the
results of the last section are those results at that proof.

As in the rest of this library's open substacks of `Curves` (Section 0E0E), an open substack is a
strictly full subcategory of the category of families of curves whose inclusion is representable
by algebraic spaces and an open immersion; nothing about it uses that `Curves` is algebraic.

## References

* [Stacks Project, Tag 0E0G](https://stacks.math.columbia.edu/tag/0E0G)
* [Stacks Project, Tag 0E08](https://stacks.math.columbia.edu/tag/0E08)
* [Stacks Project, Tag 0E09](https://stacks.math.columbia.edu/tag/0E09)
* [Stacks Project, Tag 0E0C](https://stacks.math.columbia.edu/tag/0E0C)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The geometrically reduced fibre locus of a morphism of algebraic spaces does not change when
the morphism is precomposed with an isomorphism of the source: the fibres over every
field-valued point are isomorphic. -/
theorem geometricallyReducedFibreLocus_iso_comp {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X' ≅ X) (f : X ⟶ Y) (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    geometricallyReducedFibreLocus B S hS (e.hom ≫ f) hX' hY =
      geometricallyReducedFibreLocus B S hS f hX hY := by
  ext y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  refine (mem_geometricallyReducedFibreLocus_iff B S hS (e.hom ≫ f) hX' hY p).trans
    (Iff.trans ?_ (mem_geometricallyReducedFibreLocus_iff B S hS f hX hY p).symm)
  let g : B.obj p.contained ⟶ B.obj hS := ⟨p.toBase⟩
  let R := OverShriek.relocalizeRestrict g
  let σ := restrictedSection B S hS Y p.contained g p.value
  have hiso := pullback.map_isIso (R.map (e.hom ≫ f)) σ (R.map f) σ (R.map e.hom) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, Functor.map_comp]) (by rw [Category.comp_id, Category.id_comp])
  exact isGeometricallyReduced_congr_iso p.carrier B p.contained _ _ (@asIso _ _ _ _ _ hiso)

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The set of points of the base of a family of curves whose fibre is geometrically reduced
(Stacks 0E08). -/
def CurveFamily.geometricallyReducedBaseLocus (X : CurveFamily B hZ) :
    Set (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
  Space.geometricallyReducedFibreLocus B integerBase hZ X.toBase.hom X.total.property
    (schemeSpace X.base).property

/-- Condition (1)(b) of Stacks 0E0G: every fibre of the family of curves is geometrically
reduced (Stacks 0E08). -/
abbrev IsGeometricallyReducedFamily : ObjectProperty (CurveFamily B hZ) := fun X =>
  ∀ y, Space.IsGeometricallyReducedFibreAt B integerBase hZ X.toBase.hom X.total.property
    (schemeSpace X.base).property y

/-- **Stacks 0E09 for families of curves.** For a morphism of families of curves, the locus of
points of the base of the source with geometrically reduced fibre is the inverse image of that
locus of the target under the morphism of base schemes. -/
theorem CurveFamily.preimage_geometricallyReducedBaseLocus {X Y : CurveFamily B hZ}
    (φ : X ⟶ Y) :
    Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        CurveFamily.geometricallyReducedBaseLocus B hZ Y =
      CurveFamily.geometricallyReducedBaseLocus B hZ X := by
  have sq := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  rw [geometricallyReducedBaseLocus, geometricallyReducedBaseLocus,
    ← Space.geometricallyReducedFibreLocus_pullback B integerBase hZ Y.toBase.hom
      (schemeSpaceMap φ.baseMap).hom Y.total.property (schemeSpace Y.base).property
      (schemeSpace X.base).property,
    ← sq.isoPullback_hom_snd]
  exact (Space.geometricallyReducedFibreLocus_iso_comp B integerBase hZ sq.isoPullback _ _ _ _).symm

/-- A family of curves has geometrically reduced fibres exactly when its locus of points with
geometrically reduced fibre is the whole base. -/
theorem isGeometricallyReducedFamily_iff_geometricallyReducedBaseLocus_eq_univ
    (X : CurveFamily B hZ) :
    IsGeometricallyReducedFamily B hZ X ↔
      CurveFamily.geometricallyReducedBaseLocus B hZ X = Set.univ :=
  Set.eq_univ_iff_forall.symm

/-- Geometric reducedness of the fibres passes from a family of curves to every family mapping
to it. -/
theorem CurveFamily.isGeometricallyReducedFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsGeometricallyReducedFamily B hZ Y) : IsGeometricallyReducedFamily B hZ X := by
  rw [isGeometricallyReducedFamily_iff_geometricallyReducedBaseLocus_eq_univ,
    ← CurveFamily.preimage_geometricallyReducedBaseLocus B hZ φ,
    (isGeometricallyReducedFamily_iff_geometricallyReducedBaseLocus_eq_univ B hZ Y).mp hY,
    Set.preimage_univ]

/-- **Condition (o) of Section 0E0E for `Curves^{geomred}`**, from the openness of the
geometrically reduced fibre locus (the assertion of Stacks 0E0C, taken as the argument
`hopen`): a family of curves mapping to `G` has geometrically reduced fibres exactly when its
morphism of base schemes sends every point into the locus of `G`. -/
theorem isOpenCurvesLocus_isGeometricallyReducedFamily_of_isOpen
    (hopen : ∀ G : CurveFamily B hZ, IsOpen (CurveFamily.geometricallyReducedBaseLocus B hZ G)) :
    IsOpenCurvesLocus B hZ (IsGeometricallyReducedFamily B hZ) := by
  refine IsOpenCurvesLocus.of_points fun G => ⟨_, hopen G, fun F a => ?_⟩
  rw [isGeometricallyReducedFamily_iff_geometricallyReducedBaseLocus_eq_univ,
    ← CurveFamily.preimage_geometricallyReducedBaseLocus B hZ a, Set.range_subset_iff,
    Set.eq_univ_iff_forall]
  rfl

/-! ### Part (2): the family of a proper scheme over a field -/

/-- The family of curves attached to a proper flat morphism of schemes of finite presentation
`g : T ⟶ W` has geometrically reduced fibres exactly when `g` is geometrically reduced. -/
theorem isGeometricallyReducedFamily_curveFamilyOfSchemeMorphism_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsGeometricallyReducedFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      GeometricallyReduced ((BigFppfOver.toScheme B integerBase hZ).map g) :=
  Space.forall_isGeometricallyReducedFibreAt_yoneda_map_iff B integerBase hZ g

/-- **Condition (2)(b) of Stacks 0E0G.** Let `X` be a proper scheme of dimension at most one
over a field `k`, presented by a proper flat morphism of finite presentation `T ⟶ W` of the site
with `W` the spectrum of `k`. The family of curves attached to it has geometrically reduced
fibres exactly when `X` is geometrically reduced over `k` (Stacks 035V). -/
theorem isGeometricallyReducedFamily_curveFamilyOfSchemeMorphism_iff_over_field
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hk : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k)) :
    IsGeometricallyReducedFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      IsGeometricallyReducedOver ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hk) := by
  have _ : MorphismProperty.RespectsIso (@GeometricallyReduced : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [isGeometricallyReducedFamily_curveFamilyOfSchemeMorphism_iff]
  exact (MorphismProperty.cancel_right_of_respectsIso _ _ _).symm.trans
    (geometricallyReduced_iff_forall_isGeometricallyReducedAt _)

/-! ### The open substack `Curves^{geomred}` -/

section OpenSubstack

variable (h0E0C : ∀ {X Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B integerBase hZ X) (hY : IsAlgebraicSpace B integerBase hZ Y),
    Space.IsFlat B integerBase hZ f → Space.IsProper B integerBase hZ f →
      Space.IsFinitePresentation B integerBase hZ f →
      IsOpen (Space.geometricallyReducedFibreLocus B integerBase hZ f hX hY))

include h0E0C

/-- Condition (o) of Section 0E0E for `Curves^{geomred}`, from the openness of the
geometrically reduced fibre locus of a flat proper morphism of finite presentation, the
statement of Stacks 0E0C, for any proof `h0E0C` of it. At the library's proof
`AlgebraicGeometry.Space.isOpen_geometricallyReducedFibreLocus` this is
`AlgebraicGeometry.isOpenCurvesLocus_curvesGeomred`. -/
theorem isOpenCurvesLocus_isGeometricallyReducedFamily :
    IsOpenCurvesLocus B hZ (IsGeometricallyReducedFamily B hZ) :=
  isOpenCurvesLocus_isGeometricallyReducedFamily_of_isOpen B hZ fun G =>
    h0E0C G.toBase.hom G.total.property (schemeSpace G.base).property G.flat G.proper
      G.finitePresentation

/-- **Stacks 0E0G, the open substack**, for any proof `h0E0C` of the statement of Stacks 0E0C
(at the library's proof this is `AlgebraicGeometry.curvesGeomred_isOpenSubstack`).
`Curves^{geomred}`, the strictly full subcategory of families of curves with geometrically
reduced fibres, is an open substack of `Curves`: its inclusion is representable by algebraic
spaces and an open immersion. -/
theorem curvesGeometricallyReduced_isOpenSubstack :
    ObjectProperty.IsClosedUnderIsomorphisms (IsGeometricallyReducedFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ _
          (isOpenCurvesLocus_isGeometricallyReducedFamily B hZ h0E0C).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ _
          (isOpenCurvesLocus_isGeometricallyReducedFamily B hZ h0E0C).prop_of_hom) :=
  isOpenImmersion_curvesSubstackInclusion
    (isOpenCurvesLocus_isGeometricallyReducedFamily B hZ h0E0C)

/-- **Stacks 0E0G, part (1)**, for any proof `h0E0C` of the statement of Stacks 0E0C (at the
library's proof this is `AlgebraicGeometry.factors_curvesGeomred_iff`). The classifying morphism of
a family of curves `X ⟶ S` factors through `Curves^{geomred}` exactly when the fibres of
`X ⟶ S` are geometrically reduced (Stacks 0E08). -/
theorem factors_curvesGeometricallyReduced_iff (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        (IsGeometricallyReducedFamily B hZ).FullSubcategory,
        z ⋙ (IsGeometricallyReducedFamily B hZ).ι = y) ↔
      IsGeometricallyReducedFamily B hZ (y.obj (Over.mk (𝟙 U.left))) :=
  factors_curvesSubstack_iff (isOpenCurvesLocus_isGeometricallyReducedFamily B hZ h0E0C) U y hy

/-- **Stacks 0E0G, part (2)**, for any proof `h0E0C` of the statement of Stacks 0E0C. Let `X`
be a proper scheme of dimension at most one over a field `k`, presented by a proper flat morphism
of finite presentation `T ⟶ W` of the site with `W` the spectrum of `k`. The classifying morphism
of `X` factors through `Curves^{geomred}` exactly when `X` is geometrically reduced over `k`. For
`X` given as a scheme over `Spec k` alone, at the library's proof of Stacks 0E0C, see
`AlgebraicGeometry.factors_curvesGeomred_over_field_iff`. -/
theorem factors_curvesGeometricallyReduced_over_field_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hk : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅
      curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        (IsGeometricallyReducedFamily B hZ).FullSubcategory,
        z ⋙ (IsGeometricallyReducedFamily B hZ).ι = y) ↔
      IsGeometricallyReducedOver ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hk) := by
  rw [factors_curvesSubstack_iff_of_iso (isOpenCurvesLocus_isGeometricallyReducedFamily B hZ h0E0C)
    U y hy _ e]
  exact isGeometricallyReducedFamily_curveFamilyOfSchemeMorphism_iff_over_field B hZ g hflat
    hproper hlfp hqc hsep hqsep hdim k hk

end OpenSubstack

/-! ### Part (2) for a proper scheme over a field -/

/-- **Condition (2)(b) of Stacks 0E0G for a proper scheme over a field.** The family of curves of
a proper scheme `X` of dimension at most one over a field `k` has geometrically reduced fibres
exactly when `X` is geometrically reduced over `k` (Stacks 035V). -/
theorem isGeometricallyReducedFamily_curveFamilyOfScheme_iff
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) :
    IsGeometricallyReducedFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      IsGeometricallyReducedOver X.hom := by
  let g := integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk
    X.hom
  have hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom :=
    Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g
      (inferInstanceAs (QuasiCompact X.hom))
  have hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 (inferInstanceAs (IsSeparated X.hom))
  have hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2
      (inferInstanceAs (QuasiSeparated X.hom))
  exact (isGeometricallyReducedFamily_curveFamilyOfSchemeMorphism_iff B hZ g
    (inferInstanceAs (Flat X.hom)) (inferInstanceAs (IsProper X.hom))
    (inferInstanceAs (LocallyOfFinitePresentation X.hom)) hqc hsep hqsep hdim).trans
    (geometricallyReduced_iff_forall_isGeometricallyReducedAt X.hom)

/-! ### Stacks 0E0G -/

/-- **Condition (o) of Section 0E0E for `Curves^{geomred}`.** A family of curves mapping to a
family `G` has geometrically reduced fibres exactly when its morphism of base schemes sends every
point into the locus of points of the base of `G` with geometrically reduced fibre, which is open
by Stacks 0E0C (`AlgebraicGeometry.Space.isOpen_geometricallyReducedFibreLocus`). -/
@[ega "IV 12.2.4" "(v), special case"]
theorem isOpenCurvesLocus_curvesGeomred :
    IsOpenCurvesLocus B hZ (IsGeometricallyReducedFamily B hZ) :=
  isOpenCurvesLocus_isGeometricallyReducedFamily B hZ
    (Space.isOpen_geometricallyReducedFibreLocus B integerBase hZ)

/-- **Stacks 0E0G, the open substack.** `Curves^{geomred}`, the strictly full subcategory of
families of curves whose fibres are geometrically reduced (Stacks 0E08), is an open substack of
`Curves`: its inclusion is representable by algebraic spaces and an open immersion. -/
@[stacks 0E0G "the open substack Curves^{geomred} of Curves"]
theorem curvesGeomred_isOpenSubstack :
    ObjectProperty.IsClosedUnderIsomorphisms (IsGeometricallyReducedFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ _ (isOpenCurvesLocus_curvesGeomred B hZ).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ _ (isOpenCurvesLocus_curvesGeomred B hZ).prop_of_hom) :=
  isOpenImmersion_curvesSubstackInclusion (isOpenCurvesLocus_curvesGeomred B hZ)

/-- **Stacks 0E0G, part (1).** The classifying morphism of a family of curves `X ⟶ S` factors
through `Curves^{geomred}` exactly when the fibres of `X ⟶ S` are geometrically reduced
(Stacks 0E08). -/
@[stacks 0E0G "part (1): the classifying morphism of a family of curves factors through \
Curves^{geomred} iff the fibres of the family are geometrically reduced"]
theorem factors_curvesGeomred_iff (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        (IsGeometricallyReducedFamily B hZ).FullSubcategory,
        z ⋙ (IsGeometricallyReducedFamily B hZ).ι = y) ↔
      IsGeometricallyReducedFamily B hZ (y.obj (Over.mk (𝟙 U.left))) :=
  factors_curvesSubstack_iff (isOpenCurvesLocus_curvesGeomred B hZ) U y hy

/-- **Stacks 0E0G, part (2).** Let `X` be a proper scheme of dimension at most one over a field
`k` (with `Spec k` in the site, so that the classifying morphism `Spec k ⟶ Curves` of `X`
exists). The classifying morphism of `X` factors through `Curves^{geomred}` exactly when `X` is
geometrically reduced over `k`. -/
@[stacks 0E0G "part (2): for a proper scheme of dimension at most one over a field, the \
classifying morphism factors through Curves^{geomred} iff the scheme is geometrically reduced \
over the field"]
theorem factors_curvesGeomred_over_field_iff
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        (IsGeometricallyReducedFamily B hZ).FullSubcategory,
        z ⋙ (IsGeometricallyReducedFamily B hZ).ι = y) ↔
      IsGeometricallyReducedOver X.hom := by
  rw [factors_curvesSubstack_iff_of_iso (isOpenCurvesLocus_curvesGeomred B hZ) U y hy _ e]
  exact isGeometricallyReducedFamily_curveFamilyOfScheme_iff B hZ k hk X hdim

/-- **Stacks 0E0G.** There is an open substack `Curves^{geomred} ⊂ Curves` — the strictly full
subcategory of families of curves with geometrically reduced fibres, whose inclusion is
representable by algebraic spaces and an open immersion — such that (1) the classifying morphism
of a family of curves `X ⟶ S` factors through it exactly when the fibres of `X ⟶ S` are
geometrically reduced (Stacks 0E08), and (2) for a proper scheme `X` of dimension at most one
over a field `k`, the classifying morphism of `X` factors through it exactly when `X` is
geometrically reduced over `k`. -/
@[stacks 0E0G "the whole statement: the open substack Curves^{geomred} and parts (1) and (2)"]
theorem curvesGeomred_isOpenSubstack_and_factors_iff :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsGeometricallyReducedFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ _ (isOpenCurvesLocus_curvesGeomred B hZ).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ _ (isOpenCurvesLocus_curvesGeomred B hZ).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          (IsGeometricallyReducedFamily B hZ).FullSubcategory,
          z ⋙ (IsGeometricallyReducedFamily B hZ).ι = y) ↔
        IsGeometricallyReducedFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          (IsGeometricallyReducedFamily B hZ).FullSubcategory,
          z ⋙ (IsGeometricallyReducedFamily B hZ).ι = y) ↔
        IsGeometricallyReducedOver X.hom)) :=
  ⟨curvesGeomred_isOpenSubstack B hZ, factors_curvesGeomred_iff B hZ,
    factors_curvesGeomred_over_field_iff B hZ⟩

section SmallModel

universe w

/-- **Stacks 0E0G on the small model of the stack of curves.** Given that the stack of curves is
algebraic (`h`, the statement of Tag 0D5A), its small model
`AlgebraicGeometry.curvesAlgebraicStack` has an open substack whose objects are exactly the
families of curves with geometrically reduced fibres; in particular a proper scheme `X` of
dimension at most one over a field lies in it exactly when `X` is geometrically reduced over the
field. This takes `h` and so is unregistered. -/
theorem exists_curvesGeomred_openSubstack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    ∃ U : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
      (∀ F : CurveFamily B hZ,
        U.property ((curvesSmallEquivalence B hZ h).functor.obj F) ↔
          IsGeometricallyReducedFamily B hZ F) ∧
      ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
        (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1),
        U.property ((curvesSmallEquivalence B hZ h).functor.obj
            (curveFamilyOfScheme X B hZ hk hdim)) ↔
          IsGeometricallyReducedOver X.hom :=
  ⟨curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_curvesGeomred B hZ),
    curvesSmallOpenSubstack_property_iff B hZ h _,
    fun k _ hk X _ hdim => (curvesSmallOpenSubstack_property_iff B hZ h _ _).trans
      (isGeometricallyReducedFamily_curveFamilyOfScheme_iff B hZ k hk X hdim)⟩

end SmallModel

end AlgebraicGeometry

end
