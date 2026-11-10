module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting a groupoid in algebraic spaces over a field extension

Let `G` be a groupoid in algebraic spaces over `S` whose object space is the algebraic space
of the spectrum of a field `k`, and let `k ⊆ k'` be a field extension. The restriction of `G`
along the induced morphism `Spec k' ⟶ Spec k` of object spaces is built from the fibre-product
diagram

```
        R'  ⟶  Spec k' ×_{Spec k} R  ⟶  R
        ↓            ↓                  ↓
  R ×_{Spec k} Spec k'  ⟶  Spec k'  ⟶  Spec k
```

Every arrow occurring in that diagram — the morphism of object spaces, the source and target
of `G`, the four projections of the two intermediate fibre products, the two projections of the
arrow space of the restriction, and the source, target and canonical map to `R` of the
restriction — is surjective, flat and universally open. The canonical map from the arrows of
the restriction to the arrows of `G` is in addition affine.

## Main definitions

* `AlgebraicGeometry.Space.fieldSpace`: the spectrum of a field over `S`, as an algebraic
  space over `S`.
* `AlgebraicGeometry.Space.fieldSpaceMap`: the morphism of algebraic spaces induced by a
  field extension.
* `AlgebraicGeometry.Space.restrictionObjectMap`: that morphism, read as a morphism to the
  object space of a groupoid whose object space is prescribed to be `fieldSpace`.
* `AlgebraicGeometry.Space.RestrictionDiagramMap`: the arrows of the diagram defining the
  restriction.

## Main results

* `AlgebraicGeometry.Space.isSurjective_of_restrictionDiagramMap`,
  `AlgebraicGeometry.Space.isFlat_of_restrictionDiagramMap` and
  `AlgebraicGeometry.Space.universallyOpen_of_restrictionDiagramMap`: **Stacks 06E1**, every
  arrow of the diagram is surjective, flat and universally open.
* `AlgebraicGeometry.Space.isAffineHom_restrictionArrowsToArrows`: **Stacks 06E1**, the
  canonical map from the arrows of the restriction to the arrows of `G` is affine.

## Implementation notes

The arrows of the diagram are collected into the inductive predicate
`AlgebraicGeometry.Space.RestrictionDiagramMap` on morphisms of algebraic spaces, so that the
three universal assertions of the tag are single statements quantified over that predicate
rather than a list of a dozen separate lemmas; the fourth assertion concerns one named arrow
only and is stated for it.

Flatness and universal openness of the arrows pointing at the object space need no hypothesis
beyond the object space being a field spectrum: a morphism of schemes whose target is the
spectrum of a field is flat and universally open, and both properties are étale local on source
and target, so they can be checked on one surjective étale chart. Surjectivity of the source
and target of `G` comes from the identity arrows, read off the evaluated groupoid at each test
object. Everything else is stability of the three properties under base change and composition,
Stacks 03MG, 03MH, 03MN, 03MO, 03Z3 and 03Z4, together with the affine analogues 03WH and
03WI.

The hypothesis on the object space is an *equality* `G.objects = fieldSpace ...`, not an
isomorphism, because that is the shape in which the situation arises: the object space is
prescribed. The morphism `restrictionObjectMap` therefore carries an `eqToHom`, whose
surjectivity, flatness, universal openness and affineness are those of an isomorphism.

## References

* [Stacks Project, Tag 06E1](https://stacks.math.columbia.edu/tag/06E1)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

/-- The spectrum of a field, with a structure morphism to the base, regarded as an algebraic
space over the base. -/
noncomputable def fieldSpace {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)
    {k : Type u} [Field k] (hk : C.Contains (Spec (.of k)))
    (structureMap : Spec (.of k) ⟶ S) :
    AlgebraicSpaces C S hS :=
  schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))

/-- The morphism between the algebraic spaces of two field spectra induced by a field
extension. -/
noncomputable def fieldSpaceMap {S : Scheme.{u}} (C : BigFppfSite.{u})
    (hS : C.Contains S) {k k' : Type u} [Field k] [Field k']
    (hk : C.Contains (Spec (.of k))) (hk' : C.Contains (Spec (.of k')))
    (structureMap : Spec (.of k) ⟶ S) (i : k →+* k') :
    fieldSpace C hS hk' (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) ⟶
      fieldSpace C hS hk structureMap :=
  schemeSpaceMap
    (Over.homMk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op⟩ :
      C.obj hk' ⟶ C.obj hk) rfl)

/-- The morphism induced by a field extension, read as a morphism to the object space of a
groupoid in algebraic spaces whose object space is the spectrum of the smaller field. This is
the morphism along which the groupoid is restricted. -/
noncomputable def restrictionObjectMap {S : Scheme.{u}} (C : BigFppfSite.{u})
    (hS : C.Contains S) {k k' : Type u} [Field k] [Field k']
    (hk : C.Contains (Spec (.of k))) (hk' : C.Contains (Spec (.of k')))
    (structureMap : Spec (.of k) ⟶ S) (i : k →+* k')
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (hU : G.objects = fieldSpace C hS hk structureMap) :
    fieldSpace C hS hk' (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) ⟶
      G.objects :=
  fieldSpaceMap C hS hk hk' structureMap i ≫ eqToHom hU.symm

/-- The arrows of the diagram defining the restriction of a groupoid in algebraic spaces over
a field extension: the morphism of object spaces, the source and target of the groupoid, the
projections of the two intermediate fibre products, the two projections onto them, and the
source, the target and the canonical map to the arrows of the groupoid of the restriction. -/
inductive RestrictionDiagramMap {S : Scheme.{u}}
    (C : BigFppfSite.{u}) (hS : C.Contains S)
    {k k' : Type u} [Field k] [Field k']
    (hk : C.Contains (Spec (.of k))) (hk' : C.Contains (Spec (.of k')))
    (structureMap : Spec (.of k) ⟶ S) (i : k →+* k')
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (hU : G.objects = fieldSpace C hS hk structureMap) :
    {X Y : AlgebraicSpaces C S hS} → (X ⟶ Y) → Prop where
  /-- The morphism of object spaces induced by the field extension. -/
  | fieldExtension : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (restrictionObjectMap C hS hk hk' structureMap i G hU)
  /-- The source of the groupoid. -/
  | source : RestrictionDiagramMap C hS hk hk' structureMap i G hU G.source
  /-- The target of the groupoid. -/
  | target : RestrictionDiagramMap C hS hk hk' structureMap i G hU G.target
  /-- The projection of `R ×_{s, U, g} U'` to the arrows of the groupoid. -/
  | sourceBase : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (fiberProductFst G.source
        (restrictionObjectMap C hS hk hk' structureMap i G hU))
  /-- The projection of `R ×_{s, U, g} U'` to the larger field spectrum. -/
  | sourceExtension : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (fiberProductSnd G.source
        (restrictionObjectMap C hS hk hk' structureMap i G hU))
  /-- The projection of `U' ×_{g, U, t} R` to the larger field spectrum. -/
  | targetExtension : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (fiberProductFst
        (restrictionObjectMap C hS hk hk' structureMap i G hU) G.target)
  /-- The projection of `U' ×_{g, U, t} R` to the arrows of the groupoid. -/
  | targetBase : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (fiberProductSnd
        (restrictionObjectMap C hS hk hk' structureMap i G hU) G.target)
  /-- The projection of the arrows of the restriction to `R ×_{s, U, g} U'`. -/
  | arrowsToSourcePullback : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (fiberProductSnd
        (fiberProductSnd
          (restrictionObjectMap C hS hk hk' structureMap i G hU) G.target)
        (fiberProductFst G.source
          (restrictionObjectMap C hS hk hk' structureMap i G hU)))
  /-- The projection of the arrows of the restriction to `U' ×_{g, U, t} R`. -/
  | arrowsToTargetPullback : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (fiberProductFst
        (fiberProductSnd
          (restrictionObjectMap C hS hk hk' structureMap i G hU) G.target)
        (fiberProductFst G.source
          (restrictionObjectMap C hS hk hk' structureMap i G hU)))
  /-- The source of the restriction. -/
  | restrictedSource : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (restrictionSource G
        (restrictionObjectMap C hS hk hk' structureMap i G hU))
  /-- The target of the restriction. -/
  | restrictedTarget : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (restrictionTarget G
        (restrictionObjectMap C hS hk hk' structureMap i G hU))
  /-- The canonical map from the arrows of the restriction to the arrows of the groupoid. -/
  | restrictedArrowsToArrows : RestrictionDiagramMap C hS hk hk' structureMap i G hU
      (restrictionArrowsToArrows G
        (restrictionObjectMap C hS hk hk' structureMap i G hU))

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)
  {k k' : Type u} [Field k] [Field k']
  (hk : C.Contains (Spec (.of k))) (hk' : C.Contains (Spec (.of k')))
  (structureMap : Spec (.of k) ⟶ S) (i : k →+* k')
  {B : AlgebraicSpaces C S hS}
  (G : GroupoidInAlgebraicSpaces C S hS B)
  (hU : G.objects = fieldSpace C hS hk structureMap)

/-! ### Isomorphisms -/

section Isomorphisms

attribute [local instance] pointTopology

private theorem isSurjective_of_isIso {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) [IsIso f] : IsSurjective C S hS f :=
  (pointsHomeomorphOfIso C S hS (asIso f)).surjective

private theorem isOpenMorphism_of_isIso {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) [IsIso f] : IsOpenMorphism C S hS f :=
  (pointsHomeomorphOfIso C S hS (asIso f)).isOpenMap

private theorem universallyOpen_of_isIso {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) [IsIso f] : UniversallyOpen C S hS f := by
  intro Z _ g
  have : IsIso (pullback.fst g f) := (IsPullback.of_hasPullback g f).isIso_fst_of_isIso
  exact isOpenMorphism_of_isIso C hS (pullback.fst g f)

private theorem isAffineHom_of_isIso {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) [IsIso f] : IsAffineHom C S hS f := by
  intro Z g
  refine ⟨Z, g ≫ inv f, 𝟙 _, ?_⟩
  have hsq : IsPullback (g ≫ inv f) (yoneda.map (𝟙 _)) f g := by
    apply IsPullback.of_vert_isIso
    exact ⟨by simp⟩
  simpa using hsq

end Isomorphisms

/-! ### Base change along the chosen fibre products -/

private theorem isSurjective_fiberProductFst
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hg : IsSurjective C S hS g.hom) :
    IsSurjective C S hS (fiberProductFst f g).hom :=
  isSurjective_of_isPullback C S hS
    (AlgebraicSpaces.isPullback_fiberProduct C S hS f g).flip hg

private theorem isSurjective_fiberProductSnd
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsSurjective C S hS f.hom) :
    IsSurjective C S hS (fiberProductSnd f g).hom :=
  isSurjective_of_isPullback C S hS
    (AlgebraicSpaces.isPullback_fiberProduct C S hS f g) hf

private theorem isFlat_fiberProductFst
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hg : IsFlat C S hS g.hom) :
    IsFlat C S hS (fiberProductFst f g).hom :=
  (isFlat_isStableUnderBaseChange C S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct C S hS f g).flip hg

private theorem isFlat_fiberProductSnd
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsFlat C S hS f.hom) :
    IsFlat C S hS (fiberProductSnd f g).hom :=
  (isFlat_isStableUnderBaseChange C S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct C S hS f g) hf

private theorem isAffineHom_fiberProductFst
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hg : IsAffineHom C S hS g.hom) :
    IsAffineHom C S hS (fiberProductFst f g).hom :=
  IsAffineHom.of_isPullback (IsPullback.of_hasPullback f.hom g.hom).flip hg

private theorem isAffineHom_fiberProductSnd
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsAffineHom C S hS f.hom) :
    IsAffineHom C S hS (fiberProductSnd f g).hom :=
  IsAffineHom.of_isPullback (IsPullback.of_hasPullback f.hom g.hom) hf

private theorem universallyOpen_fiberProductFst
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hg : UniversallyOpen C S hS g.hom) :
    UniversallyOpen C S hS (fiberProductFst f g).hom :=
  universallyOpen_pullback C S hS Z.property Y.property X.property g.hom f.hom hg

private theorem universallyOpen_fiberProductSnd
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : UniversallyOpen C S hS f.hom) :
    UniversallyOpen C S hS (fiberProductSnd f g).hom := by
  have hproj : (pullbackSymmetry f.hom g.hom).hom ≫ pullback.fst g.hom f.hom =
      pullback.snd f.hom g.hom :=
    pullbackSymmetry_hom_comp_fst f.hom g.hom
  have hP : IsAlgebraicSpace C S hS (pullback f.hom g.hom) :=
    isAlgebraicSpace_pullback C S hS f.hom g.hom X.property Z.property Y.property
  have hP' : IsAlgebraicSpace C S hS (pullback g.hom f.hom) :=
    isAlgebraicSpace_pullback C S hS g.hom f.hom Z.property X.property Y.property
  have hfirst : UniversallyOpen C S hS (pullback.fst g.hom f.hom) :=
    universallyOpen_pullback C S hS X.property Y.property Z.property f.hom g.hom hf
  change UniversallyOpen C S hS (pullback.snd f.hom g.hom)
  rw [← hproj]
  exact universallyOpen_comp C S hS hP hP' Z.property _ _
    (universallyOpen_of_isIso C hS (pullbackSymmetry f.hom g.hom).hom) hfirst

/-! ### Surjectivity -/

/-- A morphism of presheaves on the big fppf site of `S` is surjective on points as soon as
every field-valued point of the target is in the image of a section of the source over the
same test object. -/
private theorem isSurjective_of_pointwise_lift
    {X Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (lift : ∀ p : FieldValuedPoint C S hS Y,
      ∃ a : X.obj (Opposite.op p.siteObject),
        f.app (Opposite.op p.siteObject) a = p.value) :
    IsSurjective C S hS f := by
  intro x
  refine Quot.inductionOn x ?_
  intro p
  obtain ⟨a, ha⟩ := lift p
  let q : FieldValuedPoint C S hS X :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := a }
  refine ⟨q.class C S hS X, ?_⟩
  change (FieldValuedPoint.map C S hS X f q).class C S hS Y = p.class C S hS Y
  apply Quot.sound
  refine ⟨p, ⟨𝟙 p.siteObject, ?_⟩, FieldValuedPoint.dominates_refl C S hS Y p⟩
  change Y.map (𝟙 p.siteObject).op (f.app (Opposite.op p.siteObject) a) = p.value
  simpa only [op_id, Functor.map_id_apply] using ha

/-- Every field-valued point of the object space of a groupoid in algebraic spaces is the
source and the target of an identity arrow over the same test object. -/
private theorem exists_arrow_source_eq_and_target_eq (p : FieldValuedPoint C S hS G.objects.1) :
    ∃ a : G.arrows.1.obj (Opposite.op p.siteObject),
      G.source.hom.app (Opposite.op p.siteObject) a = p.value ∧
        G.target.hom.app (Opposite.op p.siteObject) a = p.value := by
  let F := G.toGroupoidInFunctors
  let : Groupoid (F.Evaluation (Opposite.op p.siteObject)) :=
    F.evaluationGroupoid (Opposite.op p.siteObject)
  let x₀ : F.Evaluation (Opposite.op p.siteObject) := p.value
  exact ⟨_, (F.evaluationArrowEquiv (Opposite.op p.siteObject) x₀ x₀ (𝟙 x₀)).2⟩

/-- The source of a groupoid in algebraic spaces is surjective on points: every point of the
object space is the source of an identity arrow. -/
private theorem isSurjective_source : IsSurjective C S hS G.source.hom :=
  isSurjective_of_pointwise_lift C hS G.source.hom fun p ↦
    (exists_arrow_source_eq_and_target_eq C hS G p).imp fun _ h ↦ h.1

/-- The target of a groupoid in algebraic spaces is surjective on points: every point of the
object space is the target of an identity arrow. -/
private theorem isSurjective_target : IsSurjective C S hS G.target.hom :=
  isSurjective_of_pointwise_lift C hS G.target.hom fun p ↦
    (exists_arrow_source_eq_and_target_eq C hS G p).imp fun _ h ↦ h.2

/-- The morphism of algebraic spaces induced by a field extension is surjective: it is
represented by `Spec k' ⟶ Spec k`, which is surjective because `k'` is a faithfully flat
`k`-algebra. -/
private theorem isSurjective_fieldSpaceMap :
    IsSurjective C S hS (fieldSpaceMap C hS hk hk' structureMap i).hom := by
  let T := BigFppfOver.toScheme C S hS
  let V : BigFppfOver C S hS := Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)
  let V' : BigFppfOver C S hS :=
    Over.mk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap⟩ :
      C.obj hk' ⟶ C.obj hS)
  let a : V' ⟶ V :=
    Over.homMk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op⟩ : C.obj hk' ⟶ C.obj hk) rfl
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  have : P.IsStableUnderBaseChange := BigFppfOver.isStableUnderBaseChange_inverseImage C S hS _
  have hrel : P.presheaf (yoneda.map a) :=
    (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).2 (by
      change Surjective (T.map a)
      change Surjective (Scheme.Spec.map (CommRingCat.ofHom i).op)
      let φ : CommRingCat.of k ⟶ CommRingCat.of k' := CommRingCat.ofHom i
      have hFaithfullyFlat : (CommRingCat.Hom.hom φ).FaithfullyFlat := by
        let : Algebra k k' := (CommRingCat.Hom.hom φ).toAlgebra
        exact Module.FaithfullyFlat.instOfNontrivialOfFree k k'
      have hFlatSurj : Flat (Spec.map φ) ∧ Surjective (Spec.map φ) :=
        (AlgebraicGeometry.flat_and_surjective_SpecMap_iff φ).2 hFaithfullyFlat
      simpa [φ] using hFlatSurj.2)
  change IsSurjective C S hS (yoneda.map a)
  exact (presheafSurjective_iff_isSurjective_yoneda C S hS (yoneda.obj V)
    (isAlgebraicSpace_yoneda C S hS V) V' (yoneda.map a)).mp hrel

private theorem isSurjective_restrictionObjectMap :
    IsSurjective C S hS (restrictionObjectMap C hS hk hk' structureMap i G hU).hom := by
  have : IsIso (eqToHom hU.symm :
      fieldSpace C hS hk structureMap ⟶ G.objects).hom :=
    (ObjectProperty.isIso_hom_iff _).2 inferInstance
  change IsSurjective C S hS
    ((fieldSpaceMap C hS hk hk' structureMap i ≫ eqToHom hU.symm).hom)
  exact isSurjective_comp C S hS
    (isSurjective_fieldSpaceMap C hS hk hk' structureMap i)
    (isSurjective_of_isIso C hS (eqToHom hU.symm :
      fieldSpace C hS hk structureMap ⟶ G.objects).hom)

/-! ### Flatness and universal openness over a field -/

/-- Every morphism of algebraic spaces whose target is the algebraic space of the spectrum of
a field is flat: on a surjective étale chart it becomes a morphism of schemes whose target is
an integral scheme with one point. -/
private theorem isFlat_to_fieldSpace
    {Y : AlgebraicSpaces C S hS} (hY : Y = fieldSpace C hS hk structureMap)
    {X : AlgebraicSpaces C S hS} (f : X ⟶ Y) :
    IsFlat C S hS f.hom := by
  cases hY
  let T := BigFppfOver.toScheme C S hS
  let V : BigFppfOver C S hS := Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)
  let q : yoneda.obj V ⟶ yoneda.obj V := 𝟙 _
  let Qsurj := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  let Qetale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have : Qsurj.IsStableUnderBaseChange := BigFppfOver.isStableUnderBaseChange_inverseImage C S hS _
  have : Qetale.IsStableUnderBaseChange := BigFppfOver.isStableUnderBaseChange_inverseImage C S hS _
  have hq_surj : Qsurj.presheaf q := by
    simpa [Qsurj, q, T] using
      (MorphismProperty.relative_map_iff (F := yoneda) (P := Qsurj)).2
        (show Surjective (T.map (𝟙 V)) by infer_instance)
  have hq_etale : Qetale.presheaf q := by
    simpa [Qetale, q, T] using
      (MorphismProperty.relative_map_iff (F := yoneda) (P := Qetale)).2
        (show Etale (T.map (𝟙 V)) by infer_instance)
  obtain ⟨U, p, α, hcomm, hp_surj, hp_etale⟩ :=
    exists_surjective_etale_presentation_lift C S hS X.property
      (isAlgebraicSpace_yoneda C S hS V) f.hom V q hq_surj hq_etale
  apply (holdsOnEveryEtaleChart_iff_surjectiveChart C S hS
    (@Flat : MorphismProperty Scheme.{u}) Flat.isEtaleLocalOnSourceAndTarget
    X.property (isAlgebraicSpace_yoneda C S hS V) f.hom).2
  refine ⟨U, V, p, q, α, hp_etale, hq_etale, hp_surj, hcomm.symm, ?_⟩
  change Flat (T.map α)
  have : Subsingleton (T.obj V) := inferInstanceAs (Subsingleton (Spec (.of k)))
  have : IsIntegral (T.obj V) := inferInstanceAs (IsIntegral (Spec (.of k)))
  infer_instance

/-- Every morphism of algebraic spaces whose target is the algebraic space of the spectrum of
a field is universally open. This is Stacks 06DN, for the prescribed target. -/
@[sga "4 VIII 9.4.4" "more general"]
private theorem universallyOpen_to_fieldSpace
    {Y : AlgebraicSpaces C S hS} (hY : Y = fieldSpace C hS hk structureMap)
    {X : AlgebraicSpaces C S hS} (f : X ⟶ Y) :
    UniversallyOpen C S hS f.hom := by
  cases hY
  exact universallyOpen_to_field C S hS X.property
    (K := Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)) (k := k) (Iso.refl _) f.hom

/-! ### Affineness -/

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is affine
induces an affine morphism of algebraic spaces. -/
private theorem isAffineHom_yonedaMap {U V : BigFppfOver C S hS} (a : U ⟶ V)
    (ha : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme C S hS).map a)) :
    IsAffineHom C S hS (yoneda.map a) := by
  intro Z g
  let T := BigFppfOver.toScheme C S hS
  let I := BigAffineFppf.inclusion C S hS
  let b : I.obj Z ⟶ V := yoneda.preimage g
  have hb : yoneda.map b = g := yoneda.map_preimage g
  let W₀ := pullback a b
  let p₀ := pullback.fst a b
  let q₀ := pullback.snd a b
  have hsq : IsPullback p₀ q₀ a b := IsPullback.of_hasPullback a b
  have : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  have hsqT : IsPullback (T.map p₀) (T.map q₀) (T.map a) (T.map b) := IsPullback.map T hsq
  have hqAffine : _root_.AlgebraicGeometry.IsAffineHom (T.map q₀) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqT ha
  have hWaffine : IsAffine (T.obj W₀) := by
    let : IsAffine (T.obj (I.obj Z)) := BigAffineFppf.isAffine_toScheme_obj C S hS Z
    exact AlgebraicGeometry.isAffine_of_isAffineHom (T.map q₀)
  let W : BigAffineFppf C S hS := ⟨W₀, hWaffine⟩
  let p : I.obj W ⟶ U := show W₀ ⟶ U from p₀
  let q : I.obj W ⟶ I.obj Z := show W₀ ⟶ I.obj Z from q₀
  refine ⟨W, yoneda.map p, q, ?_⟩
  have hsqY : IsPullback (yoneda.map p₀) (yoneda.map q₀) (yoneda.map a) (yoneda.map b) :=
    IsPullback.map yoneda hsq
  simpa [I, b, W₀, p₀, q₀, p, q, Category.assoc, hb] using hsqY

private theorem isAffineHom_fieldSpaceMap :
    IsAffineHom C S hS (fieldSpaceMap C hS hk hk' structureMap i).hom := by
  let a : (Over.mk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap⟩ :
      C.obj hk' ⟶ C.obj hS) : BigFppfOver C S hS) ⟶
      Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS) :=
    Over.homMk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op⟩ : C.obj hk' ⟶ C.obj hk) rfl
  change IsAffineHom C S hS (yoneda.map a)
  exact isAffineHom_yonedaMap C hS a (inferInstanceAs
    (_root_.AlgebraicGeometry.IsAffineHom (Scheme.Spec.map (CommRingCat.ofHom i).op)))

private theorem isAffineHom_restrictionObjectMap :
    IsAffineHom C S hS (restrictionObjectMap C hS hk hk' structureMap i G hU).hom := by
  have : IsIso (eqToHom hU.symm :
      fieldSpace C hS hk structureMap ⟶ G.objects).hom :=
    (ObjectProperty.isIso_hom_iff _).2 inferInstance
  change IsAffineHom C S hS
    ((fieldSpaceMap C hS hk hk' structureMap i ≫ eqToHom hU.symm).hom)
  exact isAffineHom_comp C S hS _ _
    (isAffineHom_fieldSpaceMap C hS hk hk' structureMap i)
    (isAffineHom_of_isIso C hS (eqToHom hU.symm :
      fieldSpace C hS hk structureMap ⟶ G.objects).hom)

/-! ### The three universal properties of the diagram -/

/-- A property of morphisms of algebraic spaces that is stable under base change and composition
and holds for the morphism of object spaces, the source and the target of the groupoid, holds for
every arrow of the diagram defining the restriction. -/
private theorem property_of_restrictionDiagramMap
    (P : ∀ {X Y : AlgebraicSpaces C S hS}, (X ⟶ Y) → Prop)
    (hfst : ∀ {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y),
      P g → P (fiberProductFst f g))
    (hsnd : ∀ {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Z ⟶ Y),
      P f → P (fiberProductSnd f g))
    (hcomp : ∀ {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      P f → P g → P (f ≫ g))
    (hg : P (restrictionObjectMap C hS hk hk' structureMap i G hU))
    (hs : P G.source) (ht : P G.target)
    {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (hf : RestrictionDiagramMap C hS hk hk' structureMap i G hU f) : P f := by
  set g := restrictionObjectMap C hS hk hk' structureMap i G hU
  have hP1 := hfst G.source g hg
  have hP2 := hsnd g G.target hg
  have hToSource := hsnd (fiberProductSnd g G.target) (fiberProductFst G.source g) hP2
  have hToTarget := hfst (fiberProductSnd g G.target) (fiberProductFst G.source g) hP1
  induction hf with
  | fieldExtension => exact hg
  | source => exact hs
  | target => exact ht
  | sourceBase => exact hP1
  | sourceExtension => exact hsnd G.source g hs
  | targetExtension => exact hfst g G.target ht
  | targetBase => exact hP2
  | arrowsToSourcePullback => exact hToSource
  | arrowsToTargetPullback => exact hToTarget
  | restrictedSource => exact hcomp _ _ hToSource (hsnd G.source g hs)
  | restrictedTarget => exact hcomp _ _ hToTarget (hfst g G.target ht)
  | restrictedArrowsToArrows => exact hcomp _ _ hToTarget hP2

/-- **Stacks 06E1.** Every arrow of the diagram defining the restriction of a groupoid in
algebraic spaces whose object space is the spectrum of a field, over a field extension, is
surjective. -/
@[stacks 06E1 "surjective"]
theorem isSurjective_of_restrictionDiagramMap
    {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (hf : RestrictionDiagramMap C hS hk hk' structureMap i G hU f) :
    IsSurjective C S hS f.hom :=
  property_of_restrictionDiagramMap C hS hk hk' structureMap i G hU
    (fun f => IsSurjective C S hS f.hom) (isSurjective_fiberProductFst C hS)
    (isSurjective_fiberProductSnd C hS) (fun _ _ hf hg => isSurjective_comp C S hS hf hg)
    (isSurjective_restrictionObjectMap C hS hk hk' structureMap i G hU)
    (isSurjective_source C hS G) (isSurjective_target C hS G) f hf

/-- **Stacks 06E1.** Every arrow of the diagram defining the restriction of a groupoid in
algebraic spaces whose object space is the spectrum of a field, over a field extension, is
flat. -/
@[stacks 06E1 "flat"]
theorem isFlat_of_restrictionDiagramMap
    {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (hf : RestrictionDiagramMap C hS hk hk' structureMap i G hU f) :
    IsFlat C S hS f.hom :=
  property_of_restrictionDiagramMap C hS hk hk' structureMap i G hU
    (fun f => IsFlat C S hS f.hom) (isFlat_fiberProductFst C hS) (isFlat_fiberProductSnd C hS)
    (fun {X Y Z} _ _ hf hg =>
      isFlat_comp C S hS X.property Y.property Z.property _ _ hf hg)
    (isFlat_to_fieldSpace C hS hk structureMap hU _)
    (isFlat_to_fieldSpace C hS hk structureMap hU _)
    (isFlat_to_fieldSpace C hS hk structureMap hU _) f hf

/-- **Stacks 06E1.** Every arrow of the diagram defining the restriction of a groupoid in
algebraic spaces whose object space is the spectrum of a field, over a field extension, is
universally open. -/
@[stacks 06E1 "universally open"]
theorem universallyOpen_of_restrictionDiagramMap
    {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (hf : RestrictionDiagramMap C hS hk hk' structureMap i G hU f) :
    UniversallyOpen C S hS f.hom :=
  property_of_restrictionDiagramMap C hS hk hk' structureMap i G hU
    (fun f => UniversallyOpen C S hS f.hom) (universallyOpen_fiberProductFst C hS)
    (universallyOpen_fiberProductSnd C hS)
    (fun {X Y Z} _ _ hf hg =>
      universallyOpen_comp C S hS X.property Y.property Z.property _ _ hf hg)
    (universallyOpen_to_fieldSpace C hS hk structureMap hU _)
    (universallyOpen_to_fieldSpace C hS hk structureMap hU _)
    (universallyOpen_to_fieldSpace C hS hk structureMap hU _) f hf

/-- **Stacks 06E1.** The canonical map from the arrows of the restriction of a groupoid in
algebraic spaces over a field extension to the arrows of the groupoid is affine. -/
@[stacks 06E1 "affine dotted arrow"]
theorem isAffineHom_restrictionArrowsToArrows :
    IsAffineHom C S hS
      (restrictionArrowsToArrows G
        (restrictionObjectMap C hS hk hk' structureMap i G hU)).hom := by
  set g := restrictionObjectMap C hS hk hk' structureMap i G hU
  have hg : IsAffineHom C S hS g.hom :=
    isAffineHom_restrictionObjectMap C hS hk hk' structureMap i G hU
  have hP2 : IsAffineHom C S hS (fiberProductSnd g G.target).hom :=
    isAffineHom_fiberProductSnd C hS g G.target hg
  have hP1 : IsAffineHom C S hS (fiberProductFst G.source g).hom :=
    isAffineHom_fiberProductFst C hS G.source g hg
  have hToTarget : IsAffineHom C S hS
      (fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g)).hom :=
    isAffineHom_fiberProductFst C hS
      (fiberProductSnd g G.target) (fiberProductFst G.source g) hP1
  exact isAffineHom_comp C S hS _ _ hToTarget hP2

end AlgebraicGeometry.Space

end
