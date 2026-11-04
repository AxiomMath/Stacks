module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FieldFibreDegreeBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusStrictlyFull
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.NoetherianDescent

/-!
# Locally Noetherian fibres of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `y` be a point of
`Y`. The fibre of `f` over `y` can be formed in three different ways, and they all agree on
whether the result is locally Noetherian: one may take an étale chart `V ⟶ Y` by a scheme
together with a point `v` of `V` above `y` and form the fibre over the residue field of `v`,
one may do that for *every* such chart, or one may take an arbitrary field-valued
representative of `y` and base change along it. The fibre over a point is then *called*
locally Noetherian when these conditions hold, and this holds automatically when `f` is
locally of finite type.

## Main definitions

* `AlgebraicGeometry.Space.IsLocallyNoetherianFiberAt`: local Noetherianity of the base
  change of `f` along the morphism presented by a field-valued point of `Y`.
* `AlgebraicGeometry.Space.IsLocallyNoetherianFiber`: the fibre of `f` over a point of `Y` is
  locally Noetherian.
* `AlgebraicGeometry.Space.HasLocallyNoetherianFibersAtPoints`: every fibre of `f` is locally
  Noetherian.

## Main results

* `AlgebraicGeometry.Space.isLocallyNoetherianFiber_tfae`: the three chart-free and
  chart-based conditions agree.
* `AlgebraicGeometry.Space.isLocallyNoetherianFiberAt_iff_exists`: when `y` has a field-valued
  representative presenting it by a monomorphism, the condition may be tested at that
  representative alone.
* `AlgebraicGeometry.Space.hasLocallyNoetherianFibersAtPoints_of_isLocallyOfFiniteType`: a morphism
  locally of finite type has locally Noetherian fibres.
* `AlgebraicGeometry.Space.isLocallyNoetherian_fiber_of_etale_pullback_chart` and
  `AlgebraicGeometry.Space.locallyNoetherianFibers_of_etale_pullback_chart`: the chart
  morphism of a morphism, taken over an étale chart of the target, has a locally Noetherian
  fibre over every point above which the fibre of the morphism is locally Noetherian, hence
  locally Noetherian fibres when the morphism has.
* `AlgebraicGeometry.isLocallyNoetherian_fiber_iso_comp`: precomposition with an isomorphism
  leaves local Noetherianity of the fibres of a morphism of schemes unchanged.
* `AlgebraicGeometry.Space.presheafProperty_comp`,
  `AlgebraicGeometry.Space.presheafProperty_pullback_fst` and
  `AlgebraicGeometry.Space.presheafProperty_of_isPullback`: the property of morphisms of
  presheaves on the big fppf site of `S` induced by a property of morphisms of schemes is
  stable under composition and under base change.

## Implementation notes

Local Noetherianity of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.IsLocallyNoetherian` in the sense of
`AlgebraicGeometry.Space.HasEtaleLocalProperty`, and the fibre over a field-valued point `p`
of `Y` is the presheaf fibre product of `f` with the morphism
`AlgebraicGeometry.Space.fieldMorphism` that `p` presents. In the chart conditions the fibre
is taken at the canonical field-valued representative
`AlgebraicGeometry.Space.schemePointRepresentative` of the chosen scheme point, that is over
its residue field, which is what the source means by `X_v`; only the third condition allows an
arbitrary field-valued representative.

The substance of the equivalence is that a field-valued representative with locally Noetherian
fibre forces every chart to have one. Given a chart `V ⟶ Y`, a point `v` of `V` above `y` and a
representative `Spec k ⟶ Y` of `y`, an étale chart `A` of `V ×_Y Spec k` carries a point above
both, and its residue field `κ` is finite over `k` because `A ⟶ Spec k` is étale, hence
unramified. So `X_κ ⟶ X_k` is locally of finite type and `X_κ` is locally Noetherian by Stacks
04ZK, while `X_κ ⟶ X_{κ(v)}` is surjective, affine and flat — being the base change of a
morphism of spectra of fields — so `X_{κ(v)}` is locally Noetherian by descent. That the map
`Spec κ ⟶ Spec κ(v)` exists at all is the factorisation of a field-valued point through the
canonical representative, which is a monomorphism.

## References

* [Stacks Project, Tag 0CUW](https://stacks.math.columbia.edu/tag/0CUW)
* [Stacks Project, Tag 0CUX](https://stacks.math.columbia.edu/tag/0CUX)
* [Stacks Project, Tag 0CUY](https://stacks.math.columbia.edu/tag/0CUY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Morphisms between spectra of fields -/

/-- Every morphism between spectra of fields is flat, surjective and affine: its target has
a field as its only local ring, its source is nonempty and its target has one point, and both
are affine. -/
private theorem flat_surjective_isAffineHom_fieldSpec (K L : Type u) [Field K] [Field L]
    (g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) :
    Flat g ∧ Surjective g ∧ IsAffineHom g :=
  ⟨flat_of_isField_stalk g fun _ ↦ isField_stalk_Spec_field K _, inferInstance, inferInstance⟩

/-! ### Fibres of a morphism precomposed with an isomorphism -/

/-- Local Noetherianity of the fibres is unchanged by composing with an isomorphism on the
source. -/
lemma isLocallyNoetherian_fiber_iso_comp {A A' W : Scheme.{u}} (e : A ≅ A')
    (k : A' ⟶ W) (h : ∀ y, IsLocallyNoetherian (k.fiber y)) (y : W) :
    IsLocallyNoetherian ((e.hom ≫ k).fiber y) := by
  let m : (e.hom ≫ k).fiber y ⟶ k.fiber y :=
    pullback.map (e.hom ≫ k) (W.fromSpecResidueField y) k (W.fromSpecResidueField y)
      e.hom (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hm : IsIso m := by
    dsimp only [m, Scheme.Hom.fiber]
    infer_instance
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (P := fun Z : Scheme.{u} => IsLocallyNoetherian Z) (asIso m).symm (h y)

namespace Space

/-! ### Comparison of cartesian squares -/

/-- Two cartesian squares over the same morphism of a cospan compare: the map of fibre
products induced by a factorisation of one leg is itself cartesian over that factorisation. -/
private theorem isPullback_pullbackMap {C : Type*} [Category C] [HasPullbacks C]
    {X Y U V : C} (f : X ⟶ Y) (β₀ : U ⟶ Y) (β : V ⟶ Y) (a : V ⟶ U) (hβ : β = a ≫ β₀) :
    IsPullback (pullback.map f β f β₀ (𝟙 _) a (𝟙 _) (by simp) (by simpa using hβ))
      (pullback.snd f β) (pullback.snd f β₀) a := by
  have hsq : IsPullback
      (pullback.map f β f β₀ (𝟙 _) a (𝟙 _) (by simp) (by simpa using hβ) ≫
        pullback.fst f β₀)
      (pullback.snd f β) f (a ≫ β₀) := by
    simpa only [pullback.map, pullback.lift_fst, Category.comp_id, ← hβ] using
      IsPullback.of_hasPullback f β
  exact hsq.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f β₀)

/-! ### Local Noetherianity of a fibre -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibre of `f` at a field-valued point `p` of its target is locally Noetherian: the base
change of `f` along the morphism presented by `p` admits a locally Noetherian surjective étale
atlas. -/
abbrev IsLocallyNoetherianFiberAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) : Prop :=
  HasEtaleLocalProperty B S hS (pullback f (fieldMorphism B S hS Y p))
    (fun T : Scheme.{u} => IsLocallyNoetherian T)

/-- Local Noetherianity of the fibre descends along a factorisation of field-valued points: if
the morphism presented by `p` factors through the one presented by `p₀`, then the fibre at `p₀`
is locally Noetherian as soon as the fibre at `p` is, the comparison being the base change of a
morphism of spectra of fields, hence surjective, affine and flat. -/
private theorem isLocallyNoetherianFiberAt_of_factor {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {p p₀ : FieldValuedPoint B S hS Y} (α : p.siteObject ⟶ p₀.siteObject)
    (hβ : fieldMorphism B S hS Y p = yoneda.map α ≫ fieldMorphism B S hS Y p₀)
    (hN : IsLocallyNoetherianFiberAt B S hS f p) :
    IsLocallyNoetherianFiberAt B S hS f p₀ := by
  obtain ⟨hαFlat, hαSurjective, hαAffine⟩ :=
    flat_surjective_isAffineHom_fieldSpec p₀.carrier p.carrier
      (show Spec (CommRingCat.of p.carrier) ⟶ Spec (CommRingCat.of p₀.carrier) from
        (BigFppfOver.toScheme B S hS).map α)
  have hSurjectiveBC : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) := inferInstance
  have hαAffineSpace : Space.IsAffineHom B S hS (yoneda.map α) :=
    isAffineHom_of_presheaf
      ((presheaf_yoneda_map_iff B S hS isAffineHom_isStableUnderBaseChange α).2 hαAffine)
  let X₀ : AlgebraicSpaces B S hS :=
    ⟨pullback f (fieldMorphism B S hS Y p₀),
      isAlgebraicSpace_pullback B S hS f (fieldMorphism B S hS Y p₀) hX
        (isAlgebraicSpace_yoneda B S hS p₀.siteObject) hY⟩
  let X₁ : AlgebraicSpaces B S hS :=
    ⟨pullback f (fieldMorphism B S hS Y p),
      isAlgebraicSpace_pullback B S hS f (fieldMorphism B S hS Y p) hX
        (isAlgebraicSpace_yoneda B S hS p.siteObject) hY⟩
  let P₀ : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj p₀.siteObject, isAlgebraicSpace_yoneda B S hS p₀.siteObject⟩
  let P₁ : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj p.siteObject, isAlgebraicSpace_yoneda B S hS p.siteObject⟩
  let m : X₁ ⟶ X₀ := ObjectProperty.homMk
    (pullback.map f (fieldMorphism B S hS Y p) f (fieldMorphism B S hS Y p₀) (𝟙 _)
      (yoneda.map α) (𝟙 _) (by simp) (by simpa using hβ))
  let π₁ : X₁ ⟶ P₁ := ObjectProperty.homMk (pullback.snd f (fieldMorphism B S hS Y p))
  let π₀ : X₀ ⟶ P₀ := ObjectProperty.homMk (pullback.snd f (fieldMorphism B S hS Y p₀))
  let α' : P₁ ⟶ P₀ := ObjectProperty.homMk (yoneda.map α)
  have hsquarePre : IsPullback m.hom π₁.hom π₀.hom α'.hom :=
    isPullback_pullbackMap f (fieldMorphism B S hS Y p₀) (fieldMorphism B S hS Y p)
      (yoneda.map α) hβ
  have hsquare : IsPullback m π₁ π₀ α' :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F ↦ IsAlgebraicSpace B S hS F)) hsquarePre
  have hα'Surjective : IsSurjective B S hS α'.hom :=
    (surjective_yonedaMap_iff_surjective_pointsMap B S hS α).1
      ((presheaf_yoneda_map_iff B S hS hSurjectiveBC α).2 hαSurjective)
  have hα'Flat : IsFlat B S hS α'.hom := isFlat_yoneda_map B S hS α hαFlat
  exact isLocallyNoetherian_of_surjective_affine_flat B S hS m.hom X₁.property X₀.property
    (isSurjective_of_isPullback B S hS hsquare.flip hα'Surjective)
    (Space.IsAffineHom.of_isPullback hsquarePre.flip hαAffineSpace)
    (by
      let _ := isFlat_isStableUnderBaseChange B S hS
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun ⦃D E : AlgebraicSpaces B S hS⦄ (k : D ⟶ E) => IsFlat B S hS k.hom)
        hsquare.flip hα'Flat)
    hN

/-- The map from the canonical representative of a point `x` of an étale chart `A` to the
spectrum of a field `k`, through an unramified morphism `j : A ⟶ Spec k`, is locally of finite
type: it is the spectrum of the residue field extension `κ(x) / k`, which is finite. -/
private theorem locallyOfFiniteType_toScheme_map_siteHom_comp
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS Y) {A : BigFppfOver B S hS} (j : A ⟶ p.siteObject)
    [Unramified ((BigFppfOver.toScheme B S hS).map j)]
    (x : (BigFppfOver.toScheme B S hS).obj A) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      ((schemePointRepresentative B S hS A x).siteHom ≫ j)) := by
  let : Algebra
      (((BigFppfOver.toScheme B S hS).obj p.siteObject).residueField
        ((BigFppfOver.toScheme B S hS).map j x))
      (((BigFppfOver.toScheme B S hS).obj A).residueField x) :=
    (((BigFppfOver.toScheme B S hS).map j).residueFieldMap x).hom.toAlgebra
  let : Module.Finite
      (((BigFppfOver.toScheme B S hS).obj p.siteObject).residueField
        ((BigFppfOver.toScheme B S hS).map j x))
      (((BigFppfOver.toScheme B S hS).obj A).residueField x) := by
    simpa using finite_residueField_of_unramified ((BigFppfOver.toScheme B S hS).map j) x
  let : Algebra.FiniteType
      (((BigFppfOver.toScheme B S hS).obj p.siteObject).residueField
        ((BigFppfOver.toScheme B S hS).map j x))
      (((BigFppfOver.toScheme B S hS).obj A).residueField x) :=
    Module.Finite.finiteType _
  have htMap : (BigFppfOver.toScheme B S hS).map
        ((schemePointRepresentative B S hS A x).siteHom ≫ j) =
      Spec.map (((BigFppfOver.toScheme B S hS).map j).residueFieldMap x) ≫
        ((BigFppfOver.toScheme B S hS).obj p.siteObject).fromSpecResidueField
          ((BigFppfOver.toScheme B S hS).map j x) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
      ((BigFppfOver.toScheme B S hS).map j) x,
      ← toScheme_map_siteHom_schemePointRepresentative B S hS A x]
    exact (BigFppfOver.toScheme B S hS).map_comp _ j
  rw [htMap]
  have hfirst : LocallyOfFiniteType
      (Spec.map (((BigFppfOver.toScheme B S hS).map j).residueFieldMap x)) := by
    show LocallyOfFiniteType
      (Spec (CommRingCat.of (((BigFppfOver.toScheme B S hS).obj A).residueField x)) ↘
        Spec (CommRingCat.of
          (((BigFppfOver.toScheme B S hS).obj p.siteObject).residueField
            ((BigFppfOver.toScheme B S hS).map j x))))
    infer_instance
  have : IsIso (((BigFppfOver.toScheme B S hS).obj p.siteObject).fromSpecResidueField
      ((BigFppfOver.toScheme B S hS).map j x)) :=
    isIso_fromSpecResidueField_of_field p.carrier _
  exact MorphismProperty.comp_mem _ _ _ hfirst inferInstance

/-- The base change `pullback.snd a b` of a morphism `a` of algebraic spaces which is locally of
finite type is locally of finite type. -/
private theorem isLocallyOfFiniteType_pullback_snd {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (a : X ⟶ Z) (b : Y ⟶ Z)
    (ha : IsLocallyOfFiniteType B S hS a) : IsLocallyOfFiniteType B S hS (pullback.snd a b) := by
  let _ := isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃D E : AlgebraicSpaces B S hS⦄ (m : D ⟶ E) => IsLocallyOfFiniteType B S hS m.hom)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk a : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk b : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)) ha

/-- Local Noetherianity of the fibre is inherited by a field-valued point `q` of the spectrum of
the field of `p` whose structure map is locally of finite type, by Stacks 04ZK applied to the
base change of `f` along it. -/
private theorem isLocallyNoetherianFiberAt_map_of_locallyOfFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {p : FieldValuedPoint B S hS Y} (hp : IsLocallyNoetherianFiberAt B S hS f p)
    (q : FieldValuedPoint B S hS (yoneda.obj p.siteObject))
    (hq : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (q.value : q.siteObject ⟶ p.siteObject))) :
    IsLocallyNoetherianFiberAt B S hS f
      (FieldValuedPoint.map B S hS (yoneda.obj p.siteObject) (fieldMorphism B S hS Y p) q) := by
  let pY : yoneda.obj p.siteObject ⟶ Y := fieldMorphism B S hS Y p
  let t : q.siteObject ⟶ p.siteObject := q.value
  let PP : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj p.siteObject, isAlgebraicSpace_yoneda B S hS p.siteObject⟩
  have hZ₀ : HasEtaleLocalProperty B S hS (pullback pY f)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_of_iso B S hS _ (pullbackSymmetry f pY) hp
  let Z₀S : AlgebraicSpaces B S hS :=
    ⟨pullback pY f, isAlgebraicSpace_pullback B S hS pY f PP.property hX hY⟩
  let πP₀ : Z₀S ⟶ PP := ObjectProperty.homMk (pullback.fst pY f)
  let QP : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj q.siteObject, isAlgebraicSpace_yoneda B S hS q.siteObject⟩
  let t' : QP ⟶ PP := ObjectProperty.homMk (yoneda.map t)
  let Z₁S := AlgebraicSpaces.fiberProduct B S hS t' πP₀
  let πQ : Z₁S ⟶ QP := ObjectProperty.homMk
    (pullback.fst (yoneda.map t) (pullback.fst pY f))
  let πZ : Z₁S ⟶ Z₀S := ObjectProperty.homMk
    (pullback.snd (yoneda.map t) (pullback.fst pY f))
  have hsq₁ : IsPullback πQ πZ t' πP₀ :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS t' πP₀
  have htLFT : IsLocallyOfFiniteType B S hS (yoneda.map t) :=
    holdsOnEveryEtaleChart_yoneda_map B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget t hq
  have hπZLFT : IsLocallyOfFiniteType B S hS πZ.hom :=
    isLocallyOfFiniteType_pullback_snd B S hS QP.property Z₀S.property PP.property _ _ htLFT
  have hZ₁ : HasEtaleLocalProperty B S hS Z₁S.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z₁S.property Z₀S.property πZ.hom
      hπZLFT hZ₀
  have hqmap : fieldMorphism B S hS Y
      (FieldValuedPoint.map B S hS (yoneda.obj p.siteObject) pY q) = yoneda.map t ≫ pY := by
    apply yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply]
    rfl
  show HasEtaleLocalProperty B S hS (pullback f (fieldMorphism B S hS Y
    (FieldValuedPoint.map B S hS (yoneda.obj p.siteObject) pY q))) _
  refine hasEtaleLocalProperty_of_iso B S hS _ ?_ hZ₁
  refine Iso.symm ?_
  rw [hqmap]
  exact pullbackSymmetry f (yoneda.map t ≫ pY) ≪≫
    (pullbackRightPullbackFstIso pY f (yoneda.map t)).symm

/-- Given an étale chart `g : V ⟶ Y`, a point `v` of `V` and a field-valued point `p` of `Y` in
the same class, some étale chart `A` of `V ×_Y Spec k` carries a point `x` whose canonical
representative maps to the class of `v` in `V`, the chart being étale over `Spec k`. -/
private theorem exists_etale_chart_point_of_class_eq {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (p : FieldValuedPoint B S hS Y)
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y} (hgEtale : IsEtale B S hS g)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hpoint : pointsMap B S hS (yoneda.obj V) g
      ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) = p.class B S hS Y) :
    ∃ (A : BigFppfOver B S hS) (j : A ⟶ p.siteObject) (l : A ⟶ V)
      (x : (BigFppfOver.toScheme B S hS).obj A),
      Etale ((BigFppfOver.toScheme B S hS).map j) ∧
      yoneda.map l ≫ g = yoneda.map j ≫ fieldMorphism B S hS Y p ∧
      (FieldValuedPoint.map B S hS (yoneda.obj A) (yoneda.map l)
        (schemePointRepresentative B S hS A x)).class B S hS (yoneda.obj V) =
        (schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V) := by
  let pY : yoneda.obj p.siteObject ⟶ Y := fieldMorphism B S hS Y p
  let VP : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let PP : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj p.siteObject, isAlgebraicSpace_yoneda B S hS p.siteObject⟩
  let YP : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let g' : VP ⟶ YP := ObjectProperty.homMk g
  let p' : PP ⟶ YP := ObjectProperty.homMk pY
  let W := AlgebraicSpaces.fiberProduct B S hS g' p'
  let πV : W ⟶ VP := ObjectProperty.homMk (pullback.fst g pY)
  let πP : W ⟶ PP := ObjectProperty.homMk (pullback.snd g pY)
  have hsq : IsPullback πV πP g' p' := AlgebraicSpaces.isPullback_fiberProduct B S hS g' p'
  have hmatch : pointsMap B S hS (yoneda.obj V) g
        ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) =
      pointsMap B S hS (yoneda.obj p.siteObject) pY
        ((p.tautologicalPoint B S hS Y).class B S hS (yoneda.obj p.siteObject)) :=
    hpoint.trans (pointsMap_fieldMorphism_tautologicalPoint B S hS Y p).symm
  obtain ⟨w, hwV, -⟩ := exists_point_of_isPullback B S hS hsq
    ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V))
    ((p.tautologicalPoint B S hS Y).class B S hS (yoneda.obj p.siteObject)) hmatch
  obtain ⟨A, a, haSurjective, haEtale⟩ := W.property.exists_atlas
  obtain ⟨zA, hzA⟩ :=
    (surjective_iff_surjective_pointsMap B S hS W.1 W.property A a).mp haSurjective w
  obtain ⟨r, rfl⟩ := Quot.exists_rep zA
  let rA := schemePointRepresentative B S hS A (schemePoint B S hS A r)
  have hAclass : pointsMap B S hS (yoneda.obj A) a (rA.class B S hS (yoneda.obj A)) = w :=
    (congrArg (pointsMap B S hS (yoneda.obj A) a)
      (schemePointRepresentative_class B S hS A r)).trans hzA
  let j : A ⟶ p.siteObject := yoneda.preimage (a ≫ πP.hom)
  have hj : yoneda.map j = a ≫ πP.hom := yoneda.map_preimage _
  let l : A ⟶ V := yoneda.preimage (a ≫ πV.hom)
  have hl : yoneda.map l = a ≫ πV.hom := yoneda.map_preimage _
  have hπPEtale : IsEtale B S hS πP.hom := isEtale_of_isPullback B S hS πV πP g' p' hsq hgEtale
  refine ⟨A, j, l, schemePoint B S hS A r,
    (presheaf_yoneda_map_etale_iff B S hS j).1 (by rw [hj]; exact hπPEtale A a haEtale), ?_, ?_⟩
  · rw [hl, hj, Category.assoc, Category.assoc]
    exact congrArg (a ≫ ·) (by simpa [g', p'] using congrArg (fun k ↦ k.hom) hsq.w)
  · calc _ = pointsMap B S hS (yoneda.obj A) (yoneda.map l) (rA.class B S hS (yoneda.obj A)) :=
          (pointsMap_class B S hS (yoneda.obj A) (yoneda.map l) rA).symm
      _ = pointsMap B S hS W.1 πV.hom
            (pointsMap B S hS (yoneda.obj A) a (rA.class B S hS (yoneda.obj A))) := by
          rw [hl]
          exact congrFun (pointsMap_comp B S hS (yoneda.obj A) a πV.hom) _
      _ = _ := by rw [hAclass, hwV]

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` and a point `y` of `Y`, local
Noetherianity of the fibre of `f` over the residue field of a point of an étale scheme chart of
`Y` above `y` holds for some such chart exactly when it holds for every such chart, and exactly
when the base change of `f` along some field-valued representative of `y` is locally
Noetherian. -/
@[stacks 0CUW "conditions (1), (2) and (3)"]
theorem isLocallyNoetherianFiber_tfae
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (y : points B S hS Y) :
    List.TFAE [
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
          (v : (BigFppfOver.toScheme B S hS).obj V),
        IsEtale B S hS g ∧
          pointsMap B S hS (yoneda.obj V) g
            ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) = y ∧
          IsLocallyNoetherianFiberAt B S hS f
            (FieldValuedPoint.map B S hS (yoneda.obj V) g
              (schemePointRepresentative B S hS V v))),
      (∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
          (v : (BigFppfOver.toScheme B S hS).obj V),
        IsEtale B S hS g →
          pointsMap B S hS (yoneda.obj V) g
            ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) = y →
          IsLocallyNoetherianFiberAt B S hS f
            (FieldValuedPoint.map B S hS (yoneda.obj V) g
              (schemePointRepresentative B S hS V v))),
      (∃ p : FieldValuedPoint B S hS Y,
        p.class B S hS Y = y ∧ IsLocallyNoetherianFiberAt B S hS f p)
    ] := by
  classical
  tfae_have 1 → 3 := by
    rintro ⟨V, g, v, -, hpoint, hfibre⟩
    exact ⟨FieldValuedPoint.map B S hS (yoneda.obj V) g (schemePointRepresentative B S hS V v),
      (pointsMap_class B S hS (yoneda.obj V) g _).symm.trans hpoint, hfibre⟩
  tfae_have 2 → 1 := by
    intro hall
    obtain ⟨V, g, hgSurjective, hgEtale⟩ := hY.exists_atlas
    obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS Y hY V g).mp hgSurjective y
    obtain ⟨q, rfl⟩ := Quot.exists_rep z
    have hpoint : pointsMap B S hS (yoneda.obj V) g
        ((schemePointRepresentative B S hS V (schemePoint B S hS V q)).class B S hS
          (yoneda.obj V)) = y :=
      (congrArg (pointsMap B S hS (yoneda.obj V) g)
        (schemePointRepresentative_class B S hS V q)).trans hz
    have hgEtale' : IsEtale B S hS g := (isEtale_iff_presheaf_of_yoneda B S hS g).2 hgEtale
    exact ⟨V, g, schemePoint B S hS V q, hgEtale', hpoint,
      hall V g (schemePoint B S hS V q) hgEtale' hpoint⟩
  tfae_have 3 → 2 := by
    rintro ⟨p, hpy, hpFibre⟩ V g v hgEtale hpoint
    obtain ⟨A, j, l, x, hjEtale, hlj, hx⟩ :=
      exists_etale_chart_point_of_class_eq B S hS hY p hgEtale v (hpoint.trans hpy.symm)
    let : Unramified ((BigFppfOver.toScheme B S hS).map j) := unramified_of_etale _
    let rA := schemePointRepresentative B S hS A x
    let qP := FieldValuedPoint.map B S hS (yoneda.obj A) (yoneda.map j) rA
    have hqLFibre := isLocallyNoetherianFiberAt_map_of_locallyOfFiniteType B S hS hX hY f
      hpFibre qP (locallyOfFiniteType_toScheme_map_siteHom_comp B S hS p j x)
    let qV := FieldValuedPoint.map B S hS (yoneda.obj A) (yoneda.map l) rA
    let pV := schemePointRepresentative B S hS V v
    have : Mono (fieldMorphism B S hS (yoneda.obj V) pV) :=
      mono_fieldMorphism_schemePointRepresentative B S hS V v
    obtain ⟨φ, hφ, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS
      (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) pV qV hx.symm
    have hφ' : φ ≫ pV.value = qV.value := hφ
    let qVY : FieldValuedPoint B S hS Y := FieldValuedPoint.map B S hS (yoneda.obj V) g qV
    let q₀ : FieldValuedPoint B S hS Y := FieldValuedPoint.map B S hS (yoneda.obj V) g pV
    have hqVYvalue : qVY.value =
        (FieldValuedPoint.map B S hS (yoneda.obj p.siteObject) (fieldMorphism B S hS Y p)
          qP).value :=
      congrArg (fun k : yoneda.obj A ⟶ Y ↦ k.app (Opposite.op rA.siteObject) rA.value) hlj
    have hqVYFibre : IsLocallyNoetherianFiberAt B S hS f qVY := by
      show HasEtaleLocalProperty B S hS (pullback f (yonedaEquiv.symm qVY.value)) _
      rw [hqVYvalue]
      exact hqLFibre
    have hβ : fieldMorphism B S hS Y qVY = yoneda.map φ ≫ fieldMorphism B S hS Y q₀ := by
      rw [fieldMorphism_map_yoneda, fieldMorphism_map_yoneda]
      show yoneda.map qV.value ≫ g = yoneda.map φ ≫ yoneda.map pV.value ≫ g
      rw [← hφ', Functor.map_comp, Category.assoc]
    exact isLocallyNoetherianFiberAt_of_factor B S hS hX hY f (p := qVY) φ hβ hqVYFibre
  tfae_finish

/-- If a point `y` of `Y` has a field-valued representative presenting it by a monomorphism,
then the fibre of `f` over that representative is locally Noetherian exactly when the fibre over
some field-valued representative of `y` is. -/
@[stacks 0CUW "condition (4): a monomorphic representative"]
theorem isLocallyNoetherianFiberAt_iff_exists
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (y : points B S hS Y) (p₀ : FieldValuedPoint B S hS Y)
    [Mono (fieldMorphism B S hS Y p₀)] (hp₀ : p₀.class B S hS Y = y) :
    IsLocallyNoetherianFiberAt B S hS f p₀ ↔
      ∃ p : FieldValuedPoint B S hS Y,
        p.class B S hS Y = y ∧ IsLocallyNoetherianFiberAt B S hS f p := by
  refine ⟨fun hN ↦ ⟨p₀, hp₀, hN⟩, ?_⟩
  rintro ⟨p, hp, hN⟩
  obtain ⟨α, hα, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS Y hY
    p₀ p (hp₀.trans hp.symm)
  refine isLocallyNoetherianFiberAt_of_factor B S hS hX hY f α ?_ hN
  show yonedaEquiv.symm p.value = yoneda.map α ≫ yonedaEquiv.symm p₀.value
  rw [← hα]
  exact (yonedaEquiv_symm_naturality_left α Y p₀.value).symm

/-! ### The definition and the finite type case -/

/-- The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over `S` above a point `y` of `Y`
is *locally Noetherian* when the base change of `f` along some field-valued representative of
`y` is locally Noetherian.

By `AlgebraicGeometry.Space.isLocallyNoetherianFiber_tfae` this is equivalent to the fibre
over the residue field of a point above `y` of some, equivalently of every, étale scheme chart
of `Y` being locally Noetherian. -/
@[stacks 0CUX "the fibre over a point"]
abbrev IsLocallyNoetherianFiber {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (y : points B S hS Y) : Prop :=
  ∃ p : FieldValuedPoint B S hS Y,
    p.class B S hS Y = y ∧ IsLocallyNoetherianFiberAt B S hS f p

/-- A morphism of algebraic spaces over `S` has *locally Noetherian fibres* when its fibre
above every point of its target is locally Noetherian.

`AlgebraicGeometry.Space.HasLocallyNoetherianFibers` is the every-chart reading of the same
condition, quantifying instead over the points of the étale scheme charts of the target; by
`AlgebraicGeometry.Space.isLocallyNoetherianFiber_tfae` the two agree pointwise. -/
@[stacks 0CUX "all fibres"]
abbrev HasLocallyNoetherianFibersAtPoints {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) : Prop :=
  ∀ y : points B S hS Y, IsLocallyNoetherianFiber B S hS f y

/-- The fibre of a morphism locally of finite type is locally Noetherian at **every**
field-valued point of the target: the spectrum of a field is Noetherian and finite type is
stable under base change, so Stacks 04ZK applies to the base change of `f` along the morphism
presented by any field-valued point, with no condition relating it to a prescribed point. -/
theorem isLocallyNoetherianFiberAt_of_isLocallyOfFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y) :
    IsLocallyNoetherianFiberAt B S hS f p := by
  have hP : IsAlgebraicSpace B S hS (yoneda.obj p.siteObject) :=
    isAlgebraicSpace_yoneda B S hS p.siteObject
  have hW : IsAlgebraicSpace B S hS (pullback f (fieldMorphism B S hS Y p)) :=
    isAlgebraicSpace_pullback B S hS f (fieldMorphism B S hS Y p) hX hP hY
  have hPNoetherian :
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj p.siteObject) := by
    show IsLocallyNoetherian (Spec (CommRingCat.of p.carrier))
    exact isLocallyNoetherian_Spec.mpr inferInstance
  have hPAtlas : HasEtaleLocalProperty B S hS (yoneda.obj p.siteObject)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj p.siteObject)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) p.siteObject (Iso.refl _)).2 hPNoetherian
  exact isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hW hP
    (pullback.snd f (fieldMorphism B S hS Y p))
    (isLocallyOfFiniteType_pullback_snd B S hS hX hP hY _ _ hf) hPAtlas

/-- A morphism of algebraic spaces over `S` which is locally of finite type has locally
Noetherian fibres: the spectrum of a field is Noetherian, so Stacks 04ZK applies to the base
change of `f` along any field-valued representative of a point of the target. -/
@[stacks 0CUY]
theorem hasLocallyNoetherianFibersAtPoints_of_isLocallyOfFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    HasLocallyNoetherianFibersAtPoints B S hS f := fun y => by
  obtain ⟨p, hp⟩ := Quot.exists_rep y
  exact ⟨p, hp, isLocallyNoetherianFiberAt_of_isLocallyOfFiniteType B S hS hX hY f hf p⟩

/-! ### Properties of presheaf morphisms induced by properties of scheme morphisms -/

attribute [local instance] etale_isStableUnderComposition

/-- A property of morphisms of schemes stable under composition induces, by inverse image
along the functor to schemes and passage to the relative property, a property of morphisms of
presheaves on the big fppf site of `S` which is again stable under composition. -/
theorem presheafProperty_comp (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f)
    (hg : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf g) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (f ≫ g) :=
  MorphismProperty.comp_mem _ _ _ hf hg

/-- The base change of a morphism of presheaves on the big fppf site of `S` along another
morphism, that is the first projection of their fibre product, inherits the induced property
of any property `P` of morphisms of schemes. No stability hypothesis on `P` is needed: a
relative property is stable under base change by construction. -/
theorem presheafProperty_pullback_fst (P : MorphismProperty Scheme.{u})
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hg : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf g) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst f g) := by
  let Q := P.inverseImage (BigFppfOver.toScheme B S hS)
  let _ : Q.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  exact MorphismProperty.pullback_fst f g hg

/-- In a cartesian square of presheaves on the big fppf site of `S`, the side parallel to a
morphism with the induced property of a property `P` of morphisms of schemes again has it. -/
theorem presheafProperty_of_isPullback (P : MorphismProperty Scheme.{u})
    {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (hsq : IsPullback a b f g)
    (hg : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf g) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf a := by
  let Q := P.inverseImage (BigFppfOver.toScheme B S hS)
  let _ : Q.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  exact MorphismProperty.of_isPullback hsq.flip hg

/-! ### Local Noetherianity of the fibres of a chart morphism -/

/-- Base changing an étale chart of the target to the residue field of one of its points gives
an étale scheme over the corresponding fibre of the algebraic space, so the fibre of the chart
morphism over a point `v` is locally Noetherian as soon as the fibre of the morphism of spaces
over the image of `v` is. -/
lemma isLocallyNoetherian_fiber_of_etale_pullback_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (hg : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g) (h : U ⟶ V)
    (comm : a ≫ pullback.snd f g = yoneda.map h)
    (haEtale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hf : IsLocallyNoetherianFiber B S hS f (pointsMap B S hS (yoneda.obj V) g
      ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)))) :
    IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber v) := by
  let T := BigFppfOver.toScheme B S hS
  have hgEtale : IsEtale B S hS g := fun W φ hφ =>
    presheafProperty_comp B S hS (@Etale.{u}) φ g hφ hg
  let r := (schemePointRepresentative B S hS V v).siteHom
  let q := FieldValuedPoint.map B S hS (yoneda.obj V) g (schemePointRepresentative B S hS V v)
  have hpoint : pointsMap B S hS (yoneda.obj V) g
      ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) =
      q.class B S hS Y := pointsMap_class B S hS (yoneda.obj V) g _
  have htfae := isLocallyNoetherianFiber_tfae B S hS hX hY f (q.class B S hS Y)
  have hall := (htfae.out 3 2).mp (by rw [← hpoint]; exact hf)
  have hlocal := hall V g v hgEtale hpoint
  change HasEtaleLocalProperty B S hS (pullback f (fieldMorphism B S hS Y q))
    (fun Z : Scheme.{u} => IsLocallyNoetherian Z) at hlocal
  rw [fieldMorphism_map_yoneda B S hS Y g (schemePointRepresentative B S hS V v)] at hlocal
  let Uv := pullback h r
  let av : yoneda.obj Uv ⟶ pullback (pullback.snd f g) (yoneda.map r) :=
    pullback.lift (yoneda.map (pullback.fst h r) ≫ a) (yoneda.map (pullback.snd h r)) (by
      rw [Category.assoc, comm, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg yoneda.map pullback.condition)
  have hav : IsPullback av (yoneda.map (pullback.fst h r))
      (pullback.fst (pullback.snd f g) (yoneda.map r)) a := by
    apply IsPullback.of_right
      (t := (IsPullback.of_hasPullback (pullback.snd f g) (yoneda.map r)).flip)
    · simp only [av, pullback.lift_snd]
      simpa [comm] using ((IsPullback.of_hasPullback h r).map yoneda).flip
    · simp only [av, pullback.lift_fst]
  have havEtale := presheafProperty_of_isPullback B S hS (@Etale.{u}) hav haEtale
  let e := pullbackLeftPullbackSndIso f g (yoneda.map r)
  have hchartEtale : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf (av ≫ e.hom) :=
    (MorphismProperty.cancel_right_of_respectsIso
      (P := (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf) av e.hom).mpr havEtale
  have hFiber := isAlgebraicSpace_pullback B S hS f (yoneda.map r ≫ g) hX
    (isAlgebraicSpace_yoneda B S hS _) hY
  have hUv : IsLocallyNoetherian (T.obj Uv) :=
    (exists_atlas_iff_forall_etale B S hS _
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z) hFiber).mp hlocal Uv (av ≫ e.hom)
        hchartEtale
  have hr : T.map r = (T.obj V).fromSpecResidueField v :=
    toScheme_map_siteHom_schemePointRepresentative B S hS V v
  let eScheme : T.obj Uv ≅ pullback (T.map h) (T.map r) := PreservesPullback.iso T h r
  rw [hr] at eScheme
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (P := fun Z : Scheme.{u} => IsLocallyNoetherian Z) eScheme hUv

/-- Base changing an étale chart of the target to the residue field of one of its points gives
an étale scheme over the corresponding fibre of the algebraic space, so the chart morphism has
locally Noetherian fibres as soon as the morphism of spaces does. -/
lemma locallyNoetherianFibers_of_etale_pullback_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (hg : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g) (h : U ⟶ V)
    (comm : a ≫ pullback.snd f g = yoneda.map h)
    (haEtale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∀ v, IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber v) := fun v =>
  isLocallyNoetherian_fiber_of_etale_pullback_chart B S hS hX hY f V g hg U a h comm haEtale v
    (hf _)

end Space

end AlgebraicGeometry

end
