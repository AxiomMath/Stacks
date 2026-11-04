module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReducedConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionFieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed

/-!
# Part (2) of Stacks 0E1I: a proper scheme over a field

Let `X` be a proper scheme of dimension at most one over a field `k`. Part (2) of Stacks 0E1I
says that the family of curves `X → Spec k` lies in `Curves^{grc,1}` exactly when `X` is
geometrically reduced, geometrically connected and of dimension `1` over `k`. This file proves the
three translations from the fibrewise conditions of `AlgebraicGeometry.IsGrc1CurveFamily` on the
algebraic space side to the scheme-theoretic notions over `k`.

## Main definitions

* `AlgebraicGeometry.fieldSiteObject`: the spectrum of a field as an object of the big fppf site
  of `Spec(ℤ)`, and `AlgebraicGeometry.fieldSiteObject.point` its tautological field-valued
  point.

## Main results

* `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_pullback_of_isSepClosed`: a scheme
  over a field is geometrically connected exactly when its base change to one separably closed
  extension is connected (Stacks 054N and 0363).
* `AlgebraicGeometry.Space.geometricFiberComponentCount_yoneda_map_eq_one_iff`: the fibre of a
  represented morphism over a field-valued point has one connected component exactly when the
  scheme-theoretic fibre product is connected.
* `AlgebraicGeometry.Space.forall_numberGeometricConnectedComponents_yoneda_map_eq_one_iff`:
  the geometric fibres of `X → Spec k` are connected exactly when `X` is geometrically connected
  over `k`.
* `AlgebraicGeometry.Space.fiberDimension_yoneda_map_fieldSiteObject`: the fibre dimension of
  `X → Spec k` is the dimension of `X`.
* `AlgebraicGeometry.isGrc1CurveFamily_curveFamilyOfSchemeMorphism_iff`: condition (2)(b) of
  Stacks 0E1I, for the family of curves of a proper flat morphism `X → Spec k` of the site, from
  the translation of geometric reducedness
  (`AlgebraicGeometry.Space.forall_isGeometricallyReducedFibreAt_yoneda_map_iff`, taken as an
  input in its exact form).

## Implementation notes

The declaration taking the translation of geometric reducedness as an argument is
`AlgebraicGeometry.isGrc1CurveFamily_curveFamilyOfSchemeMorphism_iff`; it is applied to the
library's translation in
`AlgebraicGeometry.isGrc1CurveFamily_curveFamilyOfSchemeMorphism_iff_geometricallyReduced`, and
part (2) of Stacks 0E1I is `AlgebraicGeometry.factors_curvesGrc1_over_field_iff`. The family of
curves of a proper scheme over a field is the one of
`AlgebraicGeometry.curveFamilyOfSchemeMorphism`, at a morphism `X ⟶ Spec k` of the site.

## References

* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
* [Stacks Project, Tag 054N](https://stacks.math.columbia.edu/tag/054N)
* [Stacks Project, Tag 0363](https://stacks.math.columbia.edu/tag/0363)
* [Stacks Project, Tag 0E1B](https://stacks.math.columbia.edu/tag/0E1B)
* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

/-- **Geometric connectedness over a field is read on one separably closed extension.** A scheme
`X` over a field `k` is geometrically connected exactly when its base change along a morphism
`Spec K ⟶ Spec k` with `K` separably closed is connected: the base change is geometrically
connected over `K` exactly when it is connected (Stacks 0363), and geometric connectedness
descends along field extensions (Stacks 054N). -/
theorem geometricallyConnected_iff_connectedSpace_pullback_of_isSepClosed {k K : Type u}
    [Field k] [Field K] [IsSepClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (s : Spec (.of K) ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔ ConnectedSpace ↥(pullback f s) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  let : Algebra k K := φ.hom.toAlgebra
  have hφ : φ = CommRingCat.ofHom (algebraMap k K) := rfl
  rw [hφ, geometricallyConnected_iff_baseChange_fieldExtension k K f,
    geometricallyConnected_iff_connectedSpace K]

/-- Connectedness of a topological space is its having exactly one connected component. -/
theorem connectedSpace_iff_cardinalMk_connectedComponents_eq_one (α : Type*)
    [TopologicalSpace α] :
    ConnectedSpace α ↔ Cardinal.mk (_root_.ConnectedComponents α) = 1 := by
  rw [Cardinal.eq_one_iff_unique, ConnectedComponents.nonempty_iff_nonempty]
  refine ⟨fun _ => ⟨inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨hs, ⟨x⟩⟩
  rw [connectedSpace_iff_connectedComponent]
  exact ⟨x, Set.eq_univ_of_forall fun y => (ConnectedComponents.coe_eq_coe').mp
    (hs.elim (ConnectedComponents.mk y) (ConnectedComponents.mk x))⟩

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The fibre of a represented morphism over a field-valued point.** For a morphism `g : T ⟶ W`
of the big fppf site and a field-valued point `q` of `W`, the fibre of `h_T ⟶ h_W` over `q` has
exactly one connected component exactly when the scheme-theoretic fibre product
`T ×_W Spec κ(q)` is connected: the fibre product is formed in the site, Yoneda preserves it,
and the points of a represented presheaf are the points of the representing scheme. -/
theorem geometricFiberComponentCount_yoneda_map_eq_one_iff {T W : BigFppfOver B S hS}
    (g : T ⟶ W) (q : FieldValuedPoint B S hS (yoneda.obj W)) :
    geometricFiberComponentCount B S hS (yoneda.map g) q = 1 ↔
      ConnectedSpace ↥(pullback ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map q.value)) := by
  have hσ : yonedaEquiv.symm q.value = yoneda.map q.value :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm
  have hsq : IsPullback (yoneda.map (pullback.fst g q.value)) (yoneda.map (pullback.snd g q.value))
      (yoneda.map g) (yonedaEquiv.symm q.value) := by
    rw [hσ]
    exact (IsPullback.of_hasPullback g q.value).map yoneda
  let h : points B S hS (pullback (yoneda.map g) (yonedaEquiv.symm q.value)) ≃ₜ
      ↥(pullback ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map q.value)) :=
    (pointsHomeomorphOfIso B S hS hsq.isoPullback).symm.trans
      ((schemePointsHomeomorph B S hS _).trans ((IsPullback.of_hasPullback g q.value).map
        (BigFppfOver.toScheme B S hS)).isoPullback.schemeIsoToHomeo)
  unfold geometricFiberComponentCount
  rw [Cardinal.toENat_eq_one, ← connectedSpace_iff_cardinalMk_connectedComponents_eq_one]
  exact h.connectedSpace_iff

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The spectrum of a field `k`, with a structure morphism `t` to `Spec(ℤ)`, as an object of the
big fppf site of `Spec(ℤ)`. -/
abbrev fieldSiteObject {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (t : Spec (.of k) ⟶ integerBase) : BigFppfOver B integerBase hZ :=
  Over.mk (⟨t⟩ : B.obj hk ⟶ B.obj hZ)

/-- The tautological field-valued point of the spectrum of a field: the field itself, with the
identity as its section. -/
def fieldSiteObject.point {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (t : Spec (.of k) ⟶ integerBase) :
    Space.FieldValuedPoint B integerBase hZ (yoneda.obj (fieldSiteObject B hZ hk t)) where
  carrier := k
  contained := hk
  toBase := t
  value := 𝟙 _

variable {B hZ}

namespace Space

variable {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {t : Spec (.of k) ⟶ integerBase}

/-- The spectrum of a field has one point: every point of the presheaf it represents is the class
of the tautological field-valued point. -/
theorem eq_class_fieldSiteObject_point
    (s : points B integerBase hZ (yoneda.obj (fieldSiteObject B hZ hk t))) :
    s = (fieldSiteObject.point B hZ hk t).class B integerBase hZ _ := by
  obtain ⟨q, rfl⟩ := Quot.exists_rep s
  exact points_yoneda_eq_fieldPoint B integerBase hZ (fieldSiteObject.point B hZ hk t) q

/-- **The geometric fibres of a scheme over a field are connected exactly when it is
geometrically connected.** For a morphism `g : T ⟶ Spec k` of the site, the geometric fibres of
`h_T ⟶ h_{Spec k}` have one connected component each exactly when the scheme `T` is
geometrically connected over `k`. -/
theorem forall_numberGeometricConnectedComponents_yoneda_map_eq_one_iff
    {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ fieldSiteObject B hZ hk t) :
    (∀ s, numberGeometricConnectedComponents B integerBase hZ (yoneda.map g) s = 1) ↔
      GeometricallyConnected
        ((BigFppfOver.toScheme B integerBase hZ).map g : _ ⟶ Spec (.of k)) := by
  have key : ∀ q : GeometricPoint B integerBase hZ (yoneda.obj (fieldSiteObject B hZ hk t)),
      numberGeometricConnectedComponents B integerBase hZ (yoneda.map g) q.image = 1 ↔
        GeometricallyConnected
          ((BigFppfOver.toScheme B integerBase hZ).map g : _ ⟶ Spec (.of k)) := by
    intro q
    have : IsAlgClosed q.val.carrier := q.property
    rw [numberGeometricConnectedComponents_eq B integerBase hZ
      (isAlgebraicSpace_yoneda B integerBase hZ T) (isAlgebraicSpace_yoneda B integerBase hZ _)
      (yoneda.map g) q, geometricFiberComponentCount_yoneda_map_eq_one_iff]
    exact (geometricallyConnected_iff_connectedSpace_pullback_of_isSepClosed _ _).symm
  refine ⟨fun h => ?_, fun h s => ?_⟩
  · obtain ⟨q, -⟩ := exists_geometricRepresentative B integerBase hZ _
      ((fieldSiteObject.point B hZ hk t).class B integerBase hZ _)
    exact (key q).mp (h _)
  · obtain ⟨q, rfl⟩ := exists_geometricRepresentative B integerBase hZ _ s
    exact (key q).mpr h

/-- **The fibre dimension of a scheme over a field is its dimension.** For a morphism of finite
type `g : T ⟶ Spec k` of the site, the dimension of the fibre of `h_T ⟶ h_{Spec k}` over the
point of `Spec k` is the Krull dimension of `T` (Stacks 0D4M at the tautological point). -/
theorem fiberDimension_yoneda_map_fieldSiteObject {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ fieldSiteObject B hZ hk t)
    (hf : IsFiniteType B integerBase hZ (yoneda.map g))
    (s : points B integerBase hZ (yoneda.obj (fieldSiteObject B hZ hk t))) :
    fiberDimension B integerBase hZ (yoneda.map g) s =
      topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
  let p := fieldSiteObject.point B hZ hk t
  have hσ : yonedaEquiv.symm p.value = (𝟙 _ : yoneda.obj (p.siteObject B integerBase hZ _) ⟶
      yoneda.obj (fieldSiteObject B hZ hk t)) :=
    (Equiv.symm_apply_eq _).mpr rfl
  have : IsIso (yonedaEquiv.symm p.value) := by
    rw [hσ]
    exact IsIso.id _
  rw [eq_class_fieldSiteObject_point s, (fiberDimension_eq_dimension_pullback B integerBase hZ
      (yoneda.map g) (isAlgebraicSpace_yoneda B integerBase hZ T)
      (isAlgebraicSpace_yoneda B integerBase hZ _) hf p).1,
    dimension_eq_of_iso B integerBase hZ _ (isAlgebraicSpace_yoneda B integerBase hZ T)
      (asIso (pullback.snd (yonedaEquiv.symm p.value) (yoneda.map g))),
    dimension_yoneda_eq_topologicalKrullDim]

end Space

/-! ### Part (2) of Stacks 0E1I -/

section PartTwo

variable {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {t : Spec (.of k) ⟶ integerBase}

-- The translation of geometric reducedness of the fibres of a represented morphism into
-- geometric reducedness of the morphism of schemes, in the exact form of
-- `AlgebraicGeometry.Space.forall_isGeometricallyReducedFibreAt_yoneda_map_iff` over `Spec(ℤ)`.
variable (hyred : ∀ {U A : BigFppfOver B integerBase hZ} (g : A ⟶ U),
    (∀ y, Space.IsGeometricallyReducedFibreAt B integerBase hZ (yoneda.map g)
        (isAlgebraicSpace_yoneda B integerBase hZ A) (isAlgebraicSpace_yoneda B integerBase hZ U)
        y) ↔
      GeometricallyReduced ((BigFppfOver.toScheme B integerBase hZ).map g))

include hyred in
/-- **Condition (2)(b) of Stacks 0E1I.** Let `X` be a proper scheme of dimension at most one over
a field `k`, presented by a proper flat morphism `g : X ⟶ Spec k` of finite presentation of the
big fppf site of `Spec(ℤ)`. The family of curves of `g` has geometric fibres that are reduced,
connected and of dimension `1` exactly when `X` is geometrically reduced over `k`, geometrically
connected over `k`, and of dimension `1`. -/
theorem isGrc1CurveFamily_curveFamilyOfSchemeMorphism_iff {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ fieldSiteObject B hZ hk t)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsGrc1CurveFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      GeometricallyReduced ((BigFppfOver.toScheme B integerBase hZ).map g) ∧
        GeometricallyConnected
          ((BigFppfOver.toScheme B integerBase hZ).map g : _ ⟶ Spec (.of k)) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 := by
  let X := curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim
  have hdimiff : CurveFamily.HasFibresOfDimensionOne B hZ X ↔
      topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 := by
    unfold CurveFamily.HasFibresOfDimensionOne
    have hfd := Space.fiberDimension_yoneda_map_fieldSiteObject g X.proper.2.1
    simp only [Nat.cast_one]
    exact ⟨fun h => (hfd _).symm.trans
      (h ((fieldSiteObject.point B hZ hk t).class B integerBase hZ _)), fun h s => (hfd s).trans h⟩
  exact and_congr (hyred g)
    (and_congr (Space.forall_numberGeometricConnectedComponents_yoneda_map_eq_one_iff g) hdimiff)

end PartTwo

end AlgebraicGeometry

end
