module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Geometric reducedness of an algebraic space after a field extension

Let `k` be a field and let `X` be an algebraic space over `k`. Geometric reducedness of `X`
over `k` is a condition on the base changes `X_{k'}`: it says that all of them are reduced,
and in positive characteristic it is already implied by the reducedness of a single one, the
base change to `k^{1/p}`. Consequently it is insensitive to replacing `k` by an extension
field: `X` is geometrically reduced at a point exactly when `X_{k'}` is geometrically reduced
at a point above it.

## Main results

* `AlgebraicGeometry.Space.isGeometricallyReduced_tfae`: the six equivalent tests for geometric
  reducedness of Stacks 0E03, phrased on the base changes `U ×_{Spec k} Spec k'` of the étale
  scheme charts `U → X`. The statement in terms of the base changes `X_{k'}` themselves is
  `AlgebraicGeometry.Space.isGeometricallyReduced_tfae_isReduced_baseChange`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedBaseChange`.
* `AlgebraicGeometry.Space.isGeometricallyReducedAt_relocalizeRestrict_iff` and
  `AlgebraicGeometry.Space.isGeometricallyReduced_relocalizeRestrict_iff` are Stacks 0E04,
  the pointwise and the global invariance of geometric reducedness under a field extension.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_of_isGeometricallyReduced`: a
  geometrically reduced algebraic space is reduced.
* `AlgebraicGeometry.Space.isGeometricallyReduced_of_isReduced`: over a perfect field the
  converse holds.

## Implementation notes

The base change of `X` along `k ⊆ k'` is the restriction of `X` to the smaller base
`Spec k'`, `CategoryTheory.OverShriek.relocalizeRestrict` along
`AlgebraicGeometry.Space.fieldExtensionMap`, and it is an algebraic space by Stacks 03I5.
A point of `X_{k'}` lies over a point of `X` when it is carried to it by
`AlgebraicGeometry.Space.pointsOfRelocalizeRestrict`, the map `|X_{k'}| → |X|`.

The chart form of Stacks 0E03 reduces the statement for `X` to the scheme statement for its
étale charts, and lets the extension field range over all of `Type u`. The exponential
characteristic is used in place of the source's `p > 0`, so the statement also covers
characteristic zero, where it degenerates to Stacks 0E02 because `k^{1/p} = k`.

The base-changed chart of Stacks 0E04 is `U ×_{Spec k} Spec k'`, formed in the big fppf site;
`CategoryTheory.OverShriek.restrictYonedaIso` identifies the presheaf it represents with the
restriction of the presheaf represented by `U`, and the étaleness and surjectivity of the
base-changed chart are the two instances of
`CategoryTheory.OverShriek.relative_relocalizeRestrict_map` already used to prove Stacks 03I5.
Given a field-valued point of the base-changed chart, the field-valued point of the original
chart underneath it is obtained by composing its structure morphism with `Spec k' → Spec k`,
so no amalgamation of fields is needed; the global statement then follows from the pointwise
one, since `|X_{k'}| → |X|` is surjective.

## References

* [Stacks Project, Tag 0E03](https://stacks.math.columbia.edu/tag/0E03)
* [Stacks Project, Tag 0E04](https://stacks.math.columbia.edu/tag/0E04)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The characterizations in terms of base change -/

/-- Chart form of Stacks 0E03. Let `k` be a field of exponential characteristic `p` and let `X`
be an algebraic space over `k`. Then `X` is geometrically reduced over `k` if and only if, for
every étale scheme chart `U → X`, the scheme `U ×_{Spec k} Spec k'` is reduced for every field
extension `k'/k`, if and only if this holds for every finite purely inseparable extension
`k'/k`, if and only if it holds for each of `k' = k^{1/p}`, `k^{perf}` and `k̄`.

Reducedness of the base change `X_{k'}` itself is equivalent to the chart condition by
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_relocalizeRestrict_iff`; the statement
in terms of `X_{k'}` is `AlgebraicGeometry.Space.isGeometricallyReduced_tfae_isReduced_baseChange`.
This form lets `k'` range over all fields of `Type u`, not only those whose spectrum lies in the
chosen big fppf site. -/
theorem isGeometricallyReduced_tfae (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (kperf : Type u) [Field kperf] [Algebra k kperf] [ExpChar kperf p] [PerfectRing kperf p]
    [IsPerfectClosure (algebraMap k kperf) p]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] :
    let isReducedBaseChange := fun (k' : Type u) [Field k'] [Algebra k k'] ↦
      ∀ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
        IsEtale B (Spec (.of k)) hk a →
          IsReduced (pullback (B.inclusion.map U.hom)
            (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    List.TFAE
      [ IsGeometricallyReduced k B hk X hX,
        ∀ (k' : Type u) [Field k'] [Algebra k k'], isReducedBaseChange k',
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'], isReducedBaseChange k',
        isReducedBaseChange (AdjoinPthRoots k),
        isReducedBaseChange kperf,
        isReducedBaseChange kbar ] := by
  have hChart := isGeometricallyReduced_iff_forall_etaleChart k B hk X hX
  have hScheme := fun U : BigFppfOver B (Spec (.of k)) hk ↦
    _root_.AlgebraicGeometry.geometricallyReduced_tfae k p (B.inclusion.map U.hom) kperf kbar
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h k' _ _ U a ha
      have hiff := (hScheme U).out 1 2
      exact hiff.mp (hChart.mp h U a ha) k'
    · intro h
      refine hChart.mpr fun U a ha ↦ ?_
      have hiff := (hScheme U).out 2 1
      exact hiff.mp fun k' _ _ ↦ h k' U a ha
  tfae_have 2 ↔ 3 := by
    refine ⟨fun h k' _ _ _ _ U a ha ↦ h k' U a ha, fun h k' _ _ U a ha ↦ ?_⟩
    have hiff := (hScheme U).out 3 2
    exact hiff.mp (fun L _ _ _ _ ↦ h L U a ha) k'
  tfae_have 3 ↔ 4 := by
    constructor
    · intro h U a ha
      have hiff := (hScheme U).out 3 4
      exact hiff.mp fun k' _ _ _ _ ↦ h k' U a ha
    · intro h k' _ _ _ _ U a ha
      have hiff := (hScheme U).out 4 3
      exact hiff.mp (h U a ha) k'
  tfae_have 4 ↔ 5 :=
    ⟨fun h U a ha ↦ ((hScheme U).out 4 5).mp (h U a ha),
      fun h U a ha ↦ ((hScheme U).out 5 4).mp (h U a ha)⟩
  tfae_have 5 ↔ 6 :=
    ⟨fun h U a ha ↦ ((hScheme U).out 5 6).mp (h U a ha),
      fun h U a ha ↦ ((hScheme U).out 6 5).mp (h U a ha)⟩
  tfae_finish

/-! ### Invariance under extension of the ground field -/

section FieldExtension

/-- Geometric reducedness at a point of a scheme over a field is carried along an isomorphism
of schemes over that field. -/
private theorem isGeometricallyReducedAt_of_iso {F : Type u} [Field F] {Y Z : Scheme.{u}}
    (f : Y ⟶ Spec (.of F)) (g : Z ⟶ Spec (.of F)) (e : Y ≅ Z) (he : e.hom ≫ g = f) (y : Y) :
    _root_.AlgebraicGeometry.IsGeometricallyReducedAt f y →
      _root_.AlgebraicGeometry.IsGeometricallyReducedAt g (e.hom y) := by
  simp only [_root_.AlgebraicGeometry.IsGeometricallyReducedAt]
  intro h L _ _ z hz
  let φ : Spec (.of L) ⟶ Spec (.of F) := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let eL : (pullback f φ : Scheme) ≅ (pullback g φ : Scheme) :=
    asIso (pullback.map f φ g φ e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← he]) (by simp))
  have hproj : eL.hom ≫ pullback.fst g φ = pullback.fst f φ ≫ e.hom := pullback.lift_fst _ _ _
  have hfst (w : (pullback f φ : Scheme)) :
      pullback.fst g φ (eL.hom w) = e.hom (pullback.fst f φ w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun m : (pullback f φ : Scheme) ⟶ Z ↦ m w) hproj
  have hinj : Function.Injective e.hom := fun a b hab ↦ by simpa using congrArg e.inv hab
  have hz' : pullback.fst f φ (eL.inv z) = y := by
    refine hinj ?_
    rw [← hfst (eL.inv z)]
    simpa using hz
  have hzz : eL.hom (eL.inv z) = z := by
    rw [← Scheme.Hom.comp_apply, eL.inv_hom_id]
    rfl
  have : _root_.IsReduced ((pullback f φ).presheaf.stalk (eL.inv z)) := h L (eL.inv z) hz'
  let E := (asIso (eL.hom.stalkMap (eL.inv z))).commRingCatIsoToRingEquiv
  rw [← hzz]
  exact isReduced_of_injective E.toRingHom E.injective

/-- Geometric reducedness at a point of a scheme over a field transports along an isomorphism
of schemes over that field. -/
private theorem isGeometricallyReducedAt_congr_iso {F : Type u} [Field F] {Y Z : Scheme.{u}}
    (f : Y ⟶ Spec (.of F)) (g : Z ⟶ Spec (.of F)) (e : Y ≅ Z) (he : e.hom ≫ g = f) (y : Y) :
    _root_.AlgebraicGeometry.IsGeometricallyReducedAt f y ↔
      _root_.AlgebraicGeometry.IsGeometricallyReducedAt g (e.hom y) := by
  refine ⟨isGeometricallyReducedAt_of_iso f g e he y, fun h ↦ ?_⟩
  simpa using isGeometricallyReducedAt_of_iso g f e.symm (by rw [← he]; simp) (e.hom y) h

/-- Geometric reducedness of an algebraic space at a point is tested by the scheme-level
property at the point of any étale chart selected by a field-valued point above it. -/
private theorem isGeometricallyReducedAt_iff_of_etaleChart (k : Type u) [Field k]
    (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (x : points B (Spec (.of k)) hk X)
    (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X)
    (ha : IsEtale B (Spec (.of k)) hk a) (q : FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj U))
    (hq : pointsMap B (Spec (.of k)) hk (yoneda.obj U) a (q.class B (Spec (.of k)) hk _) = x) :
    IsGeometricallyReducedAt k B hk X hX x ↔
      _root_.AlgebraicGeometry.IsGeometricallyReducedAt (B.inclusion.map U.hom)
        (schemePoint B (Spec (.of k)) hk U q) :=
  ⟨fun h ↦ (isGeometricallyReducedAt_iff_forall_etaleChart k B hk X hX x).mp h U a ha q hq,
    fun h ↦ (isGeometricallyReducedAt_iff_exists_etaleChart k B hk X hX x).mpr
      ⟨U, a, ha, q, hq, h⟩⟩

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (.of k))) (hk' : B.Contains (Spec (.of k')))
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- The base change along `k ⊆ k'` of a chart of `X` with a property of morphisms of schemes
inherits that property: restriction to a smaller base is reindexing, which leaves the
underlying morphism of schemes untouched. -/
private theorem presheaf_relocalizeRestrict_chart
    (Q : MorphismProperty Scheme.{u}) (hQ : Q.RespectsIso)
    (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf a) :
    (MorphismProperty.inverseImage Q
        (BigFppfOver.toScheme B (Spec (.of k')) hk')).presheaf
      ((OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom ≫
        (OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).map a) := by
  have _ : Q.RespectsIso := hQ
  have _ : (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B (Spec (.of k')) hk')).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (OverShriek.relative_relocalizeRestrict_map (fieldExtensionMap B k k' hk hk')
      (inverseImage_restrictReindexSnd B (Spec (.of k')) (Spec (.of k)) hk' hk
        (fieldExtensionMap B k k' hk hk') Q) ha)

/-- A field-valued point of the base-changed chart, read as a field-valued point of the
original chart: compose its structure morphism with `Spec k' → Spec k` and its section with
the first projection of the base change. -/
private noncomputable def fieldValuedPointOfBaseChange
    (U : BigFppfOver B (Spec (.of k)) hk)
    (q : FieldValuedPoint B (Spec (.of k')) hk'
      (yoneda.obj ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U))) :
    FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj U) :=
  FieldValuedPoint.ofRelocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
    (fieldExtensionMap B k k' hk hk') (yoneda.obj U)
    (FieldValuedPoint.map B (Spec (.of k')) hk'
      (yoneda.obj ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U))
      (OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom q)

/-- Applying a morphism of presheaves over `Spec k` commutes with reading a field-valued point
of a restriction as a field-valued point over `Spec k`. -/
private theorem ofRelocalizeRestrict_map
    {F G : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (q : FieldValuedPoint B (Spec (.of k')) hk'
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).obj F)) :
    FieldValuedPoint.ofRelocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
        (fieldExtensionMap B k k' hk hk') G
        (FieldValuedPoint.map B (Spec (.of k')) hk' _
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).map α) q) =
      FieldValuedPoint.map B (Spec (.of k)) hk F α
        (FieldValuedPoint.ofRelocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
          (fieldExtensionMap B k k' hk hk') F q) := rfl

/-- The point of `X` under the point of `X_{k'}` selected by a field-valued point of the
base-changed chart is the one selected by the underlying field-valued point of the chart. -/
private theorem pointsOfRelocalizeRestrict_pointsMap_baseChange
    (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X)
    (q : FieldValuedPoint B (Spec (.of k')) hk'
      (yoneda.obj ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U))) :
    pointsOfRelocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
        (fieldExtensionMap B k k' hk hk') X
        (pointsMap B (Spec (.of k')) hk' _
          ((OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom ≫
            (OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).map a)
          (q.class B (Spec (.of k')) hk' _)) =
      pointsMap B (Spec (.of k)) hk (yoneda.obj U) a
        ((fieldValuedPointOfBaseChange k k' B hk hk' U q).class B (Spec (.of k)) hk
          (yoneda.obj U)) := by
  rw [pointsMap_class, pointsOfRelocalizeRestrict_class, pointsMap_class]
  refine congrArg (fun r ↦ FieldValuedPoint.class B (Spec (.of k)) hk X r) ?_
  rw [show FieldValuedPoint.map B (Spec (.of k')) hk' _
      ((OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom ≫
        (OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).map a) q =
    FieldValuedPoint.map B (Spec (.of k')) hk' _
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).map a)
      (FieldValuedPoint.map B (Spec (.of k')) hk' _
        (OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom q) from rfl]
  exact ofRelocalizeRestrict_map k k' B hk hk' a _

/-- The scheme point of the base-changed chart selected by a field-valued point maps, along
the first projection of the base change, to the scheme point of the original chart selected by
the field-valued point underneath it. -/
private theorem schemePoint_fieldValuedPointOfBaseChange
    (U : BigFppfOver B (Spec (.of k)) hk)
    (q : FieldValuedPoint B (Spec (.of k')) hk'
      (yoneda.obj ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U))) :
    (B.inclusion.map (pullback.fst U.hom (fieldExtensionMap B k k' hk hk')))
        (schemePoint B (Spec (.of k')) hk'
          ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U) q) =
      schemePoint B (Spec (.of k)) hk U (fieldValuedPointOfBaseChange k k' B hk hk' U q) := by
  change (B.inclusion.map (pullback.fst U.hom (fieldExtensionMap B k k' hk hk')))
      ((B.inclusion.map q.value.left) (IsLocalRing.closedPoint q.carrier)) =
    (B.inclusion.map
      ((OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom.app
        (Opposite.op (q.siteObject B (Spec (.of k')) hk' _)) q.value).left)
      (IsLocalRing.closedPoint q.carrier)
  rw [OverShriek.restrictYonedaIso_hom_app_left, Functor.map_comp]
  rfl

/-- The scheme underlying the base change of a chart along `k ⊆ k'` is the fibre product of
the chart with `Spec k'` over `Spec k`: the big fppf site has fibre products and its inclusion
into all schemes preserves them. -/
private theorem isPullback_baseChangeChart (U : BigFppfOver B (Spec (.of k)) hk) :
    IsPullback (B.inclusion.map (pullback.fst U.hom (fieldExtensionMap B k k' hk hk')))
      (B.inclusion.map (pullback.snd U.hom (fieldExtensionMap B k k' hk hk')))
      (B.inclusion.map U.hom) (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
  have _ : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  have hsq : IsPullback (pullback.fst U.hom (fieldExtensionMap B k k' hk hk'))
      (pullback.snd U.hom (fieldExtensionMap B k k' hk hk')) U.hom
      (fieldExtensionMap B k k' hk hk') := IsPullback.of_hasPullback _ _
  have h := hsq.map B.inclusion
  rwa [map_fieldExtensionMap] at h

/-- **Stacks 0E04 on a chart.** An étale scheme chart of `X` is geometrically reduced at a
point exactly when its base change along `k ⊆ k'` is geometrically reduced at a point above
it: this is the scheme statement Stacks 0384, transported along the identification of the
base change of the chart with the fibre product of schemes. -/
private theorem isGeometricallyReducedAt_baseChangeChart_iff
    (U : BigFppfOver B (Spec (.of k)) hk)
    (q : FieldValuedPoint B (Spec (.of k')) hk'
      (yoneda.obj ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U))) :
    _root_.AlgebraicGeometry.IsGeometricallyReducedAt (B.inclusion.map U.hom)
        (schemePoint B (Spec (.of k)) hk U
          (fieldValuedPointOfBaseChange k k' B hk hk' U q)) ↔
      _root_.AlgebraicGeometry.IsGeometricallyReducedAt
        (B.inclusion.map ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U).hom)
        (schemePoint B (Spec (.of k')) hk'
          ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U) q) := by
  have hpb := isPullback_baseChangeChart k k' B hk hk' U
  have hbase : pullback.fst (B.inclusion.map U.hom)
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      (hpb.isoPullback.hom (schemePoint B (Spec (.of k')) hk'
        ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U) q)) =
      schemePoint B (Spec (.of k)) hk U
        (fieldValuedPointOfBaseChange k k' B hk hk' U q) := by
    rw [← schemePoint_fieldValuedPointOfBaseChange k k' B hk hk' U q,
      ← Scheme.Hom.comp_apply, hpb.isoPullback_hom_fst]
  refine (_root_.AlgebraicGeometry.isGeometricallyReducedAt_iff_baseChange_fieldExtension
    k k' (B.inclusion.map U.hom) _ _ hbase).trans ?_
  exact (isGeometricallyReducedAt_congr_iso
    (B.inclusion.map ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U).hom)
    (pullback.snd (B.inclusion.map U.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))) hpb.isoPullback
    hpb.isoPullback_hom_snd _).symm

/-- **Stacks 0E04, pointwise statement.** An algebraic space over a field `k` is geometrically
reduced at a point `x` exactly when its base change to a field extension `k'/k` is
geometrically reduced at any point `x'` lying over `x`. -/
@[stacks 0E04 "pointwise equivalence"]
theorem isGeometricallyReducedAt_relocalizeRestrict_iff
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (x : points B (Spec (.of k)) hk X)
    (x' : points B (Spec (.of k')) hk'
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).obj X))
    (hx : pointsOfRelocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
      (fieldExtensionMap B k k' hk hk') X x' = x) :
    IsGeometricallyReducedAt k B hk X hX x ↔
      IsGeometricallyReducedAt k' B hk'
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).obj X)
        (isAlgebraicSpace_relocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
          (fieldExtensionMap B k k' hk hk') X hX) x' := by
  have hX' := isAlgebraicSpace_relocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
    (fieldExtensionMap B k k' hk hk') X hX
  obtain ⟨U, a, hasurj, haetale⟩ := hX.exists_atlas
  have haetale' : IsEtale B (Spec (.of k)) hk a :=
    (isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hk a).mpr haetale
  have hetale' := presheaf_relocalizeRestrict_chart k k' B hk hk' X
    (@AlgebraicGeometry.Etale.{u}) AlgebraicGeometry.etale_respectsIso U a haetale
  have hsurj' := presheaf_relocalizeRestrict_chart k k' B hk hk' X
    (@AlgebraicGeometry.Surjective.{u}) inferInstance U a hasurj
  obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B (Spec (.of k')) hk' _ hX'
    ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U) _).mp hsurj' x'
  obtain ⟨q, rfl⟩ := Quot.exists_rep z
  have hz' : pointsMap B (Spec (.of k')) hk' _
      ((OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom ≫
        (OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).map a)
      (q.class B (Spec (.of k')) hk' _) = x' := hz
  have hetale'' : IsEtale B (Spec (.of k')) hk'
      ((OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom ≫
        (OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).map a) :=
    (isEtale_iff_presheaf_of_yoneda B (Spec (.of k')) hk' _).mpr hetale'
  have hqx : pointsMap B (Spec (.of k)) hk (yoneda.obj U) a
      ((fieldValuedPointOfBaseChange k k' B hk hk' U q).class B (Spec (.of k)) hk
        (yoneda.obj U)) = x := by
    rw [← pointsOfRelocalizeRestrict_pointsMap_baseChange k k' B hk hk' X U a q, hz', hx]
  have hL := isGeometricallyReducedAt_iff_of_etaleChart k B hk X hX x U a haetale' _ hqx
  have hR := isGeometricallyReducedAt_iff_of_etaleChart k' B hk' _ hX' _ _ _ hetale'' q rfl
  rw [← hz']
  exact hL.trans
    ((isGeometricallyReducedAt_baseChangeChart_iff k k' B hk hk' U q).trans hR.symm)

/-- **Stacks 0E04, global statement.** An algebraic space over a field `k` is geometrically
reduced over `k` exactly when its base change to a field extension `k'/k` is geometrically
reduced over `k'`. -/
@[stacks 0E04 "global equivalence"]
theorem isGeometricallyReduced_relocalizeRestrict_iff
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsGeometricallyReduced k B hk X hX ↔
      IsGeometricallyReduced k' B hk'
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).obj X)
        (isAlgebraicSpace_relocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
          (fieldExtensionMap B k k' hk hk') X hX) := by
  refine ⟨fun h x' ↦
    (isGeometricallyReducedAt_relocalizeRestrict_iff k k' B hk hk' X hX _ x' rfl).mp (h _),
    fun h x ↦ ?_⟩
  obtain ⟨x', hx'⟩ := surjective_pointsOfRelocalizeRestrict_fieldExtension B k k' hk hk'
    (fieldExtensionMap B k k' hk hk') X x
  exact (isGeometricallyReducedAt_relocalizeRestrict_iff k k' B hk hk' X hX x x' hx').mpr (h x')

end FieldExtension

/-! ### Comparison with plain reducedness -/

section Reduced

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- A scheme geometrically reduced over a field is reduced: its base change along the identity
of the ground field is the scheme itself. -/
@[ega "IV 4.6.1" "(b) ⇒ (e)", ega "IV 7.3.9" "(i): (vi') implies (vi)"]
private theorem isReduced_of_geometricallyReduced (F : Type u) [Field F] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of F)) [_root_.AlgebraicGeometry.GeometricallyReduced f] : IsReduced Y :=
  _root_.AlgebraicGeometry.GeometricallyReduced.geometrically_isReduced
    (𝟙 (Spec (.of F))) (𝟙 Y) f IsPullback.of_id_fst

/-- A geometrically reduced algebraic space over a field is reduced: by Stacks 0DMS every
étale scheme chart is geometrically reduced over the field, hence reduced. -/
theorem hasEtaleLocalProperty_isReduced_of_isGeometricallyReduced
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (h : IsGeometricallyReduced k B hk X hX) :
    HasEtaleLocalProperty B (Spec (.of k)) hk X (fun Y : Scheme.{u} => IsReduced Y) := by
  refine (exists_atlas_iff_forall_etale B (Spec (.of k)) hk X
    (fun Y : Scheme.{u} => IsReduced Y) hX).mpr fun V g hg ↦ ?_
  have hgr := (isGeometricallyReduced_iff_forall_etaleChart k B hk X hX).mp h V g
    (isEtale_of_presheaf_etale B (Spec (.of k)) hk hg)
  have := hgr
  exact isReduced_of_geometricallyReduced k (B.inclusion.map V.hom)

/-- **Stacks 0E02, part (2).** Over a perfect field a reduced algebraic space is geometrically
reduced: by Stacks 0DMS it suffices that every étale scheme chart is geometrically reduced,
which over a perfect field is Stacks 020I. -/
@[stacks 0E02 "part (2)"]
theorem isGeometricallyReduced_of_isReduced [PerfectField k]
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hred : HasEtaleLocalProperty B (Spec (.of k)) hk X (fun Y : Scheme.{u} => IsReduced Y)) :
    IsGeometricallyReduced k B hk X hX := by
  refine (isGeometricallyReduced_iff_forall_etaleChart k B hk X hX).mpr fun V g hg ↦ ?_
  have hV : IsReduced (B.inclusion.obj V.left) :=
    (exists_atlas_iff_forall_etale B (Spec (.of k)) hk X
      (fun Y : Scheme.{u} => IsReduced Y) hX).mp hred V g
      (presheaf_etale_of_isEtale B (Spec (.of k)) hk hg)
  have := hV
  exact _root_.AlgebraicGeometry.geometricallyReduced_of_isReduced (B.inclusion.map V.hom)

end Reduced

end AlgebraicGeometry.Space

end
