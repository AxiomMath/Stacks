module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReducedOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusStrictlyFull
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreOverFieldValuedPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections

/-!
# Families of curves whose geometric fibres are reduced, connected and of dimension one

The stack `Curves^{grc,1}` of Stacks 0E1I consists of the families of curves `f : X → S` whose
geometric fibres are reduced, connected and of dimension `1`. This file defines that condition
on a family of curves, proves that it is inherited along morphisms of families (so it cuts out a
strictly full subcategory of `Curves`, fibred in groupoids over the big fppf site of `Spec(ℤ)`),
that it gives `k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields (the input of Stacks 0E1J), and
that for the family of a proper scheme `X` of dimension at most one over a field `k` it says
that `X` is geometrically reduced, geometrically connected and of dimension `1`.

## Main definitions

* `AlgebraicGeometry.IsGrcDimOneFamily`: the geometric fibres of the family are reduced and
  connected, and the family has relative dimension `1`.
* `AlgebraicGeometry.curvesGrcDimOne`: the strictly full subcategory `Curves^{grc,1}` of
  families with that property, as a category fibred in groupoids over the big fppf site of
  `Spec(ℤ)`.

## Main results

* `AlgebraicGeometry.CurveFamily.isGrcDimOneFamily_of_hom`: the property passes to every family
  mapping to a family with the property.
* `AlgebraicGeometry.isGeometricallyReducedFamily_iff_forall_geometricPoint`: the fibres of a
  family of curves are geometrically reduced (Stacks 0E08) exactly when its geometric fibres are
  reduced.
* `AlgebraicGeometry.CurveFamily.bijective_algebraMap_fibre_of_isGrcDimOneFamily`:
  `k = H⁰(X_k, 𝒪_{X_k})` on every fibre over a field (Stacks 0E0S).
* `AlgebraicGeometry.isGrcDimOneFamily_curveFamilyOfScheme_iff`: for the family of a proper
  scheme `X` of dimension at most one over a field `k`, the property says that `X` is
  geometrically reduced, geometrically connected and of dimension `1`.

## Implementation notes

"Reduced" for a geometric fibre `X_ȳ`, an algebraic space over the algebraically closed field of
`ȳ`, is reducedness of an étale chart (`AlgebraicGeometry.Space.HasEtaleLocalProperty`), and
"connected" is connectedness of its space of points (`AlgebraicGeometry.Space.ConnectedPoints`),
as in `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_fibre_of_geometricFibres`.
"The geometric fibres have dimension `1`" is read as relative dimension `1` in the sense of
Stacks 06LR (2) (`AlgebraicGeometry.Space.HasRelativeDimension`), the reading the source's proof
of Stacks 0E1I uses: the dimension of a fibre is the dimension of its geometric fibres, and a
connected Noetherian scheme of dimension `1` has all its irreducible components of dimension `1`,
so it is equidimensional of dimension `1`, which is relative dimension `1` over the field. For
the family of a scheme over a field this equivalence is proved here
(`AlgebraicGeometry.isGrcDimOneFamily_curveFamilyOfScheme_iff`).

No declaration here carries a Stacks attribute: Stacks 0E1I, whose condition this is, is not
registered here.

## References

* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
* [Stacks Project, Tag 0E1K](https://stacks.math.columbia.edu/tag/0E1K)
* [Stacks Project, Tag 0E07](https://stacks.math.columbia.edu/tag/0E07)
* [Stacks Project, Tag 0E0S](https://stacks.math.columbia.edu/tag/0E0S)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The fibre of a cartesian square.** For a cartesian square of algebraic spaces with
`f' : X' ⟶ Y'` the base change of `f : X ⟶ Y` along `g : Y' ⟶ Y`, the fibre of `f'` over a
field-valued point of `Y'` is isomorphic to the fibre of `f` over its image in `Y`. -/
theorem nonempty_fibreOverFieldValuedPoint_iso_of_isPullback {X X' Y Y' : AlgebraicSpaces B S hS}
    {fst : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback fst f' f g)
    (p : FieldValuedPoint B S hS Y'.1) :
    Nonempty (fibreOverFieldValuedPoint B S hS f'.hom p ≅
      fibreOverFieldValuedPoint B S hS f.hom (p.map B S hS Y'.1 g.hom)) := by
  have hf' : f'.hom = h.isoPullback.hom.hom ≫ (pullback.snd f g).hom :=
    (congrArg (fun k => k.hom) h.isoPullback_hom_snd).symm
  let e : X'.1 ≅ (pullback f g).1 :=
    { hom := h.isoPullback.hom.hom
      inv := h.isoPullback.inv.hom
      hom_inv_id := congrArg (fun k => k.hom) h.isoPullback.hom_inv_id
      inv_hom_id := congrArg (fun k => k.hom) h.isoPullback.inv_hom_id }
  exact ⟨eqToIso (congrArg (fun φ => fibreOverFieldValuedPoint B S hS φ p) hf') ≪≫
    restrictedFibreIsoOfIso B S hS e (pullback.snd f g).hom p.contained _ p.value ≪≫
    fibreOverFieldValuedPointPullbackSndIso B S hS f g p⟩

/-- Every field-valued point is dominated by one whose field of definition is algebraically
closed: an algebraic closure of its field. -/
theorem exists_dominates_isAlgClosed (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B S hS F) :
    ∃ q : FieldValuedPoint B S hS F, IsAlgClosed q.carrier ∧
      FieldValuedPoint.Dominates B S hS F q p := by
  have hkbar : B.Contains (Spec (.of (AlgebraicClosure p.carrier))) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit p.contained
      ((Algebra.IsAlgebraic.cardinalMk_le_max p.carrier (AlgebraicClosure p.carrier)).trans_eq
        (max_comm _ _))
  let φ : Spec (.of (AlgebraicClosure p.carrier)) ⟶ Spec (.of p.carrier) :=
    Spec.map (CommRingCat.ofHom (algebraMap p.carrier (AlgebraicClosure p.carrier)))
  let m : (Over.mk (⟨φ ≫ p.toBase⟩ : B.obj hkbar ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      p.siteObject := Over.homMk (⟨φ⟩ : B.obj hkbar ⟶ B.obj p.contained) (by ext; rfl)
  exact ⟨{ carrier := AlgebraicClosure p.carrier
           contained := hkbar
           toBase := φ ≫ p.toBase
           value := F.map m.op p.value }, inferInstance, ⟨m, rfl⟩⟩

/-- **Connectedness of the fibre of a represented morphism over a field-valued point.** For a
morphism `g : T ⟶ W` of the big fppf site and a field-valued point `q` of `W`, the fibre of
`h_T ⟶ h_W` over `q`, an algebraic space over the field of `q`, is connected exactly when the
scheme-theoretic fibre product `T ×_W Spec κ(q)` is connected: the lower-shriek extension of the
fibre to the site over `S` is the presheaf fibre product, which Yoneda identifies with the
representable presheaf of the fibre product of schemes, and none of these steps changes the
space of points. -/
theorem connectedPoints_fibreOverFieldValuedPoint_yoneda_map_iff {T W : BigFppfOver B S hS}
    (g : T ⟶ W) (q : FieldValuedPoint B S hS (yoneda.obj W)) :
    ConnectedPoints B (Spec (.of q.carrier)) q.contained
        (fibreOverFieldValuedPoint B S hS (yoneda.map g) q) ↔
      ConnectedSpace ↥(pullback ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map q.value)) := by
  have hσ : yonedaEquiv.symm q.value = yoneda.map q.value :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm
  have hsq : IsPullback (yoneda.map (pullback.fst g q.value))
      (yoneda.map (pullback.snd g q.value)) (yoneda.map g) (yonedaEquiv.symm q.value) := by
    rw [hσ]
    exact (IsPullback.of_hasPullback g q.value).map yoneda
  have hsch := (IsPullback.of_hasPullback g q.value).map (BigFppfOver.toScheme B S hS)
  let h : points B (Spec (.of q.carrier)) q.contained
        (fibreOverFieldValuedPoint B S hS (yoneda.map g) q) ≃ₜ
      ↥(pullback ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map q.value)) :=
    (relocalizedPointsHomeo B (Spec (.of q.carrier)) S q.contained hS q.siteObject.hom
        (fiberOverField B S hS (yoneda.map g) q)
        (fiberOverField_isAlgebraicSpace B S hS (isAlgebraicSpace_yoneda B S hS T)
          (isAlgebraicSpace_yoneda B S hS W) (yoneda.map g) q)).trans
      ((pointsHomeomorphOfIso B S hS (extendFiberOverFieldIso B S hS (yoneda.map g) q)).trans
        ((pointsHomeomorphOfIso B S hS hsq.isoPullback).symm.trans
          ((schemePointsHomeomorph B S hS _).trans hsch.isoPullback.schemeIsoToHomeo)))
  exact h.connectedSpace_iff

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Condition (1)(b) of Stacks 0E1I.** The geometric fibres of the family of curves
`f : X → S` are reduced and connected — for every geometric point `ȳ` of `S` the fibre `X_ȳ` is
reduced (on an étale chart) and its space of points is connected — and `f` has relative
dimension `1` (Stacks 06LR (2)), that is, the fibres have dimension `1` at each of their
points. -/
def IsGrcDimOneFamily : ObjectProperty (CurveFamily B hZ) := fun X =>
  (∀ y : Space.GeometricPoint B integerBase hZ (schemeSpace X.base).obj,
      Space.HasEtaleLocalProperty B (Spec (.of y.1.carrier)) y.1.contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom y.1)
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T)) ∧
    (∀ y : Space.GeometricPoint B integerBase hZ (schemeSpace X.base).obj,
      Space.ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom y.1)) ∧
    Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom

variable {B hZ}

/-- **The fibres of a family of curves are geometrically reduced (Stacks 0E08) exactly when its
geometric fibres are reduced** (Stacks 0E07): a field-valued point is dominated by a geometric
point, over whose algebraically closed — hence perfect — field reducedness of the fibre is
geometric reducedness. -/
theorem isGeometricallyReducedFamily_iff_forall_geometricPoint (X : CurveFamily B hZ) :
    IsGeometricallyReducedFamily B hZ X ↔
      ∀ y : Space.GeometricPoint B integerBase hZ (schemeSpace X.base).obj,
        Space.HasEtaleLocalProperty B (Spec (.of y.1.carrier)) y.1.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom y.1)
          (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T) := by
  refine ⟨fun h y => (Space.isGeometricallyReducedFibreAt_iff_forall_isReduced B integerBase hZ
    X.toBase.hom X.total.property (schemeSpace X.base).property _).mp (h _) y.1 rfl, fun h x => ?_⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨q, hq, hdom⟩ := Space.exists_dominates_isAlgClosed _ p
  change Space.IsGeometricallyReducedFibreAt B integerBase hZ X.toBase.hom X.total.property
    (schemeSpace X.base).property (p.class B integerBase hZ _)
  rw [← Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B integerBase hZ _
      ⟨q, Space.FieldValuedPoint.dominates_refl B integerBase hZ _ q, hdom⟩,
    Space.isGeometricallyReducedFibreAt_class_iff]
  exact Space.isGeometricallyReduced_of_isReduced q.carrier B q.contained _
    (Space.isAlgebraicSpace_fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom
      X.total.property (schemeSpace X.base).property q) (h ⟨q, hq⟩)

namespace CurveFamily

/-- The fibre of a family of curves over a field-valued point of the base of a family mapping
to it is the fibre of the target family over the image point: the square is cartesian. -/
theorem nonempty_fibreOverFieldValuedPoint_iso_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj) :
    Nonempty (Space.fibreOverFieldValuedPoint B integerBase hZ F.toBase.hom p ≅
      Space.fibreOverFieldValuedPoint B integerBase hZ G.toBase.hom
        (p.map B integerBase hZ _ (schemeSpaceMap a.baseMap).hom)) :=
  Space.nonempty_fibreOverFieldValuedPoint_iso_of_isPullback a.cartesian p

/-- **The condition of `Curves^{grc,1}` is inherited along morphisms of families of curves**:
the geometric fibres of a base change are geometric fibres of the original family, and relative
dimension is unchanged by base change. -/
theorem isGrcDimOneFamily_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G)
    (hG : IsGrcDimOneFamily B hZ G) : IsGrcDimOneFamily B hZ F := by
  obtain ⟨hred, hconn, hdim⟩ := hG
  refine ⟨fun y => ?_, fun y => ?_, fun x => ?_⟩
  · obtain ⟨e⟩ := nonempty_fibreOverFieldValuedPoint_iso_of_hom a y.1
    exact Space.hasEtaleLocalProperty_of_iso B (Spec (.of y.1.carrier)) y.1.contained _ e.symm
      (hred (Space.geometricPointMap (schemeSpaceMap a.baseMap).hom y))
  · obtain ⟨e⟩ := nonempty_fibreOverFieldValuedPoint_iso_of_hom a y.1
    exact Space.connectedSpace_of_presheafIso B (Spec (.of y.1.carrier)) y.1.contained e.symm
      (hconn (Space.geometricPointMap (schemeSpaceMap a.baseMap).hom y))
  · exact (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ a _ x).mpr (hdim _)

/-- **`k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields** for a family in `Curves^{grc,1}`: its
geometric fibres are reduced and connected (Stacks 0E0S). -/
theorem bijective_algebraMap_fibre_of_isGrcDimOneFamily {X : CurveFamily B hZ}
    (hX : IsGrcDimOneFamily B hZ X)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
      p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p))) :=
  X.bijective_algebraMap_fibre_of_geometricFibres hX.1 hX.2.1 p

end CurveFamily

/-! ### The family of a proper scheme over a field -/

section OverField

variable {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k)))
  [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)

/-- **Geometric connectedness is read on one geometric fibre.** For a proper scheme `X` of
dimension at most one over a field `k` and a geometric point `ȳ : Spec K ⟶ Spec k` of the base
of its family of curves, the fibre over `ȳ` is connected exactly when `X` is geometrically
connected over `k`: the fibre is `X ×_k K`
(`AlgebraicGeometry.Space.connectedPoints_fibreOverFieldValuedPoint_yoneda_map_iff`), which over
the algebraically closed field `K` is geometrically connected exactly when it is connected
(Stacks 0363), and geometric connectedness descends along `K/k` (Stacks 054N). -/
theorem connectedPoints_fibre_curveFamilyOfScheme_iff
    (y : Space.GeometricPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj) :
    Space.ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ
          (curveFamilyOfScheme X B hZ hk hdim).toBase.hom y.1) ↔
      GeometricallyConnected X.hom := by
  have : IsAlgClosed y.1.carrier := y.2
  refine (Space.connectedPoints_fibreOverFieldValuedPoint_yoneda_map_iff _ y.1).trans ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective
    ((BigFppfOver.toScheme B integerBase hZ).map y.1.value :
      Spec (.of y.1.carrier) ⟶ Spec (.of k))
  let : Algebra k y.1.carrier := φ.hom.toAlgebra
  have hφ' : (BigFppfOver.toScheme B integerBase hZ).map y.1.value =
      Spec.map (CommRingCat.ofHom (algebraMap k y.1.carrier)) := hφ.symm
  change ConnectedSpace ↥(pullback X.hom
    ((BigFppfOver.toScheme B integerBase hZ).map y.1.value)) ↔ _
  rw [hφ', geometricallyConnected_iff_baseChange_fieldExtension k y.1.carrier X.hom,
    geometricallyConnected_iff_connectedSpace y.1.carrier]

/-- **Condition (2)(b) of Stacks 0E1I.** The family of curves of a proper scheme `X` of
dimension at most one over a field `k` has reduced, connected geometric fibres and relative
dimension `1` exactly when `X` is geometrically reduced, geometrically connected and of
dimension `1` over `k`.

Reducedness is `AlgebraicGeometry.isGeometricallyReducedFamily_iff_forall_geometricPoint` and
Stacks 035V (`AlgebraicGeometry.isGeometricallyReducedFamily_curveFamilyOfScheme_iff`),
connectedness is `AlgebraicGeometry.connectedPoints_fibre_curveFamilyOfScheme_iff` at the
geometric point of an algebraic closure of `k`. Over a field, relative dimension `1` is
equidimensionality of dimension `1`; conversely a proper geometrically reduced and geometrically
connected scheme over `k` has `k = H⁰(X, 𝒪_X)` (Stacks 0FD2), so being of dimension `1` it is
equidimensional. -/
theorem isGrcDimOneFamily_curveFamilyOfScheme_iff :
    IsGrcDimOneFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      IsGeometricallyReducedOver X.hom ∧ GeometricallyConnected X.hom ∧
        topologicalKrullDim X.left = 1 := by
  have hX : B.Contains X.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk
  -- a geometric point of the base, over an algebraic closure of `k`
  let p₀ : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj :=
    ⟨k, hk, specULiftZIsTerminal.from _, 𝟙 _⟩
  obtain ⟨q₀, hq₀, -⟩ := Space.exists_dominates_isAlgClosed _ p₀
  have hconn : (∀ y : Space.GeometricPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj,
      Space.ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ
          (curveFamilyOfScheme X B hZ hk hdim).toBase.hom y.1)) ↔ GeometricallyConnected X.hom :=
    ⟨fun h => (connectedPoints_fibre_curveFamilyOfScheme_iff hk X hdim ⟨q₀, hq₀⟩).mp
      (h ⟨q₀, hq₀⟩), fun h y => (connectedPoints_fibre_curveFamilyOfScheme_iff hk X hdim y).mpr h⟩
  have hred := (isGeometricallyReducedFamily_iff_forall_geometricPoint
    (curveFamilyOfScheme X B hZ hk hdim)).symm.trans
    (isGeometricallyReducedFamily_curveFamilyOfScheme_iff B hZ k hk X hdim)
  have hreldim : Nonempty X.left →
      (Space.HasRelativeDimension 1 B integerBase hZ
          (curveFamilyOfScheme X B hZ hk hdim).toBase.hom ↔
        TopologicalSpace.Equidimensional X.left ∧ topologicalKrullDim X.left = (1 : ℕ)) :=
    fun hne => hasRelativeDimension_schemeSpaceMap_iff_equidimensional B hZ 1
      (integerSiteMap B hZ hX hk X.hom) k rfl (inferInstanceAs (LocallyOfFiniteType X.hom)) hne
  unfold IsGrcDimOneFamily
  rw [hred, hconn]
  refine and_congr_right fun hr => and_congr_right fun hc => ?_
  have : ConnectedSpace X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := X.hom)
  have : GeometricallyReduced X.hom :=
    (geometricallyReduced_iff_forall_isGeometricallyReducedAt X.hom).mpr hr
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) :=
    (isIso_globalSections_iff_geometricallyConnected k X.hom).mpr hc
  rw [hreldim inferInstance]
  exact ⟨fun hd => by exact_mod_cast hd.2, fun hd =>
    ⟨equidimensional_of_isIso_globalSections_of_dimension_one k X.hom hd, by exact_mod_cast hd⟩⟩

end OverField

variable (B hZ) in
/-- **The stack `Curves^{grc,1}`.** The strictly full subcategory of families of curves whose
geometric fibres are reduced, connected and of dimension `1`, as a category fibred in groupoids
over the big fppf site of `Spec(ℤ)` (Stacks 0E0E): the condition is inherited along morphisms of
families. -/
def curvesGrcDimOne :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsGrcDimOneFamily B hZ) CurveFamily.isGrcDimOneFamily_of_hom

end AlgebraicGeometry

end
