module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Points of finite type of an algebraic space (Stacks 0487, 06EF, 06EG, 06EH, 06EJ, 06EK, 06EL)

A point of an algebraic space over `S` is a *finite type point* when it is represented by a
field-valued point whose morphism to the space is locally of finite type. Equivalently it is
the image of a closed point of a scheme étale over the space, and the scheme may be taken
affine. The finite type points behave like the closed points of a Jacobson scheme: every
nonempty locally closed set of points contains one, so they are dense in every closed set,
and a surjective morphism which is locally of finite type maps them onto the finite type
points of its target.

This is the algebraic-space counterpart of the scheme-level material in
`StacksFrontier/AlgebraicGeometry/Morphisms/JacobsonPoints/Basic.lean`, and every proof below
reduces to it along a scheme chart.

The file closes with Stacks 0487: a morphism locally of finite type is surjective exactly
when it is surjective on points valued in every algebraically closed field over the base.

## Main definitions

* `AlgebraicGeometry.Space.IsFiniteTypePoint` and
  `AlgebraicGeometry.Space.finiteTypePoints` are **Stacks 06EG**, the predicate and the set of
  points it cuts out.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_isClosed_etaleChart` is
  **Stacks 06EF**, and is at the same time the assertion of **Stacks 06EH** for arbitrary
  scheme charts: a point is of finite type exactly when it is the image of a closed point of a
  scheme étale over the space.
* `AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_isAffine_isClosed_etaleChart` is the
  assertion of **Stacks 06EH** for affine scheme charts.
* `AlgebraicGeometry.Space.inter_finiteTypePoints_nonempty` and
  `AlgebraicGeometry.Space.closure_inter_finiteTypePoints` are the two assertions of
  **Stacks 06EK**: a nonempty locally closed set of points contains a finite type point, and
  the finite type points of a closed set are dense in it.
* `AlgebraicGeometry.Space.mapsTo_finiteTypePoints`: a locally finite type morphism carries
  finite type points to finite type points.
* `AlgebraicGeometry.Space.image_finiteTypePoints_eq` is **Stacks 06EJ**.
* `AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_singleton_space` is the equivalence of
  conditions (1) and (2) of **Stacks 06EL**: a point is of finite type exactly when it is the
  image of an algebraic space with a single point which is locally of finite type over the
  space.
* `AlgebraicGeometry.Space.isFiniteTypePoint_pointsMap_of_isSurjective_fieldPoint` is the
  implication from condition (3) to condition (1) of **Stacks 06EL**. The remaining
  implication, from condition (1) to condition (3), is
  `AlgebraicGeometry.Space.exists_mono_isLocallyOfFiniteType_etale_fieldPoint_of_isFiniteTypePoint`
  in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FiniteTypePointMonomorphism.lean`.
* `AlgebraicGeometry.Space.isSurjective_iff_surjective_app_isAlgClosed` is **Stacks 0487**.
* `AlgebraicGeometry.Space.toScheme_map_schemePointRepresentative_value`: the morphism of
  schemes underlying the residue field representative of a point of a scheme of the site is
  `AlgebraicGeometry.Scheme.fromSpecResidueField` at that point.

## Implementation notes

The predicate of Stacks 06EG is the first of the two equivalent conditions of Stacks 06EF,
which is the one that makes sense for an arbitrary presheaf on the big fppf site of `S`;
algebraicity is a hypothesis of the results, exactly as in the source. Both the predicate and
the set are abbreviations, so a client may use the underlying existential and the `Set` API
without conversion lemmas.

A point of a scheme chart `U` of `X` is recorded in the statements of Stacks 06EF and 06EH as
the point `AlgebraicGeometry.Space.schemePoint` underlying a field-valued point of the
presheaf `U` represents, which is the same datum by the bijection of Stacks 03BX, clause (1),
and is the datum the map on points of Stacks 03BU acts on.

The passage between a point of a scheme chart and a point of the represented presheaf is
`AlgebraicGeometry.Space.schemePointRepresentative`, the field-valued point given by the
residue field at that point, together with
`AlgebraicGeometry.Space.injective_pointsToScheme`; in particular the residue field
representative of a *finite type* point of the chart is locally of finite type over it,
because its underlying morphism of schemes is `Scheme.fromSpecResidueField`. That one
observation is what reduces Stacks 06EF, 06EH and 06EK to Stacks 02J3 and 02J4. The topology
on the points is `AlgebraicGeometry.Space.pointTopology` of Stacks 03BX, installed as a local
instance, and it agrees with the topology of a chart scheme by
`AlgebraicGeometry.Space.schemePointsHomeomorph`.

Condition (2) of Stacks 06EL, that `|Z|` be a singleton, is the conjunction of
`Nonempty (AlgebraicGeometry.Space.points B S hS Z)` and
`Subsingleton (AlgebraicGeometry.Space.points B S hS Z)`, as in Stacks 06QW; condition (3)
records the surjective étale morphism from a field spectrum as a field-valued point of `Z`
whose morphism is surjective and étale. The implication from condition (1) to condition (3),
which is where the monomorphism of the source's argument is built, is
`AlgebraicGeometry.Space.exists_mono_isLocallyOfFiniteType_etale_fieldPoint_of_isFiniteTypePoint`
in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FiniteTypePointMonomorphism.lean`; it is
kept out of this file because it rests on the residual space of Stacks 06QZ, whose
construction imports a great deal more. Conditions (1) and (2) are already witnessed by the
spectrum of the field of a locally finite type representative of the point, which is why the
equivalence below needs none of that; and for the same reason the étale and monomorphism
hypotheses of condition (3) are not used in the implication to condition (1), which needs
only surjectivity of the chart and local finite type of the morphism.

Stacks 06EK is proved directly from a surjective étale scheme chart rather than along the
reduced induced subspace structure on the locally closed set: the latter is only available
conditionally on effective descent for immersions (see the note in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Immersions.lean`), whereas the statement of
the tag assumes no descent.

For Stacks 0487 the sets `X(k)` and `Y(k)` are the values of the two presheaves at the object
of the big fppf site over `S` given by a structure morphism `Spec k ⟶ S`; the hypothesis that
`Spec k` lie in the chosen site is what makes those values available, and the quantifier runs
over every algebraically closed field of the working universe whose spectrum does. The
substantial direction base changes a surjective étale chart of `X` to `Spec k`, where the
resulting scheme is Jacobson because it is locally of finite type over a field, so it has a
closed point, and `AlgebraicGeometry.pointOfClosedPoint` turns that closed point into the
required `k`-point.

## References

* [Stacks Project, Tag 0487](https://stacks.math.columbia.edu/tag/0487)
* [Stacks Project, Tag 06EF](https://stacks.math.columbia.edu/tag/06EF)
* [Stacks Project, Tag 06EG](https://stacks.math.columbia.edu/tag/06EG)
* [Stacks Project, Tag 06EH](https://stacks.math.columbia.edu/tag/06EH)
* [Stacks Project, Tag 06EJ](https://stacks.math.columbia.edu/tag/06EJ)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
* [Stacks Project, Tag 06EL](https://stacks.math.columbia.edu/tag/06EL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Finite type points of a scheme

Two facts about the finite type points of a scheme which the chart arguments below need and
which `StacksFrontier/AlgebraicGeometry/Morphisms/JacobsonPoints/Basic.lean` only uses
internally. -/

/-- A closed point of a scheme is a finite type point: the morphism from the spectrum of its
residue field is a closed immersion. -/
private theorem isFiniteTypePoint_of_isClosed_singleton {Z : Scheme.{u}} {z : Z}
    (hz : IsClosed ({z} : Set Z)) : AlgebraicGeometry.IsFiniteTypePoint z := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Z.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  have hlft : LocallyOfFiniteType (Z.fromSpecResidueField z) := inferInstance
  exact ((finiteType_specField_tfae (Z.fromSpecResidueField z)).out 2 1).mp hlft

/-- A finite type point of a scheme is closed in some affine open neighbourhood of it. This is
the implication from condition (2) to condition (4) of Stacks 01TA for the morphism from the
spectrum of the residue field at that point. -/
private theorem exists_affineOpen_isClosed_singleton {Z : Scheme.{u}} {z : Z}
    (hz : AlgebraicGeometry.IsFiniteTypePoint z) :
    ∃ (V : Z.affineOpens) (hzV : z ∈ V.1), IsClosed ({(⟨z, hzV⟩ : V.1)} : Set V.1) := by
  obtain ⟨V, -, w, hw, hclosed, -⟩ :=
    ((finiteType_specField_tfae (Z.fromSpecResidueField z)).out 2 4).mp hz.1
  have hwz : (w : Z) = z :=
    hw.trans ((Scheme.SpecToEquivOfField_apply_fst _ _ _).trans
      (Scheme.fromSpecResidueField_apply _ _))
  refine ⟨V, hwz ▸ w.2, ?_⟩
  rw [show (⟨z, hwz ▸ w.2⟩ : V.1) = w from Subtype.ext hwz.symm]
  exact hclosed

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is deep (see the docstring)
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_finiteTypePoints :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_finiteTypePoints
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The definition -/

/-- **Stacks 06EG.** A point of an algebraic space over `S` is a *finite type point* when some
field-valued point representing it has a morphism to the space which is locally of finite
type. -/
@[stacks 06EG "finite type point"]
abbrev IsFiniteTypePoint (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (x : points B S hS X) : Prop :=
  ∃ p : FieldValuedPoint B S hS X, p.class B S hS X = x ∧
    IsLocallyOfFiniteType B S hS (yonedaEquiv.symm p.value)

/-- **Stacks 06EG.** The set `X_{ft-pts}` of finite type points of an algebraic space
over `S`. -/
@[stacks 06EG "set of finite type points"]
abbrev finiteTypePoints (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Set (points B S hS X) :=
  {x | IsFiniteTypePoint B S hS X x}

/-! ### Transport between a chart and the space -/

/-- A morphism of the big fppf site over `S` is locally of finite type as a morphism of
algebraic spaces exactly when the morphism of schemes underlying it is. This is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` for the property of being
locally of finite type. -/
public theorem isLocallyOfFiniteType_yoneda_map_iff {U V : BigFppfOver B S hS} (k : U ⟶ V) :
    IsLocallyOfFiniteType B S hS (yoneda.map k) ↔
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k) :=
  holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget k

/-- The morphism of schemes underlying the residue field representative of a point of a chart
scheme is `AlgebraicGeometry.Scheme.fromSpecResidueField` at that point.

The representative of `AlgebraicGeometry.Space.schemePointRepresentative` is built as the
`CategoryTheory.Functor.preimage` under the fully faithful inclusion of the site of the
canonical morphism out of the spectrum of the residue field, so this is that inclusion
cancelling the preimage. -/
theorem toScheme_map_schemePointRepresentative_value (U : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj U) :
    (BigFppfOver.toScheme B S hS).map (schemePointRepresentative B S hS U z).value =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField z := by
  change B.inclusion.map (B.inclusion.preimage _) = _
  rw [Functor.map_preimage]

/-- The residue field representative of a finite type point of a chart scheme is locally of
finite type over the chart. -/
private theorem isLocallyOfFiniteType_schemePointRepresentative (U : BigFppfOver B S hS)
    {z : (BigFppfOver.toScheme B S hS).obj U}
    (hz : AlgebraicGeometry.IsFiniteTypePoint z) :
    IsLocallyOfFiniteType B S hS
      (yonedaEquiv.symm (schemePointRepresentative B S hS U z).value) := by
  rw [show yonedaEquiv.symm (schemePointRepresentative B S hS U z).value =
      yoneda.map (schemePointRepresentative B S hS U z).value from
    yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]),
    isLocallyOfFiniteType_yoneda_map_iff, toScheme_map_schemePointRepresentative_value]
  exact hz.1

/-- Pushing a locally finite type field-valued point forward along a locally finite type
morphism of algebraic spaces gives a locally finite type field-valued point. -/
private theorem isLocallyOfFiniteType_map_value
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS X)
    (hp : IsLocallyOfFiniteType B S hS (yonedaEquiv.symm p.value)) :
    IsLocallyOfFiniteType B S hS (yonedaEquiv.symm (FieldValuedPoint.map B S hS X f p).value) := by
  rw [show yonedaEquiv.symm (FieldValuedPoint.map B S hS X f p).value =
      yonedaEquiv.symm p.value ≫ f from
    (yonedaEquiv_symm_naturality_right (p.siteObject B S hS X) f p.value).symm]
  exact isLocallyOfFiniteType_comp B S hS
    (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS X)) hX hY _ _ hp hf

/-- Two ways of composing two morphisms of presheaves agree on points when the composites
agree. -/
private theorem pointsMap_pointsMap_eq_of_comp_eq {F G G' H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} {b : G ⟶ H} {a' : F ⟶ G'} {b' : G' ⟶ H} (h : a ≫ b = a' ≫ b')
    (w : points B S hS F) :
    pointsMap B S hS G b (pointsMap B S hS F a w) =
      pointsMap B S hS G' b' (pointsMap B S hS F a' w) := by
  rw [← Function.comp_apply (f := pointsMap B S hS G b), ← pointsMap_comp, h, pointsMap_comp]
  rfl

/-- The image in `|X|` of a finite type point of a scheme étale over `X` is a finite type
point. -/
private theorem isFiniteTypePoint_pointsMap_schemePointRepresentative
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X} (hφ : IsEtale B S hS φ)
    {z : (BigFppfOver.toScheme B S hS).obj U}
    (hz : AlgebraicGeometry.IsFiniteTypePoint z) :
    IsFiniteTypePoint B S hS X
      (pointsMap B S hS (yoneda.obj U) φ
        ((schemePointRepresentative B S hS U z).class B S hS (yoneda.obj U))) := by
  refine ⟨FieldValuedPoint.map B S hS (yoneda.obj U) φ (schemePointRepresentative B S hS U z),
    (pointsMap_class B S hS (yoneda.obj U) φ (schemePointRepresentative B S hS U z)).symm, ?_⟩
  exact isLocallyOfFiniteType_map_value B S hS φ (isAlgebraicSpace_yoneda B S hS U) hX
    (isLocallyOfFiniteType_of_isEtale B S hS hX hφ) _
    (isLocallyOfFiniteType_schemePointRepresentative B S hS U hz)

/-- A locally finite type morphism of algebraic spaces over `S` carries finite type points to
finite type points. This is the algebraic-space counterpart of Stacks 02J3, and is the easy
inclusion of `AlgebraicGeometry.Space.image_finiteTypePoints_eq`. -/
@[stacks 06EI]
theorem mapsTo_finiteTypePoints {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    Set.MapsTo (pointsMap B S hS X f) (finiteTypePoints B S hS X)
      (finiteTypePoints B S hS Y) := by
  intro x hx
  obtain ⟨p, hpx, hplft⟩ := hx
  refine ⟨FieldValuedPoint.map B S hS X f p, by rw [← hpx, pointsMap_class], ?_⟩
  exact isLocallyOfFiniteType_map_value B S hS f hX hY hf p hplft

/-! ### Finite type points and closed points of étale charts -/

/-- The substantial half of Stacks 06EF: a finite type point of an algebraic space over `S` is
the image of a closed point of an *affine* scheme étale over it.

A surjective étale chart `U ⟶ X` is base changed to the spectrum of the field of a locally
finite type representative of the point; the base change is a nonempty scheme locally of
finite type over `U`, so it has a finite type point by Stacks 02J4, whose image in `U` is a
finite type point by Stacks 02J3 and is therefore closed in an affine open of `U`. That
affine open, étale over `X` by Stacks 03FT, is the required chart. -/
private theorem exists_isAffine_isClosed_etaleChart_of_isFiniteTypePoint
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {x : points B S hS X} (hx : IsFiniteTypePoint B S hS X x) :
    ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
      (p : FieldValuedPoint B S hS (yoneda.obj U)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧ IsEtale B S hS φ ∧
        IsClosed ({schemePoint B S hS U p} : Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
        pointsMap B S hS (yoneda.obj U) φ (p.class B S hS (yoneda.obj U)) = x := by
  obtain ⟨p, hpx, hplft⟩ := hx
  obtain ⟨U, φ, hφsurj, hφetale⟩ := hX.exists_atlas
  set A := p.siteObject B S hS X
  set η : yoneda.obj A ⟶ X := yonedaEquiv.symm p.value
  set W := hφsurj.rep.pullback η
  set fst := hφsurj.rep.fst' η
  set snd := hφsurj.rep.snd η
  have hsq : IsPullback (yoneda.map fst) (yoneda.map snd) φ η := hφsurj.rep.isPullback' η
  have hsndSurj : Surjective ((BigFppfOver.toScheme B S hS).map snd) :=
    hφsurj.property η (yoneda.map fst) snd hsq
  have hsndEtale : Etale ((BigFppfOver.toScheme B S hS).map snd) :=
    hφetale.property η (yoneda.map fst) snd hsq
  have hfstLft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map fst) :=
    hplft W U (yoneda.map snd) φ fst
      ((presheaf_yoneda_map_etale_iff B S hS snd).2 hsndEtale) hφetale hsq.w
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map fst) := hfstLft
  obtain ⟨w₀, -⟩ := hsndSurj.surj (IsLocalRing.closedPoint p.carrier)
  obtain ⟨w, -, hwft⟩ := AlgebraicGeometry.inter_finiteTypePoints_nonempty
    (S := (BigFppfOver.toScheme B S hS).obj W) (T := Set.univ)
    isClosed_univ.isLocallyClosed ⟨w₀, Set.mem_univ _⟩
  have hyft : AlgebraicGeometry.IsFiniteTypePoint
      ((BigFppfOver.toScheme B S hS).map fst w) :=
    AlgebraicGeometry.mapsTo_finiteTypePoints ((BigFppfOver.toScheme B S hS).map fst) hwft
  obtain ⟨V, hyV, hyclosed⟩ := exists_affineOpen_isClosed_singleton hyft
  -- The affine open `V` of `U`, as an object of the site étale over `X`.
  have hVsize : B.Contains V.1.toScheme :=
    Scheme.size_lt_of_isOpenImmersion V.1.ι U.left.property
  set α : B.obj hVsize ⟶ U.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj hVsize) ⟶ B.inclusion.obj U.left from V.1.ι) with hα
  set Uv : BigFppfOver B S hS := Over.mk (α ≫ U.hom)
  set j : Uv ⟶ U := Over.homMk α
  have hjmap : (BigFppfOver.toScheme B S hS).map j = V.1.ι := by
    change B.inclusion.map α = _
    rw [hα, Functor.map_preimage]
  have hjEtale : Etale ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hjmap]; infer_instance
  set z : (BigFppfOver.toScheme B S hS).obj Uv :=
    show V.1.toScheme from ⟨(BigFppfOver.toScheme B S hS).map fst w, hyV⟩
  refine ⟨Uv, yoneda.map j ≫ φ, schemePointRepresentative B S hS Uv z, V.2,
    isEtale_comp B S hS
      ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map j)).2
        ((presheaf_yoneda_map_etale_iff B S hS j).2 hjEtale))
      ((isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφetale), ?_, ?_⟩
  · rw [schemePointRepresentative_point B S hS Uv z]
    exact hyclosed
  · -- The two charts see the same point of `U`, hence the same point of `|X|`.
    have hkey : pointsMap B S hS (yoneda.obj Uv) (yoneda.map j)
          ((schemePointRepresentative B S hS Uv z).class B S hS (yoneda.obj Uv)) =
        pointsMap B S hS (yoneda.obj W) (yoneda.map fst)
          ((schemePointRepresentative B S hS W w).class B S hS (yoneda.obj W)) := by
      refine injective_pointsToScheme B S hS U ?_
      rw [pointsToScheme_pointsMap, pointsToScheme_pointsMap]
      change (BigFppfOver.toScheme B S hS).map j (schemePoint B S hS Uv _) =
        (BigFppfOver.toScheme B S hS).map fst (schemePoint B S hS W _)
      rw [schemePointRepresentative_point, schemePointRepresentative_point, hjmap]
      rfl
    rw [pointsMap_comp, Function.comp_apply, hkey]
    exact (pointsMap_pointsMap_eq_of_comp_eq B S hS hsq.w _).trans
      ((FieldValuedPoint.pointsMap_eq_class B S hS p _).trans hpx)

/-- The easy half of Stacks 06EF: the image of a closed point of a scheme étale over an
algebraic space over `S` is a finite type point.

A closed point of a scheme is a finite type point of it by Stacks 01TA, and its residue field
representative represents the same point of the chart as the given one. -/
private theorem isFiniteTypePoint_of_isClosed_etaleChart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {x : points B S hS X} {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hφ : IsEtale B S hS φ) {p : FieldValuedPoint B S hS (yoneda.obj U)}
    (hclosed : IsClosed ({schemePoint B S hS U p} :
      Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hpx : pointsMap B S hS (yoneda.obj U) φ (p.class B S hS (yoneda.obj U)) = x) :
    IsFiniteTypePoint B S hS X x := by
  have hmain := isFiniteTypePoint_pointsMap_schemePointRepresentative B S hS hX hφ
    (isFiniteTypePoint_of_isClosed_singleton hclosed)
  rw [show (schemePointRepresentative B S hS U (schemePoint B S hS U p)).class B S hS
        (yoneda.obj U) = p.class B S hS (yoneda.obj U) from
    schemePointRepresentative_class B S hS U p, hpx] at hmain
  exact hmain

/-- **Stacks 06EF**, and the assertion of **Stacks 06EH** for arbitrary scheme charts. A point
of an algebraic space over `S` is a finite type point exactly when it is the image of a closed
point of a scheme étale over the space. -/
@[stacks 06EF, stacks 06EH "all scheme charts"]
theorem isFiniteTypePoint_iff_exists_isClosed_etaleChart
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    IsFiniteTypePoint B S hS X x ↔
      ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
        (p : FieldValuedPoint B S hS (yoneda.obj U)),
        IsEtale B S hS φ ∧
          IsClosed ({schemePoint B S hS U p} : Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
          pointsMap B S hS (yoneda.obj U) φ (p.class B S hS (yoneda.obj U)) = x := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨U, φ, p, -, hφ, hclosed, hpx⟩ :=
      exists_isAffine_isClosed_etaleChart_of_isFiniteTypePoint B S hS hX hx
    exact ⟨U, φ, p, hφ, hclosed, hpx⟩
  · rintro ⟨U, φ, p, hφ, hclosed, hpx⟩
    exact isFiniteTypePoint_of_isClosed_etaleChart B S hS hX hφ hclosed hpx

/-- **Stacks 06EH**, the assertion for affine scheme charts. A point of an algebraic space
over `S` is a finite type point exactly when it is the image of a closed point of an affine
scheme étale over the space. -/
@[stacks 06EH "affine scheme charts"]
theorem isFiniteTypePoint_iff_exists_isAffine_isClosed_etaleChart
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    IsFiniteTypePoint B S hS X x ↔
      ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
        (p : FieldValuedPoint B S hS (yoneda.obj U)),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧ IsEtale B S hS φ ∧
          IsClosed ({schemePoint B S hS U p} : Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
          pointsMap B S hS (yoneda.obj U) φ (p.class B S hS (yoneda.obj U)) = x := by
  refine ⟨exists_isAffine_isClosed_etaleChart_of_isFiniteTypePoint B S hS hX, ?_⟩
  rintro ⟨U, φ, p, -, hφ, hclosed, hpx⟩
  exact isFiniteTypePoint_of_isClosed_etaleChart B S hS hX hφ hclosed hpx

/-! ### Finite type points in locally closed sets of points -/

section LocallyClosed

attribute [local instance] pointTopology

/-- **Stacks 06EK**, locally closed subsets. A nonempty locally closed set of points of an
algebraic space over `S` contains a finite type point.

The set is pulled back to a surjective étale scheme chart, where it is again nonempty and
locally closed because the map on points is continuous and surjective and the point topology
of a represented presheaf is the topology of the representing scheme; Stacks 02J4 produces a
finite type point there and its image in `|X|` is a finite type point by Stacks 02J3. -/
@[stacks 06EK "locally closed subsets"]
theorem inter_finiteTypePoints_nonempty (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) {T : Set (points B S hS X)}
    (hT : IsLocallyClosed T) (hne : T.Nonempty) :
    (T ∩ finiteTypePoints B S hS X).Nonempty := by
  obtain ⟨U, φ, hφsurj, hφetale⟩ := hX.exists_atlas
  have hφEtale : IsEtale B S hS φ := (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφetale
  set e := schemePointsHomeomorph B S hS U
  set Tp := pointsMap B S hS (yoneda.obj U) φ ⁻¹' T with hTp
  have hTsLc : IsLocallyClosed (e.symm ⁻¹' Tp) :=
    (hT.preimage (continuous_pointsMap B S hS φ)).preimage e.symm.continuous
  obtain ⟨t, ht⟩ := hne
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U φ).1 hφsurj t
  have hTsNe : (e.symm ⁻¹' Tp).Nonempty := by
    refine ⟨e z, ?_⟩
    rw [Set.mem_preimage, Homeomorph.symm_apply_apply, hTp, Set.mem_preimage, hz]
    exact ht
  obtain ⟨z₀, hz₀, hz₀ft⟩ :=
    AlgebraicGeometry.inter_finiteTypePoints_nonempty hTsLc hTsNe
  refine ⟨pointsMap B S hS (yoneda.obj U) φ
      ((schemePointRepresentative B S hS U z₀).class B S hS (yoneda.obj U)), ?_,
    isFiniteTypePoint_pointsMap_schemePointRepresentative B S hS hX hφEtale hz₀ft⟩
  have hcl : e ((schemePointRepresentative B S hS U z₀).class B S hS (yoneda.obj U)) = z₀ :=
    schemePointRepresentative_point B S hS U z₀
  have hmem : e.symm z₀ ∈ Tp := hz₀
  rwa [← hcl, Homeomorph.symm_apply_apply] at hmem

/-- **Stacks 06EK**, closed subsets. The finite type points lying in a closed set of points of
an algebraic space over `S` are dense in it. -/
@[stacks 06EK "closed subsets"]
theorem closure_inter_finiteTypePoints (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) {T : Set (points B S hS X)} (hT : IsClosed T) :
    closure (T ∩ finiteTypePoints B S hS X) = T := by
  refine le_antisymm (closure_minimal Set.inter_subset_left hT) fun x hx ↦ ?_
  rw [mem_closure_iff]
  intro V hV hxV
  obtain ⟨y, hyTV, hyft⟩ := inter_finiteTypePoints_nonempty B S hS X hX
    (hT.isLocallyClosed.inter hV.isLocallyClosed) ⟨x, hx, hxV⟩
  exact ⟨y, hyTV.2, hyTV.1, hyft⟩

/-! ### The image of the finite type points -/

/-- **Stacks 06EJ.** A surjective morphism of algebraic spaces over `S` which is locally of
finite type maps the finite type points of its source onto the finite type points of its
target.

One inclusion is `AlgebraicGeometry.Space.mapsTo_finiteTypePoints`. For the other, a
finite type point of the target is represented by a locally finite type morphism from a field
spectrum; the fibre product of the source with that field spectrum over the target is a
nonempty algebraic space locally of finite type over the source, so it has a finite type point
by Stacks 06EK, whose image in the source is the required point. -/
@[stacks 06EJ]
theorem image_finiteTypePoints_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hsurj : IsSurjective B S hS f) :
    pointsMap B S hS X f '' finiteTypePoints B S hS X = finiteTypePoints B S hS Y := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact mapsTo_finiteTypePoints B S hS f hX hY hf hx
  · rintro y ⟨p, hpy, hplft⟩
    set A := p.siteObject B S hS Y
    set fs : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
    set gs : (⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨Y, hY⟩ := ObjectProperty.homMk (yonedaEquiv.symm p.value)
    set πX : AlgebraicSpaces.fiberProduct B S hS fs gs ⟶ ⟨X, hX⟩ :=
      ObjectProperty.homMk (pullback.fst fs.hom gs.hom)
    set πK : AlgebraicSpaces.fiberProduct B S hS fs gs ⟶
      ⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩ :=
      ObjectProperty.homMk (pullback.snd fs.hom gs.hom)
    have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS fs gs
    have hKsurj : IsSurjective B S hS πK.hom :=
      isSurjective_of_isPullback B S hS hsq hsurj
    obtain ⟨z₀, -⟩ := surjective_pointsToScheme B S hS A
      (IsLocalRing.closedPoint p.carrier)
    obtain ⟨w₀, -⟩ := hKsurj z₀
    obtain ⟨w, -, hwft⟩ := inter_finiteTypePoints_nonempty B S hS
      (AlgebraicSpaces.fiberProduct B S hS fs gs).1
      (AlgebraicSpaces.fiberProduct B S hS fs gs).property (T := Set.univ)
      isClosed_univ.isLocallyClosed ⟨w₀, Set.mem_univ _⟩
    have hπXlft : IsLocallyOfFiniteType B S hS πX.hom :=
      (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hsq.flip hplft
    refine ⟨pointsMap B S hS (AlgebraicSpaces.fiberProduct B S hS fs gs).1 πX.hom w,
      mapsTo_finiteTypePoints B S hS πX.hom
        (AlgebraicSpaces.fiberProduct B S hS fs gs).property hX hπXlft hwft, ?_⟩
    have hcond : πX.hom ≫ f = πK.hom ≫ gs.hom := by
      change pullback.fst fs.hom gs.hom ≫ f = pullback.snd fs.hom gs.hom ≫ gs.hom
      exact pullback.condition
    exact (pointsMap_pointsMap_eq_of_comp_eq B S hS hcond _).trans
      ((FieldValuedPoint.pointsMap_eq_class B S hS p _).trans hpy)

/-! ### Algebraic spaces with one point lying over a point -/

/-- A point of an algebraic space over `S` which admits a surjective field-valued chart is
the point of that chart. -/
private theorem eq_class_of_isSurjective_fieldPoint
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : FieldValuedPoint B S hS Z)
    (hsurj : IsSurjective B S hS (yonedaEquiv.symm z.value)) (w : points B S hS Z) :
    w = z.class B S hS Z := by
  obtain ⟨v, rfl⟩ := hsurj w
  exact FieldValuedPoint.pointsMap_eq_class B S hS z v

/-- **Stacks 06EL, conditions (1) and (2).** A point of an algebraic space over `S` is a
finite type point exactly when it is the unique point of the image of an algebraic space with
exactly one point which is locally of finite type over the space.

A locally finite type representative of the point is such a space, the spectrum of a field
having one point; conversely `|Z|` is nonempty, so it contains a finite type point of `Z` by
Stacks 06EK, and the image of that point is a finite type point by Stacks 06EI and is the
given point because the image of `|Z|` is a singleton. -/
theorem isFiniteTypePoint_iff_exists_singleton_space
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    IsFiniteTypePoint B S hS X x ↔
      ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z) (f : Z ⟶ X),
        Nonempty (points B S hS Z) ∧ Subsingleton (points B S hS Z) ∧
          IsLocallyOfFiniteType B S hS f ∧ Set.range (pointsMap B S hS Z f) = {x} := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨p, hpx, hplft⟩ := hx
    obtain ⟨z₀, -⟩ := surjective_pointsToScheme B S hS (p.siteObject B S hS X)
      (IsLocalRing.closedPoint p.carrier)
    have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS X)) := by
      change Subsingleton (Spec (CommRingCat.of p.carrier))
      infer_instance
    refine ⟨yoneda.obj (p.siteObject B S hS X),
      isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS X), yonedaEquiv.symm p.value,
      ⟨z₀⟩, ⟨fun a b ↦ injective_pointsToScheme B S hS _ (hsub.elim _ _)⟩,
      hplft, ?_⟩
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨⟨z₀, (FieldValuedPoint.pointsMap_eq_class B S hS p z₀).trans hpx⟩, ?_⟩
    rintro - ⟨w, rfl⟩
    exact (FieldValuedPoint.pointsMap_eq_class B S hS p w).trans hpx
  · rintro ⟨Z, hZ, f, ⟨z⟩, -, hflft, hrange⟩
    obtain ⟨w, -, hwft⟩ := inter_finiteTypePoints_nonempty B S hS Z hZ (T := Set.univ)
      isClosed_univ.isLocallyClosed ⟨z, Set.mem_univ z⟩
    rw [← (Set.eq_singleton_iff_unique_mem.1 hrange).2 _ (Set.mem_range_self w)]
    exact mapsTo_finiteTypePoints B S hS f hZ hX hflft hwft

/-- **Stacks 06EL, condition (3) implies condition (1).** Let `f : Z ⟶ X` be a morphism of
algebraic spaces over `S` which is locally of finite type and a monomorphism, and let `z` be
a field-valued point of `Z` whose morphism is surjective and étale. Then the image of `z`
is a finite type point of `X`.

Every point of `Z` is the point of the chart `z`, so `|Z|` is a singleton and condition (2)
holds for `Z` and `f`. -/
theorem isFiniteTypePoint_pointsMap_of_isSurjective_fieldPoint
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (f : Z ⟶ X) (z : FieldValuedPoint B S hS Z)
    (hsurj : IsSurjective B S hS (yonedaEquiv.symm z.value))
    (_hetale : IsEtale B S hS (yonedaEquiv.symm z.value))
    (hflft : IsLocallyOfFiniteType B S hS f) (_hmono : Mono f) :
    IsFiniteTypePoint B S hS X (pointsMap B S hS Z f (z.class B S hS Z)) := by
  refine (isFiniteTypePoint_iff_exists_singleton_space B S hS X hX _).2
    ⟨Z, hZ, f, ⟨z.class B S hS Z⟩,
      ⟨fun a b ↦ (eq_class_of_isSurjective_fieldPoint B S hS z hsurj a).trans
        (eq_class_of_isSurjective_fieldPoint B S hS z hsurj b).symm⟩, hflft, ?_⟩
  refine Set.eq_singleton_iff_unique_mem.2 ⟨Set.mem_range_self _, ?_⟩
  rintro - ⟨w, rfl⟩
  exact congrArg _ (eq_class_of_isSurjective_fieldPoint B S hS z hsurj w)

end LocallyClosed

/-! ### Surjectivity on points over algebraically closed fields -/

/-- **Stacks 0487.** A morphism of algebraic spaces over `S` which is locally of finite type is
surjective exactly when, for every algebraically closed field `k` of the working universe whose
spectrum lies in the chosen site and every structure morphism `Spec k ⟶ S`, the induced map
`X(k) ⟶ Y(k)` is surjective. -/
@[stacks 0487, ega "IV 1.3.7" "more general", ega "I 6.3.10" "more general"]
theorem isSurjective_iff_surjective_app_isAlgClosed
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    IsSurjective B S hS f ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
        (b : Spec (.of k) ⟶ S),
        Function.Surjective
          (f.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))) := by
  constructor
  · intro hsurj k _ _ hk b
    set T : BigFppfOver B S hS := Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)
    intro y
    set q : yoneda.obj T ⟶ Y := yonedaEquiv.symm y with hq
    obtain ⟨U, a, hasurj, haetale⟩ := hX.exists_atlas
    have hcompSurj : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (a ≫ f) :=
      (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY U (a ≫ f)).2 (by
        rw [show IsSurjective B S hS (a ≫ f) =
          Function.Surjective (pointsMap B S hS (yoneda.obj U) (a ≫ f)) from rfl,
          pointsMap_comp]
        exact hsurj.comp
          ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).1 hasurj))
    have hcompLft : IsLocallyOfFiniteType B S hS (a ≫ f) :=
      isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS U) hX hY _ _
        (isLocallyOfFiniteType_of_isEtale B S hS hX
          ((isEtale_iff_presheaf_of_yoneda B S hS a).2 haetale)) hf
    set P := hcompSurj.rep.pullback q
    set rP := hcompSurj.rep.fst' q
    set sP := hcompSurj.rep.snd q
    have hsq : IsPullback (yoneda.map rP) (yoneda.map sP) (a ≫ f) q :=
      hcompSurj.rep.isPullback' q
    have hsPSurj : Surjective ((BigFppfOver.toScheme B S hS).map sP) :=
      hcompSurj.property q (yoneda.map rP) sP hsq
    -- The base change of `a ≫ f` to `Spec k` is locally of finite type.
    have hsPLft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map sP) := by
      rw [← isLocallyOfFiniteType_yoneda_map_iff]
      refine (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
        (f := (ObjectProperty.homMk q :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨Y, hY⟩))
        (g := (ObjectProperty.homMk (a ≫ f) :
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨Y, hY⟩))
        (f' := (ObjectProperty.homMk (yoneda.map rP) :
          (⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
        (g' := (ObjectProperty.homMk (yoneda.map sP) :
          (⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
        (IsPullback.of_map_of_faithful
          (F := ObjectProperty.ι
            (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) hsq)
        hcompLft
    -- `Spec k` is Jacobson, hence so is the base change, so it has a closed point.
    have : JacobsonSpace ((BigFppfOver.toScheme B S hS).obj T) :=
      inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of k)))
    have : JacobsonSpace ((BigFppfOver.toScheme B S hS).obj P) :=
      LocallyOfFiniteType.jacobsonSpace ((BigFppfOver.toScheme B S hS).map sP)
    obtain ⟨p₀, -⟩ := hsPSurj.surj (IsLocalRing.closedPoint k)
    obtain ⟨zP, -, hzP⟩ := nonempty_inter_closedPoints
      (X := (BigFppfOver.toScheme B S hS).obj P) (Z := Set.univ)
      ⟨p₀, Set.mem_univ _⟩ isClosed_univ.isLocallyClosed
    -- A closed point of a scheme locally of finite type over an algebraically closed field
    -- is a `k`-point, hence a section of the base change.
    set g : (BigFppfOver.toScheme B S hS).obj P ⟶ Spec (CommRingCat.of k) :=
      (BigFppfOver.toScheme B S hS).map sP
    have : LocallyOfFiniteType g := hsPLft
    set sec : Spec (CommRingCat.of k) ⟶ (BigFppfOver.toScheme B S hS).obj P :=
      pointOfClosedPoint g zP (mem_closedPoints_iff.mp hzP)
    have hsecComp : sec ≫ (BigFppfOver.toScheme B S hS).map sP =
        𝟙 (Spec (CommRingCat.of k)) := pointOfClosedPoint_comp g zP _
    -- Transport the section to the site.
    set secBase : B.obj hk ⟶ P.left :=
      B.inclusion.preimage (X := B.obj hk) (Y := P.left) sec with hsecBase
    have hsecBaseW : secBase ≫ P.hom = T.hom := by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, hsecBase, Functor.map_preimage]
      calc sec ≫ B.inclusion.map P.hom
          = (sec ≫ B.inclusion.map sP.left) ≫ B.inclusion.map T.hom := by
            rw [Category.assoc, ← Functor.map_comp, Over.w sP]
        _ = B.inclusion.map T.hom := by
            rw [show sec ≫ B.inclusion.map sP.left = 𝟙 _ from hsecComp, Category.id_comp]
    set sOver : T ⟶ P := Over.homMk secBase hsecBaseW
    have hsOverComp : sOver ≫ sP = 𝟙 T := by
      ext
      change B.inclusion.map secBase ≫ B.inclusion.map sP.left = 𝟙 _
      rw [hsecBase, Functor.map_preimage]
      exact hsecComp
    refine ⟨a.app (Opposite.op T) ((yoneda.map rP).app (Opposite.op T) sOver), ?_⟩
    have hw := congrArg (fun α : yoneda.obj P ⟶ Y ↦ α.app (Opposite.op T) sOver) hsq.w
    simp only [NatTrans.comp_app, types_comp_apply] at hw
    rw [hw]
    change q.app (Opposite.op T) (sOver ≫ sP) = y
    rw [hsOverComp, hq]
    exact yonedaEquiv.apply_symm_apply y
  · intro hall y
    obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS Y y
    have : IsAlgClosed p.val.carrier := p.property
    obtain ⟨x, hx⟩ := hall p.val.carrier p.val.contained p.val.toBase p.val.value
    refine ⟨FieldValuedPoint.class B S hS X
      ⟨p.val.carrier, p.val.contained, p.val.toBase, x⟩, ?_⟩
    rw [pointsMap_class, ← hp]
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS Y
      ⟨p.val, ?_, FieldValuedPoint.dominates_refl B S hS Y p.val⟩
    have hx' : f.app (Opposite.op (p.val.siteObject B S hS Y)) x = p.val.value := hx
    refine ⟨𝟙 (p.val.siteObject B S hS Y), ?_⟩
    change Y.map (𝟙 (p.val.siteObject B S hS Y)).op
      (f.app (Opposite.op (p.val.siteObject B S hS Y)) x) = p.val.value
    rw [hx']
    simp

end AlgebraicGeometry.Space

end
