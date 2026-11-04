module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionAntitone
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart

/-!
# The scheme situation of a represented good space

In Situation 0EDT let `Y = h_V` be a good algebraic space over `B` represented by a scheme `V`.
Then `V` is a base situation of Chapter 42 of the Stacks Project: it is locally Noetherian,
being étale locally so; it is universally catenary, being locally of finite type over the
universally catenary space `B`; and `δ_{Y/B}`, which is a dimension function on `|Y|` by
Stacks 0EDN, is a dimension function on `V` through the identification of points of Stacks
03BX. This is the reduction "we may assume `Y` is a scheme" of the proofs of Chapter 82: the
scheme theory of `V` over itself, and of every scheme locally of finite type over `V`, computes
δ-dimensions as the space theory over `B` does.

## Main definitions

* `AlgebraicGeometry.Space.representedChowSituation`: the base situation of Chapter 42 on the
  scheme `V` representing a good space, with the dimension function `δ_{h_V/B}`.

## Main results

* `AlgebraicGeometry.Space.isDeltaCompatible_representedChowSituation`: `V` over itself is
  δ-compatible with `h_V` over `B`.
* `AlgebraicGeometry.Space.IsDeltaCompatible.comp`: δ-compatibility passes from `h_V` to a
  scheme `U` locally of finite type over `V`, with the composite structure morphism; the two
  relative transcendence degrees agree for a morphism of schemes, Stacks 04NM read on the
  identity chart, and both sides are additive in towers, Stacks 04NR.
* `AlgebraicGeometry.Space.isDeltaCompatible_representedChowSituation_comp`: hence a morphism
  `U → V` of schemes over `B`, with `h_V` good, makes `U` δ-compatible over the situation of
  `V`.

## References

* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 04NR](https://stacks.math.columbia.edu/tag/04NR)
* [Stacks Project, Tag 0ED8](https://stacks.math.columbia.edu/tag/0ED8)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-- The scheme representing a good space is locally Noetherian: the good space has an étale
atlas by a locally Noetherian scheme, and for a represented space that is a property of the
representing scheme, Stacks 03E8. -/
theorem isLocallyNoetherian_of_isGood_yoneda {V : BigFppfOver D.site D.base D.base_mem}
    (sY : yoneda.obj V ⟶ D.space) (hY : D.IsGood sY) :
    IsLocallyNoetherian ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V) :=
  (exists_atlas_iff_of_representable D.site D.base D.base_mem (yoneda.obj V)
    (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).1
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)

/-- The scheme representing a good space is universally catenary: the space is universally
catenary, being locally of finite type over the universally catenary base, Stacks 0ED8, and the
identity is an étale chart of it. -/
theorem isUniversallyCatenary_of_isGood_yoneda {V : BigFppfOver D.site D.base D.base_mem}
    (sY : yoneda.obj V ⟶ D.space) (hY : D.IsGood sY)
    [IsLocallyNoetherian ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V)] :
    Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V) :=
  isUniversallyCatenary_chart_of_isUniversallyCatenary D.site D.base D.base_mem hY.1
    (isUniversallyCatenary_of_isLocallyOfFiniteType D.site D.base D.base_mem D.isAlgebraicSpace
      hY.1 D.universallyCatenary sY hY.2.2)
    V (𝟙 _) (isEtale_of_isIso D.site D.base D.base_mem (𝟙 _))

/-- **The base situation of a represented good space.** For a good space `h_V → B` represented
by a scheme `V`, the base situation of Chapter 42, Stacks 02QL, on `V`: locally Noetherian and
universally catenary, with the dimension function `δ_{h_V/B}` of Stacks 0EDN read on the points
of `V`. -/
abbrev representedChowSituation {V : BigFppfOver D.site D.base D.base_mem}
    (sY : yoneda.obj V ⟶ D.space) (hY : D.IsGood sY) : Stacks.Chow.ChowSituation.{u} :=
  haveI := isLocallyNoetherian_of_isGood_yoneda D sY hY
  { S := (BigFppfOver.toScheme D.site D.base D.base_mem).obj V
    isUniversallyCatenary := isUniversallyCatenary_of_isGood_yoneda D sY hY
    dimensionFunction := (deltaDimensionFunction D sY hY).comp
      (schemePointsHomeomorph D.site D.base D.base_mem V).symm.isOpenEmbedding }

/-- The base scheme of the situation of a represented good space is the representing scheme. -/
@[simp]
theorem representedChowSituation_S {V : BigFppfOver D.site D.base D.base_mem}
    (sY : yoneda.obj V ⟶ D.space) (hY : D.IsGood sY) :
    (representedChowSituation D sY hY).S = (BigFppfOver.toScheme D.site D.base D.base_mem).obj V :=
  rfl

/-- The dimension function of the situation of a represented good space is `δ_{h_V/B}`, read at
the corresponding point of `h_V`. -/
theorem representedChowSituation_dimensionFunction_apply
    {V : BigFppfOver D.site D.base D.base_mem} (sY : yoneda.obj V ⟶ D.space) (hY : D.IsGood sY)
    (y : (BigFppfOver.toScheme D.site D.base D.base_mem).obj V) :
    (representedChowSituation D sY hY).dimensionFunction y =
      D.deltaValue sY ((pointsEquivScheme D.site D.base D.base_mem V).symm y) :=
  deltaDimensionFunction_apply D sY hY _

/-- **A represented good space over its own situation.** The scheme `V` over itself, with the
dimension function `δ_{h_V/B}`, is δ-compatible with the good space `h_V → B`. -/
theorem isDeltaCompatible_representedChowSituation {V : BigFppfOver D.site D.base D.base_mem}
    (sY : yoneda.obj V ⟶ D.space) (hY : D.IsGood sY) :
    IsDeltaCompatible D V sY (representedChowSituation D sY hY)
      (𝟙 ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V)) := by
  intro y
  rw [Stacks.Chow.relativeDimension_id, representedChowSituation_dimensionFunction_apply]
  exact congrArg _ ((pointsEquivScheme D.site D.base D.base_mem V).symm_apply_apply y)

/-- The relative transcendence degree, Stacks 04NM, of the morphism of represented spaces
induced by a morphism of schemes `g`, at a point, is the transcendence degree of the residue
field extension of `g` at the corresponding point: read it on the identity charts. -/
theorem hasTranscendenceDegreeAt_yoneda_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (x : points B S hS (yoneda.obj U)) :
    HasTranscendenceDegreeAt B S hS (yoneda.map g) x
      (Cardinal.toENat (Stacks.Chow.residueTrdeg ((BigFppfOver.toScheme B S hS).map g)
        (pointsToScheme B S hS U x))) := by
  have h := (hasTranscendenceDegreeAt_pointsMap_iff B S hS
    (Cardinal.toENat (Stacks.Chow.residueTrdeg ((BigFppfOver.toScheme B S hS).map g)
      (pointsToScheme B S hS U x))) (yoneda.map g) U V (𝟙 _) (𝟙 _) g
    (presheaf_etale_of_iso B S hS (Iso.refl _)) (presheaf_etale_of_iso B S hS (Iso.refl _))
    (by simp)
    (pointsToScheme B S hS U x)).2 rfl
  rwa [pointsMap_id, id_eq, show (pointsEquivScheme B S hS U).symm (pointsToScheme B S hS U x) =
    x from (pointsEquivScheme B S hS U).symm_apply_apply x] at h

variable {D}

/-- **δ-compatibility along a morphism of schemes.** Let `h_V → B` be good, and let the scheme
situation `C` with `t₀ : V → C.S` be δ-compatible with it. If `g : U → V` is a morphism of
schemes locally of finite type and `h_U → B` is the composite `h_U → h_V → B`, then `C` with
`U → V → C.S` is δ-compatible with `h_U → B`. Both dimension functions grow along `g` by the
transcendence degree of the residue field extension, Stacks 04NR on the space side and the tower
law on the scheme side. -/
theorem IsDeltaCompatible.comp {U V : BigFppfOver D.site D.base D.base_mem}
    {sY : yoneda.obj V ⟶ D.space} (hY : D.IsGood sY) {C : Stacks.Chow.ChowSituation.{u}}
    {t₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj V ⟶ C.S}
    [LocallyOfFiniteType t₀] (h : IsDeltaCompatible D V sY C t₀) (g : U ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map g)] :
    IsDeltaCompatible D U (yoneda.map g ≫ sY) C
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map g ≫ t₀) := by
  intro x
  set g₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map g
  have hU := isAlgebraicSpace_yoneda D.site D.base D.base_mem U
  have hV := isAlgebraicSpace_yoneda D.site D.base D.base_mem V
  have hg : IsLocallyOfFiniteType D.site D.base D.base_mem (yoneda.map g) :=
    (isLocallyOfFiniteType_yoneda_map_iff D.site D.base D.base_mem g).2 inferInstance
  obtain ⟨n, hn⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem sY hY.2.2
    (pointsMap D.site D.base D.base_mem (yoneda.obj U) (yoneda.map g) x)
  have hcomp := hasTranscendenceDegreeAt_comp D.site D.base D.base_mem hU hV D.isAlgebraicSpace
    (yoneda.map g) sY x _ _ (hasTranscendenceDegreeAt_yoneda_map D.site D.base D.base_mem g x) hn
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1
    (Stacks.Chow.residueTrdeg_lt_aleph0 g₀ (pointsToScheme D.site D.base D.base_mem U x))
  rw [Stacks.Chow.relativeDimension_comp_eq_add_trdeg, ← pointsToScheme_pointsMap, h,
    BaseSpaceDimensionSituation.deltaValue, BaseSpaceDimensionSituation.deltaValue,
    inducedDimensionValue_eq D.site D.base D.base_mem hU D.isAlgebraicSpace _ _
      (isLocallyOfFiniteType_comp D.site D.base D.base_mem hU hV D.isAlgebraicSpace _ _ hg hY.2.2)
      x _ hcomp,
    inducedDimensionValue_eq D.site D.base D.base_mem hV D.isAlgebraicSpace _ _ hY.2.2 _ _ hn,
    pointsMap_comp_apply, hm]
  simp only [Cardinal.toNat_natCast, map_natCast, ENat.toNat_natCast]
  rw [show ((m : ℕ∞) + (n : ℕ∞)).toNat = m + n from rfl]
  push_cast
  ring

/-- **A scheme over a represented good space.** Let `h_V → B` be good and let `g : U → V` be a
morphism of schemes locally of finite type. Then the scheme `U` with `g` into the situation of
`V` is δ-compatible with the good space `h_U → h_V → B`. -/
theorem isDeltaCompatible_representedChowSituation_comp
    {U V : BigFppfOver D.site D.base D.base_mem} (sY : yoneda.obj V ⟶ D.space)
    (hY : D.IsGood sY) (g : U ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map g)] :
    IsDeltaCompatible D U (yoneda.map g ≫ sY) (representedChowSituation D sY hY)
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) := by
  have h := (isDeltaCompatible_representedChowSituation D sY hY).comp hY g
  rwa [Category.comp_id] at h

end AlgebraicGeometry.Space

end
