module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions

/-!
# Conditions (4), (1) and (2) of Stacks 03JV

Let `F` be an algebraic space over a scheme `S` and let `x` be a point of `|F|` which is the
class of a field-valued point whose presenting morphism `Spec(k) ⟶ F` is a quasi-compact
monomorphism — condition (4) of Stacks 03JV. This file proves condition (1): for every affine
scheme `U` and every étale `φ : h_U ⟶ F`, the fibres of `|U| → |F|` and of `|R| → |F|` above
`x` are finite, where `R = h_U ×_F h_U`. It also proves that condition (1) implies
condition (2), the same finiteness for the members of one étale covering family.

## Main results

* `AlgebraicGeometry.Space.finite_rep_pullback_fieldMorphism_of_isQuasiCompact`: the object of
  the site representing `Spec(k) ×_F U`, for a field-valued point with quasi-compact presenting
  morphism and an étale chart with quasi-compact source, has finitely many points.
* `AlgebraicGeometry.Space.finite_setFibre_of_isQuasiCompact_fieldMorphism`: the fibre of
  `|U| → |F|` above the class of a field-valued point with quasi-compact presenting morphism
  is finite, for every étale chart with quasi-compact source.
* `HasQuasiCompactMonomorphicFieldRepresentative.hasFiniteFibresOnEveryAffineEtaleChart`, in
  the namespace `AlgebraicGeometry.Space`, is Stacks 03JV, condition (4) implies condition (1).
* `HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteFibresOnSomeEtaleCover` is Stacks 03JV,
  condition (1) implies condition (2), and
  `HasQuasiCompactMonomorphicFieldRepresentative.hasFiniteFibresOnSomeEtaleCover` is their
  composite.

## Implementation notes

The source proves (5) ⟹ (1) and uses the monomorphism of condition (4) only through
(4) ⟹ (5). The proof below splits condition (1) differently, and uses both halves of
condition (4).

The fibre of `|U| → |F|` is handled as the source does. Quasi-compactness of
`Spec(k) ⟶ F` in the sense of Stacks 03HE, applied to the quasi-compact algebraic space
`h_U`, makes the field fibre `h_U ×_F Spec(k)` a quasi-compact algebraic space; étaleness of
the chart makes it representable by an object of the site which is étale over `Spec(k)`, hence
quasi-compact and étale over a one-point scheme, hence finite
(`AlgebraicGeometry.finite_of_etale_of_subsingleton`). Every point of the fibre lifts to it by
Stacks 03H4, so the fibre is contained in the image of a finite set. Only the quasi-compactness
half of condition (4) enters here, which is why the statement is made for an arbitrary
quasi-compact field-valued representative.

For the fibre of `|R| → |F|` the source goes through the structure of `Spec(k) ×_F U` as a
finite disjoint union of spectra of finite separable extensions of `k` and a monomorphism into
its self-product over `Spec(k)` (Stacks 03DP). That route is not taken. Instead the fibre of
`|R| → |F|` above `x` is the union, over the pairs `(a, b)` of points of the — now known
finite — fibre of `|U| → |F|` above `x`, of the sets of Stacks 0AC2 attached to the cartesian
square presenting `R`, and each of those is finite by Stacks 0AC7
(`AlgebraicGeometry.Space.finite_fibrePoints_of_mono_of_isQuasiFiniteAt`), whose two
hypotheses are exactly the monomorphism half of condition (4) and quasi-finiteness of the
chart at a point, the latter supplied by étaleness. So the monomorphism is load-bearing in this
proof, and it is used at a different place from where the source uses it.

Condition (2) is obtained from condition (1) and not the other way round, which is the opposite
of the source's direction of work: the quantifier of condition (1) runs over affine étale
charts, and Stacks 03FX produces an étale atlas whose source is a disjoint union of affine
opens, so the covering family of condition (2) can simply be read off it. The index type of
condition (2) is forced to `Type u`, and the family 03FX produces is indexed by a type of that
universe, so the departure recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions` costs nothing here.

Nothing is claimed about the remaining implications of Stacks 03JV: the tags below name single
arrows, as the tags in `StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions`
name single conditions. In particular the equivalence the tag asserts is *not* proved: no two of
the six conditions are shown to imply each other.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 0AC7](https://stacks.math.columbia.edu/tag/0AC7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_quasiCompactPointsFiniteFibres
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The fibre of a chart above a quasi-compact field-valued representative -/

/-- The object of the site representing the base change `Spec(k) ×_F U` of a quasi-compact
field-valued representative along an étale chart with quasi-compact source has finitely many
points. -/
theorem finite_rep_pullback_fieldMorphism_of_isQuasiCompact
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F)
    (hp : IsQuasiCompact B S hS (fieldMorphism B S hS F p))
    {U : BigFppfOver B S hS} (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    {φ : yoneda.obj U ⟶ F}
    (hφp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    Finite ((BigFppfOver.toScheme B S hS).obj
      (hφp.rep.pullback (fieldMorphism B S hS F p))) := by
  have sqW := hφp.rep.isPullback (fieldMorphism B S hS F p)
  have hWet : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (hφp.rep.snd (fieldMorphism B S hS F p))) :=
    hφp.property_snd _
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hqcs : IsQuasiCompactSpace B S hS (pullback φ (fieldMorphism B S hS F p)) :=
    hp (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (isQuasiCompactSpace_yoneda_obj B S hS hU) φ
  have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (hφp.rep.pullback (fieldMorphism B S hS F p))) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (hqcs.of_iso B S hS
        ((IsPullback.of_hasPullback φ (fieldMorphism B S hS F p)).isoIsPullback _ _ sqW))
  exact finite_of_etale_of_subsingleton ((BigFppfOver.toScheme B S hS).map
    (hφp.rep.snd (fieldMorphism B S hS F p)))

/-- **The chart-fibre half of condition (1) of Stacks 03JV.** Let `p` be a field-valued point
of a presheaf `F` on the big fppf site of `S` whose presenting morphism `Spec(k) ⟶ F` is
quasi-compact in the sense of Stacks 03HE, and let `φ : h_U ⟶ F` be étale with `U` of
quasi-compact underlying scheme. Then the fibre of `|U| → |F|` above the point represented by
`p` is finite. -/
theorem finite_setFibre_of_isQuasiCompact_fieldMorphism
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F)
    (hp : IsQuasiCompact B S hS (fieldMorphism B S hS F p))
    {U : BigFppfOver B S hS} (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    {φ : yoneda.obj U ⟶ F} (hφ : IsEtale B S hS φ) :
    (setFibre B S hS φ p).Finite := by
  have hφp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ := presheaf_etale_of_isEtale B S hS hφ
  have sqW := hφp.rep.isPullback (fieldMorphism B S hS F p)
  have hfin := finite_rep_pullback_fieldMorphism_of_isQuasiCompact B S hS p hp hU hφp
  have hpts : Finite (points B S hS (yoneda.obj
      (hφp.rep.pullback (fieldMorphism B S hS F p)))) :=
    Finite.of_equiv _ (pointsEquivScheme B S hS _).symm
  refine Set.Finite.subset (Set.finite_range (pointsMap B S hS _
    (hφp.rep.fst (fieldMorphism B S hS F p)))) ?_
  intro a ha
  have ha' : pointsMap B S hS (yoneda.obj U) φ a = p.class B S hS F := ha
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS sqW a
    ((p.tautologicalPoint B S hS F).class B S hS (yoneda.obj p.siteObject))
    (ha'.trans (pointsMap_fieldMorphism_tautologicalPoint B S hS F p).symm)
  exact ⟨w, hw⟩

/-! ### Condition (4) implies condition (1) -/

/-- **Stacks 03JV, condition (4) implies condition (1).** If a point `x` of an algebraic space
`F` over `S` is the class of a field-valued point whose presenting morphism `Spec(k) ⟶ F` is a
quasi-compact monomorphism, then for every affine scheme `U` and every étale `φ : h_U ⟶ F` the
fibres of `|U| → |F|` and of `|R| → |F|` above `x`, where `R = h_U ×_F h_U`, are both finite. -/
@[stacks 03JV "part (4) implies part (1)"]
theorem HasQuasiCompactMonomorphicFieldRepresentative.hasFiniteFibresOnEveryAffineEtaleChart
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS F x) :
    HasFiniteFibresOnEveryAffineEtaleChart B S hS F x := by
  obtain ⟨p, hpx, hmono, hqc⟩ := h
  intro U hUaff φ hφ
  have hUcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    have := hUaff
    inferInstance
  -- The chart fibre, from quasi-compactness alone.
  have hchart : (chartFibre B S hS F φ x).Finite := by
    rw [← hpx]
    exact finite_setFibre_of_isQuasiCompact_fieldMorphism B S hS p hqc hUcpt hφ
  refine ⟨hchart, ?_⟩
  -- The square presenting the relation, as a diagram of Stacks 0AC1.
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let D : PointsFibresDiagram B S hS :=
    { W := pullback φ φ
      Z := yoneda.obj U
      X := yoneda.obj U
      Y := F
      W_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS φ φ hUalg hUalg hF
      Z_isAlgebraicSpace := hUalg
      X_isAlgebraicSpace := hUalg
      Y_isAlgebraicSpace := hF
      q := pullback.snd φ φ
      p := pullback.fst φ φ
      f := φ
      g := φ
      isPullback := IsPullback.of_hasPullback φ φ }
  have hqf : ∀ b : points B S hS (yoneda.obj U), IsQuasiFiniteAt B S hS φ b := fun b =>
    isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hUalg
      (isLocallyQuasiFinite_of_isEtale' B S hS hφ) b
  -- Both projections of a point of the relation fibre lie in the chart fibre.
  have hsub : relationFibre B S hS F φ x ⊆
      ⋃ a ∈ chartFibre B S hS F φ x, ⋃ b ∈ chartFibre B S hS F φ x,
        {r : points B S hS (pullback φ φ) |
          pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r = a ∧
          pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r = b} := by
    intro r hr
    have ha : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r) = x := by
      rw [← pointsMap_comp_apply]
      exact hr
    have hb : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r) = x := by
      rwa [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply]
    exact Set.mem_biUnion ha (Set.mem_biUnion hb ⟨rfl, rfl⟩)
  refine Set.Finite.subset (Set.Finite.biUnion hchart fun a ha =>
    Set.Finite.biUnion hchart fun b hb => ?_) hsub
  have ha' : pointsMap B S hS (yoneda.obj U) φ a = x := ha
  have hb' : pointsMap B S hS (yoneda.obj U) φ b = x := hb
  have hcomm : pointsMap B S hS D.X D.f a = pointsMap B S hS D.Z D.g b := ha'.trans hb'.symm
  have hy : HasMonomorphicFieldRepresentative B S hS D.Y
      (pointsMap B S hS D.X D.f a) := by
    change HasMonomorphicFieldRepresentative B S hS F (pointsMap B S hS (yoneda.obj U) φ a)
    rw [ha']
    exact ⟨p, hpx, hmono⟩
  exact finite_fibrePoints_of_mono_of_isQuasiFiniteAt D a b hcomm hy (hqf b)

/-! ### Condition (1) implies condition (2) -/

/-- **Stacks 03JV, condition (1) implies condition (2).** An algebraic space over `S` has an
étale covering family by affine schemes, so the finiteness condition of condition (1), which
quantifies over *every* affine étale chart, is in particular satisfied by the members of one
covering family. -/
@[stacks 03JV "part (1) implies part (2)"]
theorem HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteFibresOnSomeEtaleCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasFiniteFibresOnEveryAffineEtaleChart B S hS F x) :
    HasFiniteFibresOnSomeEtaleCover B S hS F x := by
  obtain ⟨U, f, I, W, j, e, hfS, hfE, hWaff, hje, -, hjE, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS F hF
  refine ⟨I, W, fun i => yoneda.map (j i) ≫ f,
    fun i => isEtale_of_presheaf_etale B S hS (hjE i), ?_,
    fun i => h (W i) (hWaff i) _ (isEtale_of_presheaf_etale B S hS (hjE i))⟩
  intro y
  obtain ⟨u, hu⟩ := isSurjective_of_presheafSurjective B S hS f hfS y
  -- The affine opens `W i` cover `U` on underlying schemes, so the scheme point below `u`
  -- comes from one of them.
  obtain ⟨i, w, hw⟩ : ∃ (i : I) (w : (BigFppfOver.toScheme B S hS).obj (W i)),
      (BigFppfOver.toScheme B S hS).map (j i) w = pointsToScheme B S hS U u := by
    set z := (sigmaMk fun k => (BigFppfOver.toScheme B S hS).obj (W k)).symm
      (e.inv (pointsToScheme B S hS U u)) with hz
    refine ⟨z.1, z.2, ?_⟩
    have hι : Sigma.ι (fun k => (BigFppfOver.toScheme B S hS).obj (W k)) z.1 z.2 =
        e.inv (pointsToScheme B S hS U u) := by
      rw [← sigmaMk_mk, hz, Homeomorph.apply_symm_apply]
    rw [← hje z.1, Scheme.Hom.comp_apply, hι, ← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  obtain ⟨a, ha⟩ := surjective_pointsToScheme B S hS (W i) w
  have hau : pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (j i)) a = u :=
    injective_pointsToScheme B S hS U
      (by rw [pointsToScheme_pointsMap_yoneda B S hS (j i) a, ha, hw])
  refine ⟨pointsMap B S hS (yoneda.obj (W i))
    (Sigma.ι (fun k => yoneda.obj (W k)) i) a, ?_⟩
  rwa [← pointsMap_comp_apply, Sigma.ι_desc, pointsMap_comp_apply, hau]

/-- **Stacks 03JV, condition (4) implies condition (2).** The composite of the two implications
above: condition (4) gives condition (1), which gives condition (2). -/
@[stacks 03JV "part (4) implies part (2)"]
theorem HasQuasiCompactMonomorphicFieldRepresentative.hasFiniteFibresOnSomeEtaleCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS F x) :
    HasFiniteFibresOnSomeEtaleCover B S hS F x :=
  (h.hasFiniteFibresOnEveryAffineEtaleChart B S hS F hF).hasFiniteFibresOnSomeEtaleCover
    B S hS F hF

end AlgebraicGeometry.Space

end
