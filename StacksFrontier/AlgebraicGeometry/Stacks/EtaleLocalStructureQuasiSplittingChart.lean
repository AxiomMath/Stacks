module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingAffineLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureQuasiSplitting
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackCell
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# Two steps of the proof of Stacks 0DU3

The proof of **Stacks 0DU3** (the étale local structure of a quasi-DM algebraic stack with
separated diagonal) applies **Stacks 04S0** to the restriction of the groupoid `R = U ×_𝒳 U` of a
flat, locally quasi-finite chart to an affine open `U`, and then reads off the point of the
resulting quotient stack over the given point of `𝒳`. This file supplies the two steps of that
argument which are statements about groupoid schemes and about points of quotient stacks alone.

## Main results

* `AlgebraicGeometry.Stack.EtaleLocalStructure.restriction_groupoidPreRelation_mem`: the
  pre-relation `(t, s)` of a restriction of a groupoid scheme inherits every base-change-stable
  property of the pre-relation of the groupoid (it is a base change of it, Stacks 044D).
* `AlgebraicGeometry.Stack.EtaleLocalStructure.isSeparated_source_of_isAffine`: the source map of
  a groupoid scheme with affine object scheme and separated pre-relation is separated.
* `Stack.EtaleLocalStructure.exists_isAffine_isFinite_flat_subgroupoid_of_isSeparated`:
  **Stacks 04S0** at a groupoid scheme with affine object scheme whose source and target are
  separated, flat and locally of finite presentation and whose source is locally quasi-finite,
  with the quasi-splitting delivered as a groupoid scheme of the shape of clause (3) of
  Stacks 0DU3, included in the restriction by the identity on objects.
* `AlgebraicGeometry.Stack.pointsMap_congr_of_obj_eq`: the map on points of a 1-morphism over
  the site depends only on its map on objects.
* `AlgebraicGeometry.Stack.pointsMap_quotientStackProjection_comp_quotientStackMap`: on points,
  the projection `S_U ⟶ [U/R]` of Stacks 044R intertwines the 1-morphism `[φ]` of Stacks 046Q
  with the map of object spaces of `φ`;
  `pointsMap_quotientStackProjection_comp_quotientStackMap_comp` and
  `pointsMap_quotientStackProjection_comp_quotientStackMap_point` are the same inside a further
  1-morphism, the second on a point of the object space.

## Implementation notes

Situation 04RV asks that `s` and `t` be separated; for the restriction of the chart groupoid to
an affine open `U` this comes from the separatedness of `(t, s)` (a base change of the diagonal of
`𝒳`) composed with the separated projection `U ×_S U ⟶ U`, which is
`isSeparated_source_of_isAffine`. The points statement is proved on objects only: the
2-isomorphism of Stacks 046Q relates `[φ]` to the pointwise map, and the pointwise map agrees on
objects with the map of object spaces on the nose, which is all a map on points sees.

## References

* [Stacks Project, Tag 044D](https://stacks.math.columbia.edu/tag/044D)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04S0](https://stacks.math.columbia.edu/tag/04S0)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

universe u

open Stacks.Groupoids

/-- The pre-relation of a restriction of a groupoid scheme has every base-change-stable property
which the pre-relation of the groupoid has. -/
theorem restriction_groupoidPreRelation_mem {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (R : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (h : P (AlgebraicGeometry.groupoidPreRelation G).left) :
    P (AlgebraicGeometry.groupoidPreRelation R.groupoid).left := by
  obtain ⟨e, he, -⟩ := AlgebraicGeometry.exists_iso_restriction_groupoidPreRelation G g R
  have hres : P (AlgebraicGeometry.PreRelation.restrict
      (AlgebraicGeometry.groupoidPreRelation G) g).left :=
    AlgebraicGeometry.overFibreProduct_fst _ _ h
  have h1 : P (e.hom ≫ AlgebraicGeometry.PreRelation.restrict
      (AlgebraicGeometry.groupoidPreRelation G) g).left := by
    rw [Over.comp_left]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    exact (P.cancel_left_of_respectsIso _ _).mpr hres
  rw [he, Over.comp_left] at h1
  have : IsIso (prod.map (eqToHom R.objects_eq) (eqToHom R.objects_eq) :
      (R.groupoid.objects ⨯ R.groupoid.objects : Over S) ⟶ _).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (prod.map (eqToHom R.objects_eq)
      (eqToHom R.objects_eq))))
  exact (P.cancel_right_of_respectsIso _ _).mp h1

/-- The source map of a groupoid scheme with affine object scheme and separated pre-relation is
separated. -/
theorem isSeparated_source_of_isAffine {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left]
    [AlgebraicGeometry.IsSeparated (AlgebraicGeometry.groupoidPreRelation G).left] :
    AlgebraicGeometry.IsSeparated G.source.left := by
  have hsnd : AlgebraicGeometry.IsSeparated
      (prod.snd : (G.objects ⨯ G.objects : Over S) ⟶ G.objects).left := by
    have hU : AlgebraicGeometry.IsSeparated G.objects.hom := by
      have : AlgebraicGeometry.IsSeparated (G.objects.hom ≫ terminal.from S) := by
        rw [show G.objects.hom ≫ terminal.from S = terminal.from G.objects.left from
          terminal.hom_ext _ _]
        infer_instance
      exact AlgebraicGeometry.IsSeparated.of_comp G.objects.hom (terminal.from S)
    rw [show (prod.snd : (G.objects ⨯ G.objects : Over S) ⟶ G.objects).left =
      (Over.prodLeftIsoPullback G.objects G.objects).hom ≫ pullback.snd _ _ by
        simp]
    have : AlgebraicGeometry.IsSeparated (pullback.snd G.objects.hom G.objects.hom) :=
      MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsSeparated)
        (IsPullback.of_hasPullback G.objects.hom G.objects.hom) hU
    infer_instance
  have hcomp : G.source.left = (AlgebraicGeometry.groupoidPreRelation G).left ≫
      (prod.snd : (G.objects ⨯ G.objects : Over S) ⟶ G.objects).left := by
    rw [← Over.comp_left]
    simp [AlgebraicGeometry.groupoidPreRelation]
  rw [hcomp]
  infer_instance
/-- **Stacks 04S0 at a groupoid scheme with affine object scheme and separated, flat, locally
finitely presented source and target, the source locally quasi-finite, delivered as a groupoid
scheme of the shape of clause (3) of Stacks 0DU3.** There are an affine `U''`, an étale
`g : U'' ⟶ U` and a point `u''` over `u` such that every groupoid scheme realizing `R|_{U''}`
contains a quasi-splitting over `u''`, which is a groupoid scheme on the same object scheme with
affine structure schemes and finite, flat, locally finitely presented source and target. -/
theorem exists_isAffine_isFinite_flat_subgroupoid_of_isSeparated {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    [IsAffine G.objects.left]
    [AlgebraicGeometry.IsSeparated G.source.left] [AlgebraicGeometry.IsSeparated G.target.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    [LocallyQuasiFinite G.source.left] :
    ∃ (U'' : Over S) (g : U'' ⟶ G.objects) (u'' : U''.left),
      IsAffine U''.left ∧ Etale g.left ∧ g.left.base u'' = u ∧
      ∀ R : AlgebraicGeometry.GroupoidScheme.Restriction G g,
        ∃ (H : GroupoidScheme S) (φ : GroupoidScheme.Hom H R.groupoid),
          (∃ hobj : H.objects = R.groupoid.objects, φ.mapObjects = eqToHom hobj) ∧
          AlgebraicGeometry.IsOpenImmersion φ.mapArrows.left ∧
          (∃ p : H.arrows.left, φ.mapArrows.left.base p =
            R.groupoid.identity.left.base ((eqToHom R.objects_eq.symm).left.base u'')) ∧
          IsAffine H.objects.left ∧ IsAffine H.arrows.left ∧
          AlgebraicGeometry.IsFinite H.source.left ∧ Flat H.source.left ∧
          LocallyOfFinitePresentation H.source.left ∧
          AlgebraicGeometry.IsFinite H.target.left ∧ Flat H.target.left ∧
          LocallyOfFinitePresentation H.target.left := by
  let D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u} :=
    { S := S
      groupoid := G
      u := u
      sourceQuasiFiniteAtIdentity :=
        (AlgebraicGeometry.forall_quasiFiniteAt_iff G.source.left).mpr
          ⟨inferInstance, inferInstance⟩ (G.identity.left.base u) }
  have : IsAffine D.groupoid.objects.left := inferInstanceAs (IsAffine G.objects.left)
  have : Flat D.groupoid.source.left := inferInstanceAs (Flat G.source.left)
  have : LocallyOfFinitePresentation D.groupoid.source.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.source.left)
  have : Flat D.groupoid.target.left := inferInstanceAs (Flat G.target.left)
  have : LocallyOfFinitePresentation D.groupoid.target.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.target.left)
  obtain ⟨U', gp, R', U'', j, u'', -, -, haff, -, het, hbase, -, -, hqs⟩ :=
    GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation D C hS hU hR hP hK
  refine ⟨U'', j ≫ R'.hom.mapObjects, u'', haff, het, hbase, fun R => ?_⟩
  have := het
  have : IsAffine R.groupoid.objects.left := by rw [R.objects_eq]; exact haff
  have hsrc : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsStableUnderComposition], P G.source.left → P (j ≫ R'.hom.mapObjects).left →
      P R.groupoid.source.left ∧ P R.groupoid.target.left := by
    intro P _ _ hs hg
    have h := AlgebraicGeometry.overFibreProduct_comp (pullback.snd (j ≫ R'.hom.mapObjects)
      G.target) G.source (AlgebraicGeometry.overFibreProduct_snd _ G.target hg) hs
    exact ⟨AlgebraicGeometry.restriction_source_mem G _ R P h,
      AlgebraicGeometry.restriction_target_mem G _ R P h⟩
  obtain ⟨h1, h2⟩ := hsrc @Flat inferInstance inferInstance
  obtain ⟨h3, h4⟩ := hsrc @LocallyOfFinitePresentation inferInstance inferInstance
  have := h1
  have := h2
  have := h3
  have := h4
  obtain ⟨P⟩ := hqs R
  have : IsIso (eqToHom P.objects_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom P.objects_eq.symm)))
  have := P.arrows_open
  have hobjaff : IsAffine P.subgroupoid.objects.left := by
    rw [P.objects_eq]
    infer_instance
  have hflat : ∀ (f : P.subgroupoid.arrows ⟶ P.subgroupoid.objects)
      (f' : R.groupoid.arrows ⟶ R.groupoid.objects),
      P.inclusion.mapArrows ≫ f' = f ≫ P.inclusion.mapObjects → Flat f'.left →
      LocallyOfFinitePresentation f'.left → Flat f.left ∧ LocallyOfFinitePresentation f.left := by
    intro f f' h _ _
    have : f.left = P.inclusion.mapArrows.left ≫ f'.left ≫ (eqToHom P.objects_eq.symm).left := by
      rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, h,
        P.mapObjects_eq, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [this]
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨hsflat, hslfp⟩ := hflat _ _ P.inclusion.map_source h1 h3
  obtain ⟨htflat, htlfp⟩ := hflat _ _ P.inclusion.map_target h2 h4
  have := P.source_finite
  exact ⟨P.subgroupoid, P.inclusion, ⟨P.objects_eq, P.mapObjects_eq⟩, P.arrows_open,
    P.contains_identity, hobjaff, isAffine_of_isAffineHom P.subgroupoid.source.left,
    P.source_finite, hsflat, hslfp, P.target_finite, htflat, htlfp⟩

end AlgebraicGeometry.Stack.EtaleLocalStructure

namespace AlgebraicGeometry.Stack

universe u v t v' t'

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- The map on points of a 1-morphism over the site depends only on its map on objects. -/
theorem pointsMap_congr_of_obj_eq {𝒳 : BasedCategory.{v, t} (BigFppfOver C S hS)}
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver C S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (F G : 𝒳 ⥤ᵇ 𝒴) (h : ∀ x, F.obj x = G.obj x) :
    pointsMap C S hS 𝒳 h𝒳 h𝒴 F = pointsMap C S hS 𝒳 h𝒳 h𝒴 G := by
  funext p
  induction p using Quotient.inductionOn with
  | h p =>
    show pointClass C S hS 𝒴 h𝒴 (fieldValuedPointMap C S hS 𝒳 F p) =
      pointClass C S hS 𝒴 h𝒴 (fieldValuedPointMap C S hS 𝒳 G p)
    congr 1
    cases p
    simp only [fieldValuedPointMap, h]

variable {B : AlgebraicSpaces C S hS}

/-- The inclusion of the object space into the pointwise groupoid fibration, as a 1-morphism over
the site. -/
noncomputable def pointwiseObjectInclusionBased (G : GroupoidInAlgebraicSpaces C S hS B) :
    (fibredCategory C S hS G.objects.obj).val ⥤ᵇ
      presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors) :=
  ⟨pointwiseObjectInclusion G, rfl⟩

/-- **The projection of Stacks 044R commutes with the induced 1-morphism of Stacks 046Q on
points.** -/
theorem pointsMap_quotientStackProjection_comp_quotientStackMap
    {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    pointsMap C S hS _ (fibredCategory C S hS G.objects.obj).property
        (isFiberedInGroupoids_quotientStack H)
        (BasedFunctor.comp (quotientStackProjection G) (quotientStackMap φ)) =
      pointsMap C S hS _ (fibredCategory C S hS G.objects.obj).property
        (isFiberedInGroupoids_quotientStack H)
        (BasedFunctor.comp (associatedMap C S hS φ.toGroupoidHom.mapObjects).1.hom
          (quotientStackProjection H)) := by
  have h1 := pointsMap_eq_of_basedNatTrans C S hS _ (fibredCategory C S hS G.objects.obj).property
    (isFiberedInGroupoids_quotientStack H)
    (BasedCategory.whiskerLeft (pointwiseObjectInclusionBased G) (quotientStackMap_commutes φ).hom)
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · exact pointsMap_congr_of_obj_eq _ _ _ _ (fun x => rfl)
  · exact pointsMap_congr_of_obj_eq _ _ _ _ (fun x => rfl)

/-- On points, the projection `S_{U₁} ⟶ [U₁/R₁]` followed by `[φ]` is the map of object spaces
followed by the projection, inside any further 1-morphism. -/
theorem pointsMap_quotientStackProjection_comp_quotientStackMap_comp
    {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver C S hS)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    (X : quotientStack H ⥤ᵇ 𝒵) :
    pointsMap C S hS _ (fibredCategory C S hS G.objects.obj).property h𝒵
        (BasedFunctor.comp (quotientStackProjection G) (BasedFunctor.comp (quotientStackMap φ) X)) =
      pointsMap C S hS _ (fibredCategory C S hS G.objects.obj).property h𝒵
        (BasedFunctor.comp (associatedMap C S hS φ.toGroupoidHom.mapObjects).1.hom
          (BasedFunctor.comp (quotientStackProjection H) X)) := by
  funext z
  have h := congrFun (pointsMap_quotientStackProjection_comp_quotientStackMap φ) z
  have e1 := pointsMap_comp C S hS _ (fibredCategory C S hS G.objects.obj).property
    (isFiberedInGroupoids_quotientStack H) h𝒵
    (BasedFunctor.comp (quotientStackProjection G) (quotientStackMap φ)) X z
  have e2 := pointsMap_comp C S hS _ (fibredCategory C S hS G.objects.obj).property
    (isFiberedInGroupoids_quotientStack H) h𝒵
    (BasedFunctor.comp (associatedMap C S hS φ.toGroupoidHom.mapObjects).1.hom
      (quotientStackProjection H)) X z
  rw [h] at e1
  exact e1.symm.trans e2

/-- The step of `pointsMap_chainHom` at one morphism of groupoids, on a point of the object
space. -/
theorem pointsMap_quotientStackProjection_comp_quotientStackMap_point
    {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver C S hS)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    (X : quotientStack H ⥤ᵇ 𝒵) (z : Space.points C S hS G.objects.obj) :
    pointsMap C S hS _ (fibredCategory C S hS G.objects.obj).property h𝒵
        (BasedFunctor.comp (quotientStackProjection G) (BasedFunctor.comp (quotientStackMap φ) X))
        (spacePointMap C S hS G.objects.obj (fibredCategory C S hS G.objects.obj)
          (BasedFunctor.id _) z) =
      pointsMap C S hS _ (fibredCategory C S hS H.objects.obj).property h𝒵
        (BasedFunctor.comp (quotientStackProjection H) X)
        (spacePointMap C S hS H.objects.obj (fibredCategory C S hS H.objects.obj)
          (BasedFunctor.id _) (Space.pointsMap C S hS _ φ.toGroupoidHom.mapObjects z)) := by
  refine (congrFun (pointsMap_quotientStackProjection_comp_quotientStackMap_comp φ 𝒵 h𝒵 X)
    _).trans ?_
  refine (pointsMap_comp C S hS _ (fibredCategory C S hS G.objects.obj).property
    (fibredCategory C S hS H.objects.obj).property h𝒵 _ _ _).symm.trans ?_
  exact congrArg _ (spacePointMap_pointsMap_associatedMap C S hS _ z).symm

end AlgebraicGeometry.Stack

end
