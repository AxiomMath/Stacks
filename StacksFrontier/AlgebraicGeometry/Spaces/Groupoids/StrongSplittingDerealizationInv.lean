module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialitySourceTargetCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealization

/-!
# The open cut out by a splitting is closed under inverses

Let `G` be a groupoid scheme over `S` whose object, arrow and composable-pair schemes a big
fppf site contains, let `p : X ⟶ U` be a morphism to its object scheme, and let `Rs` realize the
restriction of the realization of `G` along `p`.  The open subscheme of the arrow scheme of the
restriction of `G` cut out by an open finite subgroupoid of `Rs` contains the inverse of each of
its points.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_eq_groupoidInverse_of_openFiniteSubgroupoid`:
  an open finite subgroupoid contains the inverse of each of its arrows.
* `Stacks.Groupoids.GroupoidScheme.splittingInverseHom_eq`: the de-realized inverse of the
  restriction of the groupoid scheme is the inversion of the realized restriction.
* `Stacks.Groupoids.GroupoidScheme.mem_splittingOpens_restrictionInverse`: the open cut out by a
  splitting is closed under the inverse of the restriction of the groupoid scheme.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

noncomputable section

universe u v

namespace Deformation

/-- Composites of equal pairs of arrows of an evaluated groupoid agree.  The composability
witness appears in the type of a composite, so this congruence replaces a rewrite. -/
theorem GroupoidInFunctors.compose_eq_of_arrows_eq {J : Type u} [Category.{v} J]
    (K : GroupoidInFunctors J) (J' : J) {a a' b b' : K.arrows.obj J'}
    (h : K.source.app J' a = K.target.app J' b)
    (h' : K.source.app J' a' = K.target.app J' b')
    (ha : a = a') (hb : b = b') :
    K.compose J' a b h = K.compose J' a' b' h' := by
  subst ha
  subst hb
  rfl

/-- **The inverse of an arrow of an evaluated groupoid composed before the arrow is the identity
at its source.** -/
theorem compose_inverseArrow_self {J : Type u} [Category.{v} J] (K : GroupoidInFunctors J)
    (J' : J) (a : K.arrows.obj J')
    (w : K.source.app J' (inverseArrow K J' a) = K.target.app J' a) :
    K.compose J' (inverseArrow K J' a) a w = K.identity J' (K.source.app J' a) := by
  let := K.evaluationGroupoid J'
  have hq : (K.evaluationArrowEquiv J' (K.source.app J' a) (K.target.app J' a)
      ((K.evaluationArrowEquiv J' (K.source.app J' a) (K.target.app J' a)).symm
        ⟨a, rfl, rfl⟩)).1 = a :=
    congrArg Subtype.val
      ((K.evaluationArrowEquiv J' (K.source.app J' a) (K.target.app J' a)).apply_symm_apply _)
  have hi : (K.evaluationArrowEquiv J' (K.target.app J' a) (K.source.app J' a)
      (Groupoid.inv ((K.evaluationArrowEquiv J' (K.source.app J' a)
        (K.target.app J' a)).symm ⟨a, rfl, rfl⟩))).1 = inverseArrow K J' a :=
    ((inverseArrow_val K J'
      ((K.evaluationArrowEquiv J' (K.source.app J' a) (K.target.app J' a)).symm
        ⟨a, rfl, rfl⟩)).symm.trans (congrArg (inverseArrow K J') hq)).symm
  refine Eq.trans (GroupoidInFunctors.compose_eq_of_arrows_eq K J' w
    ((K.evaluationArrowEquiv J' (K.target.app J' a) (K.source.app J' a)
      (Groupoid.inv ((K.evaluationArrowEquiv J' (K.source.app J' a)
        (K.target.app J' a)).symm ⟨a, rfl, rfl⟩))).2.1.trans
      ((K.evaluationArrowEquiv J' (K.source.app J' a) (K.target.app J' a)
        ((K.evaluationArrowEquiv J' (K.source.app J' a)
          (K.target.app J' a)).symm ⟨a, rfl, rfl⟩)).2.2).symm) hi.symm hq.symm) ?_
  refine (K.evaluationArrowEquiv_comp J'
    ((K.evaluationArrowEquiv J' (K.source.app J' a) (K.target.app J' a)).symm ⟨a, rfl, rfl⟩)
    (Groupoid.inv ((K.evaluationArrowEquiv J' (K.source.app J' a)
      (K.target.app J' a)).symm ⟨a, rfl, rfl⟩))).symm.trans ?_
  exact congrArg (fun e => (K.evaluationArrowEquiv J' (K.source.app J' a)
    (K.source.app J' a) e).1)
    (Groupoid.comp_inv ((K.evaluationArrowEquiv J' (K.source.app J' a)
      (K.target.app J' a)).symm ⟨a, rfl, rfl⟩))

end Deformation

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **An open finite subgroupoid contains the inverse of each of its arrows.**

The subgroupoid is a groupoid in functors on the ambient object space, so it has an inverse of
the given arrow; that inverse is an arrow of the ambient groupoid which composes with the given
one to the ambient identity arrow, because composition in the subgroupoid is the restriction of
the ambient composition and the identity of the subgroupoid is idempotent, and left inverses in
the ambient groupoid are unique. -/
theorem exists_eq_groupoidInverse_of_openFiniteSubgroupoid
    (K : GroupoidInAlgebraicSpaces C S hS B) (H : OpenFiniteSubgroupoid K)
    (T : (BigFppfOver C S hS)ᵒᵖ) (b : H.arrows.toFunctor.obj T) :
    ∃ c : H.arrows.toFunctor.obj T,
      H.arrows.ι.app T c = (groupoidInverse K).app T (H.arrows.ι.app T b) := by
  let F : Deformation.GroupoidInFunctors ((BigFppfOver C S hS)ᵒᵖ) :=
    { objects := K.objects.obj
      arrows := H.arrows.toFunctor
      source := H.arrows.ι ≫ K.source.hom
      target := H.arrows.ι ≫ K.target.hom
      comp := H.comp
      pointwiseGroupoid := H.pointwiseGroupoid }
  have hidfact : ∀ z : F.Evaluation T,
      H.arrows.ι.app T (F.identity T z) = K.toGroupoidInFunctors.identity T z := by
    intro z
    have hs : K.source.hom.app T (H.arrows.ι.app T (F.identity T z)) = z :=
      (F.evaluationArrowEquiv T z z (𝟙 z)).2.1
    have ht : K.target.hom.app T (H.arrows.ι.app T (F.identity T z)) = z :=
      (F.evaluationArrowEquiv T z z (𝟙 z)).2.2
    have haa : F.compose T (F.identity T z) (F.identity T z) (hs.trans ht.symm) =
        F.identity T z := by
      have hh := F.evaluationArrowEquiv_comp T (𝟙 z) (𝟙 z)
      rw [Category.id_comp] at hh
      exact hh.symm
    exact (Deformation.GroupoidInFunctors.identity_eq_of_idempotent
      K.toGroupoidInFunctors T z (H.arrows.ι.app T (F.identity T z)) hs ht
      ((H.comp_restricts T ⟨(F.identity T z, F.identity T z), hs.trans ht.symm⟩).symm.trans
        (congrArg (H.arrows.ι.app T) haa))).symm
  refine ⟨Deformation.inverseArrow F T b, ?_⟩
  have hcs : K.source.hom.app T (H.arrows.ι.app T (Deformation.inverseArrow F T b)) =
      K.target.hom.app T (H.arrows.ι.app T b) :=
    Deformation.inverseArrow_source F T b
  have hct : K.target.hom.app T (H.arrows.ι.app T (Deformation.inverseArrow F T b)) =
      K.source.hom.app T (H.arrows.ι.app T b) :=
    Deformation.inverseArrow_target F T b
  have hinvs : K.source.hom.app T ((groupoidInverse K).app T (H.arrows.ι.app T b)) =
      K.target.hom.app T (H.arrows.ι.app T b) :=
    congrArg (fun k => k (H.arrows.ι.app T b))
      (NatTrans.congr_app (groupoidInverse_source K) T)
  have hinvt : K.target.hom.app T ((groupoidInverse K).app T (H.arrows.ι.app T b)) =
      K.source.hom.app T (H.arrows.ι.app T b) :=
    congrArg (fun k => k (H.arrows.ι.app T b))
      (NatTrans.congr_app (groupoidInverse_target K) T)
  have hsub : K.toGroupoidInFunctors.compose T
      (H.arrows.ι.app T (Deformation.inverseArrow F T b)) (H.arrows.ι.app T b) hcs =
      K.toGroupoidInFunctors.identity T (K.source.hom.app T (H.arrows.ι.app T b)) :=
    ((H.comp_restricts T ⟨(Deformation.inverseArrow F T b, b), hcs⟩).symm.trans
      (congrArg (H.arrows.ι.app T)
        (Deformation.compose_inverseArrow_self F T b hcs))).trans
      (hidfact (K.source.hom.app T (H.arrows.ι.app T b)))
  have hamb : K.toGroupoidInFunctors.compose T
      ((groupoidInverse K).app T (H.arrows.ι.app T b)) (H.arrows.ι.app T b) hinvs =
      K.toGroupoidInFunctors.identity T (K.source.hom.app T (H.arrows.ι.app T b)) :=
    (Deformation.GroupoidInFunctors.compose_eq_of_arrows_eq K.toGroupoidInFunctors T
      hinvs
      ((Deformation.inverseArrow_source K.toGroupoidInFunctors T
        (H.arrows.ι.app T b)))
      (groupoidInverse_app K T (H.arrows.ι.app T b)) rfl).trans
      (Deformation.compose_inverseArrow_self K.toGroupoidInFunctors T
        (H.arrows.ι.app T b) _)
  exact Deformation.GroupoidInFunctors.left_inverse_unique K.toGroupoidInFunctors T
    (K.source.hom.app T (H.arrows.ι.app T b)) (K.target.hom.app T (H.arrows.ι.app T b))
    (H.arrows.ι.app T b) (H.arrows.ι.app T (Deformation.inverseArrow F T b))
    ((groupoidInverse K).app T (H.arrows.ι.app T b)) rfl rfl hcs hct hinvs hinvt hsub hamb

/-- **An open finite subgroupoid is closed under inverses on points.**  The inverse of a point of
the arrow space lying in the subgroupoid again lies in it. -/
theorem exists_pointsMap_groupoidInverse_of_openFiniteSubgroupoid
    (K : GroupoidInAlgebraicSpaces C S hS B) (H : OpenFiniteSubgroupoid K)
    (z : Space.points C S hS H.arrows.toFunctor) :
    ∃ z' : Space.points C S hS H.arrows.toFunctor,
      Space.pointsMap C S hS H.arrows.toFunctor H.arrows.ι z' =
        Space.pointsMap C S hS K.arrows.obj (groupoidInverse K)
          (Space.pointsMap C S hS H.arrows.toFunctor H.arrows.ι z) := by
  induction z using Quot.ind with | _ q =>
  obtain ⟨c, hc⟩ := exists_eq_groupoidInverse_of_openFiniteSubgroupoid K H
    (Opposite.op q.siteObject) q.value
  refine ⟨Space.FieldValuedPoint.class C S hS H.arrows.toFunctor
    { carrier := q.carrier, field := q.field, contained := q.contained, toBase := q.toBase,
      value := c }, ?_⟩
  exact congrArg (fun v => Space.FieldValuedPoint.class C S hS K.arrows.obj
    { carrier := q.carrier, field := q.field, contained := q.contained, toBase := q.toBase,
      value := v }) hc

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)
  {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
  (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)

/-- The composite of a composable pair of generalized arrows of a realization is the composite,
in the groupoid scheme, of the two morphisms of schemes they come from. -/
theorem realization_compose_eq (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (G.realization C hS hU hR hP).arrows.obj.obj T)
    (h : (G.realization C hS hU hR hP).source.hom.app T a =
      (G.realization C hS hU hR hP).target.hom.app T b)
    (f g : (siteToOver C hS).obj T.unop ⟶ G.arrows) (w : f ≫ G.source = g ≫ G.target)
    (ha : yonedaSchemePointEquiv C hS hR T a = f)
    (hb : yonedaSchemePointEquiv C hS hR T b = g) :
    yonedaSchemePointEquiv C hS hR T
        ((G.realization C hS hU hR hP).toGroupoidInFunctors.compose T a b h) =
      G.compose f g w := by
  have w₀ : yonedaSchemePointEquiv C hS hR T a ≫ G.source =
      yonedaSchemePointEquiv C hS hR T b ≫ G.target :=
    (congrArg (fun k => k ≫ G.source) ha).trans
      (w.trans (congrArg (fun k => k ≫ G.target) hb.symm))
  exact (realizationComp_app G C hS hU hR hP T ⟨(a, b), h⟩ w₀).trans
    (AlgebraicGeometry.groupoidCompose_arrow_eq _ f _ g w₀ w ha hb)

variable (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
    (realizationMap G C hS hU hR hP hX p))
  (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid Rs.groupoid)

/-! ### The de-realized inverse of a restriction -/

/-- The inverse of the restriction of a groupoid scheme, read as a morphism to the arrow space of
a realization of the restriction of its realization. -/
def splittingInverseHom :
    yoneda.obj (schemeSiteObject C hS hRA) ⟶ Rs.groupoid.arrows.obj :=
  yoneda.map (schemeSiteMap C hS hRA hRA (restrictionInverse G p)) ≫
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom

/-- Precomposing `φ` with an endomorphism `i` swaps two endpoint maps, provided both factor through
a common map `k` and `i` swaps the factors. -/
private theorem comp_comp_eq_of_comp_eq_comp {𝒟 : Type*} [Category 𝒟] {Y A Z O : 𝒟}
    (i : Y ⟶ Y) (φ : Y ⟶ A) (s t : A ⟶ O) (σ τ : Y ⟶ Z) (k : Z ⟶ O)
    (hs : φ ≫ s = σ ≫ k) (ht : φ ≫ t = τ ≫ k) (hi : i ≫ σ = τ) :
    (i ≫ φ) ≫ s = φ ≫ t := by
  rw [Category.assoc, hs, ← Category.assoc, hi, ht]

/-- The source of the de-realized inverse is the target of the arrow. -/
theorem splittingInverseHom_comp_source :
    splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs ≫ Rs.groupoid.source.hom =
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        Rs.groupoid.target.hom := by
  refine comp_comp_eq_of_comp_eq_comp _ _ _ _ _ _ _
    (restrictionArrowsSpaceIso_hom_comp_source G C hS hU hR hP hX p hA hB hRA Rs)
    (restrictionArrowsSpaceIso_hom_comp_target G C hS hU hR hP hX p hA hB hRA Rs) ?_
  rw [← yoneda.map_comp, ← schemeSiteMap_comp, restrictionInverse_comp_source]

/-- The target of the de-realized inverse is the source of the arrow. -/
theorem splittingInverseHom_comp_target :
    splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs ≫ Rs.groupoid.target.hom =
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        Rs.groupoid.source.hom := by
  refine comp_comp_eq_of_comp_eq_comp _ _ _ _ _ _ _
    (restrictionArrowsSpaceIso_hom_comp_target G C hS hU hR hP hX p hA hB hRA Rs)
    (restrictionArrowsSpaceIso_hom_comp_source G C hS hU hR hP hX p hA hB hRA Rs) ?_
  rw [← yoneda.map_comp, ← schemeSiteMap_comp, restrictionInverse_comp_target]

/-- The ambient arrow underlying the de-realized inverse is the inverse in the groupoid scheme of
the underlying arrow. -/
theorem splittingInverseHom_comp_mapArrows :
    splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs ≫ Rs.hom.toGroupoidHom.mapArrows =
      yoneda.map (schemeSiteMap C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse)) := by
  have hcomp : yoneda.map (schemeSiteMap C hS hRA hRA (restrictionInverse G p)) ≫
      yoneda.map (schemeSiteMap C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p)) =
      yoneda.map (schemeSiteMap C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse)) := by
    rw [← yoneda.map_comp, ← schemeSiteMap_comp, restrictionInverse_comp_arrowsToArrows]
  change (yoneda.map (schemeSiteMap C hS hRA hRA (restrictionInverse G p)) ≫
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) ≫
      Rs.hom.toGroupoidHom.mapArrows = _
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun k =>
    yoneda.map (schemeSiteMap C hS hRA hRA (restrictionInverse G p)) ≫ k)
    (restrictionArrowsSpaceIso_hom_comp_mapArrows G C hS hU hR hP hX p hA hB hRA Rs)).trans hcomp

/-- The ambient point of the source of an arrow of the realized restriction is the Yoneda image
of the source of the restriction of the groupoid scheme, followed by the restricting morphism. -/
theorem restrictionArrowsSpaceIso_hom_comp_source_comp_mapObjects :
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        Rs.groupoid.source.hom ≫ Rs.hom.toGroupoidHom.mapObjects =
      yoneda.map (schemeSiteMap C hS hRA hU
        (AlgebraicGeometry.restrictionSource G p ≫ p)) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ Rs.hom.toGroupoidHom.mapObjects)
    (restrictionArrowsSpaceIso_hom_comp_source G C hS hU hR hP hX p hA hB hRA Rs)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k =>
    yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)) ≫ k)
    (restrictionObjectsObj_eq_symm_comp_mapObjects G C hS hU hR hP hX p Rs)).trans ?_
  exact (yoneda.map_comp _ _).symm.trans (congrArg (fun k => yoneda.map k)
    (schemeSiteMap_comp C hS hRA hX hU (AlgebraicGeometry.restrictionSource G p) p).symm)

/-- **The de-realized inverse of a restriction is the inversion of the realized restriction**, on
sections over a test object.

Both are arrows of the realized restriction with the endpoints of an inverse of the given arrow
whose underlying ambient arrows compose with that of the given one to the ambient identity arrow:
for the inversion because a morphism of groupoids commutes with the two inversions, and for the
de-realized inverse because the inverse of the restriction of the groupoid scheme composes with
its arrow to the identity at its source. -/
theorem splittingInverseHom_app_eq (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : (yoneda.obj (schemeSiteObject C hS hRA)).obj T) :
    (GroupoidInAlgebraicSpaces.groupoidInverse Rs.groupoid).app T
        ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z) =
      (splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs).app T z := by
  have hbs : Rs.groupoid.source.hom.app T
        ((GroupoidInAlgebraicSpaces.groupoidInverse Rs.groupoid).app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) =
      Rs.groupoid.target.hom.app T
        ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z) :=
    congrArg (fun k => k ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app
      T z)) (NatTrans.congr_app
        (GroupoidInAlgebraicSpaces.groupoidInverse_source Rs.groupoid) T)
  have hbt : Rs.groupoid.target.hom.app T
        ((GroupoidInAlgebraicSpaces.groupoidInverse Rs.groupoid).app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) =
      Rs.groupoid.source.hom.app T
        ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z) :=
    congrArg (fun k => k ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app
      T z)) (NatTrans.congr_app
        (GroupoidInAlgebraicSpaces.groupoidInverse_target Rs.groupoid) T)
  have hcs : Rs.groupoid.source.hom.app T
        ((splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs).app T z) =
      Rs.groupoid.target.hom.app T
        ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z) :=
    congrArg (fun k => k z) (NatTrans.congr_app
      (splittingInverseHom_comp_source G C hS hU hR hP hX p hA hB hRA Rs) T)
  have hct : Rs.groupoid.target.hom.app T
        ((splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs).app T z) =
      Rs.groupoid.source.hom.app T
        ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z) :=
    congrArg (fun k => k z) (NatTrans.congr_app
      (splittingInverseHom_comp_target G C hS hU hR hP hX p hA hB hRA Rs) T)
  have hmb : Rs.hom.toGroupoidHom.mapArrows.app T
        ((GroupoidInAlgebraicSpaces.groupoidInverse Rs.groupoid).app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) =
      Deformation.inverseArrow (G.realization C hS hU hR hP).toGroupoidInFunctors T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) :=
    (congrArg (fun k => k ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app
      T z)) (NatTrans.congr_app
        (GroupoidInAlgebraicSpaces.Hom.mapArrows_comp_groupoidInverse Rs.hom) T)).symm.trans
      (GroupoidInAlgebraicSpaces.groupoidInverse_app (G.realization C hS hU hR hP) T _)
  have wb : (G.realization C hS hU hR hP).source.hom.app T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((GroupoidInAlgebraicSpaces.groupoidInverse Rs.groupoid).app T
            ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z))) =
      (G.realization C hS hU hR hP).target.hom.app T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) :=
    (Rs.hom.toGroupoidHom.map_source T _).trans
      ((congrArg (Rs.hom.toGroupoidHom.mapObjects.app T) hbs).trans
        (Rs.hom.toGroupoidHom.map_target T _).symm)
  have wc : (G.realization C hS hU hR hP).source.hom.app T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs).app T z)) =
      (G.realization C hS hU hR hP).target.hom.app T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) :=
    (Rs.hom.toGroupoidHom.map_source T _).trans
      ((congrArg (Rs.hom.toGroupoidHom.mapObjects.app T) hcs).trans
        (Rs.hom.toGroupoidHom.map_target T _).symm)
  have hb : (G.realization C hS hU hR hP).toGroupoidInFunctors.compose T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((GroupoidInAlgebraicSpaces.groupoidInverse Rs.groupoid).app T
            ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)))
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) wb =
      (G.realization C hS hU hR hP).toGroupoidInFunctors.identity T
        (Rs.hom.toGroupoidHom.mapObjects.app T (Rs.groupoid.source.hom.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z))) :=
    (Deformation.GroupoidInFunctors.compose_eq_of_arrows_eq
      (G.realization C hS hU hR hP).toGroupoidInFunctors T wb
      (Deformation.inverseArrow_source (G.realization C hS hU hR hP).toGroupoidInFunctors T _)
      hmb rfl).trans
      ((Deformation.compose_inverseArrow_self
        (G.realization C hS hU hR hP).toGroupoidInFunctors T _ _).trans
        (congrArg ((G.realization C hS hU hR hP).toGroupoidInFunctors.identity T)
          (Rs.hom.toGroupoidHom.map_source T _)))
  have ptc : yonedaSchemePointEquiv C hS hR T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs).app T z)) =
      yonedaSchemePointEquiv C hS hRA T z ≫
        (AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse) :=
    (congrArg (yonedaSchemePointEquiv C hS hR T) (congrArg (fun k => k z)
      (NatTrans.congr_app
        (splittingInverseHom_comp_mapArrows G C hS hU hR hP hX p hA hB hRA Rs) T))).trans
      (yonedaSchemePointEquiv_map C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse) T z)
  have pta : yonedaSchemePointEquiv C hS hR T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) =
      yonedaSchemePointEquiv C hS hRA T z ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p :=
    (congrArg (yonedaSchemePointEquiv C hS hR T) (congrArg (fun k => k z)
      (NatTrans.congr_app (restrictionArrowsSpaceIso_hom_comp_mapArrows
        G C hS hU hR hP hX p hA hB hRA Rs) T))).trans
      (yonedaSchemePointEquiv_map C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p) T z)
  have ptobj : yonedaSchemePointEquiv C hS hU T
        (Rs.hom.toGroupoidHom.mapObjects.app T (Rs.groupoid.source.hom.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z))) =
      yonedaSchemePointEquiv C hS hRA T z ≫ (AlgebraicGeometry.restrictionSource G p ≫ p) :=
    (congrArg (yonedaSchemePointEquiv C hS hU T) (congrArg (fun k => k z)
      (NatTrans.congr_app (restrictionArrowsSpaceIso_hom_comp_source_comp_mapObjects
        G C hS hU hR hP hX p hA hB hRA Rs) T))).trans
      (yonedaSchemePointEquiv_map C hS hRA hU
        (AlgebraicGeometry.restrictionSource G p ≫ p) T z)
  have w₂ : ((yonedaSchemePointEquiv C hS hRA T z ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.inverse) ≫ G.source =
      (yonedaSchemePointEquiv C hS hRA T z ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.target :=
    (Category.assoc _ _ _).trans (congrArg (fun k => (yonedaSchemePointEquiv C hS hRA T z ≫
      AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ k) G.source_inverse)
  have w₁ : (yonedaSchemePointEquiv C hS hRA T z ≫
        (AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse)) ≫ G.source =
      (yonedaSchemePointEquiv C hS hRA T z ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.target :=
    (congrArg (fun k => k ≫ G.source) (Category.assoc (yonedaSchemePointEquiv C hS hRA T z)
      (AlgebraicGeometry.restrictionArrowsToArrows G p) G.inverse).symm).trans w₂
  have hab : (yonedaSchemePointEquiv C hS hRA T z ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.source =
      yonedaSchemePointEquiv C hS hRA T z ≫ (AlgebraicGeometry.restrictionSource G p ≫ p) :=
    (Category.assoc _ _ _).trans (congrArg (fun k => yonedaSchemePointEquiv C hS hRA T z ≫ k)
      (AlgebraicGeometry.GroupoidScheme.restriction_condition G p).symm)
  have hc : (G.realization C hS hU hR hP).toGroupoidInFunctors.compose T
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs).app T z))
        (Rs.hom.toGroupoidHom.mapArrows.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z)) wc =
      (G.realization C hS hU hR hP).toGroupoidInFunctors.identity T
        (Rs.hom.toGroupoidHom.mapObjects.app T (Rs.groupoid.source.hom.app T
          ((restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app T z))) := by
    refine Eq.symm (realization_identity_eq G C hS hU hR hP T _ _ ?_)
    refine (realization_compose_eq G C hS hU hR hP T _ _ wc _ _ w₁ ptc pta).trans ?_
    refine (AlgebraicGeometry.groupoidCompose_arrow_eq _ ((yonedaSchemePointEquiv C hS hRA T z ≫
      AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.inverse) _ _ w₁ w₂
      (Category.assoc (yonedaSchemePointEquiv C hS hRA T z)
        (AlgebraicGeometry.restrictionArrowsToArrows G p) G.inverse).symm rfl).trans ?_
    refine (G.left_inverse _ (yonedaSchemePointEquiv C hS hRA T z ≫
      AlgebraicGeometry.restrictionArrowsToArrows G p) w₂).trans ?_
    refine ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ G.identity) hab)).trans ?_
    exact (congrArg (fun k => k ≫ G.identity) ptobj).symm
  exact GroupoidInAlgebraicSpaces.restriction_left_inverse_unique
    (G.realization C hS hU hR hP) Rs T _ _ _ _ _ rfl rfl hbs hbt hcs hct wb wc hb hc

/-- **The de-realized inverse of a restriction is the inversion of the realized
restriction.** -/
theorem splittingInverseHom_eq :
    splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs =
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        GroupoidInAlgebraicSpaces.groupoidInverse Rs.groupoid := by
  ext T z
  exact (splittingInverseHom_app_eq G C hS hU hR hP hX p hA hB hRA Rs T z).symm

/-- **The open cut out by a splitting is closed under inverses.** -/
theorem mem_splittingOpens_restrictionInverse
    (r : (AlgebraicGeometry.restrictionArrows G p).left)
    (hr : r ∈ splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) :
    (restrictionInverse G p).left.base r ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P := by
  have hrx : pointsToScheme C S hS (schemeSiteObject C hS hRA)
      ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm r) = r :=
    pointsToScheme_pointsEquivScheme_symm C hS (schemeSiteObject C hS hRA) r
  obtain ⟨zz, hzz⟩ :=
    (mem_splittingOpens_iff_of_eq G C hS hU hR hP hX p hA hB hRA Rs P hrx).1 hr
  have hrz : pointsToScheme C S hS (schemeSiteObject C hS hRA)
      (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
        (yoneda.map (schemeSiteMap C hS hRA hRA (restrictionInverse G p)))
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm r)) =
      (restrictionInverse G p).left.base r := by
    rw [pointsToScheme_pointsMap_yoneda, toScheme_map_schemeSiteMap_eq]
    exact congrArg (fun t : (AlgebraicGeometry.restrictionArrows G p).left =>
      (restrictionInverse G p).left.base t) hrx
  refine (mem_splittingOpens_iff_of_eq G C hS hU hR hP hX p hA hB hRA Rs P hrz).2 ?_
  have hdef : splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs =
      yoneda.map (schemeSiteMap C hS hRA hRA (restrictionInverse G p)) ≫
        (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom := rfl
  have hcomp : pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
        (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom
        (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
          (yoneda.map (schemeSiteMap C hS hRA hRA (restrictionInverse G p)))
          ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm r)) =
      pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
        (splittingInverseHom G C hS hU hR hP hX p hA hB hRA Rs)
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm r) := by
    rw [hdef, pointsMap_comp]
    rfl
  obtain ⟨z', hz'⟩ :=
    GroupoidInAlgebraicSpaces.exists_pointsMap_groupoidInverse_of_openFiniteSubgroupoid
      Rs.groupoid P zz
  refine ⟨z', ?_⟩
  rw [hcomp, splittingInverseHom_eq, pointsMap_comp_apply, ← hzz]
  exact hz'

end Stacks.Groupoids.GroupoidScheme

end

end
