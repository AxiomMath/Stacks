module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionQuotientMap

/-!
# The presentation datum of the self-intersection groupoid

Let `𝒰` and `𝒳` be categories fibred in groupoids over the big fppf site of a scheme `S`, and let
`f : 𝒰 ⟶ 𝒳` be a 1-morphism such that `𝒰` and its self-intersection `relation B S hS 𝒰 𝒳 f` are
represented by algebraic spaces `U` and `R` through chosen equivalences `eU` and `eR`. For an
algebraic stack `𝒳`, this file assembles the groupoid in algebraic spaces with object space `U`
and arrow space `R`, the canonical morphism from its quotient stack to `𝒳`, and a vertical
comparison of that morphism with `f` compatible with descent, into one datum.

## Main definitions

* `AlgebraicGeometry.Stack.SelfIntersection.extendsFQuotient`: the comparison of the composite of
  `eU`, the projection to the quotient stack and the canonical morphism with `f`.
* `AlgebraicGeometry.Stack.SelfIntersection.SelfIntersectionPresentation`: the presentation datum.
* `AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation`: its construction.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.isHomLift_extendsFQuotient_app`: every component of
  the comparison with `f` is vertical.
* `AlgebraicGeometry.Stack.SelfIntersection.exists_descent_compatible_quotient`: the comparison
  carries the arrow of the pointwise groupoid fibration named by an arrow of the relation to the
  inverse of its defining isomorphism.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {f : 𝒰.val ⥤ᵇ 𝒳.val}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-! ### The comparison with `f` -/

/-- The object part of the comparison: an object of the source goes to the point of the object
space it names, read as an object of the presentation of the quotient stack. -/
noncomputable def objectInclusionToPrestack (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    𝒰.val.obj ⥤ (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).obj :=
  eU.hom.functor ⋙ Stack.pointwiseObjectInclusion (selfIntersectionGroupoid eU eR hsetU) ⋙
    (Stack.quotientPrestackEquivalence (selfIntersectionGroupoid eU eR hsetU)).functor

/-- The chosen equivalence `eU` of `𝒰` with the object space, followed by the projection to the
quotient stack and by the canonical morphism `canonicalMapToStack`, is isomorphic to `f`. -/
noncomputable def extendsFQuotient (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    eU.hom.functor ⋙
        (Stack.quotientStackProjection (selfIntersectionGroupoid eU eR hsetU)).toFunctor ⋙
        (canonicalMapToStack eU eR hsetU h𝒳).toFunctor ≅ f.toFunctor :=
  Functor.isoWhiskerLeft (objectInclusionToPrestack eU eR hsetU)
      (Functor.isoWhiskerRight (unitCanonicalMapUlift eU eR hsetU h𝒳)
        (BasedCategory.uliftDown 𝒳.val)) ≪≫
    extendsF eU eR hsetU

/-- The components of `extendsFQuotient` are the components of `unitCanonicalMapUlift`, read in
`𝒳`, followed by the components of `extendsF`. -/
theorem extendsFQuotient_hom_app (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) (z : 𝒰.val.obj) :
    (extendsFQuotient eU eR hsetU h𝒳).hom.app z =
      (BasedCategory.uliftDown 𝒳.val).map
          ((unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
            ((objectInclusionToPrestack eU eR hsetU).obj z)) ≫
        (extendsFApp eU z).hom := rfl

/-- The inverse components of `extendsFQuotient`. -/
theorem extendsFQuotient_inv_app (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) (z : 𝒰.val.obj) :
    (extendsFQuotient eU eR hsetU h𝒳).inv.app z =
      (extendsFApp eU z).inv ≫
        (BasedCategory.uliftDown 𝒳.val).map
          ((unitCanonicalMapUlift eU eR hsetU h𝒳).inv.app
            ((objectInclusionToPrestack eU eR hsetU).obj z)) := rfl

/-- Every component of `extendsFQuotient` is vertical over the big fppf site. -/
theorem isHomLift_extendsFQuotient_app (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) (z : 𝒰.val.obj) :
    𝒳.val.p.IsHomLift (𝟙 (𝒰.val.p.obj z)) ((extendsFQuotient eU eR hsetU h𝒳).hom.app z) := by
  have hdown : (BasedCategory.uliftDown 𝒳.val ⋙ 𝒳.val.p :
      (stackUlift 𝒳).obj ⥤ BigFppfOver B S hS) = (stackUlift 𝒳).p :=
    BasedCategory.uliftDown_comp 𝒳.val
  have h1 := isHomLift_unitCanonicalMapUlift_app eU eR hsetU h𝒳
    ((objectInclusionToPrestack eU eR hsetU).obj z)
  have h2 : 𝒳.val.p.IsHomLift
      (𝟙 ((Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.obj
        ((objectInclusionToPrestack eU eR hsetU).obj z)))
      ((BasedCategory.uliftDown 𝒳.val).map
        ((unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
          ((objectInclusionToPrestack eU eR hsetU).obj z))) :=
    Functor.isHomLift_map_of_comp_eq hdown _ _
  have h3 : 𝒳.val.p.IsHomLift (𝟙 (𝒰.val.p.obj z))
      ((BasedCategory.uliftDown 𝒳.val).map
        ((unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
          ((objectInclusionToPrestack eU eR hsetU).obj z))) := by
    rwa [← Functor.congr_obj eU.hom.w z]
  rw [extendsFQuotient_hom_app]
  exact Functor.isHomLift_comp_of_isHomLift_id 𝒳.val.p _ _ (𝟙 (𝒰.val.p.obj z)) h3
    (isHomLift_extendsFApp eU z)

/-! ### Descent compatibility -/

/-- For an arrow `γ` of the pointwise groupoid fibration, `uliftDown` applied to the image under
`toStackUliftOfPointwise` of the image of `γ` in the presentation is the image of `γ` under
`toStackOfPointwiseGroupoid`. -/
theorem uliftDown_toStackUliftOfPointwise_map (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (γ : X ⟶ Y) :
    (BasedCategory.uliftDown 𝒳.val).map
        ((toStackUliftOfPointwise eU eR hsetU).map
          ((Stack.quotientPrestackEquivalence (selfIntersectionGroupoid eU eR hsetU)).functor.map
            γ)) =
      (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor.map γ := rfl

/-- The image under `canonicalMapToStack` of an arrow `γ` of the pointwise groupoid fibration,
conjugated by the components of `unitCanonicalMapUlift` read in `𝒳`, is the image of `γ` under
`toStackOfPointwiseGroupoid`. -/
theorem canonicalMapToStack_conj_unit (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (γ : X ⟶ Y) :
    (BasedCategory.uliftDown 𝒳.val).map
          ((unitCanonicalMapUlift eU eR hsetU h𝒳).inv.app
            ((Stack.quotientPrestackEquivalence
              (selfIntersectionGroupoid eU eR hsetU)).functor.obj X)) ≫
        (canonicalMapToStack eU eR hsetU h𝒳).toFunctor.map
          ((Stack.pointwiseToQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map γ) ≫
        (BasedCategory.uliftDown 𝒳.val).map
          ((unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
            ((Stack.quotientPrestackEquivalence
              (selfIntersectionGroupoid eU eR hsetU)).functor.obj Y)) =
      (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor.map γ := by
  have hnat : (canonicalMapUlift eU eR hsetU h𝒳).map
          ((Stack.toQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map
            ((Stack.quotientPrestackEquivalence
              (selfIntersectionGroupoid eU eR hsetU)).functor.map γ)) ≫
        (unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
          ((Stack.quotientPrestackEquivalence
            (selfIntersectionGroupoid eU eR hsetU)).functor.obj Y) =
      (unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
          ((Stack.quotientPrestackEquivalence
            (selfIntersectionGroupoid eU eR hsetU)).functor.obj X) ≫
        (toStackUliftOfPointwise eU eR hsetU).map
          ((Stack.quotientPrestackEquivalence
            (selfIntersectionGroupoid eU eR hsetU)).functor.map γ) :=
    (unitCanonicalMapUlift eU eR hsetU h𝒳).hom.naturality _
  have hinner :
      (unitCanonicalMapUlift eU eR hsetU h𝒳).inv.app
            ((Stack.quotientPrestackEquivalence
              (selfIntersectionGroupoid eU eR hsetU)).functor.obj X) ≫
          (canonicalMapUlift eU eR hsetU h𝒳).map
            ((Stack.toQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map
              ((Stack.quotientPrestackEquivalence
                (selfIntersectionGroupoid eU eR hsetU)).functor.map γ)) ≫
          (unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
            ((Stack.quotientPrestackEquivalence
              (selfIntersectionGroupoid eU eR hsetU)).functor.obj Y) =
        (toStackUliftOfPointwise eU eR hsetU).map
          ((Stack.quotientPrestackEquivalence
            (selfIntersectionGroupoid eU eR hsetU)).functor.map γ) := by
    rw [hnat, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hstep : (BasedCategory.uliftDown 𝒳.val).map
          ((unitCanonicalMapUlift eU eR hsetU h𝒳).inv.app
            ((Stack.quotientPrestackEquivalence
              (selfIntersectionGroupoid eU eR hsetU)).functor.obj X)) ≫
        (canonicalMapToStack eU eR hsetU h𝒳).toFunctor.map
          ((Stack.pointwiseToQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map γ) ≫
        (BasedCategory.uliftDown 𝒳.val).map
          ((unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
            ((Stack.quotientPrestackEquivalence
              (selfIntersectionGroupoid eU eR hsetU)).functor.obj Y)) =
      (BasedCategory.uliftDown 𝒳.val).map
        ((unitCanonicalMapUlift eU eR hsetU h𝒳).inv.app
              ((Stack.quotientPrestackEquivalence
                (selfIntersectionGroupoid eU eR hsetU)).functor.obj X) ≫
            (canonicalMapUlift eU eR hsetU h𝒳).map
                ((Stack.toQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map
                  ((Stack.quotientPrestackEquivalence
                    (selfIntersectionGroupoid eU eR hsetU)).functor.map γ)) ≫
              (unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app
                ((Stack.quotientPrestackEquivalence
                  (selfIntersectionGroupoid eU eR hsetU)).functor.obj Y)) := by
    rw [Functor.map_comp, Functor.map_comp]
    rfl
  exact hstep.trans
    ((congrArg (fun k => (BasedCategory.uliftDown 𝒳.val).map k) hinner).trans
      (uliftDown_toStackUliftOfPointwise_map eU eR hsetU γ))

/-- If `b ≫ c ≫ d = g`, then `(a ≫ b) ≫ c ≫ d ≫ e = a ≫ g ≫ e`. -/
theorem comp_assoc_conj {C : Type (u + 1)} [Category.{u} C] {P Q T V W Y : C}
    (a : P ⟶ Q) (b : Q ⟶ T) (c : T ⟶ V) (d : V ⟶ W) (e : W ⟶ Y) (g : Q ⟶ W)
    (h : b ≫ c ≫ d = g) : (a ≫ b) ≫ c ≫ d ≫ e = a ≫ g ≫ e := by
  rw [← h]
  simp

/-- The image under `canonicalMapToStack` of an arrow `γ` of the pointwise groupoid fibration,
read through `sourcePresentation_pointwise_groupoid` and conjugated by the components of
`extendsFQuotient`, is the image of `γ` under `toStackOfPointwiseGroupoid` conjugated by the
components of `extendsFApp`. -/
theorem extendsFQuotient_map_pointwise (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) {z z' : 𝒰.val.obj}
    (γ : (⟨(eU.hom.functor.obj z).base, Discrete.as (eU.hom.functor.obj z).fiber⟩ :
        (pointwiseFibration eU eR hsetU).obj) ⟶
      ⟨(eU.hom.functor.obj z').base, Discrete.as (eU.hom.functor.obj z').fiber⟩) :
    (extendsFQuotient eU eR hsetU h𝒳).inv.app z ≫
        (canonicalMapToStack eU eR hsetU h𝒳).toFunctor.map
          (eqToHom (sourcePresentation_pointwise_groupoid eU eR hsetU z).symm ≫
            (Stack.pointwiseToQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map γ ≫
            eqToHom (sourcePresentation_pointwise_groupoid eU eR hsetU z')) ≫
        (extendsFQuotient eU eR hsetU h𝒳).hom.app z' =
      (extendsFApp eU z).inv ≫
        (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor.map γ ≫ (extendsFApp eU z').hom := by
  have hmid : (eqToHom (sourcePresentation_pointwise_groupoid eU eR hsetU z).symm ≫
        (Stack.pointwiseToQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map γ ≫
        eqToHom (sourcePresentation_pointwise_groupoid eU eR hsetU z') :
      (Stack.quotientStackProjection (selfIntersectionGroupoid eU eR hsetU)).obj
          (eU.hom.functor.obj z) ⟶
        (Stack.quotientStackProjection (selfIntersectionGroupoid eU eR hsetU)).obj
          (eU.hom.functor.obj z')) =
      (Stack.pointwiseToQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map γ :=
    (Category.id_comp _).trans (Category.comp_id _)
  rw [hmid, extendsFQuotient_inv_app, extendsFQuotient_hom_app]
  exact comp_assoc_conj _ _ _ _ _ _ (canonicalMapToStack_conj_unit eU eR hsetU h𝒳 γ)

/-- For an arrow `r` of the relation, together with identifications of the base objects of its
source and its target with two equal objects of the site, there is an arrow of the pointwise
groupoid fibration, between the points the source and the target name, whose section of the arrow
space is the one `r` names, and which `toStackOfPointwiseGroupoid`, conjugated by the comparison
isomorphisms `representingComparisonIso`, carries to the inverse of the defining isomorphism of
`r`. -/
theorem exists_descentArrow_of_base_eq (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (r : (relation B S hS 𝒰 𝒳 f).val.obj) {Wy Wx : BigFppfOver B S hS}
    (hy : 𝒰.val.p.obj r.y = Wy) (hx : 𝒰.val.p.obj r.x = Wx) (hW : Wy = Wx) :
    ∃ γ : (⟨Wy, PresheafOfCategories.sectionOfObj eU r.y hy⟩ :
          (pointwiseFibration eU eR hsetU).obj) ⟶
        ⟨Wx, PresheafOfCategories.sectionOfObj eU r.x hx⟩,
      ∃ a b : (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.Evaluation (op Wx),
      ∃ g : a ⟶ b,
        HEq γ.fiber g ∧
        HEq ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
            (op Wx) a b g).1 (Discrete.as (eR.hom.functor.obj r).fiber) ∧
        (representingComparisonIso eU r.y hy).inv ≫
            (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor.map γ ≫
            (representingComparisonIso eU r.x hx).hom = r.iso.inv := by
  subst hW
  have hr : (relation B S hS 𝒰 𝒳 f).val.p.obj r = Wy := r.hy.symm.trans hy
  subst hr
  exact ⟨descentArrow eU eR hsetU r rfl, _, _, _, HEq.rfl,
    (heq_of_eq (pointwiseSection_descentArrow eU eR hsetU r rfl)).trans
      (heq_sectionOfObj eR r rfl),
    descent_compatible eU eR hsetU r⟩

/-- For an arrow `r` of the relation there is an arrow of the pointwise groupoid fibration, between
the points named by the images of the source and the target of `r` under `eU`, whose section of
the arrow space is the one `r` names, and which `canonicalMapToStack`, conjugated by the
components of `extendsFQuotient`, carries to the inverse of the defining isomorphism of `r`. -/
theorem exists_descent_compatible_quotient (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) (r : (relation B S hS 𝒰 𝒳 f).val.obj) :
    ∃ γ : (⟨(eU.hom.functor.obj r.y).base, Discrete.as (eU.hom.functor.obj r.y).fiber⟩ :
          (pointwiseFibration eU eR hsetU).obj) ⟶
        ⟨(eU.hom.functor.obj r.x).base, Discrete.as (eU.hom.functor.obj r.x).fiber⟩,
      ∃ a b : (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.Evaluation
          (op (eU.hom.functor.obj r.x).base),
      ∃ g : a ⟶ b,
        HEq γ.fiber g ∧
        HEq ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
            (op (eU.hom.functor.obj r.x).base) a b g).1
          (Discrete.as (eR.hom.functor.obj r).fiber) ∧
        (extendsFQuotient eU eR hsetU h𝒳).inv.app r.y ≫
            (canonicalMapToStack eU eR hsetU h𝒳).toFunctor.map
              (eqToHom (sourcePresentation_pointwise_groupoid eU eR hsetU r.y).symm ≫
                (Stack.pointwiseToQuotientStack (selfIntersectionGroupoid eU eR hsetU)).map γ ≫
                eqToHom (sourcePresentation_pointwise_groupoid eU eR hsetU r.x)) ≫
            (extendsFQuotient eU eR hsetU h𝒳).hom.app r.x = r.iso.inv := by
  obtain ⟨γ, a, b, g, hfiber, hsection, hdescent⟩ :=
    exists_descentArrow_of_base_eq eU eR hsetU r (Functor.congr_obj eU.hom.w r.y).symm
      (Functor.congr_obj eU.hom.w r.x).symm
      (((Functor.congr_obj eU.hom.w r.y).trans (relation_obj_y rfl)).trans
        ((Functor.congr_obj eU.hom.w r.x).trans (relation_obj_x rfl)).symm)
  exact ⟨γ, a, b, g, hfiber, hsection,
    (extendsFQuotient_map_pointwise eU eR hsetU h𝒳 γ).trans hdescent⟩

/-! ### The presentation datum -/

/-- A presentation datum for `f`: a groupoid in algebraic spaces whose object space is the chosen
representing space of `𝒰` and whose arrow space is the chosen representing space of the
self-intersection, together with a morphism from its quotient stack to `𝒳` and a vertical
comparison of that morphism with `f` compatible with descent. -/
@[stacks 04T4 "parts (4) and (5), the presentation datum: the groupoid and the canonical \
morphism from its quotient stack, as a structure"]
structure SelfIntersectionPresentation where
  /-- The base algebraic space the groupoid lives over. -/
  base : AlgebraicSpaces B S hS
  /-- The base is the final algebraic space. -/
  baseIso : base.obj ≅ yoneda.obj (Over.mk (𝟙 (B.obj hS)))
  /-- The groupoid in algebraic spaces itself. -/
  groupoid : GroupoidInAlgebraicSpaces B S hS base
  /-- Its object space is the chosen representing space of `𝒰`. -/
  objects_eq : groupoid.objects = U
  /-- Its arrow space is the chosen representing space of the self-intersection. -/
  arrows_eq : groupoid.arrows = R
  /-- Its target is the morphism of representing spaces the first projection induces. -/
  target_eq :
    (eqToHom arrows_eq : groupoid.arrows ⟶ R) ≫
      ObjectProperty.homMk (relationTargetMap eU eR) =
        groupoid.target ≫ eqToHom objects_eq
  /-- Its source is the morphism of representing spaces the second projection induces. -/
  source_eq :
    (eqToHom arrows_eq : groupoid.arrows ⟶ R) ≫
      ObjectProperty.homMk (relationSourceMap eU eR) =
        groupoid.source ≫ eqToHom objects_eq
  /-- Composition is the outer projection on the two-fibre product, after passing to the
  representing spaces. The two entries are ordered as in `comp`. -/
  comp_compatible :
    ∀ x : composable B S hS 𝒰 𝒳 f,
      ∃ p : (AlgebraicSpaces.fiberProduct B S hS groupoid.source groupoid.target).obj.obj
          (op x.base),
        HEq ((pullback.fst groupoid.source.hom groupoid.target.hom).app (op x.base) p)
          (Discrete.as (eR.hom.functor.obj x.x).fiber) ∧
        HEq ((pullback.snd groupoid.source.hom groupoid.target.hom).app (op x.base) p)
          (Discrete.as (eR.hom.functor.obj x.y).fiber) ∧
        HEq (groupoid.comp.hom.app (op x.base) p)
          (Discrete.as (eR.hom.functor.obj
            ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x)).fiber)
  /-- The chosen equivalence of `𝒰` with the fibred category of the object space. -/
  sourcePresentation : StacksRepresentableCFG.EquivalenceOver 𝒰.val.p
    (Stack.fibredCategory B S hS groupoid.objects.obj).val.p
  /-- The fibres of the chosen equivalence agree with those of `eU`. -/
  sourcePresentation_compatible :
    ∀ x : 𝒰.val.obj,
      HEq (sourcePresentation.hom.functor.obj x).fiber (eU.hom.functor.obj x).fiber
  /-- On objects the chosen presentation agrees with the pointwise quotient projection, using the
  chosen identification `eU`. -/
  sourcePresentation_pointwise :
    ∀ x : 𝒰.val.obj,
      (Stack.pointwiseToQuotientStack groupoid).obj
          ⟨(sourcePresentation.hom.functor.obj x).base,
            Discrete.as (sourcePresentation.hom.functor.obj x).fiber⟩ =
        (Stack.quotientStackProjection groupoid).obj (sourcePresentation.hom.functor.obj x)
  /-- The canonical morphism from the quotient stack to `𝒳`. -/
  canonicalMap : (Stack.quotientStack groupoid) ⥤ᵇ 𝒳.val
  /-- The comparison with `f` is vertical over the fppf site. -/
  extends_f : { α :
      ((sourcePresentation.hom.functor ⋙
        (Stack.quotientStackProjection groupoid).toFunctor ⋙
        canonicalMap.toFunctor) ≅ f.toFunctor) //
      ∀ x : 𝒰.val.obj,
        𝒳.val.p.IsHomLift (𝟙 (𝒰.val.p.obj x)) (α.hom.app x) }
  /-- The arrow of the pointwise quotient represented by a relation object is sent, after the
  vertical comparison with `f`, to the inverse of its defining isomorphism. -/
  descent_compatible :
    ∀ r : (relation B S hS 𝒰 𝒳 f).val.obj,
      ∃ γ :
          (⟨(sourcePresentation.hom.functor.obj r.y).base,
              Discrete.as (sourcePresentation.hom.functor.obj r.y).fiber⟩ :
            (presheafOfGroupoids
              (Stack.evaluationGroupoidFunctor groupoid.toGroupoidInFunctors)).obj) ⟶
          (⟨(sourcePresentation.hom.functor.obj r.x).base,
              Discrete.as (sourcePresentation.hom.functor.obj r.x).fiber⟩ :
            (presheafOfGroupoids
              (Stack.evaluationGroupoidFunctor groupoid.toGroupoidInFunctors)).obj),
        ∃ a b : groupoid.toGroupoidInFunctors.Evaluation
            (op (sourcePresentation.hom.functor.obj r.x).base),
          ∃ g : a ⟶ b,
          HEq γ.fiber g ∧
          HEq (groupoid.toGroupoidInFunctors.evaluationArrowEquiv
              (op (sourcePresentation.hom.functor.obj r.x).base) a b g).1
            (Discrete.as (eR.hom.functor.obj r).fiber) ∧
          extends_f.1.inv.app r.y ≫
              canonicalMap.toFunctor.map
                (eqToHom (sourcePresentation_pointwise r.y).symm ≫
                  (Stack.pointwiseToQuotientStack groupoid).map γ ≫
                  eqToHom (sourcePresentation_pointwise r.x)) ≫
              extends_f.1.hom.app r.x = r.iso.inv

/-- The presentation datum of an algebraic stack `𝒳`: the groupoid
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionGroupoid` over the final algebraic space,
the canonical morphism `AlgebraicGeometry.Stack.SelfIntersection.canonicalMapToStack`, the
comparison `extendsFQuotient` with `f`, and `eU` as the chosen equivalence of the object
fibration. -/
@[stacks 04T4 "parts (4) and (5), the construction: that datum built from the \
declarations of this file and its three predecessors"]
noncomputable def selfIntersectionPresentation (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    SelfIntersectionPresentation eU eR where
  base := Space.terminalSpace B S hS
  baseIso := Iso.refl _
  groupoid := selfIntersectionGroupoid eU eR (isFiberedInSetoids_source eU)
  objects_eq := rfl
  arrows_eq := rfl
  target_eq := (Category.id_comp _).trans (Category.comp_id _).symm
  source_eq := (Category.id_comp _).trans (Category.comp_id _).symm
  comp_compatible := exists_comp_compatible_groupoid eU eR (isFiberedInSetoids_source eU)
  sourcePresentation := eU
  sourcePresentation_compatible := fun _ => HEq.rfl
  sourcePresentation_pointwise :=
    sourcePresentation_pointwise_groupoid eU eR (isFiberedInSetoids_source eU)
  canonicalMap := canonicalMapToStack eU eR (isFiberedInSetoids_source eU) h𝒳
  extends_f :=
    ⟨extendsFQuotient eU eR (isFiberedInSetoids_source eU) h𝒳,
      isHomLift_extendsFQuotient_app eU eR (isFiberedInSetoids_source eU) h𝒳⟩
  descent_compatible :=
    exists_descent_compatible_quotient eU eR (isFiberedInSetoids_source eU) h𝒳

end AlgebraicGeometry.Stack.SelfIntersection

end
