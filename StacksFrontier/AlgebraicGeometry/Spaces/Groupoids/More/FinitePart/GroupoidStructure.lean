module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidTranslate

/-!
# The groupoid structure on the finite part of a groupoid

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over `B` whose source morphism is
separated and locally of finite type, and let `(U', Z_univ, s', t', c', e', i')` be the finite part
of Stacks 04RT. This file proves that the septuple is a groupoid in algebraic spaces over `B` and
constructs the canonical morphism of groupoids

`(U', Z_univ, s', t', c', e', i') ⟶ (U, R, s, t, c, e, i)`,

whose map on objects is the étale projection `g : U' ⟶ U` and whose map on arrows is the rule
`(u, Z, z) ↦ z`. Together with the two structure spaces, which are Stacks 04RU clauses (1) and (2),
this is **Stacks 04RU**.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.pointwise`: the groupoid structure on
  the septuple of the finite part at a single test scheme, obtained by reflecting the groupoid
  structure of the given groupoid along the faithful pair `(g, (u, Z, z) ↦ z)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.finitePartGroupoid`: **Stacks 04RU**, the finite
  part as a groupoid in algebraic spaces over `B`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.finitePartGroupoidHom`: **Stacks 04RU**, the
  canonical morphism of groupoids in algebraic spaces from the finite part to the given groupoid.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.arrowSpace_ext`: the faithfulness of the
  canonical map on arrows — a point of `Z_univ` is determined by its source in `U'` and its arrow
  in `R`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.unitHom_comp_target`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.invHom_comp_target` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.compHom_comp_target`: the three groupoid
  laws of Stacks 04RT which mention the target morphism `t'`.

## Implementation notes

The laws for `s'`, `e'`, `i'` and `c'` that do not mention `t'` are already available from the
construction of those morphisms, in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidCompose.lean`: each of
them is read off the two components of a point of `Z_univ`. The three laws which do mention `t'`
are identities between the *collections* a point names, because `t'` changes the collection; they
are proved here by reading them at every scheme-valued point, where Stacks 04PE, part (2), turns
the named collection into a base change, and then applying the three translation laws of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidTranslate.lean`.

Reading a law at scheme-valued points is enough because the morphisms in question land in `U'`,
which is an open subspace of the finite part: a morphism into `U'` is determined by the morphism
into the finite part it induces, and that is determined by the collections it names. The
injectivity of the inclusion of `U'` is therefore a hypothesis of the laws below; for the finite
part that `AlgebraicGeometry.GroupoidInAlgebraicSpaces.finitePart` builds, the inclusion is the
inclusion of a subfunctor and the hypothesis is discharged.

The groupoid laws themselves are not checked by hand on the collections. The pair of maps
`(u, Z) ↦ u` on objects and `(u, Z, z) ↦ z` on arrows is faithful on arrows with a common source,
because a point of `Z_univ` is a point of the ambient fibre product `U' ×_{g, U, s} R` lying in
the open subspace and is therefore determined by its two components; so
`Deformation.PointwiseGroupoid.ofFaithful` transports the laws from the given groupoid. The three
laws above are exactly the four hypotheses of that reflection which are not immediate from the
construction of the structure morphisms.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RS](https://stacks.math.columbia.edu/tag/04RS)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for limits of presheaves on `BigFppfOver C S hS` is deep
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_GroupoidStructure :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_GroupoidStructure
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for limits of presheaves on `BigFppfOver C S hS` is deep
/-- Finite products of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasLimitsOfShapeDiscrete_presheaf_GroupoidStructure (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance


/-! ### The two projections of the presheaf of composable pairs -/

/-- The first component of a composable pair of arrows, read through the comparison with the
presheaf fibre product. -/
theorem composableToPullback_fst {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U)
    (V : (BigFppfOver C S hS)ᵒᵖ) (q : (Deformation.composableArrows U R s t).obj V) :
    (pullback.fst s t).app V ((composableToPullback s t).app V q) = q.1.1 := by
  have h : composableToPullback s t ≫ pullback.fst s t = _ := pullback.lift_fst _ _ _
  exact congrArg (fun k : Deformation.composableArrows U R s t ⟶ R => k.app V q) h

/-- The second component of a composable pair of arrows, read through the comparison with the
presheaf fibre product. -/
theorem composableToPullback_snd {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U)
    (V : (BigFppfOver C S hS)ᵒᵖ) (q : (Deformation.composableArrows U R s t).obj V) :
    (pullback.snd s t).app V ((composableToPullback s t).app V q) = q.1.2 := by
  have h : composableToPullback s t ≫ pullback.snd s t = _ := pullback.lift_snd _ _ _
  exact congrArg (fun k : Deformation.composableArrows U R s t ⟶ R => k.app V q) h

namespace FinitePart

variable (fp : FinitePart G)

/-! ### Faithfulness on arrows -/

/-- The inclusion of `Z_univ` into the ambient fibre product is the point whose components are the
source morphism of the finite part and the tautological arrow. -/
theorem lift_sourceHom_arrowHom :
    pullback.lift fp.sourceHom fp.arrowHom fp.sourceHom_comp_toBase = fp.pair.subspace.ι :=
  pullback.hom_ext ((pullback.lift_fst _ _ _).trans (sourceHom_eq fp))
    ((pullback.lift_snd _ _ _).trans (arrowHom_eq fp))

/-- **Faithfulness of the canonical morphism on arrows.** Two points of `Z_univ` over a test
scheme with the same image under the source morphism and the same arrow in `R` are equal.

A point of `Z_univ` is a point of the ambient fibre product `U' ×_{g, U, s} R` lying in the open
subspace, and a point of a fibre product is determined by its two components. -/
theorem arrowSpace_ext {V : (BigFppfOver C S hS)ᵒᵖ} {x y : fp.pair.subspace.toFunctor.obj V}
    (hs : fp.sourceHom.app V x = fp.sourceHom.app V y)
    (ha : fp.arrowHom.app V x = fp.arrowHom.app V y) : x = y := by
  have key {W : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : fp.pair.subspace.toFunctor ⟶ W) :
      f.app V x = f.app V y ↔ (yonedaEquiv.symm x : yoneda.obj V.unop ⟶ _) ≫ f =
        yonedaEquiv.symm y ≫ f := by
    rw [← yonedaEquiv.injective.eq_iff, yonedaEquiv_comp, yonedaEquiv_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine Subtype.ext ((key fp.pair.subspace.ι).2 ?_)
  rw [← lift_sourceHom_arrowHom fp]
  apply pullback.hom_ext
  · rwa [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← key]
  · rwa [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← key]

/-! ### The collections named at a scheme-valued point -/

/-- The collection named by a scheme-valued point of `U'` is the base change of `Z_univ` along
that point. -/
theorem baseChangePair_pair (V : BigFppfOver C S hS) (m : yoneda.obj V ⟶ fp.objects.obj) :
    (Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
        (fp.inclusion.app (op V) (yonedaEquiv m)) =
      Space.baseChangePair C S hS G.source fp.pair (Space.schemePointHom C S hS V m) := by
  have h := Space.sections_eq_baseChangePair C S hS G.source fp.objects fp.inclusion V m
  rwa [← fp.pair_eq] at h

/-- The collection named through the source morphism at a scheme-valued point of `Z_univ`. -/
theorem baseChangePair_sourcePair (V : BigFppfOver C S hS)
    (m : yoneda.obj V ⟶ fp.pair.subspace.toFunctor) :
    Space.baseChangePair C S hS G.source (sourcePair fp) (Space.schemePointHom C S hS V m) =
      Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (m ≫ fp.sourceHom)) :=
  (Space.sections_eq_baseChangePair C S hS G.source (arrowSpace fp)
      (fp.sourceHom ≫ fp.inclusion) V m).symm.trans
    (baseChangePair_pair fp V (m ≫ fp.sourceHom))

/-- Two morphisms into `U'` agree as soon as the morphisms into the finite part they induce
agree. -/
theorem hom_ext_objects (hinj : ∀ V, Function.Injective (fp.inclusion.app V))
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {α β : F ⟶ fp.objects.obj}
    (h : α ≫ fp.inclusion = β ≫ fp.inclusion) : α = β := by
  ext V x
  exact hinj V (congrArg (fun k : F ⟶ _ => k.app V x) h)

/-- The source of the arrow at a scheme-valued point of `Z_univ` is the base of the collection
named through the source morphism. -/
theorem schemePointHom_arrowHom_comp_source (V : BigFppfOver C S hS)
    (k : yoneda.obj V ⟶ fp.pair.subspace.toFunctor) :
    (Space.schemePointHom C S hS V (k ≫ fp.arrowHom)).hom ≫ G.source.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (k ≫ fp.sourceHom))).toBase.hom := by
  change (k ≫ fp.arrowHom) ≫ G.source.hom = (k ≫ fp.sourceHom) ≫ fp.pair.toBase.hom
  simp only [Category.assoc]
  rw [fp.sourceHom_comp_toBase]

/-- The target of the arrow at a scheme-valued point of `Z_univ`, read at the arrow itself. -/
private theorem schemePointHom_arrowHom_comp_target (V : BigFppfOver C S hS)
    (k : yoneda.obj V ⟶ fp.pair.subspace.toFunctor) :
    (Space.schemePointHom C S hS V (k ≫ fp.arrowHom)).hom ≫ G.target.hom =
      (Space.schemePointHom C S hS V ((k ≫ fp.arrowHom) ≫ G.target.hom)).hom := rfl

/-- The collection named at a scheme-valued point of `U'` depends only on the point. -/
private theorem baseChangePair_schemePointHom_congr (V : BigFppfOver C S hS)
    {m m' : yoneda.obj V ⟶ fp.objects.obj} (h : m = m') :
    Space.baseChangePair C S hS G.source fp.pair (Space.schemePointHom C S hS V m) =
      Space.baseChangePair C S hS G.source fp.pair (Space.schemePointHom C S hS V m') := by
  rw [h]

/-- The section named by the target section at a scheme-valued point of `Z_univ` is the base
change of the target pair. -/
private theorem sections_targetSection_app (V : BigFppfOver C S hS)
    (g : yoneda.obj V ⟶ (arrowSpace fp).obj) :
    (Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
        ((targetSection fp).app (op V) (yonedaEquiv g)) =
      Space.baseChangePair C S hS G.source (targetPair fp) (Space.schemePointHom C S hS V g) := by
  have h := Space.sections_eq_baseChangePair C S hS G.source (arrowSpace fp)
    (targetSection fp) V g
  rwa [targetSection_spec] at h

/-- Two morphisms into `U'` agree as soon as they name the same sections at every
scheme-valued point. -/
private theorem hom_ext_objects_of_sections (hinj : ∀ V, Function.Injective (fp.inclusion.app V))
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {α β : F ⟶ fp.objects.obj}
    (h : ∀ (V : BigFppfOver C S hS) (g : yoneda.obj V ⟶ F),
      (Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
          ((α ≫ fp.inclusion).app (op V) (yonedaEquiv g)) =
        (Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
          ((β ≫ fp.inclusion).app (op V) (yonedaEquiv g))) : α = β := by
  refine hom_ext_objects fp hinj (Space.natTrans_ext_of_sections C S hS G.source _ _ fun V x => ?_)
  obtain ⟨g, rfl⟩ := yonedaEquiv.surjective x
  exact h V g

/-- **Stacks 04RT, the target rule at a scheme-valued point.** The collection named through the
target morphism at a point of `Z_univ` is the translation, by the arrow at that point, of the
collection named through the source morphism. -/
theorem baseChangePair_targetPair_translate (V : BigFppfOver C S hS)
    (m : yoneda.obj V ⟶ fp.pair.subspace.toFunctor)
    (hzs : (Space.schemePointHom C S hS V (m ≫ fp.arrowHom)).hom ≫ G.source.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (m ≫ fp.sourceHom))).toBase.hom)
    (b : schemeSpace V ⟶ G.objects)
    (hzt : (Space.schemePointHom C S hS V (m ≫ fp.arrowHom)).hom ≫ G.target.hom = b.hom) :
    Space.baseChangePair C S hS G.source (targetPair fp) (Space.schemePointHom C S hS V m) =
      translatePairOf
        (Space.baseChangePair C S hS G.source fp.pair
          (Space.schemePointHom C S hS V (m ≫ fp.sourceHom)))
        (Space.schemePointHom C S hS V (m ≫ fp.arrowHom)) hzs b hzt := by
  have harr : Space.schemePointHom C S hS V m ≫ arrowMap fp =
      Space.schemePointHom C S hS V (m ≫ fp.arrowHom) := ObjectProperty.hom_ext _ rfl
  have hbase : Space.schemePointHom C S hS V m ≫ (arrowMap fp ≫ G.target) = b :=
    ObjectProperty.hom_ext _ ((Category.assoc m fp.arrowHom G.target.hom).symm.trans hzt)
  refine (baseChangePair_translatePairOf (sourcePair fp) (arrowMap fp) (arrowMap_comp_source fp)
      (arrowMap fp ≫ G.target) rfl (Space.schemePointHom C S hS V m) ?_ ?_).trans ?_
  · exact (Category.assoc m fp.arrowHom G.source.hom).trans
      (congrArg (fun k => m ≫ k) (arrowMap_comp_source fp))
  · exact Category.assoc m fp.arrowHom G.target.hom
  · exact translatePairOf_congr (baseChangePair_sourcePair fp V m) harr hbase _ _ hzs hzt

/-- **Stacks 04RT, the target of a unit at a scheme-valued point.** -/
theorem baseChangePair_targetPair_unit (V : BigFppfOver C S hS)
    (m : yoneda.obj V ⟶ fp.objects.obj) (kc : yoneda.obj V ⟶ fp.pair.subspace.toFunctor)
    (hkcs : kc ≫ fp.sourceHom = m)
    (hkca : kc ≫ fp.arrowHom = m ≫ fp.pair.toBase.hom ≫ (identityHom G).hom) :
    Space.baseChangePair C S hS G.source (targetPair fp) (Space.schemePointHom C S hS V kc) =
      Space.baseChangePair C S hS G.source fp.pair (Space.schemePointHom C S hS V m) := by
  have hQ : Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (kc ≫ fp.sourceHom)) =
      Space.baseChangePair C S hS G.source fp.pair (Space.schemePointHom C S hS V m) :=
    baseChangePair_schemePointHom_congr fp V hkcs
  have hzt : (Space.schemePointHom C S hS V (kc ≫ fp.arrowHom)).hom ≫ G.target.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V m)).toBase.hom := by
    change (kc ≫ fp.arrowHom) ≫ G.target.hom = m ≫ fp.pair.toBase.hom
    rw [hkca]
    simp only [Category.assoc, identityHom_comp_target, Category.comp_id]
  have hzs : (Space.schemePointHom C S hS V (kc ≫ fp.arrowHom)).hom ≫ G.source.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (kc ≫ fp.sourceHom))).toBase.hom := by
    rw [hQ]
    change (kc ≫ fp.arrowHom) ≫ G.source.hom = m ≫ fp.pair.toBase.hom
    rw [hkca]
    simp only [Category.assoc, identityHom_comp_source, Category.comp_id]
  have hid₁ : ((Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V m)).toBase ≫ identityHom G).hom ≫ G.source.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V m)).toBase.hom := by
    change (m ≫ fp.pair.toBase.hom) ≫ (identityHom G).hom ≫ G.source.hom = m ≫ fp.pair.toBase.hom
    rw [identityHom_comp_source, Category.comp_id]
  have hid₂ : ((Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V m)).toBase ≫ identityHom G).hom ≫ G.target.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V m)).toBase.hom := by
    change (m ≫ fp.pair.toBase.hom) ≫ (identityHom G).hom ≫ G.target.hom = m ≫ fp.pair.toBase.hom
    rw [identityHom_comp_target, Category.comp_id]
  have harrow : Space.schemePointHom C S hS V (kc ≫ fp.arrowHom) =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V m)).toBase ≫ identityHom G :=
    ObjectProperty.hom_ext _ (by
      change kc ≫ fp.arrowHom = (m ≫ fp.pair.toBase.hom) ≫ (identityHom G).hom
      rw [hkca, Category.assoc])
  refine (baseChangePair_targetPair_translate fp V kc hzs _ hzt).trans ?_
  refine (translatePairOf_congr hQ harrow rfl hzs hzt hid₁ hid₂).trans ?_
  exact translatePairOf_identityHom _ hid₁ hid₂

variable (t' : fp.pair.subspace.toFunctor ⟶ fp.objects.obj)
  (ht' : t' ≫ fp.inclusion = targetSection fp)

include ht'

/-- The collection named through the target morphism at a scheme-valued point of `Z_univ`. -/
theorem baseChangePair_targetPair (V : BigFppfOver C S hS)
    (m : yoneda.obj V ⟶ fp.pair.subspace.toFunctor) :
    Space.baseChangePair C S hS G.source (targetPair fp) (Space.schemePointHom C S hS V m) =
      Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (m ≫ t')) := by
  refine (sections_targetSection_app fp V m).symm.trans ?_
  refine (congrArg (fun e => (Space.finiteOpenSubspacePresheaf C S hS G.source).sections V e)
    (sections_targetSection fp t' ht' V m)).symm.trans ?_
  exact baseChangePair_pair fp V (m ≫ t')

/-- **Stacks 04RT, the target of an inverse at a scheme-valued point.** -/
theorem baseChangePair_targetPair_inverse (V : BigFppfOver C S hS)
    (k kc : yoneda.obj V ⟶ fp.pair.subspace.toFunctor)
    (hkcs : kc ≫ fp.sourceHom = k ≫ t')
    (hkca : kc ≫ fp.arrowHom = (k ≫ fp.arrowHom) ≫ (inverseHom G).hom) :
    Space.baseChangePair C S hS G.source (targetPair fp) (Space.schemePointHom C S hS V kc) =
      Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (k ≫ fp.sourceHom)) := by
  have hzs₀ := schemePointHom_arrowHom_comp_source fp V k
  have hzt₀ := schemePointHom_arrowHom_comp_target fp V k
  have hT := (baseChangePair_targetPair fp t' ht' V k).symm.trans
    (baseChangePair_targetPair_translate fp V k hzs₀ _ hzt₀)
  have hQc : Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (kc ≫ fp.sourceHom)) =
      Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (k ≫ t')) :=
    baseChangePair_schemePointHom_congr fp V hkcs
  have hzs := schemePointHom_arrowHom_comp_source fp V kc
  have hzt : (Space.schemePointHom C S hS V (kc ≫ fp.arrowHom)).hom ≫ G.target.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (k ≫ fp.sourceHom))).toBase.hom := by
    change (kc ≫ fp.arrowHom) ≫ G.target.hom = (k ≫ fp.sourceHom) ≫ fp.pair.toBase.hom
    rw [hkca, Category.assoc, inverseHom_comp_target]
    exact hzs₀
  have hinvs : ((Space.schemePointHom C S hS V (k ≫ fp.arrowHom)) ≫ inverseHom G).hom ≫
      G.source.hom =
      (Space.schemePointHom C S hS V ((k ≫ fp.arrowHom) ≫ G.target.hom)).hom := by
    change ((k ≫ fp.arrowHom) ≫ (inverseHom G).hom) ≫ G.source.hom =
      (k ≫ fp.arrowHom) ≫ G.target.hom
    rw [Category.assoc, inverseHom_comp_source]
  have hinvt : ((Space.schemePointHom C S hS V (k ≫ fp.arrowHom)) ≫ inverseHom G).hom ≫
      G.target.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (k ≫ fp.sourceHom))).toBase.hom := by
    change ((k ≫ fp.arrowHom) ≫ (inverseHom G).hom) ≫ G.target.hom =
      (k ≫ fp.sourceHom) ≫ fp.pair.toBase.hom
    rw [Category.assoc, inverseHom_comp_target]
    exact hzs₀
  have harrow : Space.schemePointHom C S hS V (kc ≫ fp.arrowHom) =
      (Space.schemePointHom C S hS V (k ≫ fp.arrowHom)) ≫ inverseHom G :=
    ObjectProperty.hom_ext _ hkca
  refine (baseChangePair_targetPair_translate fp V kc hzs _ hzt).trans ?_
  refine (translatePairOf_congr (hQc.trans hT) harrow rfl hzs hzt hinvs hinvt).trans ?_
  exact translatePairOf_inverseHom _ (Space.schemePointHom C S hS V (k ≫ fp.arrowHom))
    hzs₀ hzt₀ hinvs hinvt

/-- **Stacks 04RT, the cocycle identity at a scheme-valued point.** -/
theorem baseChangePair_targetPair_compose (V : BigFppfOver C S hS)
    (k₁ k₂ kc : yoneda.obj V ⟶ fp.pair.subspace.toFunctor)
    (hcond : k₁ ≫ fp.sourceHom = k₂ ≫ t')
    (hc : (k₁ ≫ fp.arrowHom) ≫ G.source.hom = (k₂ ≫ fp.arrowHom) ≫ G.target.hom)
    (hkcs : kc ≫ fp.sourceHom = k₂ ≫ fp.sourceHom)
    (hkca : kc ≫ fp.arrowHom =
      composeHom (k₁ ≫ fp.arrowHom) (k₂ ≫ fp.arrowHom) hc) :
    Space.baseChangePair C S hS G.source (targetPair fp) (Space.schemePointHom C S hS V kc) =
      Space.baseChangePair C S hS G.source (targetPair fp)
        (Space.schemePointHom C S hS V k₁) := by
  have hzs₂ := schemePointHom_arrowHom_comp_source fp V k₂
  have hzt₂ := schemePointHom_arrowHom_comp_target fp V k₂
  have hQ₁ : Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (k₁ ≫ fp.sourceHom)) =
      translatePairOf (Space.baseChangePair C S hS G.source fp.pair
          (Space.schemePointHom C S hS V (k₂ ≫ fp.sourceHom)))
        (Space.schemePointHom C S hS V (k₂ ≫ fp.arrowHom)) hzs₂ _ hzt₂ :=
    (baseChangePair_schemePointHom_congr fp V hcond).trans
      ((baseChangePair_targetPair fp t' ht' V k₂).symm.trans
        (baseChangePair_targetPair_translate fp V k₂ hzs₂ _ hzt₂))
  have hzt₁ := schemePointHom_arrowHom_comp_target fp V k₁
  have hzs₁' := schemePointHom_arrowHom_comp_source fp V k₁
  have hcs : (composeArrow (Space.schemePointHom C S hS V (k₁ ≫ fp.arrowHom))
        (Space.schemePointHom C S hS V (k₂ ≫ fp.arrowHom)) hc).hom ≫ G.source.hom =
      (Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (k₂ ≫ fp.sourceHom))).toBase.hom :=
    (composeHom_comp_source (k₁ ≫ fp.arrowHom) (k₂ ≫ fp.arrowHom) hc).trans hzs₂
  have hct : (composeArrow (Space.schemePointHom C S hS V (k₁ ≫ fp.arrowHom))
        (Space.schemePointHom C S hS V (k₂ ≫ fp.arrowHom)) hc).hom ≫ G.target.hom =
      (Space.schemePointHom C S hS V ((k₁ ≫ fp.arrowHom) ≫ G.target.hom)).hom :=
    (composeHom_comp_target (k₁ ≫ fp.arrowHom) (k₂ ≫ fp.arrowHom) hc).trans hzt₁
  have hQc : Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (kc ≫ fp.sourceHom)) =
      Space.baseChangePair C S hS G.source fp.pair
        (Space.schemePointHom C S hS V (k₂ ≫ fp.sourceHom)) :=
    baseChangePair_schemePointHom_congr fp V hkcs
  have hzs := schemePointHom_arrowHom_comp_source fp V kc
  have hzt : (Space.schemePointHom C S hS V (kc ≫ fp.arrowHom)).hom ≫ G.target.hom =
      (Space.schemePointHom C S hS V ((k₁ ≫ fp.arrowHom) ≫ G.target.hom)).hom :=
    (congrArg (fun m => m ≫ G.target.hom) hkca).trans
      (composeHom_comp_target (k₁ ≫ fp.arrowHom) (k₂ ≫ fp.arrowHom) hc)
  have harrow : Space.schemePointHom C S hS V (kc ≫ fp.arrowHom) =
      composeArrow (Space.schemePointHom C S hS V (k₁ ≫ fp.arrowHom))
        (Space.schemePointHom C S hS V (k₂ ≫ fp.arrowHom)) hc :=
    ObjectProperty.hom_ext _ hkca
  refine (baseChangePair_targetPair_translate fp V kc hzs _ hzt).trans ?_
  refine (translatePairOf_congr hQc harrow rfl hzs hzt hcs hct).trans ?_
  refine (translatePairOf_composeArrow _ (Space.schemePointHom C S hS V (k₁ ≫ fp.arrowHom))
    (Space.schemePointHom C S hS V (k₂ ≫ fp.arrowHom)) hzs₂ hzt₂ hc hzt₁ hc hcs hct).trans ?_
  refine (translatePairOf_congr hQ₁.symm rfl rfl hc hzt₁ hzs₁' hzt₁).trans ?_
  exact (baseChangePair_targetPair_translate fp V k₁ hzs₁' _ hzt₁).symm

/-! ### The three laws for the target morphism -/

variable (hinj : ∀ V, Function.Injective (fp.inclusion.app V))

include hinj

/-- **Stacks 04RT, the target of a unit.** The target morphism of the finite part sends the unit
at a point of `U'` back to that point. -/
theorem unitHom_comp_target : unitHom fp ≫ t' = 𝟙 fp.objects.obj := by
  refine hom_ext_objects_of_sections fp hinj fun V g => ?_
  rw [Category.assoc, ht', Category.id_comp]
  refine (sections_targetSection_app fp V (g ≫ unitHom fp)).trans
    ((baseChangePair_targetPair_unit fp V g (g ≫ unitHom fp) ?_ ?_).trans ?_)
  · rw [Category.assoc, unitHom_comp_sourceHom, Category.comp_id]
  · rw [Category.assoc, unitHom_comp_arrowHom]
  · exact (baseChangePair_pair fp V g).symm

/-- **Stacks 04RT, the target of an inverse.** The target morphism of the finite part sends the
inverse of a point of `Z_univ` to its source. -/
theorem invHom_comp_target : invHom fp t' ht' ≫ t' = fp.sourceHom := by
  refine hom_ext_objects_of_sections fp hinj fun V g => ?_
  rw [Category.assoc, ht']
  have h2 := Space.sections_eq_baseChangePair C S hS G.source (arrowSpace fp)
    (fp.sourceHom ≫ fp.inclusion) V g
  refine (sections_targetSection_app fp V (g ≫ invHom fp t' ht')).trans
    ((baseChangePair_targetPair_inverse fp t' ht' V g (g ≫ invHom fp t' ht')
    ?_ ?_).trans ?_)
  · rw [Category.assoc, invHom_comp_sourceHom]
  · rw [Category.assoc, invHom_comp_arrowHom, Category.assoc]
  · exact (h2.trans (baseChangePair_sourcePair fp V g)).symm

/-- **Stacks 04RT, the cocycle identity for the target.** The target of a composite of two points
of `Z_univ` is the target of the first. -/
theorem compHom_comp_target :
    compHom fp t' ht' ≫ t' = pullback.fst fp.sourceHom t' ≫ t' := by
  refine hom_ext_objects_of_sections fp hinj fun V g => ?_
  rw [Category.assoc, Category.assoc, ht']
  have hc : ((g ≫ pullback.fst fp.sourceHom t') ≫ fp.arrowHom) ≫ G.source.hom =
      ((g ≫ pullback.snd fp.sourceHom t') ≫ fp.arrowHom) ≫ G.target.hom := by
    simpa only [Category.assoc] using g ≫= composable_compose fp t' ht'
  have hcond : (g ≫ pullback.fst fp.sourceHom t') ≫ fp.sourceHom =
      (g ≫ pullback.snd fp.sourceHom t') ≫ t' := by
    simp only [Category.assoc]
    exact congrArg (fun k => g ≫ k) pullback.condition
  refine (sections_targetSection_app fp V (g ≫ compHom fp t' ht')).trans
    ((baseChangePair_targetPair_compose fp t' ht' V
    (g ≫ pullback.fst fp.sourceHom t') (g ≫ pullback.snd fp.sourceHom t')
    (g ≫ compHom fp t' ht') hcond hc ?_ ?_).trans
      (sections_targetSection_app fp V (g ≫ pullback.fst fp.sourceHom t')).symm)
  · simp only [Category.assoc, compHom_comp_sourceHom]
  · rw [Category.assoc, compHom_comp_arrowHom]
    exact composeHom_comp_left g (composable_compose fp t' ht')
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm hc

/-! ### The septuple of the finite part is a groupoid -/

omit ht' hinj

/-- The source morphism of the finite part, as a morphism of algebraic spaces. -/
noncomputable def sourceSpaceHom : arrowSpace fp ⟶ fp.objects :=
  ObjectProperty.homMk fp.sourceHom

/-- The target morphism of the finite part, as a morphism of algebraic spaces. -/
noncomputable def targetSpaceHom : arrowSpace fp ⟶ fp.objects := ObjectProperty.homMk t'

include ht'

/-- The composition of the finite part, as a morphism of algebraic spaces out of the fibre
product of the source and the target. -/
noncomputable def compSpaceHom :
    AlgebraicSpaces.fiberProduct C S hS (sourceSpaceHom fp) (targetSpaceHom fp t') ⟶
      arrowSpace fp :=
  ObjectProperty.homMk (compHom fp t' ht')

include hinj

/-- **Stacks 04RT, the groupoid structure at a test scheme.** The septuple of the finite part is
a groupoid at every test scheme, by reflection along the faithful pair of maps `(u, Z) ↦ u` on
objects and `(u, Z, z) ↦ z` on arrows. -/
noncomputable def pointwise (V : (BigFppfOver C S hS)ᵒᵖ) :
    Deformation.PointwiseGroupoid (fp.sourceHom.app V) (t'.app V)
      (fun q => (composableToPullback fp.sourceHom t' ≫ compHom fp t' ht').app V q) := by
  refine (G.toGroupoidInFunctors.pointwiseData V).ofFaithful
    (fp.pair.toBase.hom.app V) (fp.arrowHom.app V) ?_ ?_ ?_
    ((unitHom fp).app V) ?_ ?_ ?_ ?_ ?_ ?_
    ((invHom fp t' ht').app V) ?_ ?_ ?_
  · exact fun a => (congrArg
      (fun k : fp.pair.subspace.toFunctor ⟶ G.objects.obj => k.app V a)
      fp.sourceHom_comp_toBase).symm
  · exact fun a => (congrArg
      (fun k : fp.pair.subspace.toFunctor ⟶ G.objects.obj => k.app V a)
      (comp_toBase_of_targetSection fp t' ht')).symm
  · exact fun a b hs ha => arrowSpace_ext fp hs ha
  · exact fun x => congrArg (fun k : fp.objects.obj ⟶ fp.objects.obj => k.app V x)
      (unitHom_comp_sourceHom fp)
  · exact fun x => congrArg (fun k : fp.objects.obj ⟶ fp.objects.obj => k.app V x)
      (unitHom_comp_target fp t' ht' hinj)
  · exact fun x => congrArg (fun k : fp.objects.obj ⟶ G.arrows.obj => k.app V x)
      (unitHom_comp_arrowHom fp)
  · intro q
    refine (congrArg
      (fun k : pullback fp.sourceHom t' ⟶ fp.objects.obj =>
        k.app V ((composableToPullback fp.sourceHom t').app V q))
      (compHom_comp_sourceHom fp t' ht')).trans ?_
    exact congrArg (fp.sourceHom.app V) (composableToPullback_snd fp.sourceHom t' V q)
  · intro q
    refine (congrArg
      (fun k : pullback fp.sourceHom t' ⟶ fp.objects.obj =>
        k.app V ((composableToPullback fp.sourceHom t').app V q))
      (compHom_comp_target fp t' ht' hinj)).trans ?_
    exact congrArg (t'.app V) (composableToPullback_fst fp.sourceHom t' V q)
  · intro q
    refine (congrArg
      (fun k : pullback fp.sourceHom t' ⟶ G.arrows.obj =>
        k.app V ((composableToPullback fp.sourceHom t').app V q))
      (compHom_comp_arrowHom fp t' ht')).trans ?_
    exact Deformation.GroupoidInFunctors.compose_congr G.toGroupoidInFunctors V _ _
      (congrArg (fp.arrowHom.app V) (composableToPullback_fst fp.sourceHom t' V q))
      (congrArg (fp.arrowHom.app V) (composableToPullback_snd fp.sourceHom t' V q))
  · exact fun a => congrArg
      (fun k : fp.pair.subspace.toFunctor ⟶ fp.objects.obj => k.app V a)
      (invHom_comp_sourceHom fp t' ht')
  · exact fun a => congrArg
      (fun k : fp.pair.subspace.toFunctor ⟶ fp.objects.obj => k.app V a)
      (invHom_comp_target fp t' ht' hinj)
  · exact fun a => congrArg
      (fun k : fp.pair.subspace.toFunctor ⟶ G.arrows.obj => k.app V a)
      (invHom_comp_arrowHom fp t' ht')

/-- **Stacks 04RU, the groupoid structure.** The finite part of a groupoid in algebraic spaces
over `B` is itself a groupoid in algebraic spaces over `B`: its object space is `U'`, its arrow
space is `Z_univ`, its structure morphisms are `s'`, `t'`, `c'` of Stacks 04RT, and both spaces
lie over `B` through the given groupoid. -/
noncomputable def groupoid : GroupoidInAlgebraicSpaces C S hS B where
  objects := fp.objects
  arrows := arrowSpace fp
  objectsToBase := fp.pair.toBase ≫ G.objectsToBase
  arrowsToBase := arrowMap fp ≫ G.arrowsToBase
  source := sourceSpaceHom fp
  target := targetSpaceHom fp t'
  source_over := by
    have hG : G.source.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
      congrArg (fun k : G.arrows ⟶ B => k.hom) G.source_over
    refine ObjectProperty.hom_ext _ ?_
    change fp.sourceHom ≫ fp.pair.toBase.hom ≫ G.objectsToBase.hom =
      fp.arrowHom ≫ G.arrowsToBase.hom
    rw [← Category.assoc, fp.sourceHom_comp_toBase, Category.assoc, hG]
  target_over := by
    have hG : G.target.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
      congrArg (fun k : G.arrows ⟶ B => k.hom) G.target_over
    refine ObjectProperty.hom_ext _ ?_
    change t' ≫ fp.pair.toBase.hom ≫ G.objectsToBase.hom =
      fp.arrowHom ≫ G.arrowsToBase.hom
    rw [← Category.assoc, comp_toBase_of_targetSection fp t' ht', Category.assoc, hG]
  comp := compSpaceHom fp t' ht'
  comp_over := by
    have hG : G.target.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
      congrArg (fun k : G.arrows ⟶ B => k.hom) G.target_over
    have key : compHom fp t' ht' ≫ fp.arrowHom ≫ G.target.hom =
        pullback.fst fp.sourceHom t' ≫ fp.arrowHom ≫ G.target.hom := by
      rw [← Category.assoc, compHom_comp_arrowHom, composeHom_comp_target, Category.assoc]
    refine ObjectProperty.hom_ext _ ?_
    change compHom fp t' ht' ≫ fp.arrowHom ≫ G.arrowsToBase.hom =
      pullback.fst fp.sourceHom t' ≫ fp.arrowHom ≫ G.arrowsToBase.hom
    rw [← hG]
    simpa only [Category.assoc] using key =≫ G.objectsToBase.hom
  pointwiseGroupoid := fun V => ⟨pointwise fp t' ht' hinj V⟩

/-- **Stacks 04RU, the canonical morphism of groupoids.** The morphism of groupoids in algebraic
spaces from the finite part to the given groupoid: the projection `g : U' ⟶ U` on objects and the
rule `(u, Z, z) ↦ z` on arrows. -/
noncomputable def groupoidHom : Hom (groupoid fp t' ht' hinj) G where
  toGroupoidHom :=
    { mapObjects := fp.pair.toBase.hom
      mapArrows := fp.arrowHom
      map_source := fun V a => (congrArg
        (fun k : fp.pair.subspace.toFunctor ⟶ G.objects.obj => k.app V a)
        fp.sourceHom_comp_toBase).symm
      map_target := fun V a => (congrArg
        (fun k : fp.pair.subspace.toFunctor ⟶ G.objects.obj => k.app V a)
        (comp_toBase_of_targetSection fp t' ht')).symm
      map_id := fun V x => by
        have h1 : Deformation.GroupoidInFunctors.identity
            (groupoid fp t' ht' hinj).toGroupoidInFunctors V x = (unitHom fp).app V x := by
          rw [Deformation.GroupoidInFunctors.identity_eq_pointwiseData]
          exact Deformation.PointwiseGroupoid.identityArrow_eq _ (pointwise fp t' ht' hinj V) x
        rw [h1]
        exact congrArg (fun k : fp.objects.obj ⟶ G.arrows.obj => k.app V x)
          (unitHom_comp_arrowHom fp)
      map_comp := fun V a b h =>
        (Deformation.GroupoidInFunctors.compose_congr G.toGroupoidInFunctors V _ _
          (congrArg (fp.arrowHom.app V)
            (composableToPullback_fst fp.sourceHom t' V ⟨(a, b), h⟩)).symm
          (congrArg (fp.arrowHom.app V)
            (composableToPullback_snd fp.sourceHom t' V ⟨(a, b), h⟩)).symm).trans
          (congrArg
            (fun k : pullback fp.sourceHom t' ⟶ G.arrows.obj =>
              k.app V ((composableToPullback fp.sourceHom t').app V ⟨(a, b), h⟩))
            (compHom_comp_arrowHom fp t' ht')).symm }
  mapObjects_over := rfl
  mapArrows_over := rfl

end FinitePart

/-! ### The finite part of a separated morphism locally of finite type -/

/-- The inclusion of the object space of the constructed finite part into the finite part of the
source morphism is the inclusion of a subfunctor, hence injective at every test scheme. -/
theorem finitePart_inclusion_injective
    (hsep : Space.IsSeparated C S hS G.source.hom)
    (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (V : (BigFppfOver C S hS)ᵒᵖ) :
    Function.Injective ((finitePart G hsep hft).inclusion.app V) := fun _ _ h => Subtype.ext h

/-- **Stacks 04RU, the groupoid structure.** For a groupoid in algebraic spaces over `B` whose
source morphism is separated and locally of finite type, the finite part
`(U', Z_univ, s', t', c', e', i')` is a groupoid in algebraic spaces over `B`. -/
@[stacks 04RU "the groupoid structure on the finite part"]
noncomputable def finitePartGroupoid (hsep : Space.IsSeparated C S hS G.source.hom)
    (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    GroupoidInAlgebraicSpaces C S hS B :=
  FinitePart.groupoid (finitePart G hsep hft) (targetHom hsep hft)
    (targetHom_comp_inclusion hsep hft) (finitePart_inclusion_injective hsep hft)

/-- **Stacks 04RU, the canonical morphism of groupoids.** For a groupoid in algebraic spaces over
`B` whose source morphism is separated and locally of finite type, the canonical morphism of
groupoids in algebraic spaces over `B` from the finite part to the given groupoid: on objects it
is the étale projection `g : U' ⟶ U` of Stacks 04RU, clause (1), and on arrows it is the rule
`(u, Z, z) ↦ z`. -/
@[stacks 04RU "the canonical morphism of groupoids from the finite part to the given groupoid"]
noncomputable def finitePartGroupoidHom (hsep : Space.IsSeparated C S hS G.source.hom)
    (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    Hom (finitePartGroupoid hsep hft) G :=
  FinitePart.groupoidHom (finitePart G hsep hft) (targetHom hsep hft)
    (targetHom_comp_inclusion hsep hft) (finitePart_inclusion_injective hsep hft)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
