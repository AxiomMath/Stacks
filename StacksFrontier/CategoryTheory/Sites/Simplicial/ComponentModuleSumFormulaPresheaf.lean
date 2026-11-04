module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIso
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackSumFormula
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentModulePullbackSumFormula

/-!
# The componentwise direct sum for module lower shriek, as presheaves of modules

Let `C` be a cocontinuous simplicial site (case (B) of the simplicial-site situation of
Stacks 09WE) and let `R` be a presheaf of commutative rings on its total category. The restriction
to simplicial degree `m` of the presheaf-level module lower shriek from degree `n` is the direct
sum, over the simplex maps `φ : [n] ⟶ [m]`, of the presheaf-level module pullbacks along the
transitions `f_φ`. This is Stacks 0D72 in case (B) before sheafification, stated here as an
isomorphism of presheaves of modules and as an isomorphism of functors.

The summand labelled `φ` is included by the colimit injection at the index `(u φ (V), (φ, 𝟙))` of
the comma category computing the sections over `V`.

## Main definitions

* `Stacks.Sites.ComponentModuleSumFormula.componentRestrictedPullback`: the restriction to
  degree `m` of the presheaf-level module lower shriek from degree `n`.
* `Stacks.Sites.ComponentModuleSumFormula.sumFormulaLeg` and `…sumFormulaLegNatTrans`: the
  inclusion of the summand labelled by a simplex map, as a morphism of presheaves of modules
  resp. of functors.
* `Stacks.Sites.ComponentModuleSumFormula.isColimitCofanOfEvaluationPresheafOfModules`: a cofan
  of presheaves of modules is a colimit as soon as it is one over every object.
* `Stacks.Sites.ComponentModuleSumFormula.isColimitCofanSumFormulaLegs` and
  `…componentRestrictedPullbackIsoCoproduct`: the direct-sum decomposition as presheaves of
  modules.
* `Stacks.Sites.ComponentModuleSumFormula.colimitPullbackRestrictionIsoCoproduct`: the
  direct-sum formula of Stacks 0D72 in case (B) before sheafification, as an isomorphism of
  functors.
* `Stacks.Sites.ComponentModuleSumFormula.pullbackRestrictionIsoCompCoproduct`: the same for
  Mathlib's `CategoryTheory.PresheafOfModules.pullback`.

## Main results

* `Stacks.PullbackColimit.germ_restrict`: the restriction maps of the colimit presheaf on germs,
  read through an arbitrary index of the target fibre.
* `Stacks.PullbackColimit.germ_eq_map_unit`: a germ is the restriction of a germ at the identity
  index.

## Implementation notes

The two `Ring` structures on a ring of sections, one through `CommRingCat` and one through
`RingCat`, make a goal mentioning both spellings type-incorrect at `implicit` transparency, which
blocks `rw`. The germ lemmas are therefore stated over free variables and applied as terms.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace Stacks.PullbackColimit

/-- The restriction maps of the colimit presheaf, on germs, read through an arbitrary index of
the target fibre: if a morphism `ψ` of the source sites makes the square of the two indices and
the restriction `g` commute, then restricting the germ at `T` along `g` is the germ at `T'` of
the restriction of the section along `ψ`. -/
lemma germ_restrict {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)
    (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (A : PresheafOfModules.{u} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U U' : Dᵒᵖ} (g : U ⟶ U') {T : CostructuredArrow F.op U} {T' : CostructuredArrow F.op U'}
    (ψ : T.left ⟶ T'.left) (hψ : F.op.map ψ ≫ T'.hom = T.hom ≫ g) (r : ↑(R.obj U))
    (a : A.obj T.left) :
    (obj F R A).map g (germ F R A T r a)
      = germ F R A T' ((R.map g).hom r) (A.restrictₛₗ ψ a) := by
  rw [obj_map_germ]
  exact germ_map F R A
    (CostructuredArrow.homMk (f := CostructuredArrow.mk (T.hom ≫ g)) (f' := T') ψ hψ) _ a

/-- A germ is the restriction of a germ at the identity index: the germ of `1 ⊗ a` at the index
`(V, h)` is the restriction along `h` of the germ of `1 ⊗ a` at `(V, 𝟙)`. -/
lemma germ_eq_map_unit {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)
    (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (A : PresheafOfModules.{u} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (a : A.obj T.left) :
    germ F R A T 1 a = (obj F R A).map T.hom (unit F R A T.left a) := by
  rw [unit, obj_map_germ, map_one]
  exact (germ_congr F R A (Category.id_comp T.hom) 1 a).symm

end Stacks.PullbackColimit

namespace Stacks.Sites.ComponentModuleSumFormula

section Evaluation

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}} {I : Type w}
  [HasColimitsOfShape (Discrete I) AddCommGrpCat.{u}]

/-- A cofan of presheaves of modules is a colimit as soon as it is one over every object. -/
noncomputable def isColimitCofanOfEvaluationPresheafOfModules
    {f : I → PresheafOfModules.{u} R}
    {P : PresheafOfModules.{u} R} (p : ∀ i, f i ⟶ P)
    (h : ∀ X : Cᵒᵖ, IsColimit (Cofan.mk (P.obj X) fun i => PresheafOfModules.Hom.app (p i) X)) :
    IsColimit (Cofan.mk P p) := by
  refine PresheafOfModules.evaluationJointlyReflectsColimits _ _ fun X => ?_
  refine (IsColimit.equivOfNatIsoOfIso
    ((Discrete.natIso fun _ => Iso.refl _ :
        (Discrete.functor fun i => (f i).obj X) ≅
          Discrete.functor f ⋙ PresheafOfModules.evaluation R X))
    (Cofan.mk (P.obj X) fun i => PresheafOfModules.Hom.app (p i) X)
    ((PresheafOfModules.evaluation R X).mapCocone (Cofan.mk P p))
    (Cocone.ext (Iso.refl _) ?_)) (h X)
  rintro ⟨j⟩
  change (𝟙 _ ≫ PresheafOfModules.Hom.app (p j) X) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

end Evaluation

section Legs

variable (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory}
  (R : (Grothendieck C.underlying)ᵒᵖ ⥤ CommRingCat.{u})
  (A : PresheafOfModules.{u}
    (((Grothendieck.ι C.underlying (op n)).op ⋙ R) ⋙ forget₂ CommRingCat RingCat))

/-- The restriction to simplicial degree `m` of the presheaf-level module lower shriek from
degree `n`. -/
noncomputable def componentRestrictedPullback (m : SimplexCategory) :
    PresheafOfModules.{u}
      (((Grothendieck.ι C.underlying (op m)).op ⋙ R) ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pushforward₀OfCommRingCat (Grothendieck.ι C.underlying (op m)) R).obj
    (Stacks.PullbackColimit.obj (Grothendieck.ι C.underlying (op n)) R A)

/-- The summand inclusion attached to a simplex map `φ : [n] ⟶ [m]`. -/
noncomputable def sumFormulaLeg (φ : n ⟶ m) :
    (transitionPullbackPresheafModules C R φ).obj A ⟶ componentRestrictedPullback C R A m where
  app W := colimit.ι (Stacks.PullbackColimit.diagram (Grothendieck.ι C.underlying (op n)) R A
      (op ((Grothendieck.ι C.underlying (op m)).obj W.unop)))
    (CocontinuousSimplicialSite.componentCostructuredArrow C W.unop φ)
  naturality {W W'} g := by
    refine Stacks.PullbackModel.extendScalars_hom_ext
      ((ringTransition C R φ).app W).hom fun a => ?_
    refine (Stacks.PullbackColimit.germ_restrict (Grothendieck.ι C.underlying (op n)) R A
      ((Grothendieck.ι C.underlying (op m)).op.map g)
      (T := CocontinuousSimplicialSite.componentCostructuredArrow C W.unop φ)
      (T' := CocontinuousSimplicialSite.componentCostructuredArrow C W'.unop φ)
      ((C.underlying.map φ.op).toFunctor.op.map g) ?_ 1 a).symm
    exact congrArg Quiver.Hom.op
      ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).naturality g.unop).symm

/-- The leg attached to `φ`, on sections, is the colimit injection at the distinguished index
attached to `φ`. -/
theorem sumFormulaLeg_app (φ : n ⟶ m) (W : (C.underlying.obj (op m))ᵒᵖ) :
    PresheafOfModules.Hom.app (sumFormulaLeg C R A φ) W =
      colimit.ι (Stacks.PullbackColimit.diagram (Grothendieck.ι C.underlying (op n)) R A
          (op ((Grothendieck.ι C.underlying (op m)).obj W.unop)))
        (CocontinuousSimplicialSite.componentCostructuredArrow C W.unop φ) :=
  rfl

/-- The restriction to degree `m` of the presheaf-level module lower shriek from degree `n` is the
direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the presheaf-level module pullbacks along
the transitions, with the summand labelled `φ` included by `sumFormulaLeg`. -/
noncomputable def isColimitCofanSumFormulaLegs (m : SimplexCategory) :
    IsColimit (Cofan.mk (componentRestrictedPullback C R A m)
      fun φ : n ⟶ m => sumFormulaLeg C R A φ) :=
  isColimitCofanOfEvaluationPresheafOfModules _ fun W =>
    isColimitCofanPullbackDiagramComponent C W.unop R A

/-- The restriction to degree `m` of the presheaf-level module lower shriek from degree `n` is
isomorphic, as a presheaf of modules, to the direct sum over the simplex maps `φ : [n] ⟶ [m]` of
the presheaf-level module pullbacks `f_φ^*` along the transitions. -/
noncomputable def componentRestrictedPullbackIsoCoproduct (m : SimplexCategory) :
    componentRestrictedPullback C R A m ≅
      ∐ fun φ : n ⟶ m => (transitionPullbackPresheafModules C R φ).obj A :=
  (isColimitCofanSumFormulaLegs C R A m).coconePointUniqueUpToIso (coproductIsCoproduct _)

end Legs

section Functorial

variable (C : CocontinuousSimplicialSite.{u}) (n m : SimplexCategory)
  (R : (Grothendieck C.underlying)ᵒᵖ ⥤ CommRingCat.{u})

/-- The summand inclusion attached to a simplex map `φ : [n] ⟶ [m]`, as a morphism of functors:
the presheaf-level module pullback along the transition of `φ` maps to the restriction to degree
`m` of the presheaf-level module lower shriek from degree `n`. -/
noncomputable def sumFormulaLegNatTrans (φ : n ⟶ m) :
    transitionPullbackPresheafModules C R φ ⟶
      Stacks.PullbackColimit.colimitPullback (Grothendieck.ι C.underlying (op n)) R ⋙
        PresheafOfModules.pushforward₀OfCommRingCat
          (Grothendieck.ι C.underlying (op m)) R where
  app A := sumFormulaLeg C R A φ
  naturality A A' f := by
    refine PresheafOfModules.hom_ext fun W => ?_
    refine Stacks.PullbackModel.extendScalars_hom_ext
      ((ringTransition C R φ).app W).hom fun a => ?_
    exact (Stacks.PullbackTensor.colimitPullback_map_germ_one
      (Grothendieck.ι C.underlying (op n)) R f
      (CocontinuousSimplicialSite.componentCostructuredArrow C W.unop φ) a).symm

/-- The restriction to degree `m` of the presheaf-level module lower shriek from degree `n` is,
as a functor, the direct sum over the simplex maps `φ : [n] ⟶ [m]` of the presheaf-level
module pullbacks along the transitions, with `sumFormulaLegNatTrans` as the injections. -/
noncomputable def isColimitCofanSumFormulaLegNatTrans :
    IsColimit (Cofan.mk
      (Stacks.PullbackColimit.colimitPullback (Grothendieck.ι C.underlying (op n)) R ⋙
        PresheafOfModules.pushforward₀OfCommRingCat (Grothendieck.ι C.underlying (op m)) R)
      fun φ : n ⟶ m => sumFormulaLegNatTrans C n m R φ) :=
  isColimitCofanOfEvaluation _ fun A => isColimitCofanSumFormulaLegs C R A m

/-- The restriction to simplicial degree `m` of the presheaf-level module lower shriek from degree
`n` is, as a functor, the direct sum over the simplex maps `φ : [n] ⟶ [m]` of the presheaf-level
module pullbacks `f_φ^*` along the transitions, the summand labelled `φ` being the pullback along
the transition of `φ`. -/
@[stacks 0D72 "direct-sum formula in case (B), on presheaves of modules"]
noncomputable def colimitPullbackRestrictionIsoCoproduct :
    Stacks.PullbackColimit.colimitPullback (Grothendieck.ι C.underlying (op n)) R ⋙
        PresheafOfModules.pushforward₀OfCommRingCat
          (Grothendieck.ι C.underlying (op m)) R ≅
      ∐ fun φ : n ⟶ m => transitionPullbackPresheafModules C R φ :=
  (isColimitCofanSumFormulaLegNatTrans C n m R).coconePointUniqueUpToIso
    (coproductIsCoproduct _)

variable {S : (C.underlying.obj (op n))ᵒᵖ ⥤ CommRingCat.{u}}
  (α : S ⟶ (Grothendieck.ι C.underlying (op n)).op ⋙ R)

/-- The restriction to degree `m` of `CategoryTheory.PresheafOfModules.pullback` along the
degree-`n` component inclusion is extension of scalars along `α` followed by the direct sum, over
the simplex maps `φ : [n] ⟶ [m]`, of the presheaf-level module pullbacks along the transitions. -/
noncomputable def pullbackRestrictionIsoCompCoproduct :
    PresheafOfModules.pullback.{u} (Stacks.PullbackColimit.toRingCatPullback α) ⋙
        PresheafOfModules.pushforward₀OfCommRingCat
          (Grothendieck.ι C.underlying (op m)) R ≅
      Stacks.PullbackModel.extendScalars α ⋙
        ∐ fun φ : n ⟶ m => transitionPullbackPresheafModules C R φ :=
  Functor.isoWhiskerRight (Stacks.PullbackColimit.pullbackIso α) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Stacks.PullbackModel.extendScalars α)
      (colimitPullbackRestrictionIsoCoproduct C n m R)

end Functorial

end Stacks.Sites.ComponentModuleSumFormula

end
