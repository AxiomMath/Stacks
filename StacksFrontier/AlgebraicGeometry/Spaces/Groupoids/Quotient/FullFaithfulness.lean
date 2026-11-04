module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FibreFullFaithfulness
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibreFunctor
public import StacksFrontier.CategoryTheory.Sites.Stack.FullyFaithfulOfLocalEssImage

/-!
# Full faithfulness of a morphism of quotient stacks (Stacks 046S)

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B`, and let `[f] : [U/R] ⟶ [U'/R']` be the induced morphism of quotient
stacks of Stacks 046Q. Then `[f]` is fully faithful exactly when `R` is the
restriction of `R'` along `f : U ⟶ U'`, i.e. when the square

```
  R  ⟶  R'
  ↓      ↓
U × U ⟶ U' × U'
```

formed by the arrow map of `f` and the source–target maps is cartesian.

## Main results

* `AlgebraicGeometry.Stack.fullyFaithful_quotientStackMap_iff_isPullback`: **Stacks 046S**.

## Implementation notes

The restriction condition `R = (U ×_B U) ×_{U' ×_B U'} R'` is expressed as the cartesian
source–target square of the presheaves of points on the big fppf site, with the factors in the
order source-then-target on both sides. Full faithfulness is asserted for the underlying functor
of the based functor `AlgebraicGeometry.Stack.quotientStackMap`, as the existence of a
`CategoryTheory.Functor.FullyFaithful` witness; the datum itself is not canonical, only its
existence.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w u' v' w'

variable {C : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : C.Contains S} {B : AlgebraicSpaces C S hS}

open CategoryTheory.Pseudofunctor Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans

set_option backward.isDefEq.respectTransparency false

/-- Two composites out of a representable agree iff the images of the corresponding points
agree. -/
private theorem comp_eq_comp_iff_app_eq
    {D : Type u} [Category.{v} D] {F G F' : Dᵒᵖ ⥤ Type v} {X : D}
    (α : yoneda.obj X ⟶ F) (β : yoneda.obj X ⟶ G) (φ : F ⟶ F') (ψ : G ⟶ F') :
    α ≫ φ = β ≫ ψ ↔ φ.app _ (yonedaEquiv α) = ψ.app _ (yonedaEquiv β) := by
  rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, yonedaEquiv.apply_eq_iff_eq]

private theorem evaluation_faithful_of_isPullback
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hp : IsPullback f.toGroupoidHom.mapArrows
      (prod.lift G.toGroupoidInFunctors.source G.toGroupoidInFunctors.target)
      (prod.lift H.toGroupoidInFunctors.source H.toGroupoidInFunctors.target)
      (prod.map f.toGroupoidHom.mapObjects f.toGroupoidHom.mapObjects))
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (f.toGroupoidHom.evaluation T).Faithful := by
  let G' := G.toGroupoidInFunctors
  let H' := H.toGroupoidInFunctors
  let ηG := yonedaEquiv (X := Opposite.unop T) (F := G'.arrows)
  constructor
  intro x y m n hmn
  apply G'.evaluationArrowEquiv T x y |>.injective
  apply Subtype.ext
  let a := (G'.evaluationArrowEquiv T x y m).1
  let b := (G'.evaluationArrowEquiv T x y n).1
  let α := ηG.symm a
  let β := ηG.symm b
  have hm := congrArg (fun k =>
    (H'.evaluationArrowEquiv T
      ((f.toGroupoidHom.evaluation T).obj x)
      ((f.toGroupoidHom.evaluation T).obj y) k).1) hmn
  rw [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow,
    Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow] at hm
  have hαβ : α ≫ f.toGroupoidHom.mapArrows = β ≫ f.toGroupoidHom.mapArrows := by
    rw [comp_eq_comp_iff_app_eq]
    simpa [α, β, ηG] using hm
  have hst : α ≫ prod.lift G'.source G'.target =
      β ≫ prod.lift G'.source G'.target := by
    have hsource : α ≫ G'.source = β ≫ G'.source := by
      rw [comp_eq_comp_iff_app_eq]
      simpa [α, β, ηG] using
        (G'.evaluationArrowEquiv T x y m).2.1.trans
          ((G'.evaluationArrowEquiv T x y n).2.1.symm)
    have htarget : α ≫ G'.target = β ≫ G'.target := by
      rw [comp_eq_comp_iff_app_eq]
      simpa [α, β, ηG] using
        (G'.evaluationArrowEquiv T x y m).2.2.trans
          ((G'.evaluationArrowEquiv T x y n).2.2.symm)
    apply prod.hom_ext
    · simpa [Category.assoc, prod.lift_fst, prod.map_fst] using hsource
    · simpa [Category.assoc, prod.lift_snd, prod.map_snd] using htarget
  have hab := hp.hom_ext hαβ hst
  simpa [α, β, ηG] using congrArg ηG hab

private theorem evaluation_full_of_isPullback
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hp : IsPullback f.toGroupoidHom.mapArrows
      (prod.lift G.toGroupoidInFunctors.source G.toGroupoidInFunctors.target)
      (prod.lift H.toGroupoidInFunctors.source H.toGroupoidInFunctors.target)
      (prod.map f.toGroupoidHom.mapObjects f.toGroupoidHom.mapObjects))
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (f.toGroupoidHom.evaluation T).Full := by
  let G' := G.toGroupoidInFunctors
  let H' := H.toGroupoidInFunctors
  let ηHA := yonedaEquiv (X := Opposite.unop T) (F := H'.arrows)
  let ηGA := yonedaEquiv (X := Opposite.unop T) (F := G'.arrows)
  let ηGU := yonedaEquiv (X := Opposite.unop T) (F := G'.objects)
  refine ⟨?_⟩
  intro x y m
  let a := (H'.evaluationArrowEquiv T _ _ m).1
  let α := ηHA.symm a
  let β := prod.lift (ηGU.symm x) (ηGU.symm y)
  have hβfst : β ≫ prod.fst = ηGU.symm x := by simp [β]
  have hβsnd : β ≫ prod.snd = ηGU.symm y := by simp [β]
  have hcond : α ≫ prod.lift H'.source H'.target =
      β ≫ prod.map f.toGroupoidHom.mapObjects f.toGroupoidHom.mapObjects := by
    have hsource : α ≫ H'.source = (ηGU.symm x) ≫ f.toGroupoidHom.mapObjects := by
      rw [comp_eq_comp_iff_app_eq]
      simpa [α, ηHA, ηGU, a,
        Deformation.GroupoidInFunctors.Hom.evaluation_obj] using
        (H'.evaluationArrowEquiv T _ _ m).2.1
    have htarget : α ≫ H'.target = (ηGU.symm y) ≫ f.toGroupoidHom.mapObjects := by
      rw [comp_eq_comp_iff_app_eq]
      simpa [α, ηHA, ηGU, a,
        Deformation.GroupoidInFunctors.Hom.evaluation_obj] using
        (H'.evaluationArrowEquiv T _ _ m).2.2
    apply prod.hom_ext
    · rw [Category.assoc β, prod.map_fst]
      simp [hsource, ← hβfst]
    · rw [Category.assoc β, prod.map_snd]
      simp [htarget, ← hβsnd]
  obtain ⟨q, hq₁, hq₂⟩ := hp.exists_lift α β hcond
  have hqsrc : q ≫ G'.source = ηGU.symm x := by
    rw [← hβfst]
    simpa using congrArg (· ≫ prod.fst) hq₂
  have hqtgt : q ≫ G'.target = ηGU.symm y := by
    rw [← hβsnd]
    simpa using congrArg (· ≫ prod.snd) hq₂
  have hsrc : G'.source.app T (ηGA q) = x := by
    have h := congrArg ηGU hqsrc
    rw [yonedaEquiv_comp] at h
    simpa [ηGU, ηGA] using h
  have htgt : G'.target.app T (ηGA q) = y := by
    have h := congrArg ηGU hqtgt
    rw [yonedaEquiv_comp] at h
    simpa [ηGU, ηGA] using h
  let n := (G'.evaluationArrowEquiv T x y).symm ⟨ηGA q, hsrc, htgt⟩
  refine ⟨n, ?_⟩
  apply (H'.evaluationArrowEquiv T _ _).injective
  apply Subtype.ext
  have h := congrArg (yonedaEquiv (X := Opposite.unop T) (F := H'.arrows)) hq₁
  rw [yonedaEquiv_comp] at h
  calc
    _ = f.toGroupoidHom.mapArrows.app T (G'.evaluationArrowEquiv T x y n).1 := by
      simpa using f.toGroupoidHom.evaluation_map_arrow T n
    _ = a := by simpa [ηGA, ηHA, α, n, Equiv.apply_symm_apply] using h

private noncomputable def evaluation_fullyFaithful_of_isPullback
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hp : IsPullback f.toGroupoidHom.mapArrows
      (prod.lift G.toGroupoidInFunctors.source G.toGroupoidInFunctors.target)
      (prod.lift H.toGroupoidInFunctors.source H.toGroupoidInFunctors.target)
      (prod.map f.toGroupoidHom.mapObjects f.toGroupoidHom.mapObjects))
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (f.toGroupoidHom.evaluation T).FullyFaithful := by
  letI := evaluation_full_of_isPullback f hp T
  letI := evaluation_faithful_of_isPullback f hp T
  exact Functor.FullyFaithful.ofFullyFaithful _

open CategoryTheory.Functor

private noncomputable def cogrothendieckMapFullyFaithful
    {D : Type u} [Category.{v} D]
    {P Q : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{w, u'}} (α : P ⟶ Q)
    (hα : ∀ T, (α.app ⟨op T⟩).toFunctor.FullyFaithful) :
    (CoGrothendieck.map α).FullyFaithful where
  preimage {X Y} f :=
    { base := f.base
      fiber := (hα X.base).preimage (f.fiber ≫
        (α.naturality f.base.op.toLoc).inv.toNatTrans.app Y.fiber) }
  map_preimage {X Y} f := by
    refine CoGrothendieck.Hom.ext _ _ (by rfl) ?_
    simp [CoGrothendieck.map, (hα X.base).map_preimage, ← Cat.Hom₂.comp_app]
  preimage_map {X Y} f := by
    refine CoGrothendieck.Hom.ext _ _ (by rfl) ?_
    dsimp [CoGrothendieck.map]
    rw [Category.assoc]
    simp [← Cat.Hom₂.comp_app, (hα X.base).preimage_map]

private def cogrothendieckInclusionMapIso
    {D : Type u} [Category.{v} D]
    {P Q : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{w, u'}} (α : P ⟶ Q) (T : D) :
    CoGrothendieck.ι P T ⋙ CoGrothendieck.map α ≅
      (α.app ⟨op T⟩).toFunctor ⋙ CoGrothendieck.ι Q T := by
  refine NatIso.ofComponents (fun x => ?_) ?_
  · exact Iso.refl _
  intro x y m
  simp only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
  refine CoGrothendieck.Hom.ext _ _ (by rfl) ?_
  simp only [CoGrothendieck.map, CoGrothendieck.ι,
    Functor.map_comp, op_id, Quiver.Hom.id_toLoc,
    Pseudofunctor.StrongTrans.naturality_id_hom_app, Cat.Hom.id_toFunctor,
    Category.assoc, eqToHom_refl, Category.comp_id]
  slice_lhs 2 3 =>
    rw [← Functor.map_comp]
    simp [← Cat.Hom₂.comp_app]
  simp

private noncomputable def fullyFaithful_component_of_map
    {D : Type u} [Category.{v} D]
    {P Q : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{w, u'}} (α : P ⟶ Q)
    (h : (CoGrothendieck.map α).FullyFaithful) (T : D) :
    (α.app ⟨op T⟩).toFunctor.FullyFaithful := by
  let I := Functor.Fiber.inducedFunctor (CoGrothendieck.comp_const P T)
  let K := Functor.Fiber.inducedFunctor (CoGrothendieck.comp_const Q T)
  let M := Functor.Fiber.mapOfComp (CoGrothendieck.forget P) (CoGrothendieck.forget Q)
    (CoGrothendieck.map α) (CoGrothendieck.map_comp_forget α) T
  have : (CoGrothendieck.map α).Full := h.full
  have : (CoGrothendieck.map α).Faithful := h.faithful
  have : M.Full := Functor.Fiber.full_mapOfComp (CoGrothendieck.map_comp_forget α) T
  have : M.Faithful := Functor.Fiber.faithful_mapOfComp (CoGrothendieck.map_comp_forget α) T
  let e : I ⋙ M ≅ (α.app ⟨op T⟩).toFunctor ⋙ K :=
    NatIso.ofComponents (fun a => Iso.refl _) (by
      intro a b m
      apply Functor.Fiber.hom_ext
      simpa [I, M, K, Functor.Fiber.inducedFunctor, Functor.Fiber.mapOfComp,
        Functor.Fiber.fiberInclusion, cogrothendieckInclusionMapIso] using
        (cogrothendieckInclusionMapIso α T).hom.naturality m)
  exact ((Functor.FullyFaithful.ofFullyFaithful (I ⋙ M)).ofIso e).ofCompFaithful

private theorem prod_app_ext
    {D : Type u} [Category.{v} D] {P Q : Dᵒᵖ ⥤ Type v} {T : Dᵒᵖ}
    {a b : (P ⨯ Q).obj T}
    (h₁ : (prod.fst : P ⨯ Q ⟶ P).app T a = (prod.fst : P ⨯ Q ⟶ P).app T b)
    (h₂ : (prod.snd : P ⨯ Q ⟶ Q).app T a = (prod.snd : P ⨯ Q ⟶ Q).app T b) : a = b := by
  apply (yonedaEquiv (X := unop T) (F := P ⨯ Q)).symm.injective
  apply prod.hom_ext
  · apply (yonedaEquiv (X := unop T) (F := P)).injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simpa only [Equiv.apply_symm_apply] using h₁
  · apply (yonedaEquiv (X := unop T) (F := Q)).injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simpa only [Equiv.apply_symm_apply] using h₂

private theorem isPullback_of_evaluation_fullyFaithful
    {D : Type u} [Category.{v} D]
    {G H : Deformation.GroupoidInFunctors.{u, v, v} Dᵒᵖ}
    (f : Deformation.GroupoidInFunctors.Hom G H)
    (hf : ∀ T, (f.evaluation T).FullyFaithful) :
    IsPullback f.mapArrows (prod.lift G.source G.target)
      (prod.lift H.source H.target) (prod.map f.mapObjects f.mapObjects) := by
  have hw : f.mapArrows ≫ prod.lift H.source H.target =
      prod.lift G.source G.target ≫ prod.map f.mapObjects f.mapObjects := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc]
      ext T a
      exact f.map_source T a
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc]
      ext T a
      exact f.map_target T a
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun α => α.app T) hw, ?_, ?_⟩
  · intro a b hab
    have hs : G.source.app T a = G.source.app T b := by
      simpa only [← NatTrans.comp_app_apply, prod.lift_fst] using
        congrArg ((prod.fst : G.objects ⨯ G.objects ⟶ G.objects).app T) hab.2
    have ht : G.target.app T a = G.target.app T b := by
      simpa only [← NatTrans.comp_app_apply, prod.lift_snd] using
        congrArg ((prod.snd : G.objects ⨯ G.objects ⟶ G.objects).app T) hab.2
    let x := G.source.app T a
    let y := G.target.app T a
    let m := (G.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩
    let n := (G.evaluationArrowEquiv T x y).symm ⟨b, hs.symm, ht.symm⟩
    have hmn : (f.evaluation T).map m = (f.evaluation T).map n := by
      apply (H.evaluationArrowEquiv T _ _).injective
      apply Subtype.ext
      rw [f.evaluation_map_arrow T m, f.evaluation_map_arrow T n]
      simpa only [m, n, Equiv.apply_symm_apply] using hab.1
    simpa [m, n] using
      congrArg (fun k => (G.evaluationArrowEquiv T x y k).1) ((hf T).map_injective hmn)
  · intro a p hap
    let x := (prod.fst : G.objects ⨯ G.objects ⟶ G.objects).app T p
    let y := (prod.snd : G.objects ⨯ G.objects ⟶ G.objects).app T p
    have hs : H.source.app T a = f.mapObjects.app T x := by
      have he := congrArg ((prod.fst : H.objects ⨯ H.objects ⟶ H.objects).app T) hap
      change ((prod.lift H.source H.target ≫ prod.fst).app T) a =
        ((prod.map f.mapObjects f.mapObjects ≫ prod.fst).app T) p at he
      rw [prod.lift_fst, prod.map_fst] at he
      exact he
    have ht : H.target.app T a = f.mapObjects.app T y := by
      have he := congrArg ((prod.snd : H.objects ⨯ H.objects ⟶ H.objects).app T) hap
      change ((prod.lift H.source H.target ≫ prod.snd).app T) a =
        ((prod.map f.mapObjects f.mapObjects ≫ prod.snd).app T) p at he
      rw [prod.lift_snd, prod.map_snd] at he
      exact he
    let m := (H.evaluationArrowEquiv T ((f.evaluation T).obj x)
      ((f.evaluation T).obj y)).symm ⟨a, hs, ht⟩
    let n := (hf T).preimage m
    let b := (G.evaluationArrowEquiv T x y n).1
    refine ⟨b, ?_, ?_⟩
    · have he := congrArg (fun k => (H.evaluationArrowEquiv T _ _ k).1)
        ((hf T).map_preimage m)
      rw [f.evaluation_map_arrow] at he
      simpa only [b, n, m, Equiv.apply_symm_apply] using he
    · apply prod_app_ext
      · simpa only [← NatTrans.comp_app_apply, prod.lift_fst] using
          (G.evaluationArrowEquiv T x y n).2.1
      · simpa only [← NatTrans.comp_app_apply, prod.lift_snd] using
          (G.evaluationArrowEquiv T x y n).2.2

/-- **Condition (1) of Stacks 046S.** A morphism of groupoids in presheaves whose every
evaluation is fully faithful has cartesian arrow square over the self-product of its object map:
the square formed by its arrow map, the two source–target pairs and the self-product of its object
map is a fibre product. -/
alias isPullback_mapArrows_of_evaluation_fullyFaithful := isPullback_of_evaluation_fullyFaithful

private noncomputable def toQuotientStack_fullyFaithful
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toQuotientStack G).FullyFaithful := by
  have h := (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
    (quotientPrestack G).p (quotientStack G).p
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G)
    (toQuotientStack G)
    (isFibredOneMorphism_toQuotientStack G).comp_eq).2
    (fun T => ⟨(fullyFaithful_fiberFunctor_toQuotientStack G T).some.full,
      (fullyFaithful_fiberFunctor_toQuotientStack G T).some.faithful⟩)
  have : (toQuotientStack G).Full := h.1
  have : (toQuotientStack G).Faithful := h.2
  exact Functor.FullyFaithful.ofFullyFaithful _

private noncomputable def pointwiseToQuotientStack_fullyFaithful
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwiseToQuotientStack G).FullyFaithful :=
  (quotientPrestackEquivalence G).fullyFaithfulFunctor.comp
    (toQuotientStack_fullyFaithful G)

/-- **Stacks 046S.** The induced morphism of quotient stacks `[f] : [U/R] ⟶ [U'/R']` is fully
faithful if and only if `R` is the restriction of `R'` along `f : U ⟶ U'`, i.e. if and only if
the square formed by the arrow map of `f` and the two source–target maps is cartesian. -/
@[stacks 046S]
public theorem fullyFaithful_quotientStackMap_iff_isPullback
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    Nonempty (quotientStackMap f).toFunctor.FullyFaithful ↔
      IsPullback f.toGroupoidHom.mapArrows
        (prod.lift G.toGroupoidInFunctors.source G.toGroupoidInFunctors.target)
        (prod.lift H.toGroupoidInFunctors.source H.toGroupoidInFunctors.target)
        (prod.map f.toGroupoidHom.mapObjects f.toGroupoidHom.mapObjects) := by
  let E := quotientPrestackEquivalence G
  let I := pointwiseToQuotientStack G
  let K := pointwiseToQuotientStack H
  let P := (quotientPointwiseMap f).toFunctor
  let F := (quotientStackMap f).toFunctor
  let α : P ⋙ K ≅ I ⋙ F :=
    (BasedNatTrans.forgetful _ _).mapIso (quotientStackMap_commutes f)
  let hk := pointwiseToQuotientStack_fullyFaithful H
  have : K.Faithful := hk.faithful
  constructor
  · rintro ⟨hF⟩
    have hP : P.FullyFaithful :=
      (((pointwiseToQuotientStack_fullyFaithful G).comp hF).ofIso α.symm).ofCompFaithful
    refine isPullback_of_evaluation_fullyFaithful f.toGroupoidHom fun T => ?_
    have h := fullyFaithful_component_of_map (quotientPointwiseMapData f).val
      hP (unop T)
    rw [(quotientPointwiseMapData f).property.1] at h
    exact h
  · intro hp
    let hP : P.FullyFaithful :=
      cogrothendieckMapFullyFaithful (quotientPointwiseMapData f).val (fun T => by
        rw [(quotientPointwiseMapData f).property.1]
        exact evaluation_fullyFaithful_of_isPullback f hp (op T))
    have hIF : (I ⋙ F).FullyFaithful := (hP.comp hk).ofIso α
    have hIF' : (E.functor ⋙ (toQuotientStack G ⋙ F)).FullyFaithful := hIF
    have hEF : (toQuotientStack G ⋙ F).FullyFaithful :=
      (E.fullyFaithfulInverse.comp hIF').ofIso
        ((Functor.associator E.inverse E.functor _).symm ≪≫
          isoWhiskerRight E.counitIso _ ≪≫ Functor.leftUnitor _)
    exact CategoryTheory.Functor.fullyFaithful_of_locallyEssImage_of_isMorSheaf
      (toQuotientStack G)
      (isFibredOneMorphism_toQuotientStack G).comp_eq
      (toQuotientStack_fullyFaithful G)
      (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids
        (isFiberedInGroupoids_quotientStack H) (quotientStackMap f).w)
      hEF (isFiberedInGroupoids_quotientStack G)
      (isFiberedInGroupoids_quotientStack H)
      (BigFppfOver.topology C S hS)
      (isStack_quotientStack G).isMorSheaf (isStack_quotientStack H).isMorSheaf
      (fun T x => by
        obtain ⟨R, hR, h⟩ := essImage_toQuotientStack G T x
        exact ⟨R, hR, fun f hf => h hf⟩)

end AlgebraicGeometry.Stack

end
