module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.Homology.RelativelyPerfect.Colimit

/-!
# Strictification of the finite étale restriction pseudofunctor

Restriction of finite étale covers to the open neighbourhoods of a closed subscheme is a
pseudofunctor `W ↦ FÉt_W` into `Cat`, not a functor: base change along a composite of
inclusions is only canonically isomorphic to the composite of the base changes. Before one can
speak of the colimit of the diagram one must replace it by an honest functor together with a
coherent comparison, which is what
`Stacks.FundamentalGroup.FiniteEtaleColimitPresentation` asks for in its first three fields.

This file supplies them. The strict replacement is the one of Stacks 004A as realised by
`CategoryTheory.PseudoCoherence.Strictification.strictDiagram`: the value at `W` is the full
subcategory of `FÉt_W` spanned by the covers base changed from a larger neighbourhood, with the
originating neighbourhood remembered, and the transition functors postcompose the remembered
inclusion, which is strictly functorial. What that development does not provide, and what is
built here, is the *strong transformation* of pseudofunctors comparing the strict diagram with
the original one. Its two coherence identities reduce to the right unitor and the associativity
coherence of the pseudofunctor itself, componentwise; those two reductions are isolated as
`Stacks.Strictification.mapId_app_comp` and `Stacks.Strictification.mapComp_app_comp`.

## Main definitions

* `Stacks.Strictification.mapId_app_comp`, `Stacks.Strictification.mapComp_app_comp` — the
  right unitor and associativity coherence of a `Cat`-valued pseudofunctor on a strict
  bicategory, in componentwise form.
* `Stacks.FundamentalGroup.strictRestrictionDiagram` — the strict diagram attached to a
  pseudofunctor on the neighbourhoods of a closed subscheme.
* `Stacks.FundamentalGroup.stageEval` and `Stacks.FundamentalGroup.stagePushIso` — the
  evaluation of a stage into the pseudofunctor's value there, and the comparison isomorphism
  between the two transition functors.
* `Stacks.FundamentalGroup.strictComparison` — the strong transformation
  `(strictRestrictionDiagram F).toPseudofunctor' ⟹ F`.
* `Stacks.FundamentalGroup.finiteEtaleRestrictionDiagram`,
  `Stacks.FundamentalGroup.finiteEtaleRestrictionStage` and
  `Stacks.FundamentalGroup.finiteEtaleRestrictionComparison` — the three fields `diagram`,
  `stage` and `comparison` of `FiniteEtaleColimitPresentation`, for the finite étale
  restriction pseudofunctor.
* `Stacks.FundamentalGroup.finiteEtaleColimitPresentationOfCocone` — the presentation itself,
  granted a cocone on the strict diagram and its stagewise identification with base change.

## Implementation notes

**Why the index category is kept concrete.** The strictification of a pseudofunctor into
`Cat.{v, u}` lands in `Cat.{v, max uIndex vIndex u}`, so a strong transformation between the
two can only be *stated* when the index universes are bounded by the object universe. Writing
that bound as `Cat.{v, max uIndex vIndex u}` makes every application of the strictification
leave an unsolvable universe constraint `max uIndex vIndex ?u = max uIndex vIndex u`; the
constraint disappears once the index category is the concrete `Neighborhood X Y`, which is why
everything below is stated for that index rather than for an abstract one.

**Why the index being a poset is load-bearing.** `Stacks.FundamentalGroup.strictMapId_app`
says that the unitor of the strict diagram acts as the identity on a stage object. That holds
because an object of the stage category records an arrow `o.arrow` of the index category and
the unitor transports it along `o.arrow ≫ 𝟙 = o.arrow`, an equation which is *definitional*
for a preorder category — the hom types are `ULift (PLift _)`, so structure eta and proof
irrelevance identify the two sides — and merely propositional in general.

**Why the pseudofunctor is kept abstract.** All of the above is proved for an abstract
pseudofunctor `F` and only then instantiated at the finite étale restriction pseudofunctor.
With the concrete pseudofunctor substituted throughout, the kernel has to unfold it while
checking the transports in the coherence proofs and exceeds its heartbeat budget.

## References

* [Stacks Project, Tag 0ELD](https://stacks.math.columbia.edu/tag/0ELD)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public noncomputable section

open CategoryTheory Bicategory Pseudofunctor PseudoCoherence AlgebraicGeometry
open scoped CategoryTheory.Bicategory

universe u

namespace Stacks.Strictification

/-- The right unitor coherence of a `Cat`-valued pseudofunctor on a strict bicategory, in the
form in which it occurs as a component of a `2`-morphism: the compositor at `f` and an identity,
followed by the unitor, is the transport along `f ≫ 𝟙 = f`. -/
lemma mapId_app_comp {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (D : Pseudofunctor B Cat.{u, u + 1}) {P Q : B} (f : P ⟶ Q) (x : D.obj P) :
    (D.mapComp f (𝟙 Q)).hom.toNatTrans.app x ≫
        (D.mapId Q).hom.toNatTrans.app ((D.map f).toFunctor.obj x) =
      eqToHom (congrArg (fun m : P ⟶ Q => (D.map m).toFunctor.obj x)
        (Bicategory.Strict.comp_id f)) := by
  rw [D.mapComp_id_right_hom_app, Category.assoc, ← Cat.Hom₂.comp_app, Iso.inv_hom_id,
    Cat.Hom₂.id_app]
  simp [Bicategory.Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]

/-- The associativity coherence of a `Cat`-valued pseudofunctor on a strict bicategory, in the
form in which it occurs as a component of a `2`-morphism. -/
lemma mapComp_app_comp {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (D : Pseudofunctor B Cat.{u, u + 1}) {P Q R S : B} (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ S)
    (x : D.obj P) :
    (D.mapComp f (g ≫ h)).hom.toNatTrans.app x ≫
        (D.mapComp g h).hom.toNatTrans.app ((D.map f).toFunctor.obj x) =
      eqToHom (congrArg (fun m : P ⟶ S => (D.map m).toFunctor.obj x)
        (Bicategory.Strict.assoc f g h).symm) ≫
        (D.mapComp (f ≫ g) h).hom.toNatTrans.app x ≫
        (D.map h).toFunctor.map ((D.mapComp f g).hom.toNatTrans.app x) := by
  rw [D.mapComp_assoc_right_hom_app]
  simp [Bicategory.Strict.associator_eqToIso, PrelaxFunctor.map₂_eqToHom]

end Stacks.Strictification

namespace Stacks.FundamentalGroup

open Stacks.Strictification

variable (X : Scheme.{u}) (Y : X.IdealSheafData)
  (F : Pseudofunctor (LocallyDiscrete (Neighborhood X Y)) Cat.{u, u + 1})

/-- The strict diagram replacing a pseudofunctor on the neighbourhoods of the closed subscheme
cut out by `Y`: its value at `W` records a cover of a larger neighbourhood together with the
inclusion, and its transition functors postcompose that inclusion. -/
def strictRestrictionDiagram : Neighborhood X Y ⥤ Cat.{u, u + 1} :=
  PseudoCoherence.Strictification.strictDiagram F

/-- The evaluation of a stage of the strict diagram into the value of `F` there, as a
`1`-morphism of `Cat` between the two objects compared by `strictComparison`. -/
def stageEval (W : LocallyDiscrete (Neighborhood X Y)) :
    (strictRestrictionDiagram X Y F).toPseudofunctor'.obj W ⟶ F.obj W :=
  Cat.Hom.ofFunctor (PseudoCoherence.Strictification.evaluation F W.as)

/-- The comparison isomorphism between the two ways of transporting a stage along an inclusion
of neighbourhoods: push it forward in the strict diagram and evaluate, or evaluate and apply
`F`. -/
def stagePushIso {V W : LocallyDiscrete (Neighborhood X Y)} (f : V ⟶ W) :
    (strictRestrictionDiagram X Y F).toPseudofunctor'.map f ≫ stageEval X Y F W ≅
      stageEval X Y F V ≫ F.map f :=
  Cat.Hom.isoMk (PseudoCoherence.Strictification.pushEvaluationIso F f.as)

/-- On a stage object, the comparison isomorphism is the compositor of `F` at the remembered
inclusion and the given one. -/
lemma stagePushIso_hom_app {V W : LocallyDiscrete (Neighborhood X Y)} (f : V ⟶ W)
    (o : ↑((strictRestrictionDiagram X Y F).toPseudofunctor'.obj V)) :
    (stagePushIso X Y F f).hom.toNatTrans.app o =
      (F.mapComp (PseudoCoherence.Strictification.Presentation.arrow o).toLoc f).hom.toNatTrans.app
        (PseudoCoherence.Strictification.Presentation.object o) :=
  rfl

/-- A transition functor of the strict diagram postcomposes the remembered inclusion. -/
@[simp]
lemma strictRestrictionDiagram_map_arrow {V W : LocallyDiscrete (Neighborhood X Y)} (f : V ⟶ W)
    (o : ↑((strictRestrictionDiagram X Y F).toPseudofunctor'.obj V)) :
    (PseudoCoherence.Strictification.Presentation.arrow
        (((strictRestrictionDiagram X Y F).toPseudofunctor'.map f).toFunctor.obj o)).toLoc =
      (PseudoCoherence.Strictification.Presentation.arrow o).toLoc ≫ f :=
  rfl

/-- A transition functor of the strict diagram leaves the underlying cover unchanged. -/
@[simp]
lemma strictRestrictionDiagram_map_object {V W : LocallyDiscrete (Neighborhood X Y)} (f : V ⟶ W)
    (o : ↑((strictRestrictionDiagram X Y F).toPseudofunctor'.obj V)) :
    PseudoCoherence.Strictification.Presentation.object
        (((strictRestrictionDiagram X Y F).toPseudofunctor'.map f).toFunctor.obj o) =
      PseudoCoherence.Strictification.Presentation.object o :=
  rfl

/-- The unitor of the strict diagram acts as the identity on a stage object. This uses that the
index category is a poset: the transport is along `o.arrow ≫ 𝟙 = o.arrow`, which is
definitional there. -/
lemma strictMapId_app {a : LocallyDiscrete (Neighborhood X Y)}
    (o : ↑((strictRestrictionDiagram X Y F).toPseudofunctor'.obj a)) :
    ((strictRestrictionDiagram X Y F).toPseudofunctor'.mapId a).hom.toNatTrans.app o =
      𝟙 (((strictRestrictionDiagram X Y F).toPseudofunctor'.map (𝟙 a)).toFunctor.obj o) := by
  simp only [Functor.toPseudofunctor'_mapId, eqToIso.hom, Cat.Hom₂.eqToHom_toNatTrans]
  exact eqToHom_app _ o

/-- The compositor of the strict diagram acts as the identity on a stage object; as for
`strictMapId_app`, this uses that the index category is a poset. -/
lemma strictMapComp_app {a b c : LocallyDiscrete (Neighborhood X Y)} (f : a ⟶ b) (g : b ⟶ c)
    (o : ↑((strictRestrictionDiagram X Y F).toPseudofunctor'.obj a)) :
    ((strictRestrictionDiagram X Y F).toPseudofunctor'.mapComp f g).hom.toNatTrans.app o =
      𝟙 (((strictRestrictionDiagram X Y F).toPseudofunctor'.map (f ≫ g)).toFunctor.obj o) := by
  simp only [Functor.toPseudofunctor'_mapComp, eqToIso.hom, Cat.Hom₂.eqToHom_toNatTrans]
  exact eqToHom_app _ o

/-- The comparison isomorphisms are natural in the `2`-morphisms of the index bicategory. As
the index bicategory is locally discrete this is automatic. -/
lemma stagePushIso_naturality {V W : LocallyDiscrete (Neighborhood X Y)} {f g : V ⟶ W}
    (η : f ⟶ g) :
    (strictRestrictionDiagram X Y F).toPseudofunctor'.map₂ η ▷ stageEval X Y F W ≫
        (stagePushIso X Y F g).hom =
      (stagePushIso X Y F f).hom ≫ stageEval X Y F V ◁ F.map₂ η := by
  obtain rfl := obj_ext_of_isDiscrete η
  obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
  simp

/-- The comparison isomorphisms are compatible with the identity inclusions. -/
lemma stagePushIso_id (a : LocallyDiscrete (Neighborhood X Y)) :
    (stagePushIso X Y F (𝟙 a)).hom ≫ stageEval X Y F a ◁ (F.mapId a).hom =
      ((strictRestrictionDiagram X Y F).toPseudofunctor'.mapId a).hom ▷ stageEval X Y F a ≫
        (λ_ (stageEval X Y F a)).hom ≫ (ρ_ (stageEval X Y F a)).inv := by
  apply Cat.Hom₂.ext
  ext o
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app]
  simp only [strictMapId_app, Cat.Hom.comp_toFunctor, Functor.comp_obj, Cat.Hom.id_toFunctor,
    Functor.id_obj, eqToHom_refl, Category.comp_id]
  exact (mapId_app_comp F o.arrow.toLoc o.object).trans
    ((eqToHom_refl _ _).trans ((stageEval X Y F a).toFunctor.map_id _).symm)

/-- The comparison isomorphisms are compatible with composition of inclusions. -/
lemma stagePushIso_comp {a b c : LocallyDiscrete (Neighborhood X Y)} (f : a ⟶ b) (g : b ⟶ c) :
    (stagePushIso X Y F (f ≫ g)).hom ≫ stageEval X Y F a ◁ (F.mapComp f g).hom =
      ((strictRestrictionDiagram X Y F).toPseudofunctor'.mapComp f g).hom ▷ stageEval X Y F c ≫
        (α_ ((strictRestrictionDiagram X Y F).toPseudofunctor'.map f)
          ((strictRestrictionDiagram X Y F).toPseudofunctor'.map g) (stageEval X Y F c)).hom ≫
        (strictRestrictionDiagram X Y F).toPseudofunctor'.map f ◁ (stagePushIso X Y F g).hom ≫
        (α_ ((strictRestrictionDiagram X Y F).toPseudofunctor'.map f) (stageEval X Y F b)
          (F.map g)).inv ≫
        (stagePushIso X Y F f).hom ▷ F.map g ≫
        (α_ (stageEval X Y F a) (F.map f) (F.map g)).hom := by
  apply Cat.Hom₂.ext
  ext o
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app]
  refine (mapComp_app_comp F o.arrow.toLoc f g o.object).trans ?_
  simp only [eqToHom_refl, Category.id_comp, stagePushIso_hom_app,
    strictRestrictionDiagram_map_arrow, strictRestrictionDiagram_map_object, Category.comp_id]
  set p := PseudoCoherence.Strictification.Presentation.arrow o with hp
  set q := PseudoCoherence.Strictification.Presentation.object o with hq
  refine Eq.symm (Eq.trans (congrArg (fun z => z ≫
    ((F.mapComp (p.toLoc ≫ f) g).hom.toNatTrans.app q ≫
      (F.map g).toFunctor.map ((F.mapComp p.toLoc f).hom.toNatTrans.app q))) ?_)
    (Category.id_comp _))
  exact (congrArg (stageEval X Y F c).toFunctor.map (strictMapComp_app X Y F f g o)).trans
    ((stageEval X Y F c).toFunctor.map_id _)

/-- **The coherent comparison between a pseudofunctor on the neighbourhoods of a closed
subscheme and its strictification.** Its component at a neighbourhood is the evaluation of the
stage category into the value of the pseudofunctor there, and its naturality constraints are the
compositors of the pseudofunctor at the remembered inclusions. -/
def strictComparison :
    Pseudofunctor.StrongTrans (strictRestrictionDiagram X Y F).toPseudofunctor' F where
  app := stageEval X Y F
  naturality f := stagePushIso X Y F f
  naturality_naturality η := stagePushIso_naturality X Y F η
  naturality_id a := stagePushIso_id X Y F a
  naturality_comp f g := stagePushIso_comp X Y F f g

/-- **The strict diagram of finite étale restriction.** This is the `diagram` field of
`Stacks.FundamentalGroup.FiniteEtaleColimitPresentation`. -/
def finiteEtaleRestrictionDiagram : Neighborhood X Y ⥤ Cat.{u, u + 1} :=
  strictRestrictionDiagram X Y (finiteEtaleRestrictionPseudofunctor X Y).val

/-- Each stage of the strict diagram of finite étale restriction is equivalent to the category
of finite étale covers of the corresponding neighbourhood. This is the `stage` field of
`Stacks.FundamentalGroup.FiniteEtaleColimitPresentation`. -/
def finiteEtaleRestrictionStage (W : Neighborhood X Y) :
    ↑((finiteEtaleRestrictionDiagram X Y).obj W) ≌
      FiniteEtaleOver (Neighborhood.open X Y W).toScheme :=
  PseudoCoherence.Strictification.canonicalStageEquivalence
    (finiteEtaleRestrictionPseudofunctor X Y).val W

/-- **The strong transformation identifying the strict diagram of finite étale restriction with
the finite étale restriction pseudofunctor.** This is the `comparison` field of
`Stacks.FundamentalGroup.FiniteEtaleColimitPresentation`. -/
def finiteEtaleRestrictionComparison :
    Pseudofunctor.StrongTrans (finiteEtaleRestrictionDiagram X Y).toPseudofunctor'
      (finiteEtaleRestrictionPseudofunctor X Y).val :=
  strictComparison X Y (finiteEtaleRestrictionPseudofunctor X Y).val

/-- The comparison is the chosen stage equivalence at every neighbourhood. This is the
`comparison_stage` field of `Stacks.FundamentalGroup.FiniteEtaleColimitPresentation`. -/
lemma finiteEtaleRestrictionComparison_stage (W : Neighborhood X Y) :
    (((finiteEtaleRestrictionComparison X Y).app ⟨W⟩) ≫
      eqToHom ((finiteEtaleRestrictionPseudofunctor X Y).property.choose W)).toFunctor =
      (finiteEtaleRestrictionStage X Y W).functor := by
  have h : eqToHom ((finiteEtaleRestrictionPseudofunctor X Y).property.choose W) =
      𝟙 ((finiteEtaleRestrictionPseudofunctor X Y).val.obj ⟨W⟩) := rfl
  rw [h]
  rfl

/-- **The strict presentation of finite étale restriction, granted its restriction cocone.**
The first four fields of `Stacks.FundamentalGroup.FiniteEtaleColimitPresentation` — the strict
diagram, the stage equivalences, the coherent comparison with the restriction pseudofunctor and
the identification of the comparison with the stage equivalences — are supplied by the
declarations above; this records that nothing else is needed from them, so that what remains of
the presentation is exactly a cocone on the strict diagram with vertex the finite étale covers
of the closed subscheme, together with its stagewise identification with base change. -/
def finiteEtaleColimitPresentationOfCocone
    (cocone : Limits.Cocone (finiteEtaleRestrictionDiagram X Y))
    (coconePointIso : cocone.pt ≅ Cat.of (FiniteEtaleOver Y.subscheme))
    (restriction : ∀ W : Neighborhood X Y,
      (finiteEtaleRestrictionStage X Y W).functor ⋙
          finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W) ≅
        (cocone.ι.app W).toFunctor ⋙ coconePointIso.hom.toFunctor) :
    FiniteEtaleColimitPresentation X Y where
  diagram := finiteEtaleRestrictionDiagram X Y
  stage := finiteEtaleRestrictionStage X Y
  comparison := finiteEtaleRestrictionComparison X Y
  comparison_stage := finiteEtaleRestrictionComparison_stage X Y
  cocone := cocone
  coconePointIso := coconePointIso
  restriction := restriction

end Stacks.FundamentalGroup

end
