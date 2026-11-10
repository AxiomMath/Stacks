module

public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckFunctorFrom
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentPseudofunctor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SheavesPseudofunctorBridge

/-!
# Coherence of the restriction transitions of a simplicial site (Stacks 09WF)

Stacks 09WF describes a sheaf on the total site of a simplicial site by its restrictions to the
components together with the transitions between them. For that family to be a *system* — a lax
section of the pseudofunctor of component categories — the transitions must be compatible with
the canonical comparisons of inverse images. There are two such compatibilities, one for the
unit comparison and one for the compositor. This file proves both of them.

The unit compatibility is proved first for the direct-image transition
`CategoryTheory.SimplicialSiteSituation.restrictTransition` against
`SimplicialSiteSituation.pushforwardId`, and then transported to the inverse-image transition
`SimplicialSiteSituation.fiberTransition` against
`SimplicialSiteSituation.canonicalIdentityComparison` through the topos adjunction of `f_𝟙`.

## Main results

* `CategoryTheory.Pseudofunctor.CoGrothendieck.ιNatTrans_id`,
  `CategoryTheory.Grothendieck.ιNatTrans_id`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.ιNatTrans_comp` and
  `CategoryTheory.Grothendieck.ιNatTrans_comp`: the Cartesian lifts of an
  identity base arrow, and of a composite base arrow, in terms of the unit and composition
  comparisons of the (co)Grothendieck construction. These are general facts about Mathlib's two
  Grothendieck constructions, with no site in them.
* `CategoryTheory.cocontinuousRestrictTransition_comp_pushforwardId`: the general cocontinuous
  ingredient of the unit law. If a cocontinuous site functor is the identity, then the transpose
  of the identity natural transformation cancels the identification of its direct image with the
  identity functor.
* `CategoryTheory.SimplicialSiteSituation.restrictTransition_id'`: the transition of the direct
  images attached to an identity simplex map is the inverse of `pushforwardId`.  This is the
  unit law of `...restrictTransition_id` solved for the transition.
* `CategoryTheory.SimplicialSiteSituation.fiberTransition_id`: the transition of the inverse
  images attached to an identity simplex map is `canonicalIdentityComparison`. This is the lax
  unity constraint of the system of restrictions of a total-site sheaf.
* `CategoryTheory.Adjunction.homEquiv_comp_rightAdjointUniq_hom_app`: transposing along one of
  two adjunctions with the same left adjoint, and then comparing the right adjoints, is
  transposing along the other. This is the general form of the compositor compatibility.
* `CategoryTheory.cocontinuousRestrictTransition_comp`: the general cocontinuous ingredient of
  the composition law, for the Kan-extension compositor `ranOpCompIso`.
* `CategoryTheory.cocontinuousRestrictTransition_comp_ofEq`: the same, with the composite site
  functor named by a variable and identified with the composite by a hypothesis, which is the
  form case (B) of the situation consumes.
* `CategoryTheory.SimplicialSiteSituation.restrictTransition_inl_comp` and
  `...restrictTransition_inr_comp`: the composition law for the direct-image transitions, in
  case (A) and in case (B) of the situation.
* `CategoryTheory.SimplicialSiteSituation.restrictTransition_comp'`: the composition law for the
  direct-image transitions, both cases in one theorem, solved for the transition of the
  composite.
* `CategoryTheory.SimplicialSiteSituation.fiberTransition_comp`: the transition of the inverse
  images attached to a composite simplex map is the composite of the two transitions, compared by
  `canonicalCompositionComparison`. This is the lax compositor constraint of the system of
  restrictions of a total-site sheaf.
* `CategoryTheory.SimplicialSiteSituation.total_hom_ext`: a morphism of sheaves on the total site
  is determined by its restrictions to the simplicial components.
* `CategoryTheory.SimplicialSiteSituation.restrict_map_totalHomOfFamily`: the morphism built from
  a compatible family of morphisms of the restrictions has that family as its restrictions.
* `CategoryTheory.SimplicialSiteSituation.restrictSystemFunctor_faithful` and
  `...restrictSystemFunctor_full`: the forward functor of the equivalence of Stacks 09WF is fully
  faithful.
* `CategoryTheory.SimplicialSiteSituation.system_naturality_id_app` and
  `...system_naturality_comp_app`: the two lax laws of an arbitrary system, read at the unique
  object of the terminal fibre.
* `CategoryTheory.SimplicialSiteSituation.homEquiv_canonicalCompositionComparison`: the transpose
  of a composite compared by the inverse-image compositor is the composite of the transposes
  compared by the direct-image compositor.
* `CategoryTheory.SimplicialSiteSituation.systemFibreTransition_id`,
  `...systemFibreTransition_comp`, `...systemDirectTransition_id` and
  `...systemDirectTransition_comp`: the unit and cocycle laws for the transitions of an arbitrary
  system, in inverse-image and in direct-image form.
* `CategoryTheory.SimplicialSiteSituation.pushforwardId_inl_inv_hom_app`,
  `...totalPseudofunctor_mapId_app` and `...totalPseudofunctor_mapComp_app`: in case (A) the
  direct-image unit comparison and the two comparisons of the total pseudofunctor are the
  transports along the identity and composition equalities of the cosimplicial diagram.
* `CategoryTheory.SimplicialSiteSituation.systemDirectTransition_rightOp_id` and
  `...systemDirectTransition_rightOp_comp`: those two laws in the form the contravariant
  Grothendieck construction asks for.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.restrictSystem`: the system of restrictions of a sheaf
  on the total site, as a lax section of `componentPseudofunctor`. Its two laws are the two
  compatibilities above.
* `CategoryTheory.SimplicialSiteSituation.restrictSystemFunctor`: the forward functor of the
  equivalence of Stacks 09WF, from sheaves on the total site to systems.
* `CategoryTheory.SimplicialSiteSituation.totalHomOfFamily`: the morphism of total-site sheaves
  determined by a family of morphisms of the restrictions which is compatible with the
  direct-image transitions.
* `CategoryTheory.SimplicialSiteSituation.systemSheaf`,
  `...systemFibreTransition` and `...systemDirectTransition`: the component sheaves of an
  arbitrary system and the transitions between them, in both forms.
* `CategoryTheory.SimplicialSiteSituation.systemPresheafInl`: in case (A), the presheaf on the
  total site underlying a system.
* `CategoryTheory.Grothendieck.functorFromOfEq`: a functor out of the covariant Grothendieck
  construction built from fibrewise data, with the unit and cocycle coherences stated through
  `CategoryTheory.Grothendieck.fib_map_id_eq` and `...fib_map_comp_eq`.
* `CategoryTheory.SimplicialSiteSituation.restrictPresentation`: a
  `SimplicialSheafPresentation`, all eight fields, on the single hypothesis that the system of
  restrictions is essentially surjective.

## Implementation notes

`restrictTransition`, `pushforwardId` and `pushforwardCompSymm` are each a single declaration
defined by a match on the case of the situation, so a statement about a general situation covers
both cases in one theorem and its proof splits. In case (A) the transition is restriction along
the Cartesian lift `(φ, 𝟙)` and the comparisons are Mathlib's
`Functor.sheafPushforwardContinuousId'` and `...Comp'`, so the identities reduce to equalities of
arrows of the total category. In case (B) the transition is the transpose of such a family under
the Kan-extension adjunction; for the unit law the general lemma takes the equality of site
functors as a hypothesis and substitutes it, which is what makes the transport an `Iso.refl` and
leaves a triangle identity, and for the composition law the compositor of the Kan extensions is
the comparison of the right adjoints of the two bracketings, so the transposes are related by
`Adjunction.homEquiv_comp_rightAdjointUniq_hom_app` and the naturality of a unit.

Every reduction of a situation-level statement to a general one goes through `dsimp only` on the
definitions involved, and from that point the goal is no longer type-correct at the `implicit`
transparency level, so `rw` and `simp only` stop firing: the finishing steps are therefore all
term-mode `Eq.trans`/`congrArg` chains, which elaborate at the default transparency. The one
place where an `eqToHom` has to be recognised as an identity is handled by K-like reduction, for
which `Category.comp_id` suffices as the right-hand side of an `Eq.trans`.

The two lemmas about `CategoryTheory.Grothendieck.ιNatTrans` of a composite are stated about the
fibre inclusion `CategoryTheory.Grothendieck.ι`, whose value on an object has to be unfolded to a
pair before a projection of it is type-correct. That unfolding is made available to the
elaborator by marking `CategoryTheory.Grothendieck.ι` `implicit_reducible` for the section that
contains them, which is the minimal measure: the alternative of relaxing the transparency
discipline wholesale is not needed, and no other constant has to be named.

The component categories of `componentPseudofunctor` are `AsSmall` of the categories of sheaves,
and the fibres of `terminalPseudofunctor` are the discrete category on `PUnit`, so every cell of
`restrictSystem` is a transition conjugated by `AsSmall` and evaluated at the unique object. The
conjugation is definitional but not syntactic, so each law is stated in the transition's own
spelling by a `change` and then is the corresponding law above; the universes of `AsSmall.up`
have to be written out in those `change`s, since nothing in the goal determines them.

Full faithfulness is proved against the *direct-image* transitions, not the inverse-image ones:
restriction along a cross-fibre arrow of the total category factors through the direct-image
transition, by `restrictTransition_inl_arrow` and `restrictTransition_inr_arrow`, so a family of
morphisms of the restrictions which commutes with those transitions is natural on the whole total
category. The modification law of a morphism of systems is an inverse-image statement, and the
topos adjunction of `f_φ` turns it into the direct-image one. Faithfulness needs only that every
object of the total category lies in one fibre, which is `inclusion_obj_totalObjFibre`.

The transitions of an arbitrary system are the input the inverse functor of the equivalence
needs, and they are read off in the direction opposite to the restrictions of a total-site
sheaf: there the direct-image law was proved first and transported to the inverse images, while a
system *gives* the inverse-image law, so the transport runs the other way. The bicategory `Cat`
is strict, and its strictness is usable as a rewrite here: `Bicategory.Strict.associator_eqToIso`
is what reduces the lax functoriality law to the three-factor identity, and the residual
whiskering of an identity cell is discharged in term mode.

The presheaf underlying a system is built with `Pseudofunctor.CoGrothendieck.functorFrom` at the
target category `(Type u)ᵒᵖ`, so that `Functor.leftOp` turns the resulting functor out of the
total category into a presheaf on it. In that target the three laws read with their factors in
the opposite order, and `NatTrans.rightOp` carries the direct-image transitions into the
`hom` family the construction wants. The two coherence hypotheses are then exactly the unit and
cocycle laws of the direct-image transitions, compared with the unit and compositor of the total
pseudofunctor; in case (A) all four of those are transports along equalities of the cosimplicial
diagram, so the comparison is an equality of `eqToHom`s on sections.

Case (B) needs a functor out of Mathlib's covariant `Grothendieck` construction, and
`CategoryTheory.Grothendieck.functorFrom` cannot be used for it: the types of its two coherence
hypotheses mention private auxiliary proofs of the module that defines it, so an application of
it inside an exposed definition of another module is rejected by the kernel. `functorFromOfEq`
is the same construction with those two equalities named, and its coherence proofs need no
transparency option: the residues are `eqToHom` cancellations, discharged by
`eqToHom_comp_map_eqToHom` in term mode.

Full faithfulness is what makes the presentation a one-hypothesis statement: with
`restrictSystemFunctor` full and faithful, essential surjectivity turns it into an equivalence,
and that equivalence has the actual restrictions as its components, so the two
component-restriction fields of a presentation are the identity and the unit laws of
composition. The whole remaining content of the lemma is therefore the single goal
`(restrictSystemFunctor S).EssSurj`, which is the descent construction.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Functor Opposite

universe v₁ u₁ v₂ u₂ v u

namespace CategoryTheory

/-! ### The Cartesian lifts of an identity base arrow -/

namespace Pseudofunctor.CoGrothendieck

/-- The Cartesian lift of an identity base arrow is the fibre inclusion applied to the unit
comparison of the pseudofunctor. -/
theorem ιNatTrans_id {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) (R : 𝒮) (a : F.obj ⟨op R⟩) :
    (ιNatTrans F (𝟙 R)).app a =
      (ι F R).map ((F.mapId ⟨op R⟩).hom.toNatTrans.app a) :=
  Hom.ext _ _ rfl
    ((Cat.Hom.hom_inv_id_toNatTrans_app (F.mapId ⟨op R⟩) a).symm.trans
      (Category.comp_id _).symm)

/-- The Cartesian lift of a composite base arrow factors through the fibre inclusion applied to
the composition comparison of the pseudofunctor, followed by the two Cartesian lifts. -/
theorem ιNatTrans_comp {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T)
    (a : F.obj ⟨op T⟩) :
    (ιNatTrans F (f ≫ g)).app a =
      (ι F R).map ((F.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app a) ≫
        (ιNatTrans F f).app ((F.map g.op.toLoc).toFunctor.obj a) ≫
          (ιNatTrans F g).app a := by
  have hmid : (F.map f.op.toLoc).toFunctor.map (𝟙 ((F.map g.op.toLoc).toFunctor.obj a)) ≫
        (F.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app a =
      (F.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app a := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc, ι_map_comp_ιNatTrans_app]
  refine Hom.ext _ _ rfl ?_
  refine Eq.trans ?_ (Category.comp_id _).symm
  refine Eq.trans ?_ (congrArg
    (fun t => (F.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app a ≫ t) hmid).symm
  exact (Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp g.op.toLoc f.op.toLoc) a).symm

end Pseudofunctor.CoGrothendieck

namespace Grothendieck

/-- The family of arrows attached to an identity base arrow is the transport along the unit
equality of the diagram of categories. -/
theorem ιNatTrans_id {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Cat.{v₂, u₂}} (X : C) :
    ιNatTrans (F := F) (𝟙 X) =
      eqToHom (by simp only [CategoryTheory.Functor.map_id]; rfl) := by
  apply NatTrans.ext
  funext d
  rw [eqToHom_app, Grothendieck.eqToHom_eq]
  refine Grothendieck.ext _ _ ?_ ?_
  · exact (eqToHom_refl X rfl).symm
  · exact (Category.comp_id _).trans rfl

section

attribute [local implicit_reducible] CategoryTheory.Grothendieck.ι

/-- The family of arrows attached to a composite base arrow is the composite of the two families,
transported along the composition equality of the diagram of categories.  This is the `hom_comp`
coherence that `CategoryTheory.Grothendieck.functorFrom` asks for. -/
theorem ιNatTrans_comp {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Cat.{v₂, u₂}} {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ιNatTrans (F := F) (f ≫ g) =
      ιNatTrans f ≫ Functor.whiskerLeft (F.map f).toFunctor (ιNatTrans g) ≫
        eqToHom (by simp only [CategoryTheory.Functor.map_comp]; rfl) := by
  apply NatTrans.ext
  funext d
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, Grothendieck.eqToHom_eq]
  refine Grothendieck.ext _ _ ?_ ?_
  · exact (congrArg (fun t => f ≫ t) (Category.comp_id g)).symm
  · simp only [Grothendieck.ι, Functor.comp_obj, Grothendieck.ιNatTrans, eqToHom_refl,
      Grothendieck.comp_base, Category.comp_id, Grothendieck.comp_fiber,
      CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor, Functor.id_obj,
      CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor, eqToHom_naturality,
      eqToHom_naturality_assoc, eqToHom_trans]
    exact (eqToHom_trans _ _).symm

end

end Grothendieck

/-! ### The cocontinuous ingredient -/

/-- The general cocontinuous ingredient of the identity law. If a cocontinuous site functor `w`
is the identity, then the transpose along the Kan-extension adjunction of the transport
`incl ⟶ w ⋙ incl` cancels the identification of the direct image along `w` with the identity
functor. -/
theorem cocontinuousRestrictTransition_comp_pushforwardId
    {C : Type u} [SmallCategory C] {T : Type u} [SmallCategory T]
    (J : GrothendieckTopology C) (JT : GrothendieckTopology T)
    {w : C ⥤ C} [w.IsCocontinuous J J]
    {incl : C ⥤ T} [incl.IsContinuous J JT]
    {ν : incl ⟶ w ⋙ incl}
    (hw : w = 𝟭 C) (hincl : incl = w ⋙ incl) (hν : ν = eqToHom hincl)
    (F : Sheaf JT (Type u)) :
    (w.op.ranAdjunction (Type u)).homEquiv _ _
          (Functor.whiskerRight (NatTrans.op ν) F.obj) ≫
        ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J J hw ≪≫
          (((𝟭 C).sheafAdjunctionCocontinuous (Type u) J J).ofNatIsoLeft
            (Functor.sheafPushforwardContinuousId (Type u) J)).rightAdjointUniq
            Adjunction.id).hom.app
        ((incl.sheafPushforwardContinuous (Type u) J JT).obj F)).hom = 𝟙 _ := by
  subst hw
  subst hν
  have h : hincl = rfl := rfl
  subst h
  have hid : Functor.whiskerRight (NatTrans.op
        (eqToHom (rfl : incl = 𝟭 C ⋙ incl) : incl ⟶ 𝟭 C ⋙ incl)) F.obj
      = 𝟙 (incl.op ⋙ F.obj) :=
    (congrArg (fun t => Functor.whiskerRight t F.obj) (NatTrans.op_id incl)).trans
      (Functor.whiskerRight_id' F.obj)
  have hunit : (((𝟭 C).op.ranAdjunction (Type u)).homEquiv (incl.op ⋙ F.obj)
        (incl.op ⋙ F.obj)) (𝟙 (incl.op ⋙ F.obj)) =
      ((𝟭 C).op.ranAdjunction (Type u)).unit.app (incl.op ⋙ F.obj) :=
    Adjunction.homEquiv_id _ _
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl, hid]
  refine (congrArg (fun t => t ≫ ((Iso.refl
      ((𝟭 C).sheafPushforwardCocontinuous (Type u) J J) ≪≫
      (((𝟭 C).sheafAdjunctionCocontinuous (Type u) J J).ofNatIsoLeft
        (Functor.sheafPushforwardContinuousId (Type u) J)).rightAdjointUniq
        Adjunction.id).hom.app
      ((incl.sheafPushforwardContinuous (Type u) J JT).obj F)).hom) hunit).trans ?_
  rw [Iso.refl_trans, rightAdjointUniq_sheafAdjunctionCocontinuous_id_hom_app_hom,
    Adjunction.rightAdjointUniq_id_hom_app]
  exact Adjunction.left_triangle_components ((𝟭 C).op.ranAdjunction (Type u))
    (incl.op ⋙ F.obj)

/-! ### The cocontinuous ingredient of the composition law -/

/-- Transposing a morphism along one of two adjunctions with the same left adjoint and then
comparing the two right adjoints is transposing it along the other adjunction. -/
theorem Adjunction.homEquiv_comp_rightAdjointUniq_hom_app {C D : Type*} [Category* C]
    [Category* D] {L : C ⥤ D} {R R' : D ⥤ C} (adj1 : L ⊣ R) (adj2 : L ⊣ R') (X : C) (Y : D)
    (f : L.obj X ⟶ Y) :
    adj1.homEquiv X Y f ≫ (Adjunction.rightAdjointUniq adj1 adj2).hom.app Y =
      adj2.homEquiv X Y f := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (Adjunction.rightAdjointUniq adj1 adj2).hom.naturality f, ← Category.assoc,
    Adjunction.unit_rightAdjointUniq_hom_app]

/-- The general cocontinuous ingredient of the composition law. The transpose of a composite of
two transports `i₀ ⟶ u ⋙ i₁ ⟶ u ⋙ v ⋙ i₂` along the Kan-extension adjunction of `u ⋙ v` is the
composite of the two transposes, compared by the compositor of the direct images along `u` and
along `v`. -/
theorem cocontinuousRestrictTransition_comp
    {C₀ : Type u} [SmallCategory C₀] {C₁ : Type u} [SmallCategory C₁] {C₂ : Type u}
    [SmallCategory C₂] {T : Type u} [SmallCategory T]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
    (JT : GrothendieckTopology T)
    {u : C₀ ⥤ C₁} {v : C₁ ⥤ C₂} [u.IsCocontinuous J₀ J₁] [v.IsCocontinuous J₁ J₂]
    {i₀ : C₀ ⥤ T} {i₁ : C₁ ⥤ T} {i₂ : C₂ ⥤ T}
    [i₀.IsContinuous J₀ JT] [i₁.IsContinuous J₁ JT] [i₂.IsContinuous J₂ JT]
    (νu : i₀ ⟶ u ⋙ i₁) (νv : i₁ ⟶ v ⋙ i₂) (F : Sheaf JT (Type u)) :
    ((u ⋙ v).op.ranAdjunction (Type u)).homEquiv (i₂.op ⋙ F.obj) (i₀.op ⋙ F.obj)
        (Functor.whiskerRight (NatTrans.op (νu ≫ Functor.whiskerLeft u νv)) F.obj) =
      (v.op.ranAdjunction (Type u)).homEquiv (i₂.op ⋙ F.obj) (i₁.op ⋙ F.obj)
          (Functor.whiskerRight (NatTrans.op νv) F.obj) ≫
        v.op.ran.map ((u.op.ranAdjunction (Type u)).homEquiv (i₁.op ⋙ F.obj) (i₀.op ⋙ F.obj)
            (Functor.whiskerRight (NatTrans.op νu) F.obj)) ≫
          ((sheafPushforwardCocontinuousCompIso J₀ J₁ J₂ u v).inv.app
            ((i₀.sheafPushforwardContinuous (Type u) J₀ JT).obj F)).hom := by
  have hnu : Functor.whiskerRight (NatTrans.op (νu ≫ Functor.whiskerLeft u νv)) F.obj =
      Functor.whiskerLeft u.op (Functor.whiskerRight (NatTrans.op νv) F.obj) ≫
        Functor.whiskerRight (NatTrans.op νu) F.obj := by
    apply NatTrans.ext
    funext W
    simp [← CategoryTheory.Functor.map_comp, ← op_comp]
  have hU : ((u.op.ranAdjunction (Type u)).homEquiv (v.op ⋙ i₂.op ⋙ F.obj) (i₀.op ⋙ F.obj))
        (Functor.whiskerRight (NatTrans.op (νu ≫ Functor.whiskerLeft u νv)) F.obj) =
      Functor.whiskerRight (NatTrans.op νv) F.obj ≫
        ((u.op.ranAdjunction (Type u)).homEquiv (i₁.op ⋙ F.obj) (i₀.op ⋙ F.obj))
          (Functor.whiskerRight (NatTrans.op νu) F.obj) := by
    rw [hnu, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      CategoryTheory.Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact ((u.op.ranAdjunction (Type u)).unit.naturality
      (Functor.whiskerRight (NatTrans.op νv) F.obj)).symm
  have key : (((u ⋙ v).op.ranAdjunction (Type u)).homEquiv (i₂.op ⋙ F.obj) (i₀.op ⋙ F.obj))
          (Functor.whiskerRight (NatTrans.op (νu ≫ Functor.whiskerLeft u νv)) F.obj) ≫
        (ranOpCompIso u v).hom.app (i₀.op ⋙ F.obj) =
      ((v.op.ranAdjunction (Type u)).homEquiv (i₂.op ⋙ F.obj) (i₁.op ⋙ F.obj))
          (Functor.whiskerRight (NatTrans.op νv) F.obj) ≫
        v.op.ran.map (((u.op.ranAdjunction (Type u)).homEquiv (i₁.op ⋙ F.obj)
          (i₀.op ⋙ F.obj)) (Functor.whiskerRight (NatTrans.op νu) F.obj)) := by
    rw [ranOpCompIso_def]
    simp only [Functor.op_comp_eq]
    rw [Adjunction.homEquiv_comp_rightAdjointUniq_hom_app, Adjunction.comp_homEquiv]
    refine Eq.trans (congrArg ((v.op.ranAdjunction (Type u)).homEquiv (i₂.op ⋙ F.obj)
      (u.op.ran.obj (i₀.op ⋙ F.obj))) hU) ?_
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [sheafPushforwardCocontinuousCompIso_inv_app_hom]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact (Iso.eq_comp_inv ((ranOpCompIso u v).app (i₀.op ⋙ F.obj))).mpr key

/-- The transported form of `CategoryTheory.cocontinuousRestrictTransition_comp`: the composite
site functor is named by a variable `w`, identified with `u ⋙ v` by a hypothesis, and the
transport of the direct images along that identification appears as the last factor. This is the
form a situation-level composition law consumes, because there the composite transition is the
transpose along the Kan extension of the single functor `w`. -/
theorem cocontinuousRestrictTransition_comp_ofEq
    {C₀ : Type u} [SmallCategory C₀] {C₁ : Type u} [SmallCategory C₁] {C₂ : Type u}
    [SmallCategory C₂] {T : Type u} [SmallCategory T]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
    (JT : GrothendieckTopology T)
    {u : C₀ ⥤ C₁} {v : C₁ ⥤ C₂} {w : C₀ ⥤ C₂}
    [u.IsCocontinuous J₀ J₁] [v.IsCocontinuous J₁ J₂] [w.IsCocontinuous J₀ J₂]
    [(u ⋙ v).IsCocontinuous J₀ J₂]
    {i₀ : C₀ ⥤ T} {i₁ : C₁ ⥤ T} {i₂ : C₂ ⥤ T}
    [i₀.IsContinuous J₀ JT] [i₁.IsContinuous J₁ JT] [i₂.IsContinuous J₂ JT]
    (νu : i₀ ⟶ u ⋙ i₁) (νv : i₁ ⟶ v ⋙ i₂) {νw : i₀ ⟶ w ⋙ i₂}
    (hw : u ⋙ v = w)
    (hν : νw = νu ≫ Functor.whiskerLeft u νv ≫
      eqToHom (congrArg (fun k : C₀ ⥤ C₂ => k ⋙ i₂) hw))
    (F : Sheaf JT (Type u)) :
    (w.op.ranAdjunction (Type u)).homEquiv (i₂.op ⋙ F.obj) (i₀.op ⋙ F.obj)
        (Functor.whiskerRight (NatTrans.op νw) F.obj) =
      (v.op.ranAdjunction (Type u)).homEquiv (i₂.op ⋙ F.obj) (i₁.op ⋙ F.obj)
          (Functor.whiskerRight (NatTrans.op νv) F.obj) ≫
        v.op.ran.map ((u.op.ranAdjunction (Type u)).homEquiv (i₁.op ⋙ F.obj) (i₀.op ⋙ F.obj)
            (Functor.whiskerRight (NatTrans.op νu) F.obj)) ≫
          (((sheafPushforwardCocontinuousCompIso J₀ J₁ J₂ u v).inv.app
                ((i₀.sheafPushforwardContinuous (Type u) J₀ JT).obj F)).hom ≫
            ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J₀ J₂
              hw).hom.app
                ((i₀.sheafPushforwardContinuous (Type u) J₀ JT).obj F)).hom) := by
  subst hw
  subst hν
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]
  rw [eqToHom_refl _ rfl, Category.comp_id]
  simp only [Iso.refl_hom, NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom]
  exact cocontinuousRestrictTransition_comp J₀ J₁ J₂ JT νu νv F

/-! ### The identity law for a simplicial-site situation -/

namespace SimplicialSiteSituation

/-- In case (A), the Cartesian lift attached to an identity simplex map is the fibre inclusion
applied to the transport along the unit equality of the cosimplicial diagram. -/
theorem continuousInclusionTransition_id (C : SimplicialSite.{u}) (n : SimplexCategory)
    (V : C.underlying.obj n) :
    (continuousInclusionTransition C (𝟙 n)).app V =
      (Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)).map
        ((eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_id n))).hom.app V) := by
  refine (Pseudofunctor.CoGrothendieck.ιNatTrans_id C.totalPseudofunctor (op n) V).trans ?_
  refine congrArg (Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)).map ?_
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapId, eqToIso.hom,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  rfl

/-- **Stacks 09WF.** The direct-image transition attached to an identity simplex map is the
inverse of the unit comparison `pushforwardId`. -/
theorem restrictTransition_id' (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (F : Sheaf S.totalTopology (Type u)) :
    (S.restrictTransition (𝟙 n)).app F
      = (S.pushforwardId n).inv.app ((S.restrict n).obj F) := by
  rcases S with ⟨C | C⟩
  · have := (C.isMorphismOfSites (𝟙 n)).isContinuous
    dsimp only [restrictTransition, pushforwardId, _root_.id]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    refine Eq.trans ?_ (Functor.sheafPushforwardContinuousId'_inv_app_hom_app
      (eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_id n))) (Type u)
      ((C.coverage n).toGrothendieck) _ V).symm
    exact congrArg (fun k => F.obj.map (Quiver.Hom.op k))
      (continuousInclusionTransition_id C n (unop V))
  · have hco : (C.underlying.map (𝟙 n).op).toFunctor.IsCocontinuous
        (topologyOfCoverings (C.coverage (op n)))
        (topologyOfCoverings (C.coverage (op n))) := C.isCocontinuous (𝟙 n).op
    have hcont : (Grothendieck.ι C.underlying (op n)).IsContinuous
        (topologyOfCoverings (C.coverage (op n)))
        (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
      componentFunctor_isContinuous (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
    refine (Iso.comp_hom_eq_id ((pushforwardId ⟨Sum.inr C⟩ n).app _)).mp ?_
    dsimp only [restrictTransition, pushforwardId, _root_.id, transitionMorphism, gStar,
      restrict, inclusion, componentFunctor, component, componentTopology, totalTopology,
      totalCategory]
    apply Sheaf.hom_ext
    have hincl : Grothendieck.ι C.underlying (op n) =
        (C.underlying.map (𝟙 n).op).toFunctor ⋙ Grothendieck.ι C.underlying (op n) :=
      congrArg (fun G : C.underlying.obj (op n) ⟶ C.underlying.obj (op n) =>
          G.toFunctor ⋙ Grothendieck.ι C.underlying (op n))
        (C.underlying.map_id (op n)).symm
    exact cocontinuousRestrictTransition_comp_pushforwardId
      (topologyOfCoverings (C.coverage (op n)))
      (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (w := (C.underlying.map (𝟙 n).op).toFunctor)
      (incl := Grothendieck.ι C.underlying (op n))
      (ν := Grothendieck.ιNatTrans (𝟙 n).op)
      (congrArg Cat.Hom.toFunctor (C.underlying.map_id (op n)))
      hincl (Grothendieck.ιNatTrans_id (op n)) F

/-- **Stacks 09WF.** The inverse-image transition attached to an identity simplex map is the
canonical identification of `f_𝟙⁻¹` with the identity functor. This is the lax unity constraint
for the system of restrictions of a sheaf on the total site. -/
theorem fiberTransition_id (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (F : Sheaf S.totalTopology (Type u)) :
    (fiberTransition S (𝟙 n)).app F =
      (canonicalIdentityComparison S n).hom.app ((S.restrict n).obj F) := by
  refine ((S.transitionMorphism (𝟙 n)).adj.homEquiv _ _).injective ?_
  exact (fiberTransition_adj S (𝟙 n) F).trans
    ((restrictTransition_id' S n F).trans
      (homEquiv_canonicalIdentityComparison_hom_app S n _).symm)

/-! ### The composition law in case (A) -/

/-- In case (A), the Cartesian lift attached to a composite simplex map factors through the fibre
inclusion applied to the transport along the composition equality of the cosimplicial diagram,
followed by the two Cartesian lifts. -/
theorem continuousInclusionTransition_comp (C : SimplicialSite.{u})
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (V : C.underlying.obj l) :
    (continuousInclusionTransition C (ψ ≫ φ)).app V =
      (Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)).map
          ((eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ φ)).symm).inv.app V) ≫
        (continuousInclusionTransition C φ).app ((C.underlying.map ψ).toFunctor.obj V) ≫
          (continuousInclusionTransition C ψ).app V := by
  refine (Pseudofunctor.CoGrothendieck.ιNatTrans_comp C.totalPseudofunctor φ.op ψ.op V).trans ?_
  refine congrArg (fun t =>
    (Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)).map t ≫
      (continuousInclusionTransition C φ).app ((C.underlying.map ψ).toFunctor.obj V) ≫
        (continuousInclusionTransition C ψ).app V) ?_
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapComp, eqToIso.hom,
    eqToIso.inv, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  rfl

/-- In case (A), the direct-image compositor acts on sections as restriction along the transport
of the composition equality of the cosimplicial diagram. -/
theorem pushforwardCompSymm_inl_hom_app_hom_app (C : SimplicialSite.{u})
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : Sheaf (C.coverage n).toGrothendieck (Type u)) (V : (C.underlying.obj l)ᵒᵖ) :
    ((pushforwardCompSymm ⟨Sum.inl C⟩ ψ φ).hom.app X).hom.app V =
      X.obj.map ((eqToIso
        (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ φ)).symm).inv.app (unop V)).op := by
  have := (C.isMorphismOfSites ψ).isContinuous
  have := (C.isMorphismOfSites φ).isContinuous
  have := (C.isMorphismOfSites (ψ ≫ φ)).isContinuous
  dsimp only [pushforwardCompSymm, _root_.id]
  exact Functor.sheafPushforwardContinuousComp'_hom_app_hom_app
    (eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ φ)).symm) (Type u)
    ((C.coverage l).toGrothendieck) ((C.coverage m).toGrothendieck)
    ((C.coverage n).toGrothendieck) X V

/-- **Stacks 09WF**, case (A). The direct-image transition attached to a composite simplex map is
the composite of the two transitions, compared by the direct-image compositor
`pushforwardCompSymm`. -/
theorem restrictTransition_inl_comp (C : SimplicialSite.{u}) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) :
    (restrictTransition ⟨Sum.inl C⟩ (ψ ≫ φ)).app F =
      (restrictTransition ⟨Sum.inl C⟩ ψ).app F ≫
        (transitionMorphism ⟨Sum.inl C⟩ ψ).pushforward.map
            ((restrictTransition ⟨Sum.inl C⟩ φ).app F) ≫
          (pushforwardCompSymm ⟨Sum.inl C⟩ ψ φ).hom.app
            ((restrict ⟨Sum.inl C⟩ n).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  refine (restrictTransition_inl_app C (ψ ≫ φ) F (unop V)).trans ?_
  refine (congrArg (fun k => F.obj.map (Quiver.Hom.op k))
    (continuousInclusionTransition_comp C ψ φ (unop V))).trans ?_
  have h1 : ((restrictTransition (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ).app F).hom.app V =
      F.obj.map ((continuousInclusionTransition C ψ).app (unop V)).op :=
    restrictTransition_inl_app C ψ F (unop V)
  have h2 : ((transitionMorphism (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ).pushforward.map
        ((restrictTransition ⟨Sum.inl C⟩ φ).app F)).hom.app V =
      F.obj.map ((continuousInclusionTransition C φ).app
        ((C.underlying.map ψ).toFunctor.obj (unop V))).op :=
    restrictTransition_inl_app C φ F ((C.underlying.map ψ).toFunctor.obj (unop V))
  have h3 : ((pushforwardCompSymm (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ φ).hom.app
        ((restrict ⟨Sum.inl C⟩ n).obj F)).hom.app V =
      F.obj.map ((Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)).map
        ((eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ φ)).symm).inv.app
          (unop V))).op :=
    pushforwardCompSymm_inl_hom_app_hom_app C ψ φ ((restrict ⟨Sum.inl C⟩ n).obj F) V
  have hsplit : ∀ {W X Y Z : (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalCategory}
      (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z),
      F.obj.map (a ≫ b ≫ c).op =
        F.obj.map c.op ≫ F.obj.map b.op ≫ F.obj.map a.op := by
    intro W X Y Z a b c
    simp
  rw [h1, h2, h3]
  exact hsplit _ _ _

/-! ### The composition law in case (B) -/

/-- **Stacks 09WF**, case (B). The direct-image transition attached to a composite simplex map is
the composite of the two transitions, compared by the direct-image compositor
`pushforwardCompSymm`. -/
theorem restrictTransition_inr_comp (C : CocontinuousSimplicialSite.{u})
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) :
    (restrictTransition ⟨Sum.inr C⟩ (ψ ≫ φ)).app F =
      (restrictTransition ⟨Sum.inr C⟩ ψ).app F ≫
        (transitionMorphism ⟨Sum.inr C⟩ ψ).pushforward.map
            ((restrictTransition ⟨Sum.inr C⟩ φ).app F) ≫
          (pushforwardCompSymm ⟨Sum.inr C⟩ ψ φ).hom.app
            ((restrict ⟨Sum.inr C⟩ n).obj F) := by
  have hψ : (C.underlying.map ψ.op).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op l))) :=
    C.isCocontinuous ψ.op
  have hφ : (C.underlying.map φ.op).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (op n))) (topologyOfCoverings (C.coverage (op m))) :=
    C.isCocontinuous φ.op
  have hψφ : (C.underlying.map (ψ ≫ φ).op).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (op n))) (topologyOfCoverings (C.coverage (op l))) :=
    C.isCocontinuous (ψ ≫ φ).op
  have hcomp : ((C.underlying.map φ.op).toFunctor ⋙
        (C.underlying.map ψ.op).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage (op n))) (topologyOfCoverings (C.coverage (op l))) :=
    isCocontinuous_comp _ _ (topologyOfCoverings (C.coverage (op n)))
      (topologyOfCoverings (C.coverage (op m)))
  have hl : (Grothendieck.ι C.underlying (op l)).IsContinuous
      (topologyOfCoverings (C.coverage (op l)))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    componentFunctor_isContinuous (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) l
  have hm : (Grothendieck.ι C.underlying (op m)).IsContinuous
      (topologyOfCoverings (C.coverage (op m)))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    componentFunctor_isContinuous (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m
  have hn : (Grothendieck.ι C.underlying (op n)).IsContinuous
      (topologyOfCoverings (C.coverage (op n)))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    componentFunctor_isContinuous (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  dsimp only [restrictTransition, pushforwardCompSymm, _root_.id, transitionMorphism, gStar,
    restrict, inclusion, componentFunctor, component, componentTopology, totalTopology,
    totalCategory]
  apply Sheaf.hom_ext
  exact cocontinuousRestrictTransition_comp_ofEq
    (topologyOfCoverings (C.coverage (op n))) (topologyOfCoverings (C.coverage (op m)))
    (topologyOfCoverings (C.coverage (op l)))
    (SimplicialCoverings.totalTopology C.underlying C.coverage)
    (u := (C.underlying.map φ.op).toFunctor) (v := (C.underlying.map ψ.op).toFunctor)
    (w := (C.underlying.map (ψ ≫ φ).op).toFunctor)
    (i₀ := Grothendieck.ι C.underlying (op n)) (i₁ := Grothendieck.ι C.underlying (op m))
    (i₂ := Grothendieck.ι C.underlying (op l))
    (Grothendieck.ιNatTrans φ.op) (Grothendieck.ιNatTrans ψ.op)
    (νw := Grothendieck.ιNatTrans (ψ ≫ φ).op)
    (congrArg Cat.Hom.toFunctor (C.underlying.map_comp φ.op ψ.op)).symm
    (Grothendieck.ιNatTrans_comp φ.op ψ.op) F

/-- **Stacks 09WF.** The direct-image transition attached to a composite simplex map is the
composite of the two transitions, compared by the direct-image compositor `pushforwardCompSymm`.
Both cases of the situation, in one theorem. -/
theorem restrictTransition_comp' (S : SimplicialSiteSituation.{u}) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (F : Sheaf S.totalTopology (Type u)) :
    (S.restrictTransition (ψ ≫ φ)).app F =
      (S.restrictTransition ψ).app F ≫
        (S.transitionMorphism ψ).pushforward.map ((S.restrictTransition φ).app F) ≫
          (S.pushforwardCompSymm ψ φ).hom.app ((S.restrict n).obj F) := by
  rcases S with ⟨C | C⟩
  · exact restrictTransition_inl_comp C ψ φ F
  · exact restrictTransition_inr_comp C ψ φ F

/-- Transposing a composite of two inverse-image arrows, compared by
`canonicalCompositionComparison`, gives the composite of the two transposes. -/
private theorem homEquiv_comp_canonicalCompositionComparison (S : SimplicialSiteSituation.{u})
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    {A : Sheaf (S.componentTopology l) (Type u)}
    {B : Sheaf (S.componentTopology m) (Type u)}
    {D : Sheaf (S.componentTopology n) (Type u)}
    (a : (S.transitionMorphism ψ).inverseImage.obj A ⟶ B)
    (b : (S.transitionMorphism φ).inverseImage.obj B ⟶ D) :
    (S.transitionMorphism (ψ ≫ φ)).adj.homEquiv A D
        ((canonicalCompositionComparison S ψ φ).hom.app A ≫
          (S.transitionMorphism φ).inverseImage.map a ≫ b) =
      (S.transitionMorphism ψ).adj.homEquiv A B a ≫
        (S.transitionMorphism ψ).pushforward.map
            ((S.transitionMorphism φ).adj.homEquiv B D b) ≫
          (S.pushforwardCompSymm ψ φ).hom.app D := by
  have hconj : conjugateEquiv
        ((S.transitionMorphism ψ).adj.comp (S.transitionMorphism φ).adj)
        (S.transitionMorphism (ψ ≫ φ)).adj
        ((canonicalCompositionComparison S ψ φ).hom) =
      (S.pushforwardCompSymm ψ φ).hom := by
    rw [canonicalCompositionComparison_eq_leftAdjointCompIso, Iso.symm_hom]
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have hunit := unit_conjugateEquiv
    ((S.transitionMorphism ψ).adj.comp (S.transitionMorphism φ).adj)
    (S.transitionMorphism (ψ ≫ φ)).adj
    ((canonicalCompositionComparison S ψ φ).hom) A
  rw [hconj] at hunit
  have hkey : ((S.transitionMorphism ψ).adj.comp (S.transitionMorphism φ).adj).homEquiv A D
        ((S.transitionMorphism φ).inverseImage.map a ≫ b) =
      (S.transitionMorphism ψ).adj.homEquiv A B a ≫
        (S.transitionMorphism ψ).pushforward.map
          ((S.transitionMorphism φ).adj.homEquiv B D b) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← reassoc_of% hunit,
    ← (S.pushforwardCompSymm ψ φ).hom.naturality _]
  rw [Adjunction.homEquiv_unit] at hkey
  exact (congrArg (fun t => t ≫ (S.pushforwardCompSymm ψ φ).hom.app D) hkey).trans
    (Category.assoc _ _ _)

/-- **Stacks 09WF.** The inverse-image transition attached to a composite simplex map is the
composite of the two transitions, compared by `canonicalCompositionComparison`. This is the lax
compositor constraint for the system of restrictions of a sheaf on the total site. -/
theorem fiberTransition_comp (S : SimplicialSiteSituation.{u}) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (F : Sheaf S.totalTopology (Type u)) :
    (fiberTransition S (ψ ≫ φ)).app F =
      (canonicalCompositionComparison S ψ φ).hom.app ((S.restrict l).obj F) ≫
        (S.transitionMorphism φ).inverseImage.map ((fiberTransition S ψ).app F) ≫
          (fiberTransition S φ).app F := by
  refine ((S.transitionMorphism (ψ ≫ φ)).adj.homEquiv _ _).injective ?_
  rw [fiberTransition_adj, restrictTransition_comp',
    homEquiv_comp_canonicalCompositionComparison, fiberTransition_adj, fiberTransition_adj]

/-! ### The system of restrictions of a total-site sheaf -/

/-- **Stacks 09WF.** The system of restrictions of a sheaf on the total site: its restriction to
every simplicial degree, with the inverse-image transitions as the lax naturality cells. The lax
unity and functoriality laws are `fiberTransition_id` and `fiberTransition_comp`. -/
noncomputable def restrictSystem (S : SimplicialSiteSituation.{u})
    (F : Sheaf S.totalTopology (Type u)) :
    SimplicialSheafSystem (componentPseudofunctor S) where
  app n := ((Functor.const _).obj (AsSmall.up.obj ((S.restrict n.as).obj F))).toCatHom
  naturality f :=
    { toNatTrans :=
        { app := fun _ => AsSmall.up.map ((fiberTransition S f.as).app F)
          naturality := fun _ _ _ => by
            change AsSmall.up.map ((S.transitionMorphism f.as).inverseImage.map (𝟙 _)) ≫ _
              = _ ≫ 𝟙 _
            rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
            exact (Category.id_comp _).trans (Category.comp_id _).symm } }
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    cat_disch
  naturality_id a := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change AsSmall.up.{u, u + 1, u + 1}.map
          ((canonicalIdentityComparison S a.as).inv.app ((S.restrict a.as).obj F)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map ((S.fiberTransition (𝟙 a.as)).app F) =
      𝟙 (AsSmall.up.{u, u + 1, u + 1}.obj ((S.restrict a.as).obj F))
    rw [← CategoryTheory.Functor.map_comp, fiberTransition_id, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    rfl
  naturality_comp := by
    intro a _ _ f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change AsSmall.up.{u, u + 1, u + 1}.map
          ((canonicalCompositionComparison S f.as g.as).inv.app ((S.restrict a.as).obj F)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map ((S.fiberTransition (f.as ≫ g.as)).app F) =
      AsSmall.up.{u, u + 1, u + 1}.map
          ((S.transitionMorphism g.as).inverseImage.map ((S.fiberTransition f.as).app F)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map ((S.fiberTransition g.as).app F)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      fiberTransition_comp, Iso.inv_hom_id_app_assoc]

/-- **Stacks 09WF.** The forward functor of the equivalence of Lemma 09WF: a sheaf on the total
site goes to its system of restrictions, and a morphism of sheaves to the modification whose
components are the restrictions of that morphism. -/
noncomputable def restrictSystemFunctor (S : SimplicialSiteSituation.{u}) :
    Sheaf S.totalTopology (Type u) ⥤ SimplicialSheafSystem (componentPseudofunctor S) where
  obj F := restrictSystem S F
  map {F G} α :=
    ⟨{ app := fun n =>
        { toNatTrans :=
            { app := fun _ => AsSmall.up.map ((S.restrict n.as).map α)
              naturality := fun _ _ _ =>
                (Category.id_comp _).trans (Category.comp_id _).symm } }
       naturality := fun {a b} f => by
         apply Cat.Hom₂.ext
         apply NatTrans.ext
         funext x
         change AsSmall.up.{u, u + 1, u + 1}.map
               ((S.transitionMorphism f.as).inverseImage.map ((S.restrict a.as).map α)) ≫
             AsSmall.up.{u, u + 1, u + 1}.map ((S.fiberTransition f.as).app G) =
           AsSmall.up.{u, u + 1, u + 1}.map ((S.fiberTransition f.as).app F) ≫
             AsSmall.up.{u, u + 1, u + 1}.map ((S.restrict b.as).map α)
         rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
         exact congrArg (fun t => AsSmall.up.{u, u + 1, u + 1}.map t)
           ((S.fiberTransition f.as).naturality α) }⟩
  map_id F := by
    apply Lax.LaxTrans.homCategory.ext
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change AsSmall.up.{u, u + 1, u + 1}.map ((S.restrict a.as).map (𝟙 F)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp α β := by
    apply Lax.LaxTrans.homCategory.ext
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change AsSmall.up.{u, u + 1, u + 1}.map ((S.restrict a.as).map (α ≫ β)) =
      AsSmall.up.{u, u + 1, u + 1}.map ((S.restrict a.as).map α) ≫
        AsSmall.up.{u, u + 1, u + 1}.map ((S.restrict a.as).map β)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-! ### Full faithfulness of the system of restrictions -/

/-- The simplicial degree of an object of the total category. -/
def totalObjDegree (S : SimplicialSiteSituation.{u}) : S.totalCategory → SimplexCategory :=
  match S with
  | ⟨Sum.inl _⟩ => fun X => X.base.unop
  | ⟨Sum.inr _⟩ => fun X => X.base.unop

/-- An object of the total category, read as an object of the component of its own simplicial
degree. -/
def totalObjFibre (S : SimplicialSiteSituation.{u}) (X : S.totalCategory) :
    S.component (S.totalObjDegree X) :=
  match S with
  | ⟨Sum.inl _⟩ => X.fiber
  | ⟨Sum.inr _⟩ => X.fiber

/-- Every object of the total category lies in the image of the inclusion of the component of
its own simplicial degree. -/
theorem inclusion_obj_totalObjFibre (S : SimplicialSiteSituation.{u}) (X : S.totalCategory) :
    (S.inclusion (S.totalObjDegree X)).obj (S.totalObjFibre X) = X := by
  rcases S with ⟨C | C⟩ <;> rfl

/-- **Stacks 09WF.** A morphism of sheaves on the total site is determined by its restrictions
to the simplicial components: the system of restrictions is a faithful construction. -/
theorem total_hom_ext (S : SimplicialSiteSituation.{u})
    {F G : Sheaf S.totalTopology (Type u)} {α β : F ⟶ G}
    (h : ∀ n, (S.restrict n).map α = (S.restrict n).map β) : α = β := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext Y
  obtain ⟨X⟩ := Y
  rw [← S.inclusion_obj_totalObjFibre X]
  exact congrArg (fun t => t.hom.app (op (S.totalObjFibre X))) (h (S.totalObjDegree X))

/-- In case (A) the direct image is precomposition, so it acts on a morphism of sheaves by
reindexing its components. -/
theorem pushforward_map_inl_hom_app (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    {A B : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u)}
    (γ : A ⟶ B) (V : C.underlying.obj m) :
    (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).pushforward.map γ).hom.app
        (op V) =
      γ.hom.app (op ((C.underlying.map φ).toFunctor.obj V)) := rfl

/-- In case (B) the direct image is a right Kan extension, so it acts on a morphism of sheaves
through the functoriality of that extension. -/
theorem pushforward_map_inr_hom (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    {A B : Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u)}
    (γ : A ⟶ B) :
    (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).pushforward.map γ).hom =
      (C.underlying.map φ.op).toFunctor.op.ran.map γ.hom := rfl

/-- In case (A), a family of morphisms of the restrictions which is compatible with the
direct-image transitions is natural for every cross-fibre arrow of the total category. -/
theorem totalHom_naturality_inl (C : SimplicialSite.{u})
    {F G : Sheaf (totalTopology ⟨Sum.inl C⟩) (Type u)}
    (β : ∀ n, ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrict n).obj F ⟶
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrict n).obj G)
    (hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      β m ≫ ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app G =
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app F ≫
          ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).pushforward.map (β n))
    {m n : SimplexCategory} (φ : m ⟶ n) {U : C.underlying.obj n}
    {V : C.underlying.obj m} (k : U ⟶ (C.underlying.map φ).toFunctor.obj V) :
    F.obj.map (Quiver.Hom.op
        (⟨φ.op, k⟩ : (Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)).obj U ⟶
          (Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op m)).obj V)) ≫
        (β n).hom.app (op U) =
      (β m).hom.app (op V) ≫ G.obj.map (Quiver.Hom.op
        (⟨φ.op, k⟩ : (Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)).obj U ⟶
          (Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op m)).obj V)) := by
  have hF := restrictTransition_inl_arrow C φ F k
  have hG := restrictTransition_inl_arrow C φ G k
  have hsq := congrArg (fun t => t.hom.app (op V)) (hβ φ)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    pushforward_map_inl_hom_app] at hsq
  have hnat := (β n).hom.naturality k.op
  exact (congrArg (fun t => t ≫ (β n).hom.app (op U)) hF.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t =>
          (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app F).hom.app
            (op V) ≫ t) hnat).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫
              (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrict n).obj G).obj.map k.op)
              hsq.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun t => (β m).hom.app (op V) ≫ t) hG))))))

/-- In case (B), a family of morphisms of the restrictions which is compatible with the
direct-image transitions is natural for every cross-fibre arrow of the total category. -/
theorem totalHom_naturality_inr (C : CocontinuousSimplicialSite.{u})
    {F G : Sheaf (totalTopology ⟨Sum.inr C⟩) (Type u)}
    (β : ∀ n, ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrict n).obj F ⟶
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrict n).obj G)
    (hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      β m ≫ ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app G =
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app F ≫
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).pushforward.map (β n))
    {m n : SimplexCategory} (φ : m ⟶ n) {U : C.underlying.obj (op n)}
    {V : C.underlying.obj (op m)} (f : (C.underlying.map φ.op).toFunctor.obj U ⟶ V) :
    F.obj.map (Quiver.Hom.op
        (⟨φ.op, f⟩ : (Grothendieck.ι C.underlying (op n)).obj U ⟶
          (Grothendieck.ι C.underlying (op m)).obj V)) ≫ (β n).hom.app (op U) =
      (β m).hom.app (op V) ≫ G.obj.map (Quiver.Hom.op
        (⟨φ.op, f⟩ : (Grothendieck.ι C.underlying (op n)).obj U ⟶
          (Grothendieck.ι C.underlying (op m)).obj V)) := by
  have hF := restrictTransition_inr_arrow C φ F f
  have hG := restrictTransition_inr_arrow C φ G f
  have hsq := congrArg (fun t => t.hom) (hβ φ)
  simp only [ObjectProperty.FullSubcategory.comp_hom, pushforward_map_inr_hom] at hsq
  have key := Adjunction.homEquiv_naturality_right_square
    ((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u))
    ((β m).hom) (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app G).hom
    (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app F).hom
    ((β n).hom) hsq
  have keyU := NatTrans.congr_app key (op U)
  simp only [NatTrans.comp_app] at keyU
  have hnatm := (β m).hom.naturality f.op
  exact (congrArg (fun t => t ≫ (β n).hom.app (op U)) hF.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t =>
          F.obj.map ((Grothendieck.ι C.underlying (op m)).map f).op ≫ t) keyU.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫
              ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
                (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app G).hom).app
                (op U)) hnatm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun t => (β m).hom.app (op V) ≫ t) hG))))))

/-- **Stacks 09WF.** A family of morphisms between the restrictions of two sheaves on the total
site, compatible with the direct-image transitions, comes from a morphism of the sheaves
themselves. -/
noncomputable def totalHomOfFamily (S : SimplicialSiteSituation.{u})
    {F G : Sheaf S.totalTopology (Type u)}
    (β : ∀ n, (S.restrict n).obj F ⟶ (S.restrict n).obj G)
    (hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      β m ≫ (S.restrictTransition φ).app G =
        (S.restrictTransition φ).app F ≫ (S.transitionMorphism φ).pushforward.map (β n)) :
    F ⟶ G := by
  rcases S with ⟨C | C⟩
  · exact ⟨{ app := fun X => (β X.unop.base.unop).hom.app (op X.unop.fiber)
             naturality := fun _ _ g =>
               totalHom_naturality_inl C β hβ g.unop.base.unop g.unop.fiber }⟩
  · exact ⟨{ app := fun X => (β X.unop.base.unop).hom.app (op X.unop.fiber)
             naturality := fun _ _ g =>
               totalHom_naturality_inr C β hβ g.unop.base.unop g.unop.fiber }⟩

/-- The morphism of total-site sheaves built from a compatible family restricts, in each
simplicial degree, to the given member of that family. -/
theorem restrict_map_totalHomOfFamily (S : SimplicialSiteSituation.{u})
    {F G : Sheaf S.totalTopology (Type u)}
    (β : ∀ n, (S.restrict n).obj F ⟶ (S.restrict n).obj G)
    (hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      β m ≫ (S.restrictTransition φ).app G =
        (S.restrictTransition φ).app F ≫ (S.transitionMorphism φ).pushforward.map (β n))
    (n : SimplexCategory) :
    (S.restrict n).map (S.totalHomOfFamily β hβ) = β n := by
  rcases S with ⟨C | C⟩ <;> rfl

/-- The morphism of restrictions in simplicial degree `n` underlying a morphism between the
systems of restrictions of two sheaves on the total site. -/
noncomputable def modificationComponent (S : SimplicialSiteSituation.{u})
    {F G : Sheaf S.totalTopology (Type u)}
    (Γ : (restrictSystemFunctor S).obj F ⟶ (restrictSystemFunctor S).obj G)
    (n : SimplexCategory) : (S.restrict n).obj F ⟶ (S.restrict n).obj G :=
  AsSmall.down.{u, u + 1, u + 1}.map ((Γ.as.app ⟨n⟩).toNatTrans.app ⟨PUnit.unit⟩)

/-- The components of a morphism of systems of restrictions commute with the inverse-image
transitions: this is its modification law, read at the unique object of the terminal fibre. -/
theorem fiberTransition_modificationComponent (S : SimplicialSiteSituation.{u})
    {F G : Sheaf S.totalTopology (Type u)}
    (Γ : (restrictSystemFunctor S).obj F ⟶ (restrictSystemFunctor S).obj G)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.map (S.modificationComponent Γ m) ≫
        (S.fiberTransition φ).app G =
      (S.fiberTransition φ).app F ≫ S.modificationComponent Γ n :=
  congrArg (fun t => AsSmall.down.{u, u + 1, u + 1}.map t)
    (NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans
      (Γ.as.naturality (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)))
      (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2}))

/-- The components of a morphism of systems of restrictions commute with the direct-image
transitions, which is the mate of the inverse-image law under the topos adjunction of `f_φ`. -/
theorem restrictTransition_modificationComponent (S : SimplicialSiteSituation.{u})
    {F G : Sheaf S.totalTopology (Type u)}
    (Γ : (restrictSystemFunctor S).obj F ⟶ (restrictSystemFunctor S).obj G)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.modificationComponent Γ m ≫ (S.restrictTransition φ).app G =
      (S.restrictTransition φ).app F ≫
        (S.transitionMorphism φ).pushforward.map (S.modificationComponent Γ n) := by
  rw [← fiberTransition_adj, ← fiberTransition_adj]
  exact Adjunction.homEquiv_naturality_left_square _ _ _ _ _
    (S.fiberTransition_modificationComponent Γ φ)

/-- **Stacks 09WF.** The forward functor of the equivalence is faithful. -/
instance restrictSystemFunctor_faithful (S : SimplicialSiteSituation.{u}) :
    (restrictSystemFunctor S).Faithful where
  map_injective h :=
    S.total_hom_ext fun n => congrArg (fun t => S.modificationComponent t n) h

/-- **Stacks 09WF.** The forward functor of the equivalence is full: every morphism of systems
of restrictions is the system of restrictions of a morphism of total-site sheaves. -/
instance restrictSystemFunctor_full (S : SimplicialSiteSituation.{u}) :
    (restrictSystemFunctor S).Full where
  map_surjective Γ := by
    refine ⟨S.totalHomOfFamily (S.modificationComponent Γ)
      (fun {_ _} φ => S.restrictTransition_modificationComponent Γ φ), ?_⟩
    apply Lax.LaxTrans.homCategory.ext
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change AsSmall.up.{u, u + 1, u + 1}.map ((S.restrict a.as).map
      (S.totalHomOfFamily (S.modificationComponent Γ) _)) = _
    rw [restrict_map_totalHomOfFamily]
    rfl

/-! ### The transitions of an abstract system -/

/-- The lax unity law of a system, read at the unique object of the terminal fibre: the laxity
cell of an identity simplex map is the unit comparison of the pseudofunctor. -/
theorem system_naturality_id_app
    {P : Pseudofunctor (LocallyDiscrete SimplexCategory) Cat.{u + 1, u + 1}}
    (G : SimplicialSheafSystem P) (n : SimplexCategory) :
    (G.naturality (⟨𝟙 n⟩ : (⟨n⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
        ⟨PUnit.unit⟩ =
      (P.mapId (⟨n⟩ : LocallyDiscrete SimplexCategory)).hom.toNatTrans.app
        ((G.app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩) := by
  have h := G.naturality_id (⟨n⟩ : LocallyDiscrete SimplexCategory)
  have h3 := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans h)
    (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2})
  have h4 : (P.mapId (⟨n⟩ : LocallyDiscrete SimplexCategory)).inv.toNatTrans.app
        ((G.app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
        (G.naturality (𝟙 (⟨n⟩ : LocallyDiscrete SimplexCategory))).toNatTrans.app ⟨PUnit.unit⟩ =
      (Bicategory.rightUnitor
            (G.app (⟨n⟩ : LocallyDiscrete SimplexCategory))).hom.toNatTrans.app ⟨PUnit.unit⟩ ≫
        (Bicategory.leftUnitor
            (G.app (⟨n⟩ : LocallyDiscrete SimplexCategory))).inv.toNatTrans.app ⟨PUnit.unit⟩ ≫
        (G.app (⟨n⟩ : LocallyDiscrete SimplexCategory)).toFunctor.map
          ((terminalPseudofunctor.toLax.mapId
            (⟨n⟩ : LocallyDiscrete SimplexCategory)).toNatTrans.app ⟨PUnit.unit⟩) := h3
  have h5 : (P.mapId (⟨n⟩ : LocallyDiscrete SimplexCategory)).inv.toNatTrans.app
        ((G.app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
        (G.naturality (𝟙 (⟨n⟩ : LocallyDiscrete SimplexCategory))).toNatTrans.app ⟨PUnit.unit⟩ =
      𝟙 _ := by
    refine h4.trans ?_
    change 𝟙 _ ≫ 𝟙 _ ≫
      (G.app (⟨n⟩ : LocallyDiscrete SimplexCategory)).toFunctor.map (𝟙 _) = 𝟙 _
    rw [Category.id_comp, Category.id_comp]
    exact CategoryTheory.Functor.map_id _ _
  have key := (Iso.inv_comp_eq ((Cat.Hom.toNatIso
    (P.mapId (⟨n⟩ : LocallyDiscrete SimplexCategory))).app
    ((G.app ⟨n⟩).toFunctor.obj (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2})))).mp h5
  exact key.trans (Category.comp_id _)

/-- The lax functoriality law of a system, read at the unique object of the terminal fibre: the
laxity cell of a composite simplex map is the compositor of the pseudofunctor followed by the two
laxity cells. -/
theorem system_naturality_comp_app
    {P : Pseudofunctor (LocallyDiscrete SimplexCategory) Cat.{u + 1, u + 1}}
    (G : SimplicialSheafSystem P) {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (G.naturality ((⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩) ≫
          ⟨φ⟩)).toNatTrans.app ⟨PUnit.unit⟩ =
      (P.mapComp (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
            (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).hom.toNatTrans.app
          ((G.app ⟨l⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
        (P.map (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toFunctor.map
            ((G.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
              ⟨PUnit.unit⟩) ≫
          (G.naturality (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
            ⟨PUnit.unit⟩ := by
  have h := G.naturality_comp (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
    (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)
  have h3 := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans h)
    (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2})
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp] at h3
  have hkey : (P.mapComp (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
          (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).inv.toNatTrans.app
        ((G.app ⟨l⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
      (G.naturality ((⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩) ≫
        ⟨φ⟩)).toNatTrans.app ⟨PUnit.unit⟩ =
      (P.map (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toFunctor.map
          ((G.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
            ⟨PUnit.unit⟩) ≫
        (G.naturality (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
          ⟨PUnit.unit⟩ := by
    refine h3.trans ?_
    have hid : (Bicategory.whiskerRight
          (𝟙 (𝟙 (Cat.of (Discrete PUnit.{u + 2})) ≫ 𝟙 (Cat.of (Discrete PUnit.{u + 2}))))
          (G.app (⟨n⟩ : LocallyDiscrete SimplexCategory))).toNatTrans.app
          (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2}) =
        𝟙 ((G.app (⟨n⟩ : LocallyDiscrete SimplexCategory)).toFunctor.obj ⟨PUnit.unit⟩) :=
      CategoryTheory.Functor.map_id _ _
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (fun t =>
        ((P.map (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toFunctor.map
            ((G.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
              ⟨PUnit.unit⟩) ≫
          (G.naturality (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
            ⟨PUnit.unit⟩) ≫ t) hid).trans (Category.comp_id _)
  exact ((Iso.inv_comp_eq ((Cat.Hom.toNatIso (P.mapComp
    (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
    (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩))).app
      ((G.app ⟨l⟩).toFunctor.obj (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2})))).mp hkey)

/-- The transpose of the inverse-image compositor: transposing a composite of two inverse-image
arrows, compared by `canonicalCompositionComparison`, is the composite of the two transposes,
compared by the direct-image compositor `pushforwardCompSymm`. -/
theorem homEquiv_canonicalCompositionComparison (S : SimplicialSiteSituation.{u})
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    {A : Sheaf (S.componentTopology l) (Type u)}
    {B : Sheaf (S.componentTopology m) (Type u)}
    {D : Sheaf (S.componentTopology n) (Type u)}
    (a : (S.transitionMorphism ψ).inverseImage.obj A ⟶ B)
    (b : (S.transitionMorphism φ).inverseImage.obj B ⟶ D) :
    (S.transitionMorphism (ψ ≫ φ)).adj.homEquiv A D
        ((canonicalCompositionComparison S ψ φ).hom.app A ≫
          (S.transitionMorphism φ).inverseImage.map a ≫ b) =
      (S.transitionMorphism ψ).adj.homEquiv A B a ≫
        (S.transitionMorphism ψ).pushforward.map
            ((S.transitionMorphism φ).adj.homEquiv B D b) ≫
          (S.pushforwardCompSymm ψ φ).hom.app D :=
    homEquiv_comp_canonicalCompositionComparison S ψ φ a b

/-- The sheaf in simplicial degree `n` underlying a system for the pseudofunctor of component
sheaf categories. -/
def systemSheaf (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) (n : SimplexCategory) :
    Sheaf (S.componentTopology n) (Type u) :=
  AsSmall.down.{u, u + 1, u + 1}.obj ((G.app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩)

/-- The inverse-image transition `f_φ⁻¹ Gₘ ⟶ Gₙ` underlying a system: its laxity cell, read at
the unique object of the terminal fibre. -/
noncomputable def systemFibreTransition (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.obj (S.systemSheaf G m) ⟶ S.systemSheaf G n :=
  AsSmall.down.{u, u + 1, u + 1}.map ((G.naturality ⟨φ⟩).toNatTrans.app ⟨PUnit.unit⟩)

/-- The inverse-image transition of an identity simplex map is the canonical unit comparison. -/
theorem systemFibreTransition_id (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) (n : SimplexCategory) :
    S.systemFibreTransition G (𝟙 n) =
      (canonicalIdentityComparison S n).hom.app (S.systemSheaf G n) :=
  congrArg (fun t => AsSmall.down.{u, u + 1, u + 1}.map t) (system_naturality_id_app G n)

/-- The inverse-image transition of a composite simplex map is the composite of the two
transitions, compared by the canonical compositor. -/
theorem systemFibreTransition_comp (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    S.systemFibreTransition G (ψ ≫ φ) =
      (canonicalCompositionComparison S ψ φ).hom.app (S.systemSheaf G l) ≫
        (S.transitionMorphism φ).inverseImage.map (S.systemFibreTransition G ψ) ≫
          S.systemFibreTransition G φ :=
  congrArg (fun t => AsSmall.down.{u, u + 1, u + 1}.map t)
    (system_naturality_comp_app G ψ φ)

/-- The direct-image transition `Gₘ ⟶ (f_φ)_* Gₙ` underlying a system: the mate of its
inverse-image transition under the topos adjunction of `f_φ`. -/
noncomputable def systemDirectTransition (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.systemSheaf G m ⟶ (S.transitionMorphism φ).pushforward.obj (S.systemSheaf G n) :=
  (S.transitionMorphism φ).adj.homEquiv _ _ (S.systemFibreTransition G φ)

/-- The direct-image transition of an identity simplex map is the inverse of the direct-image
unit comparison `pushforwardId`. -/
theorem systemDirectTransition_id (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) (n : SimplexCategory) :
    S.systemDirectTransition G (𝟙 n) = (S.pushforwardId n).inv.app (S.systemSheaf G n) := by
  rw [systemDirectTransition, systemFibreTransition_id]
  exact S.homEquiv_canonicalIdentityComparison_hom_app n (S.systemSheaf G n)

/-- The direct-image transition of a composite simplex map is the composite of the two
transitions, compared by the direct-image compositor `pushforwardCompSymm`. -/
theorem systemDirectTransition_comp (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    S.systemDirectTransition G (ψ ≫ φ) =
      S.systemDirectTransition G ψ ≫
        (S.transitionMorphism ψ).pushforward.map (S.systemDirectTransition G φ) ≫
          (S.pushforwardCompSymm ψ φ).hom.app (S.systemSheaf G n) := by
  rw [systemDirectTransition, systemFibreTransition_comp]
  exact S.homEquiv_canonicalCompositionComparison ψ φ (S.systemFibreTransition G ψ)
    (S.systemFibreTransition G φ)

/-! ### The underlying presheaf of a system, case (A) -/

/-- In case (A), the inverse of the direct-image unit comparison acts on sections as restriction
along the transport of the identity equality of the cosimplicial diagram. -/
theorem pushforwardId_inl_inv_hom_app (C : SimplicialSite.{u}) (n : SimplexCategory)
    (X : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u))
    (V : C.underlying.obj n) :
    (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).pushforwardId n).inv.app X).hom.app (op V) =
      X.obj.map ((eqToIso
        (congrArg Cat.Hom.toFunctor (C.underlying.map_id n))).hom.app V).op := rfl

/-- The unit comparison of the total pseudofunctor of case (A) is the transport along the
identity equality of the cosimplicial diagram. -/
theorem totalPseudofunctor_mapId_app (C : SimplicialSite.{u}) (n : SimplexCategory)
    (V : C.underlying.obj n) :
    (C.totalPseudofunctor.mapId
          (⟨op (op n)⟩ : LocallyDiscrete (SimplexCategoryᵒᵖ)ᵒᵖ)).hom.toNatTrans.app V =
      (eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_id n))).hom.app V := by
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapId, eqToIso.hom,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  rfl

/-- The compositor of the total pseudofunctor of case (A) is the transport along the composition
equality of the cosimplicial diagram. -/
theorem totalPseudofunctor_mapComp_app (C : SimplicialSite.{u}) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (V : C.underlying.obj l) :
    (C.totalPseudofunctor.mapComp ψ.op.op.toLoc φ.op.op.toLoc).hom.toNatTrans.app V =
      (eqToIso
        (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ φ)).symm).inv.app V := by
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapComp, eqToIso.hom,
    eqToIso.inv, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  rfl

/-- The unit law of the direct-image transitions of a system, in the form the contravariant
Grothendieck construction of case (A) asks for. -/
theorem systemDirectTransition_rightOp_id (C : SimplicialSite.{u})
    (G : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})))
    (R : SimplexCategoryᵒᵖ) :
    NatTrans.rightOp
        (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G (𝟙 R).unop).hom) =
      Functor.whiskerRight (C.totalPseudofunctor.mapId ⟨op R⟩).hom.toNatTrans
        (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemSheaf G R.unop).obj.rightOp) := by
  refine NatTrans.ext (funext fun V => ?_)
  refine congrArg Quiver.Hom.op ?_
  refine (congrArg (fun t => t.hom.app (op V))
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition_id G R.unop)).trans ?_
  refine (pushforwardId_inl_inv_hom_app C R.unop _ V).trans ?_
  exact congrArg (fun t =>
      (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemSheaf G R.unop)).obj.map
        (Quiver.Hom.op t))
    (totalPseudofunctor_mapId_app C R.unop V).symm

/-- The cocycle law of the direct-image transitions of a system, in the form the contravariant
Grothendieck construction of case (A) asks for. -/
theorem systemDirectTransition_rightOp_comp (C : SimplicialSite.{u})
    (G : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})))
    {R S T : SimplexCategoryᵒᵖ} (f : R ⟶ S) (g : S ⟶ T) :
    NatTrans.rightOp
        (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G
          (f ≫ g).unop).hom) =
      Functor.whiskerRight (C.totalPseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans
          (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemSheaf G R.unop).obj.rightOp) ≫
        Functor.whiskerLeft (C.totalPseudofunctor.map g.op.toLoc).toFunctor
            (NatTrans.rightOp
              (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition
                G f.unop).hom)) ≫
          NatTrans.rightOp
            (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G g.unop).hom) :=
  by
  refine NatTrans.ext (funext fun V => ?_)
  refine congrArg Quiver.Hom.op ?_
  have hcomp := congrArg (fun t => t.hom.app (op V))
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition_comp G g.unop f.unop)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hcomp
  have hCxD := (pushforwardCompSymm_inl_hom_app_hom_app C g.unop f.unop
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemSheaf G R.unop) (op V)).trans
    (congrArg (fun t =>
        (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemSheaf G R.unop)).obj.map
          (Quiver.Hom.op t))
      (totalPseudofunctor_mapComp_app C g.unop f.unop V).symm)
  refine hcomp.trans ((congrArg (fun t =>
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G g.unop).hom.app
          (op V) ≫
        ((((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism
              g.unop).pushforward.map
            ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition
              G f.unop)).hom.app (op V)) ≫ t) hCxD).trans
    (Category.assoc _ _ _).symm)

/-- **Stacks 09WF**, case (A). The presheaf on the total site underlying a system: in simplicial
degree `n` it is the sections of the component sheaf, and restriction along a cross-fibre arrow
is the direct-image transition of the system. -/
noncomputable def systemPresheafInl (C : SimplicialSite.{u})
    (G : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}))) :
    (Pseudofunctor.CoGrothendieck C.totalPseudofunctor)ᵒᵖ ⥤ Type u :=
  (Pseudofunctor.CoGrothendieck.functorFrom
    (F := C.totalPseudofunctor) (E := (Type u)ᵒᵖ)
    (fun R => (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemSheaf G R.unop).obj).rightOp)
    (fun {_ _} f => NatTrans.rightOp
      (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G f.unop).hom))
    (systemDirectTransition_rightOp_id C G)
    (fun {_ _ _} f g => systemDirectTransition_rightOp_comp C G f g)).leftOp

/-! ### The presentation, given essential surjectivity -/

/-- The system of restrictions is an equivalence as soon as it is essentially surjective: it is
full and faithful unconditionally. -/
instance restrictSystemFunctor_isEquivalence (S : SimplicialSiteSituation.{u})
    [(restrictSystemFunctor S).EssSurj] : (restrictSystemFunctor S).IsEquivalence := { }

/-- **Stacks 09WF**, reduced to essential surjectivity. A presentation of the sheaves on the
total site as systems on the component topoi, with the system of restrictions as the equivalence.
All eight fields are supplied; the only hypothesis is that the system of restrictions is
essentially surjective, which is the descent construction and is not proved here.

The component identification is the identity: the `n`th component of the system of restrictions
of a sheaf *is* its restriction, so `componentRestrictionIso` is `Iso.refl` and its naturality is
the unit laws of composition. -/
noncomputable def restrictPresentation (S : SimplicialSiteSituation.{u})
    [(restrictSystemFunctor S).EssSurj] : SimplicialSheafPresentation S where
  diagram := componentPseudofunctor S
  componentEquivalence n := componentPseudofunctorEquiv S n
  transitionIso φ := componentPseudofunctorTransitionIso S φ
  identityComparison_isCanonical n X :=
    componentPseudofunctor_identityComparison_isCanonical S n X
  compositionComparison_isCanonical ψ φ X :=
    componentPseudofunctor_compositionComparison_isCanonical S ψ φ X
  totalEquivalence := (restrictSystemFunctor S).asEquivalence
  componentRestrictionIso _ _ := Iso.refl _
  componentRestriction_naturality _ _ := (Category.comp_id _).trans (Category.id_comp _).symm

end SimplicialSiteSituation

/-! ### Functors out of the Grothendieck construction from fibrewise data -/

/-- Transport along an equality of objects cancels the image of the opposite transport. -/
@[reassoc]
theorem eqToHom_comp_map_eqToHom {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] (G : A ⥤ B) {x y : A} (h : y = x) (p : G.obj x = G.obj y) :
    eqToHom p ≫ G.map (eqToHom h) = 𝟙 (G.obj x) := by
  subst h
  simp

namespace Grothendieck

variable {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Cat.{v₂, u₂}} {E : Type u} [Category.{v} E]

/-- The fibrewise functors of a family out of the Grothendieck construction agree with their
transports along the identity of the base. -/
theorem fib_map_id_eq (fib : ∀ c, F.obj c ⥤ E) (c : C) :
    fib c = (F.map (𝟙 c)).toFunctor ⋙ fib c := by
  simp only [CategoryTheory.Functor.map_id]
  rfl

/-- The fibrewise functors of a family out of the Grothendieck construction agree with their
transports along a composite of the base. -/
theorem fib_map_comp_eq (fib : ∀ c, F.obj c ⥤ E) {c₁ c₂ c₃ : C}
    (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) :
    (F.map f).toFunctor ⋙ (F.map g).toFunctor ⋙ fib c₃ =
      (F.map (f ≫ g)).toFunctor ⋙ fib c₃ := by
  simp only [CategoryTheory.Functor.map_comp]
  rfl

variable (fib : ∀ c, F.obj c ⥤ E)
  (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c')
  (hom_id : ∀ c, hom (𝟙 c) = eqToHom (fib_map_id_eq fib c))
  (hom_comp : ∀ (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
    hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (fib_map_comp_eq fib f g))

/-- A functor out of the Grothendieck construction built from a family of functors on the fibres
and a family of natural transformations indexed by the morphisms of the base, with the unit and
cocycle coherences stated through `fib_map_id_eq` and `fib_map_comp_eq`. -/
def functorFromOfEq : Grothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by
    simp only [id_base, Functor.comp_obj, hom_id, eqToHom_app, id_fiber]
    exact eqToHom_comp_map_eqToHom (fib X.base) _ _
  map_comp {X _ Z} f g := by
    simp only [comp_base, Functor.comp_obj, hom_comp, NatTrans.comp_app,
      Functor.whiskerLeft_app, eqToHom_app, comp_fiber, CategoryTheory.Functor.map_comp,
      Category.assoc, NatTrans.naturality_assoc, Functor.comp_map]
    exact congrArg (fun t =>
        (hom f.base).app X.fiber ≫
          (hom g.base).app ((F.map f.base).toFunctor.obj X.fiber) ≫ t)
      (eqToHom_comp_map_eqToHom_assoc (fib Z.base) _ _ _)

end Grothendieck

end CategoryTheory

end
