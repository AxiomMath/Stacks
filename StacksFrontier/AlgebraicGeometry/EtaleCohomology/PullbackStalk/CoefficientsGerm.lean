module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients

/-!
# Germs and the stalk of an inverse image, with arbitrary coefficients

Let `f : T ⟶ S` be a morphism in a big étale site and let `x` be a geometric point of `T`. The
comparison `AlgebraicGeometry.smallEtalePullbackSheafFiberIso` identifies the stalk at `x` of the
inverse image of a sheaf on the small étale site of `S` with the stalk of the sheaf at the image
point `f ∘ x`, for coefficients in an arbitrary category. This file records what that comparison
does to a germ: a section over a pointed étale neighbourhood `V` of the image point, pulled back
along the unit of the inverse-image adjunction and restricted to a pointed étale neighbourhood
`U` of `x` lying over the base change of `V`, has the same germ as the original section.

For sheaves of sets this is
`AlgebraicGeometry.smallEtalePullbackStalkIso_germ`; the statement here is the same one with the
coefficients left arbitrary, hence phrased as an equality of morphisms rather than of elements.

## Main definitions

* `AlgebraicGeometry.pullbackSectionAlongHom` — the map pulling a section over `V` back to the
  inverse image over `U`, as a morphism of the coefficient category.

## Main results

* `CategoryTheory.CategoryOfElements.ι_presheafColimIsoOfNatIsoOfCoefficients_hom` and
  `CategoryTheory.CategoryOfElements.ι_sheafColimIsoOfNatIsoOfCoefficients_hom` — the invariance
  of the elements-colimit transports the canonical map from the sections at an element to the
  canonical map at the transported element.
* `AlgebraicGeometry.smallEtalePullbackSheafFiberIso_germ` and
  `AlgebraicGeometry.etaleStalkSmallEtalePullObjIso_germ` — the comparison of stalks sends the
  germ of a pulled-back section to the germ of the original section.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

universe u uA vA uC vC uP

namespace CategoryTheory.CategoryOfElements

variable {C : Type uC} [Category.{vC} C] {P Q : C ⥤ Type uP}
  {A : Type uA} [Category.{vA} A]
  [HasColimitsOfShape P.Elementsᵒᵖ A] [HasColimitsOfShape Q.Elementsᵒᵖ A]

/-- The invariance of the elements-colimit under an isomorphism of indexing functors sends the
canonical map from the sections at an element to the canonical map at the transported element. -/
public lemma ι_presheafColimIsoOfNatIsoOfCoefficients_hom (e : P ≅ Q) (F : Cᵒᵖ ⥤ A)
    (X : P.Elementsᵒᵖ) :
    colimit.ι ((CategoryOfElements.π P).op ⋙ F) X ≫
        (presheafColimIsoOfNatIsoOfCoefficients (A := A) e).hom.app F =
      colimit.ι ((CategoryOfElements.π Q).op ⋙ F)
        (op ((CategoryOfElements.map e.hom).obj X.unop)) :=
  Functor.Final.ι_colimitIso_hom (equivalenceOfNatIso e).op.functor
    ((CategoryOfElements.π Q).op ⋙ F) X

/-- The invariance of the elements-colimit stalk functor on sheaves sends the germ of a section
at an element to its germ at the transported element. -/
public lemma ι_sheafColimIsoOfNatIsoOfCoefficients_hom (J : GrothendieckTopology C) (e : P ≅ Q)
    (F : Sheaf J A) (V : P.Elements) :
    colimit.ι ((CategoryOfElements.π P).op ⋙ F.obj) (op V) ≫
        (sheafColimIsoOfNatIsoOfCoefficients (A := A) J e).hom.app F =
      colimit.ι ((CategoryOfElements.π Q).op ⋙ F.obj)
        (op ((CategoryOfElements.map e.hom).obj V)) :=
  ι_presheafColimIsoOfNatIsoOfCoefficients_hom e F.obj (op V)

end CategoryTheory.CategoryOfElements

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.obj)
  (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A] [HasProducts.{u} A]
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- Pull a section over `V` back along the unit of the inverse-image adjunction and restrict it
to an étale neighbourhood `U` mapping to the base change of `V`. -/
public def pullbackSectionAlongHom
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (V : SmallEtale B S.obj S.property) (U : SmallEtale B T.obj T.property)
    (a : U ⟶ (smallEtaleBaseChange B f).obj V) :
    F.obj.obj (op V) ⟶
      (((smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj F).obj.obj (op U) :=
  (((smallEtaleBaseChange B f).sheafAdjunctionContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op V) ≫
    (((smallEtaleBaseChange B f).sheafPullback A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).obj F).obj.map a.op

/-- **Stacks 03Q1** for arbitrary coefficients, on germs: the comparison of the stalk of an
inverse image with the stalk at the image point sends the germ of a pulled-back section to the
germ of the original section. -/
@[stacks 03Q1 "pullback_stalk on germs, arbitrary coefficients"]
public theorem smallEtalePullbackSheafFiberIso_germ
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (U : (geometricPointFiber B T.obj T.property x).Elements)
    (V : (geometricPointFiber B S.obj S.property
      (x.map (B.inclusion.map f))).Elements)
    (a : U.1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (ha : U.2.1 ≫ (SmallEtale.toScheme B T.obj T.property).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1) :
    pullbackSectionAlongHom B f A F V.1 U.1 a ≫
        colimit.ι ((CategoryOfElements.π (geometricPointFiber B T.obj T.property x)).op ⋙
            (((smallEtaleBaseChange B f).sheafPullback A
              (SmallEtale.topology B S.obj S.property)
              (SmallEtale.topology B T.obj T.property)).obj F).obj) (op U) ≫
          (smallEtalePullbackSheafFiberIso B f x A).hom.app F =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B S.obj S.property
        (x.map (B.inclusion.map f)))).op ⋙ F.obj) (op V) := by
  let J := SmallEtale.topology B S.obj S.property
  let K := SmallEtale.topology B T.obj T.property
  let u := smallEtaleBaseChange B f
  let p := geometricPointSitePoint B S.obj S.property (x.map (B.inclusion.map f))
  let q := geometricPointSitePoint B T.obj T.property x
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SmallEtale.finalIsTerminal B S.obj S.property)
      ((SmallEtale.finalIsTerminal B S.obj S.property).isTerminalObj u)
  have : HasFiniteLimits (SmallEtale B S.obj S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  have : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let eFiber : p.fiber ≅ u ⋙ q.fiber := geometricPointFiberBaseChangeIso B f x
  let eElements := CategoryOfElements.equivalenceOfNatIso eFiber
  have : InitiallySmall.{u} (u ⋙ q.fiber).Elements :=
    ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _ (fromInitialModel.{u} p.fiber.Elements)
        eElements.functor inferInstance eElements.isEquivalence_functor⟩
  have : HasColimitsOfShape p.fiber.Elementsᵒᵖ A :=
    hasColimitsOfShape_geometricPointFiber B S.obj S.property (x.map (B.inclusion.map f))
  have : HasColimitsOfShape (u ⋙ q.fiber).Elementsᵒᵖ A :=
    hasColimitsOfShape_of_finallySmall _ _
  let eComap := q.sheafFiberComapIso u (CoverPreserving.of_isContinuous u J K) A
  let eStalk := CategoryOfElements.sheafColimIsoOfNatIsoOfCoefficients (A := A) J eFiber
  let G := (u.sheafPullback A J K).obj F
  let η := ((u.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op V.1)
  change (η ≫ G.obj.map a.op) ≫
      q.toPresheafFiber U.1 U.2 G.obj ≫ (eComap.symm ≪≫ eStalk.symm).hom.app F =
    p.toPresheafFiber V.1 V.2 F.obj
  have hpoint : q.fiber.map a U.2 = eFiber.hom.app V.1 V.2 := by
    apply (geometricPointFiberBaseChangeEquiv B f x V.1).symm.injective
    change (geometricPointFiberBaseChangeEquiv B f x V.1).symm (q.fiber.map a U.2) =
      (geometricPointFiberBaseChangeEquiv B f x V.1).symm
        (geometricPointFiberBaseChangeEquiv B f x V.1 V.2)
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    change (U.2.1 ≫ (SmallEtale.toScheme B T.obj T.property).map a) ≫
      eqToHom (smallEtaleBaseChange_toScheme_obj_eq B f V.1) ≫
        B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1
    simpa using ha
  have hstalk := CategoryOfElements.ι_sheafColimIsoOfNatIsoOfCoefficients_hom (A := A) J eFiber F V
  have hcomap := Point.toSheafFiber_sheafFiberComapIso_hom q u
    (CoverPreserving.of_isContinuous u J K) F V.1
    (eFiber.hom.app V.1 V.2)
  have hw := q.toPresheafFiber_w a U.2 G.obj
  rw [hpoint] at hw
  have h : η ≫ G.obj.map a.op ≫ q.toPresheafFiber U.1 U.2 G.obj =
      p.toPresheafFiber V.1 V.2 F.obj ≫ eStalk.hom.app F ≫ eComap.hom.app F :=
    (congrArg (fun k => η ≫ k) hw).trans
      (hcomap.symm.trans
        (((congrArg (fun k => k ≫ eComap.hom.app F) hstalk).symm).trans
          (Category.assoc _ _ _)))
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Category.assoc _ _ _))).trans <|
    (congrArg (· ≫ (eStalk ≪≫ eComap).inv.app F) h).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) ((eStalk ≪≫ eComap).hom_inv_id_app F)).trans (Category.comp_id _)

/-- **Stacks 03Q1** for arbitrary coefficients, on germs and on a single sheaf. -/
@[stacks 03Q1 "pullback_stalk on germs, arbitrary coefficients, single sheaf"]
public theorem etaleStalkSmallEtalePullObjIso_germ
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (U : (geometricPointFiber B T.obj T.property x).Elements)
    (V : (geometricPointFiber B S.obj S.property
      (x.map (B.inclusion.map f))).Elements)
    (a : U.1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (ha : U.2.1 ≫ (SmallEtale.toScheme B T.obj T.property).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1) :
    pullbackSectionAlongHom B f A F V.1 U.1 a ≫
        colimit.ι ((CategoryOfElements.π (geometricPointFiber B T.obj T.property x)).op ⋙
            (((smallEtaleBaseChange B f).sheafPullback A
              (SmallEtale.topology B S.obj S.property)
              (SmallEtale.topology B T.obj T.property)).obj F).obj) (op U) ≫
          (etaleStalkSmallEtalePullObjIso B f x A F).hom =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B S.obj S.property
        (x.map (B.inclusion.map f)))).op ⋙ F.obj) (op V) :=
  smallEtalePullbackSheafFiberIso_germ B f x A F U V a ha

end AlgebraicGeometry

end
