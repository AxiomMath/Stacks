module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic

/-!
# Stalks of inverse images on small étale sites, with arbitrary coefficients

Let `f : T ⟶ S` be a morphism in a big étale site and let `x` be a geometric point of `T`. For
sheaves of sets, the stalk at `x` of the inverse image of a sheaf on the small étale site of `S`
is the stalk of the original sheaf at the image geometric point `f ∘ x`. The same holds for
sheaves with values in any category `A` admitting the colimits that form stalks and the products
that form skyscrapers: the comparison is again the composite of Mathlib's identification of the
fibre of an inverse-image point with the invariance of the elements-colimit under an isomorphism
of fibre functors, both of which are statements about an arbitrary coefficient category.

The second ingredient is recorded here in that generality. If `P ≅ Q` are isomorphic functors to
`Type u` on a category `C`, their categories of elements are equivalent over `C`, hence the
colimit of a presheaf with values in `A` restricted along the projection from `P.Elements` agrees
with the colimit of its restriction along the projection from `Q.Elements`, naturally in the
presheaf and compatibly with the restriction to sheaves.

## Main results

* `CategoryTheory.CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients` and
  `CategoryTheory.CategoryOfElements.sheafColimIsoOfNatIsoOfCoefficients` — invariance of the
  elements-colimit stalk functor, with values in an arbitrary coefficient category.
* `AlgebraicGeometry.smallEtalePullbackSheafFiberIso` — the inverse image on the small étale site
  commutes with the stalk at a geometric point, for arbitrary coefficients.
* `AlgebraicGeometry.etaleStalkSmallEtalePullObjIso` — the same comparison on a single sheaf.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u v w uA vA

namespace CategoryTheory.CategoryOfElements

variable {C : Type v} [Category.{w} C] {P Q : C ⥤ Type u}
  {A : Type uA} [Category.{vA} A]
  [HasColimitsOfShape P.Elementsᵒᵖ A] [HasColimitsOfShape Q.Elementsᵒᵖ A]

/-- The stalk functor on presheaves given by a colimit over a category of elements depends on the
indexing functor only through its isomorphism class. -/
public def presheafColimIsoOfNatIsoOfCoefficients (e : P ≅ Q) :
    (Functor.whiskeringLeft P.Elementsᵒᵖ Cᵒᵖ A).obj (Functor.Elements.π P).op ⋙ colim ≅
      (Functor.whiskeringLeft Q.Elementsᵒᵖ Cᵒᵖ A).obj (Functor.Elements.π Q).op ⋙ colim :=
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft Q.Elementsᵒᵖ Cᵒᵖ A).obj (Functor.Elements.π Q).op)
    (Functor.Final.colimIso (equivalenceOfNatIso e).op.functor)

/-- The stalk functor on sheaves given by a colimit over a category of elements depends on the
indexing functor only through its isomorphism class. -/
public def sheafColimIsoOfNatIsoOfCoefficients (J : GrothendieckTopology C) (e : P ≅ Q) :
    (sheafToPresheaf J A ⋙
      (Functor.whiskeringLeft _ _ _).obj (Functor.Elements.π P).op ⋙ colim) ≅
    (sheafToPresheaf J A ⋙
      (Functor.whiskeringLeft _ _ _).obj (Functor.Elements.π Q).op ⋙ colim) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafColimIsoOfNatIsoOfCoefficients e)

end CategoryTheory.CategoryOfElements

namespace AlgebraicGeometry

/-- **Stacks 03Q1** for arbitrary coefficients. Inverse image of a sheaf on the small étale site
commutes naturally with the stalk at a geometric point. -/
@[stacks 03Q1 "pullback_stalk, arbitrary coefficients",
  sga "4½ Arcata 2.3.3" "(f^*F)_x̄ = F_f(x̄)",
  sga "4 VIII 3.4" "(F), special case"]
public def smallEtalePullbackSheafFiberIso (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.obj)
    (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A] [HasProducts.{u} A]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] :
    (smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property) ⋙
      (geometricPointSitePoint B T.obj T.property x).sheafFiber ≅
    (geometricPointSitePoint B S.obj S.property (x.map (B.inclusion.map f))).sheafFiber := by
  let J := SmallEtale.topology B S.obj S.property
  let K := SmallEtale.topology B T.obj T.property
  let u := smallEtaleBaseChange B f
  let p := geometricPointSitePoint B S.obj S.property (x.map (B.inclusion.map f))
  let q := geometricPointSitePoint B T.obj T.property x
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SmallEtale.finalIsTerminal B S.obj S.property)
      ((SmallEtale.finalIsTerminal B S.obj S.property).isTerminalObj u)
  letI : HasFiniteLimits (SmallEtale B S.obj S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  letI : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let hcover : CoverPreserving J K u := CoverPreserving.of_isContinuous u J K
  let eFiber : geometricPointFiber B S.obj S.property (x.map (B.inclusion.map f)) ≅
      u ⋙ geometricPointFiber B T.obj T.property x :=
    geometricPointFiberBaseChangeIso B f x
  let eElements := CategoryOfElements.equivalenceOfNatIso
    (C := SmallEtale B S.obj S.property)
    (P := geometricPointFiber B S.obj S.property (x.map (B.inclusion.map f)))
    (Q := u ⋙ geometricPointFiber B T.obj T.property x) eFiber
  haveI : InitiallySmall.{u}
      (u ⋙ geometricPointFiber B T.obj T.property x).Elements :=
    ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _
        (fromInitialModel.{u} p.fiber.Elements) eElements.functor inferInstance
        eElements.isEquivalence_functor⟩
  haveI : InitiallySmall.{u} (u ⋙ q.fiber).Elements := by
    change InitiallySmall.{u} (u ⋙ geometricPointFiber B T.obj T.property x).Elements
    infer_instance
  letI : HasColimitsOfShape p.fiber.Elementsᵒᵖ A :=
    hasColimitsOfShape_geometricPointFiber B S.obj S.property (x.map (B.inclusion.map f))
  letI : HasColimitsOfShape
      (u ⋙ geometricPointFiber B T.obj T.property x).Elementsᵒᵖ A :=
    hasColimitsOfShape_of_finallySmall _ _
  let eStalk := CategoryOfElements.sheafColimIsoOfNatIsoOfCoefficients (A := A) J eFiber
  let eComap := q.sheafFiberComapIso u hcover A
  change (u.sheafPullback A J K ⋙ q.sheafFiber) ≅ p.sheafFiber
  exact eComap.symm ≪≫ eStalk.symm

/-- The stalk of an inverse image at a geometric point is the stalk of the sheaf at the image
geometric point. -/
public def etaleStalkSmallEtalePullObjIso (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
    (x : GeometricPoint T.obj) (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A]
    [HasProducts.{u} A]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    etaleStalk B T.obj T.property x
        (((smallEtaleBaseChange B f).sheafPullback A
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F).obj ≅
      etaleStalk B S.obj S.property (x.map (B.inclusion.map f)) F.obj :=
  (smallEtalePullbackSheafFiberIso B f x A).app F

end AlgebraicGeometry

end
