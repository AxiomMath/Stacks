module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem

/-!
# The identity law for the system of direct images along a limit of schemes

`Stacks.EtaleCohomology.EtaleSheafSystem` imposes only the cocycle condition, following the
source, which does not ask the map attached to an identity index to be the identity. For the
particular system `Stacks.EtaleCohomology.directImageSystem` of direct images of a sheaf along
the projections of a cone that identity law nevertheless holds, and this file proves it.

The content is a unit law for small étale base change, dual to the associativity pentagon
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_assoc`: base change along the identity is the
identity, and the comparison `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` with its second
factor an identity is the corresponding unitor. Both are proved by the uniqueness of a morphism
into a base change, whose two components are forced.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleBaseChangeIdApp`,
  `Stacks.EtaleCohomology.smallEtaleBaseChangeId` and
  `Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf` — base change along the identity, resp.
  along a morphism known to be the identity, is the identity functor on the small étale site.
* `Stacks.EtaleCohomology.systemPushforwardId` — direct image along the transition at an
  identity index of an inverse system of schemes is the identity functor on sheaves.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_id_hom_app` — **the unit law for the
  base-change comparison**: with the second factor an identity, the comparison for a composite
  is the image of the identity comparison.
* `Stacks.EtaleCohomology.coneDirectImageComp_id` — its image on direct images of sheaves.
* `Stacks.EtaleCohomology.directImageSystem_map_id` — **the identity law**: the transpose,
  under the inverse-image/direct-image adjunction at an identity index, of the map of
  `Stacks.EtaleCohomology.directImageSystem` is the canonical identification of the direct
  image along that transition with the sheaf itself.

## Implementation notes

The identity law is stated as an identity between *transposes* across the adjunction. That is
the form the map itself is defined in — `Stacks.EtaleCohomology.coneDirectImageMap` is a
transpose — and it avoids constructing the identity comparison for the inverse image, which is
the left adjoint of the direct image and so has no independent description.

No tag is placed. The identity law is not part of the source's definition of a system of
sheaves, nor of the statement of [Stacks, Tag 0EYN]; it is one of the inputs that the colimit
diagram of [Stacks, Tag 0DV2] needs, and this is the half of it that concerns the underlying
sheaves rather than their higher direct images.

## References

* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w v u

namespace Stacks.EtaleCohomology

/-! ### Base change along the identity -/

section BaseChangeId

/-- **The fibre product with an identity is the first factor.** Stated in an arbitrary
category: in the presence of an object of a small étale site the rewriting tactics cannot see
through `CategoryTheory.MorphismProperty`, so every computation below is term-mode and every
rearrangement is isolated in a statement with no étale object in it. -/
public def pullbackFstIsoOfIdRight {C : Type*} [Category* C] {X A : C} (h : A ⟶ X)
    [HasPullback h (𝟙 X)] :
    pullback h (𝟙 X) ≅ A where
  hom := pullback.fst h (𝟙 X)
  inv := pullback.lift (𝟙 A) h (by rw [Category.id_comp, Category.comp_id])
  hom_inv_id := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp])
    (by rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition,
      Category.comp_id])
  inv_hom_id := pullback.lift_fst _ _ _

/-- The rearrangement that proves the unit law, on variables in an arbitrary category. -/
public theorem unitLawRearrange {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ : C}
    {a c : O₁ ⟶ O₂} {b : O₂ ⟶ O₃} {m : O₃ ⟶ O₄} {t : O₁ ⟶ O₄} {q : O₄ ⟶ O₃}
    (hcomp : a ≫ b ≫ m = t) (hmap : c ≫ b = t ≫ q) (hq : q ≫ m = 𝟙 O₄) :
    (a ≫ b) ≫ m = (c ≫ b) ≫ m := by
  rw [Category.assoc, hcomp, hmap, Category.assoc, hq, Category.comp_id]

/-- **Base change along the identity is the identity, at one object.** The first projection of
the fibre product of an étale morphism with the identity is an isomorphism. -/
public def smallEtaleBaseChangeIdApp {X : Scheme.{u}} (V : X.Etale) :
    (smallEtaleBaseChange (𝟙 X)).obj V ≅ V :=
  MorphismProperty.Over.isoMk (pullbackFstIsoOfIdRight V.hom)
    ((pullback.condition (f := V.hom) (g := 𝟙 X)).trans (Category.comp_id _))

/-- **Base change along the identity is the identity.** -/
public def smallEtaleBaseChangeId (X : Scheme.{u}) :
    smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents smallEtaleBaseChangeIdApp
    (fun p => MorphismProperty.Over.Hom.ext (smallEtaleBaseChange_map_left_fst (𝟙 X) p))

/-- Base change along a morphism known to be the identity is the identity. -/
public def smallEtaleBaseChangeIdOf {X : Scheme.{u}} (g : X ⟶ X) (hg : g = 𝟙 X) :
    smallEtaleBaseChange g ≅ 𝟭 X.Etale :=
  eqToIso (congrArg smallEtaleBaseChange hg) ≪≫ smallEtaleBaseChangeId X

/-- The component of `Stacks.EtaleCohomology.smallEtaleBaseChangeId` is inverse to the first
projection of the fibre product with the identity. -/
public theorem smallEtaleBaseChangeId_inv_app_left_fst (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).inv.app V).left ≫ pullback.fst V.hom (𝟙 X) = 𝟙 V.left :=
  congrArg (fun h : V ⟶ V => h.left) (smallEtaleBaseChangeIdApp V).inv_hom_id

/-- The same for `Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf`. -/
public theorem smallEtaleBaseChangeIdOf_inv_app_left {X : Scheme.{u}} (g : X ⟶ X)
    (hg : g = 𝟙 X) (U : X.Etale) :
    ((smallEtaleBaseChangeIdOf g hg).inv.app U).left ≫ pullback.fst U.hom g = 𝟙 U.left := by
  subst hg
  simpa [smallEtaleBaseChangeIdOf] using smallEtaleBaseChangeId_inv_app_left_fst X U

end BaseChangeId

/-! ### The unit law for the base-change comparison -/

section UnitLaw

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Y) (hg : g = 𝟙 Y) (hfg : f = f ≫ g)

include hg in
/-- **The unit law for `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'`.** With the second
factor an identity, the comparison between base change along the composite and the composite of
the base changes is the image under the first base change of the identity comparison: both
sides are morphisms into a base change, and their first projections agree after the
isomorphism `Stacks.EtaleCohomology.smallEtaleBaseChangeIdApp`. -/
public theorem smallEtaleBaseChangeComp'_id_hom_app (U : Y.Etale) :
    (smallEtaleBaseChangeComp' f g f hfg).hom.app U =
      (smallEtaleBaseChange f).map ((smallEtaleBaseChangeIdOf g hg).inv.app U) := by
  have : IsIso (pullback.fst U.hom g) := by
    subst hg; exact (pullbackFstIsoOfIdRight U.hom).isIso_hom
  exact smallEtaleBaseChange_hom_ext f ((cancel_mono (pullback.fst U.hom g)).mp
    (unitLawRearrange (smallEtaleBaseChangeComp'_fst_fst f g f hfg U)
      (smallEtaleBaseChange_map_left_fst f ((smallEtaleBaseChangeIdOf g hg).inv.app U))
      (smallEtaleBaseChangeIdOf_inv_app_left g hg U)))

end UnitLaw

/-! ### Direct image along an identity transition -/

section SystemId

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (A : Type w) [Category.{w'} A]

/-- The component of the comparison for a composite direct image, at an object of the site. -/
public lemma smallEtalePushforwardComp'_hom_app_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (B : Type w) [Category.{w'} B]
    (F : Sheaf (smallEtaleTopology X) B) (U : (Z.Etale)ᵒᵖ) :
    ((smallEtalePushforwardComp' f g fg hfg B).hom.app F).hom.app U =
      F.obj.map (Opposite.op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop)) :=
  Category.id_comp _

/-- **Direct image along an identity transition is the identity.** -/
public def systemPushforwardId (i : Iᵒᵖ) : systemPushforward D A (𝟙 i) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (smallEtaleBaseChangeIdOf (D.map (𝟙 i)) (D.map_id i)) A _

/-- The component of `Stacks.EtaleCohomology.systemPushforwardId`. -/
public lemma systemPushforwardId_hom_app_hom_app (i : Iᵒᵖ)
    (G : Sheaf (smallEtaleTopology (D.obj i)) A) (U : ((D.obj i).Etale)ᵒᵖ) :
    ((systemPushforwardId D A i).hom.app G).hom.app U =
      G.obj.map (Opposite.op
        ((smallEtaleBaseChangeIdOf (D.map (𝟙 i)) (D.map_id i)).inv.app U.unop)) :=
  Category.comp_id _

end SystemId

/-! ### The identity law for the system of direct images -/

section IdentityLaw

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] (c : Cone D)
  (F : Sheaf (smallEtaleTopology c.pt) A)

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] in
/-- **The identification `f_{i,*}𝓕 ≅ f_{i,*}𝓕` attached to an identity transition is the
canonical one.** This is the image under direct image along the projection of the unit law
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_id_hom_app`. -/
public theorem coneDirectImageComp_id (i : Iᵒᵖ) :
    coneDirectImageComp D A c (𝟙 i) =
      Functor.isoWhiskerLeft (smallEtalePushforward (c.π.app i) A)
          (systemPushforwardId D A i) ≪≫
        Functor.rightUnitor _ := by
  refine Iso.ext (NatTrans.ext (funext fun G =>
    Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))))
  refine (smallEtalePushforwardComp'_hom_app_hom_app (c.π.app i) (D.map (𝟙 i)) (c.π.app i)
    (c.w (𝟙 i)).symm A G U).trans ?_
  refine Eq.trans (congrArg (fun z => G.obj.map (Opposite.op z))
    (smallEtaleBaseChangeComp'_id_hom_app (c.π.app i) (D.map (𝟙 i)) (D.map_id i)
      (c.w (𝟙 i)).symm U.unop)) ?_
  exact (systemPushforwardId_hom_app_hom_app D A i
    ((smallEtalePushforward (c.π.app i) A).obj G) U).symm.trans (Category.comp_id _).symm

/-- **The identity law for `Stacks.EtaleCohomology.directImageSystem`.** The map attached to an
identity index is, across the inverse-image/direct-image adjunction, the canonical
identification of the direct image along that transition with the sheaf itself; so it is the
identity, up to that identification.

`Stacks.EtaleCohomology.EtaleSheafSystem` does not impose this, following the source, which
asks only for the cocycle condition. -/
public theorem directImageSystem_map_id (i : Iᵒᵖ) :
    (systemAdjunction D A (𝟙 i)).homEquiv _ _ ((directImageSystem D A c F).map (𝟙 i)) =
      (systemPushforwardId D A i).inv.app ((directImageSystem D A c F).obj i) :=
  ((systemAdjunction D A (𝟙 i)).homEquiv _ _).apply_symm_apply _ |>.trans
    ((congrArg (fun z : _ ≅ _ => NatTrans.app (Iso.inv z) F)
      (coneDirectImageComp_id D A c i)).trans (Category.id_comp _))

end IdentityLaw

end Stacks.EtaleCohomology

end
