module

public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Functoriality of inverse image on small étale sites

A continuous functor `F : C ⥤ D` between sites whose pushforward on sheaves has a left
adjoint has an inverse image functor `F.sheafPullback A J K`, defined as a *chosen* left
adjoint. Being a choice, it is only determined up to canonical isomorphism, so the identity
and composition laws one expects of an inverse image are not available by `rfl`; they have to
be produced from the corresponding — and trivial — laws for the pushforward by uniqueness of
left adjoints. Mathlib supplies the pushforward laws
(`CategoryTheory.Functor.sheafPushforwardContinuousId`,
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`) but not the pullback ones; this file
adds them, and then specializes them to base change between small étale sites.

For small étale sites the specializations exist already for sheaves of sets, as
`AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`. The versions here hold for an
arbitrary coefficient category, which is what is needed for abelian sheaves and for sheaves of
modules, and they add the identity law, which was missing entirely.

The last group of results is the compatibility of local constancy with isomorphism of sheaves:
a sheaf isomorphic to a (finite) locally constant sheaf is itself (finite) locally constant.
Together with the two laws above this is what lets one compare the restriction of a sheaf to a
subobject computed in one step with the same restriction computed in two.

## Main definitions

* `CategoryTheory.Functor.sheafPullbackId` and
  `CategoryTheory.Functor.sheafPullbackId'` — inverse image along the identity functor, resp.
  along a functor isomorphic to it, is the identity on sheaves.
* `CategoryTheory.Functor.sheafPullbackIso` — isomorphic continuous functors have isomorphic
  inverse image functors.
* `CategoryTheory.Functor.sheafPullbackComp'` — inverse image along a composite is the
  composite of the inverse images. The special case of sheaves of sets on small sites in a
  single universe is `CategoryTheory.Functor.sheafPullbackComp`.
* `AlgebraicGeometry.smallEtaleBaseChange_idIso` — small étale base change along an identity
  morphism is the identity functor.
* `AlgebraicGeometry.smallEtaleSheafPullbackIdIso` and
  `AlgebraicGeometry.smallEtaleSheafPullbackCompIso` — the identity and composition laws for
  inverse image between small étale sites, with arbitrary coefficients.

## Main results

* `Stacks.ConstantSheaf.isLocallyConstant_congr` and
  `Stacks.ConstantSheaf.isFiniteLocallyConstant_congr` — local constancy, resp. finite local
  constancy, transfers along an isomorphism of sheaves.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃ t w u

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- Inverse image along the identity functor of a site is the identity functor on sheaves. -/
public def sheafPullbackId (A : Type u) [Category.{t} A] (J : GrothendieckTopology C)
    [((𝟭 C).sheafPushforwardContinuous A J J).IsRightAdjoint] :
    (𝟭 C).sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  Adjunction.leftAdjointUniq
    (((𝟭 C).sheafAdjunctionContinuous A J J).ofNatIsoRight
      (sheafPushforwardContinuousId A J))
    Adjunction.id

/-- Inverse image along a continuous functor isomorphic to the identity is the identity
functor on sheaves. -/
public def sheafPullbackId' {F : C ⥤ C} (e : F ≅ 𝟭 C) (A : Type u) [Category.{t} A]
    (J : GrothendieckTopology C) [F.IsContinuous J J]
    [(F.sheafPushforwardContinuous A J J).IsRightAdjoint] :
    F.sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  Adjunction.leftAdjointUniq
    ((F.sheafAdjunctionContinuous A J J).ofNatIsoRight
      (sheafPushforwardContinuousId' e A J))
    Adjunction.id

/-- Isomorphic continuous functors between sites have isomorphic inverse image functors. -/
public def sheafPullbackIso {F F' : C ⥤ D} (e : F ≅ F') (A : Type u) [Category.{t} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [F'.IsContinuous J K]
    [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(F'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    F.sheafPullback A J K ≅ F'.sheafPullback A J K :=
  Adjunction.leftAdjointUniq
    ((F.sheafAdjunctionContinuous A J K).ofNatIsoRight
      (sheafPushforwardContinuousIso e A J K))
    (F'.sheafAdjunctionContinuous A J K)

/-- When `F ⋙ G` is isomorphic to `FG`, inverse image along `FG` is the composite of the
inverse images along `F` and along `G`. -/
public def sheafPullbackComp' {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG)
    (A : Type u) [Category.{t} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L]
    [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(G.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(FG.sheafPushforwardContinuous A J L).IsRightAdjoint] :
    F.sheafPullback A J K ⋙ G.sheafPullback A K L ≅ FG.sheafPullback A J L :=
  Adjunction.leftAdjointCompIso
    (F.sheafAdjunctionContinuous A J K)
    (G.sheafAdjunctionContinuous A K L)
    (FG.sheafAdjunctionContinuous A J L)
    (sheafPushforwardContinuousComp' eFG A J K L)

end CategoryTheory.Functor

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- **Stacks 021J.** Small étale base change along an identity morphism is the identity
functor, since pullback along an identity is. -/
@[stacks 021J "small étale site functor at the identity"]
public def smallEtaleBaseChange_idIso (X : B.Scheme) :
    smallEtaleBaseChange B (𝟙 X) ≅ 𝟭 (SmallEtale B X.obj X.property) :=
  Functor.fullyFaithfulCancelRight (SmallEtale.inclusion B X.obj X.property)
    (eqToIso (smallEtaleBaseChange_comp_inclusion B (𝟙 X)) ≪≫
      Functor.isoWhiskerLeft (SmallEtale.inclusion B X.obj X.property) Over.pullbackId ≪≫
      (SmallEtale.inclusion B X.obj X.property).rightUnitor ≪≫
      (SmallEtale.inclusion B X.obj X.property).leftUnitor.symm)

/-- **Stacks 021J.** Inverse image along the identity morphism of a scheme is the identity on
sheaves on its small étale site, for any coefficient category. -/
@[stacks 021J "small étale inverse image at the identity"]
public def smallEtaleSheafPullbackIdIso (X : B.Scheme) (A : Type u₁) [Category.{v₁} A]
    [((smallEtaleBaseChange B (𝟙 X)).sheafPushforwardContinuous A
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint] :
    (smallEtaleBaseChange B (𝟙 X)).sheafPullback A
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X.obj X.property) ≅
      𝟭 (Sheaf (SmallEtale.topology B X.obj X.property) A) :=
  Functor.sheafPullbackId' (smallEtaleBaseChange_idIso B X) A _

/-- **Stacks 021J.** Inverse image along a composite of morphisms of a big étale site is the
composite of the inverse images, for any coefficient category. -/
@[stacks 021J "small étale inverse images, general coefficients"]
public def smallEtaleSheafPullbackCompIso (X Y Z : B.Scheme) (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type u₁) [Category.{v₁} A]
    [((smallEtaleBaseChange B g).sheafPushforwardContinuous A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)).IsRightAdjoint]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
    [((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint] :
    (smallEtaleBaseChange B g).sheafPullback A
        (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property) ⋙
      (smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property) ≅
    (smallEtaleBaseChange B (f ≫ g)).sheafPullback A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property) :=
  Functor.sheafPullbackComp' (smallEtaleBaseChange_compIso B X Y Z f g).val A _ _ _

end AlgebraicGeometry

namespace Stacks.ConstantSheaf

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v₂} D]

/-- **Stacks 093Q (2).** A sheaf isomorphic to a locally constant sheaf is locally
constant. -/
public theorem isLocallyConstant_congr [∀ U : C, HasWeakSheafify (J.over U) D]
    {F G : Sheaf J D} (e : F ≅ G) [hF : IsLocallyConstant J F] : IsLocallyConstant J G where
  exists_cover U := by
    obtain ⟨I, X, f, hf, h⟩ := hF.exists_cover U
    refine ⟨I, X, f, hf, fun i ↦ ?_⟩
    have := h i
    exact Sheaf.isConstant_congr _ ((J.overPullback D (X i)).mapIso e)

/-- **Stacks 093Q (3).** A sheaf isomorphic to a finite locally constant sheaf is finite
locally constant. -/
public theorem isFiniteLocallyConstant_congr {FD : D → D → Type*} {CD : D → Type w}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
    [∀ U : C, HasWeakSheafify (J.over U) D] {F G : Sheaf J D} (e : F ≅ G)
    [hF : IsFiniteLocallyConstant J F] : IsFiniteLocallyConstant J G where
  exists_finite_cover U := by
    obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
    refine ⟨I, X, f, hf, fun i ↦ ?_⟩
    obtain ⟨E, hE, ⟨c⟩⟩ := h i
    exact ⟨E, hE, ⟨c ≪≫ (J.overPullback D (X i)).mapIso e⟩⟩

end Stacks.ConstantSheaf

end
