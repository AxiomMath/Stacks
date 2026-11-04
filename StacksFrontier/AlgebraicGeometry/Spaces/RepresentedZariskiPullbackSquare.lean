module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction

/-!
# `ε^*` commutes with pullback along a morphism of representable algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S`, with underlying morphism of
schemes `g_0 : X'_0 ⟶ X_0`, and let `f = h_g : h_{T'} ⟶ h_T` be the morphism of representable
algebraic spaces it represents.  For the morphisms of ringed topoi
`ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` of
`AlgebraicGeometry.Space.representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`,
the square of pullbacks of modules

`f^* ∘ ε_T^* ≅ ε_{T'}^* ∘ g_0^*`

commutes up to a natural isomorphism.  This is the module-level form of the commutative square
of ringed sites in Stacks 08GH.

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiModulePullbackCompIso`: the natural isomorphism
  `ε_T^* ⋙ f^* ≅ g_0^* ⋙ ε_{T'}^*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The two transports of modules from the small étale site of the scheme underlying `U` to the
small étale site of `yoneda.obj U` agree. -/
def representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor (U : BigFppfOver B S hS) :
    representedModulePushforward B S hS U ≅
      (representedSmallEtaleModuleEquivalence B S hS U).functor :=
  Iso.refl _

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- **`ε^*` intertwines the two pullbacks along a morphism of representable algebraic spaces**:
`ε_T^* ⋙ f^* ≅ g_0^* ⋙ ε_{T'}^*`, for `f` the morphism of algebraic spaces represented by `g`
and `g_0` the underlying morphism of schemes. -/
def representedZariskiModulePullbackCompIso :
    representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) ≅
      Scheme.Modules.pullback (B.inclusion.map g.left) ⋙
        representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T' :=
  Functor.isoWhiskerRight
      (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS T) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
        (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS T) _ ≪≫
      representedSmallEtaleModuleEquivalencePullbackIso B S hS g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
      (associatedBigEtaleSite B) g.left).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS T').symm ≪≫
      (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS T').symm)

end AlgebraicGeometry.Space
