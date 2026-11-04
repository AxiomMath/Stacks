module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Pasting
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase

/-!
# Transport of base-change invertibility along isomorphisms of the four corners

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
whether the canonical base-change morphism `g^* f_* ⟶ f'_* (g')^*` is invertible at a module
depends on the square only up to isomorphism of its four corners.  This file proves that, in
the form needed to replace a cartesian square of affine schemes by the square of spectra of
its rings of global sections.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isEquivalence_pullback`: the inverse image
  along an isomorphism of schemes is an equivalence.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.baseChangeNatTrans_app`: the base-change
  morphism at a module as a composite of three factors.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isIso`: the
  base-change morphism of a square whose two horizontal morphisms are isomorphisms is
  invertible.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_cornerIso`:
  **the transport.**  Two squares whose corners are identified compatibly have invertible
  base-change morphisms together.

## Route

The three-factor formula is the definition of the mate, obtained by `simp`.  In it the outer
two factors are a unit and a counit of the two inverse-image--direct-image adjunctions, and
when both horizontal morphisms are isomorphisms both adjunctions are adjoint equivalences, so
both are invertible; that is `isIso_baseChangeNatTrans_of_isIso`.

The transport is then **two horizontal pastings** of
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.baseChangeNatTrans_paste`, one on each side of
the model square, so no pasting lemma for vertical composition is needed: the square of
isomorphisms on the left and the square of isomorphisms on the right are each pasted
horizontally, and in both composites every factor other than the model one is invertible by
`isIso_baseChangeNatTrans_of_isIso` or because it is a component of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.  The two equalities of horizontal morphisms
are discharged by `subst`, which is legitimate because the base-change morphism depends on the
proof of commutativity only through proof irrelevance.

Every `IsIso` for a composite is supplied by writing out `CategoryTheory.IsIso.comp_isIso`
with its arguments: the category structure on `AlgebraicGeometry.Scheme.Modules` is a
different instance from the one on `SheafOfModules`, equal to it only after unfolding a
definition that is not reducible, and instance search does not see through that.

## What is not done

**No assertion of [Stacks, Tag 02KG] is proved here, and no project tag attribute is
attached.**  No cartesian square and no quasi-coherent module appear: nothing here exhibits a
square whose base-change morphism is invertible except one whose horizontal morphisms are
already isomorphisms, which is a triviality.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.TwoSquare
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeIso

/-- The inverse image along an isomorphism of schemes is an equivalence. -/
lemma isEquivalence_pullback {X Y : Scheme.{u}} (h : X ⟶ Y) [IsIso h] :
    (Scheme.Modules.pullback h).IsEquivalence := by
  have : (Scheme.Modules.restrictFunctor h).IsEquivalence :=
    Stacks.AlgebraicGeometry.CoherentKernel.isEquivalence_restrictFunctor_inv (asIso h).symm
  exact Functor.isEquivalence_of_iso (Scheme.Modules.restrictFunctorIsoPullback h)

/-- Explicit-argument form of `IsIso.comp_isIso`, usable where instance search does not see
through the category structure on `Scheme.Modules`. -/
private theorem isIso_comp_of_isIso {C : Type*} [Category C] {A B D : C} {f : A ⟶ B}
    {g : B ⟶ D} (hf : IsIso f) (hg : IsIso g) : IsIso (f ≫ g) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ hf hg

section Model

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The base-change morphism of a square whose two horizontal morphisms are isomorphisms is
invertible. -/
theorem isIso_baseChangeNatTrans_of_isIso (w : g' ≫ f = f' ≫ g) [IsIso g'] [IsIso g]
    (F : X.Modules) : IsIso ((AffinePushforward.baseChangeNatTrans w).app F) := by
  have := isEquivalence_pullback g'
  have := isEquivalence_pullback g
  rw [Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeNatTrans_app_eq]
  have a1 : IsIso ((Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F))) := by
    have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) :=
      NatIso.isIso_app_of_isIso _ _
    exact Functor.map_isIso _ _
  have a2 : IsIso ((Scheme.Modules.pullback g).map
      ((AffinePushforward.pushforwardSquareIso w).hom.app
        ((Scheme.Modules.pullback g').obj F))) := Functor.map_isIso _ _
  have a3 : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
      ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F))) :=
    NatIso.isIso_app_of_isIso _ _
  exact isIso_comp_of_isIso a1 (isIso_comp_of_isIso a2 a3)

end Model

section Transport

variable {X'₁ X₁ S'₁ S₁ X'₂ X₂ S'₂ S₂ : Scheme.{u}}
  {g'₁ : X'₁ ⟶ X₁} {f'₁ : X'₁ ⟶ S'₁} {f₁ : X₁ ⟶ S₁} {g₁ : S'₁ ⟶ S₁}
  {g'₂ : X'₂ ⟶ X₂} {f'₂ : X'₂ ⟶ S'₂} {f₂ : X₂ ⟶ S₂} {g₂ : S'₂ ⟶ S₂}

/-- Pasting the model square on the left with a square whose horizontal morphisms are
isomorphisms leaves the base-change morphism invertible. -/
lemma isIso_baseChangeNatTrans_pasteLeft (w₂ : g'₂ ≫ f₂ = f'₂ ≫ g₂) {a : X'₁ ⟶ X'₂}
    {c : S'₁ ⟶ S'₂} [IsIso a] [IsIso c] (wa : a ≫ f'₂ = f'₁ ≫ c) (M : X₂.Modules)
    (H : IsIso ((AffinePushforward.baseChangeNatTrans w₂).app M)) :
    IsIso ((AffinePushforward.baseChangeNatTrans (comp_square w₂ wa)).app M) := by
  rw [baseChangeNatTrans_comp_square_app w₂ wa]
  have b1 : IsIso ((Scheme.Modules.pullbackComp c g₂).inv.app
      ((Scheme.Modules.pushforward f₂).obj M)) := inferInstance
  have b2 : IsIso ((Scheme.Modules.pullback c).map
      ((AffinePushforward.baseChangeNatTrans w₂).app M)) := Functor.map_isIso _ _
  have b3 : IsIso ((AffinePushforward.baseChangeNatTrans wa).app
      ((Scheme.Modules.pullback g'₂).obj M)) := isIso_baseChangeNatTrans_of_isIso _ _
  have b4 : IsIso ((Scheme.Modules.pushforward f'₁).map
      ((Scheme.Modules.pullbackComp a g'₂).hom.app M)) := Functor.map_isIso _ _
  exact isIso_comp_of_isIso b1 (isIso_comp_of_isIso b2 (isIso_comp_of_isIso b3 b4))

/-- **Transport of base-change invertibility along isomorphisms of the four corners.**  If the
two squares are identified by isomorphisms `a`, `b`, `c`, `d` of their corners, compatibly
with the vertical morphisms and with the horizontal ones, then invertibility of the
base-change morphism of the second gives invertibility of the base-change morphism of the
first. -/
theorem isIso_baseChangeNatTrans_of_cornerIso (w₁ : g'₁ ≫ f₁ = f'₁ ≫ g₁)
    (w₂ : g'₂ ≫ f₂ = f'₂ ≫ g₂) {a : X'₁ ⟶ X'₂} {b : X₂ ⟶ X₁} {c : S'₁ ⟶ S'₂} {d : S₂ ⟶ S₁}
    [IsIso a] [IsIso b] [IsIso c] [IsIso d]
    (wa : a ≫ f'₂ = f'₁ ≫ c) (wb : b ≫ f₁ = f₂ ≫ d)
    (hg' : (a ≫ g'₂) ≫ b = g'₁) (hg : (c ≫ g₂) ≫ d = g₁) (F : X₁.Modules)
    (H : IsIso ((AffinePushforward.baseChangeNatTrans w₂).app
      ((Scheme.Modules.pullback b).obj F))) :
    IsIso ((AffinePushforward.baseChangeNatTrans w₁).app F) := by
  have hin := isIso_baseChangeNatTrans_pasteLeft w₂ wa ((Scheme.Modules.pullback b).obj F) H
  have hout : IsIso ((AffinePushforward.baseChangeNatTrans
      (comp_square wb (comp_square w₂ wa))).app F) := by
    rw [baseChangeNatTrans_comp_square_app wb (comp_square w₂ wa)]
    have b1 : IsIso ((Scheme.Modules.pullbackComp (c ≫ g₂) d).inv.app
        ((Scheme.Modules.pushforward f₁).obj F)) := inferInstance
    have b2 : IsIso ((Scheme.Modules.pullback (c ≫ g₂)).map
        ((AffinePushforward.baseChangeNatTrans wb).app F)) := by
      have : IsIso ((AffinePushforward.baseChangeNatTrans wb).app F) :=
        isIso_baseChangeNatTrans_of_isIso _ _
      exact Functor.map_isIso _ _
    have b4 : IsIso ((Scheme.Modules.pushforward f'₁).map
        ((Scheme.Modules.pullbackComp (a ≫ g'₂) b).hom.app F)) := Functor.map_isIso _ _
    exact isIso_comp_of_isIso b1 (isIso_comp_of_isIso b2 (isIso_comp_of_isIso hin b4))
  subst hg'
  subst hg
  exact hout

end Transport

end Stacks.AlgebraicGeometry.AffineBaseChangeIso

end
