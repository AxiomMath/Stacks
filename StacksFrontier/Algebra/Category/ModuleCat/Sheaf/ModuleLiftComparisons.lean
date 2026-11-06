module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial

/-!
# Comparing lifts of additive functors to sheaves of `Λ`-modules

`Stacks.ModuleCatLift.moduleLift` lifts an additive functor between categories of abelian
sheaves to the categories of sheaves of `Λ`-modules. This file reads morphisms and isomorphisms
of the underlying abelian sheaves as morphisms and isomorphisms of sheaves of `Λ`-modules, and
records how the construction interacts with the identity functor.

The tool that makes this cheap is a reflection principle: a morphism of sheaves of
`Λ`-modules *is* a morphism of the underlying abelian sheaves commuting with multiplication by
every scalar, and likewise for isomorphisms.

## Main definitions

* `Stacks.ModuleCatLift.sheafHomOfForget` and `Stacks.ModuleCatLift.sheafIsoOfForget` — a
  morphism, resp. isomorphism, of the underlying abelian sheaves commuting with multiplication
  by every scalar, read as a morphism, resp. isomorphism, of sheaves of `Λ`-modules.

## Main results

* `Stacks.ModuleCatLift.moduleLift_id`: the lift is compatible with the identity functor, on the
  nose.

## Implementation notes

The coefficient ring `Λ` is an arbitrary ring, not a commutative one, for the reason explained
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift`: multiplication by `a : Λ` is
used only as an endomorphism of the *underlying abelian sheaf*.

`Stacks.ModuleCatLift.sheafHomOfForget` is built at the level of sections: the `Λ`-linear map on
sections at `U` is Mathlib's `ModuleCat.homMk` applied to the component of the given morphism of
abelian sheaves, and naturality is inherited from that morphism because
`forget₂ (ModuleCat Λ) AddCommGrpCat` is faithful. The isomorphism version does not build an
inverse by hand: the morphism it produces becomes an isomorphism of abelian sheaves after
`sheafCompose J (forget₂ (ModuleCat Λ) AddCommGrpCat)`, which reflects isomorphisms.

The comparison with the identity functor is an *equality* of functors proved by `rfl`, not
merely an isomorphism. Everything in `Stacks.ModuleCatLift.moduleLift` is arranged so that
forgetting the `Λ`-module structure is the identity; `CategoryTheory.Presheaf.IsSheaf` is a
`Prop`, so no sheaf conditions need comparing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u₁ v₁ u₂ v₂

namespace Stacks.ModuleCatLift

section Reflect

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

variable {F₁ F₂ : Sheaf J (ModuleCat.{w} Λ)}

/-- A morphism of the abelian sheaves underlying two sheaves of `Λ`-modules which commutes with
multiplication by every scalar, read as a morphism of sheaves of `Λ`-modules. On sections at
`U` it is the given additive map, which is `Λ`-linear precisely by the hypothesis `h`. -/
public def sheafHomOfForget
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₁ ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₂)
    (h : ∀ a : Λ, (sheafScalarEnd Λ J F₁ a).asHom ≫ e = e ≫ (sheafScalarEnd Λ J F₂ a).asHom) :
    F₁ ⟶ F₂ :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.homMk (e.hom.app U) fun a =>
        (NatTrans.congr_app (congrArg InducedCategory.Hom.hom (h a)) U).symm
      naturality := fun _ _ g =>
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (e.hom.naturality g) }

/-- Forgetting the `Λ`-module structure of `sheafHomOfForget Λ J e h` recovers `e`. -/
@[simp]
public lemma sheafCompose_map_sheafHomOfForget
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₁ ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₂)
    (h : ∀ a : Λ, (sheafScalarEnd Λ J F₁ a).asHom ≫ e = e ≫ (sheafScalarEnd Λ J F₂ a).asHom) :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        (sheafHomOfForget Λ J e h) = e :=
  rfl

/-- An isomorphism of the abelian sheaves underlying two sheaves of `Λ`-modules which commutes
with multiplication by every scalar, read as an isomorphism of sheaves of `Λ`-modules. -/
public def sheafIsoOfForget
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₁ ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₂)
    (h : ∀ a : Λ,
      (sheafScalarEnd Λ J F₁ a).asHom ≫ e.hom = e.hom ≫ (sheafScalarEnd Λ J F₂ a).asHom) :
    F₁ ≅ F₂ :=
  haveI : IsIso ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (sheafHomOfForget Λ J e.hom h)) := by
    rw [sheafCompose_map_sheafHomOfForget]
    infer_instance
  haveI := isIso_of_reflects_iso (sheafHomOfForget Λ J e.hom h)
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
  asIso (sheafHomOfForget Λ J e.hom h)

/-- The forward morphism of `sheafIsoOfForget Λ J e h` is `sheafHomOfForget Λ J e.hom h`. -/
@[simp]
public lemma sheafIsoOfForget_hom
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₁ ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₂)
    (h : ∀ a : Λ,
      (sheafScalarEnd Λ J F₁ a).asHom ≫ e.hom = e.hom ≫ (sheafScalarEnd Λ J F₂ a).asHom) :
    (sheafIsoOfForget Λ J e h).hom = sheafHomOfForget Λ J e.hom h :=
  rfl

/-- Forgetting the `Λ`-module structure of the forward morphism of `sheafIsoOfForget Λ J e h`
recovers `e.hom`. -/
@[simp]
public lemma sheafCompose_map_sheafIsoOfForget_hom
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₁ ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F₂)
    (h : ∀ a : Λ,
      (sheafScalarEnd Λ J F₁ a).asHom ≫ e.hom = e.hom ≫ (sheafScalarEnd Λ J F₂ a).asHom) :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        (sheafIsoOfForget Λ J e h).hom = e.hom :=
  rfl

end Reflect

section Comparisons

variable (Λ : Type r) [Ring Λ] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂}
  [Category.{v₂} C₂] (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  [J₁.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J₂.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Lifting the identity functor on abelian sheaves gives the identity functor on sheaves of
`Λ`-modules, on the nose. -/
public lemma moduleLift_id :
    moduleLift Λ J₁ J₁ (𝟭 (Sheaf J₁ AddCommGrpCat.{w})) = 𝟭 (Sheaf J₁ (ModuleCat.{w} Λ)) :=
  rfl

end Comparisons

end Stacks.ModuleCatLift

end
