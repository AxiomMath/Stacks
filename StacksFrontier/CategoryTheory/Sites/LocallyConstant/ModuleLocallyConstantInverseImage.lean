module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianRelocalizationAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleLiftComparisons
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleLiftOverPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Locally constant sheaves of modules and the inverse image of a morphism of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two small
sites — an adjoint pair with left exact inverse image, and no functor between the sites. Tag 093R
asserts that `f⁻¹` carries a locally constant sheaf of sets, groups, abelian groups, rings or
modules over a fixed ring to a locally constant sheaf of the same kind. This file proves the
assertion for sheaves of **modules over a fixed ring `Λ`**, with `Λ` an arbitrary ring, not
assumed commutative, no finiteness assumption on the local values and no final object in either
site.

## The route, and why it is not the one the groups and abelian groups cases take

The sets, groups and abelian groups cases all read the algebraic operations as an *internal*
object of the topos of sheaves of sets, push it along a finite-product-preserving functor, and
read the operations back sectionwise. For modules over a fixed ring that route is unavailable:
there is no notion of an internal module over a fixed external ring in Mathlib at all.
`Mathlib/CategoryTheory/Monoidal/Mod.lean`'s `Mod_` is a module over an *internal* monoid acting
through a `MonoidalLeftAction`, and `Mathlib/CategoryTheory/Monoidal/Internal/Module.lean`
identifies `Mon_ (ModuleCat R)` with `AlgCat R`; neither is a module over a fixed external ring.

So a sheaf of `Λ`-modules is handled here as its underlying abelian sheaf together with the ring
map `Λ →+* End` given by multiplication by scalars, which is `ModuleCat.smulNatTrans` and needs no
commutativity; and the abelian relocalization of
`StacksFrontier/CategoryTheory/Sites/LocallyConstant/AbelianLocallyConstantInverseImage.lean` is
transported along `Stacks.ModuleCatLift.moduleLift`, the lift of an additive functor on abelian
sheaves to sheaves of `Λ`-modules. The two functors that get transported are additive by
`CategoryTheory.Sites.abelianInverseImage_additive` and
`MorphismOfTopoi.abelianSectionRelocalization_additive`.

What makes the transport cheap is that `Stacks.ModuleCatLift.moduleLift` is compatible with
composition, with the identity and with restriction to a slice site *on the nose*
(`Stacks.ModuleCatLift.moduleLift_comp`, `Stacks.ModuleCatLift.moduleLift_id` and
`Stacks.ModuleCatLift.moduleLift_overPullback` are all equalities of functors proved by `rfl`).
Consequently the compatibility of the relocalization with restriction,
`MorphismOfTopoi.moduleSectionRelocalizationOverPullbackIso`, is literally the lift of the
abelian one by `Stacks.ModuleCatLift.moduleLiftNatIso`: no comparison has to be inserted at
either end.

The one comparison the lift does not supply is for *constant* sheaves, since
`constantSheaf J (ModuleCat Λ)` is not the lift of anything. It is
`Stacks.ModuleCatLift.moduleLiftConstantSheafIso`, proved in the first section below for an
arbitrary additive functor rather than for the relocalization: the crossings between
`ModuleCat Λ` and `AddCommGrpCat` it needs are instances of `rfl` lemmas, and those are
only cheap while the functor is a variable the elaborator cannot unfold.

## The faithfulness anchor

`CategoryTheory.Sites.moduleInverseImage_forgetTypesIso` identifies the sheaf of *sets*
underlying `CategoryTheory.Sites.moduleInverseImage f Λ` applied to a sheaf of `Λ`-modules with
`f.inverseImage` of the sheaf of sets underlying it. Both halves of it are identities
(`Stacks.ModuleCatLift.moduleLift_comp_sheafCompose`, an equality of functors, followed by
`CategoryTheory.Sites.abelianInverseImage_forgetIso`, which is `Iso.refl`). This is what makes
the tag below a statement about the inverse image of the morphism of topoi and not about a
neighbouring functor; the groups and abelian groups cases are anchored the same way.

## Main definitions

* `Stacks.ModuleCatLift.moduleLiftConstantSheafIso` — an additive functor on abelian sheaves
  which carries constant abelian sheaves to constant abelian sheaves lifts to a functor on
  sheaves of `Λ`-modules which carries constant sheaves to constant sheaves, with the same
  trivializing module.
* `CategoryTheory.Sites.moduleInverseImage` — the inverse image of sheaves of `Λ`-modules
  attached to a morphism of topoi, with
  `CategoryTheory.Sites.moduleInverseImage_forgetIso` identifying its underlying abelian sheaf
  with the abelian inverse image and
  `CategoryTheory.Sites.moduleInverseImage_forgetTypesIso` its underlying sheaf of sets with
  `f⁻¹`.
* `MorphismOfTopoi.moduleSectionRelocalization` — the relocalization along a section, acting on
  sheaves of `Λ`-modules.
* `MorphismOfTopoi.moduleSectionRelocalizationOverPullbackIso` — it carries the restriction of a
  sheaf of `Λ`-modules to `Y` to the restriction of its inverse image to `V`.
* `MorphismOfTopoi.moduleSectionRelocalizationConstantSheafIso` — it carries the constant sheaf
  of `Λ`-modules on a module to the constant sheaf of `Λ`-modules on the same module.
* `MorphismOfTopoi.moduleConstantIsoOverPullbackInverseImageOfSection` — a trivialization of `G`
  over `Y` plus a section `h_V^# ⟶ f⁻¹h_Y^#` give a trivialization of the inverse image of `G`
  over `V`, with the same value.

## Main results

* `MorphismOfTopoi.isLocallyConstant_moduleInverseImage_of_smallSites` — **Tag 093R** for locally
  constant sheaves of modules over a fixed ring: the inverse image of a locally constant sheaf of
  `Λ`-modules along an arbitrary morphism of topoi between the topoi of sheaves of sets on two
  small sites is locally constant.

## What of Tag 093R is *not* proved here

The source's list is "sets, groups, abelian groups, rings, modules over a fixed ring `Λ`, etc".
Four of the five are now carried: the sets case is
`MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites`, the groups case is
`MorphismOfTopoi.isLocallyConstant_grpInverseImage_of_smallSites`, the abelian groups case is
`MorphismOfTopoi.isLocallyConstant_abelianInverseImage_of_smallSites`, and the case of modules
over a fixed ring is below. Only **rings** remain.

The case of sheaves of **rings** is not proved, at this generality, anywhere in the library, and
the obstruction is a missing tool rather than a missing argument.
`Mathlib/CategoryTheory/Monoidal/Ring.lean` gives `RingObj`, `CommRingObj`, `RingObjCat C`,
`CommRingObjCat C` and the forgetful functors between them, and nothing else: there is no
`mapRingObj`, so a finite-product-preserving functor does not act on internal ring objects at
all, and there is no identification of `RingObjCat (Type u)` with `RingCat`. Neither does the
route taken in this file apply, since multiplication is not an endomorphism of an underlying
abelian sheaf.

For sheaves of rings the library does have the weaker
`Stacks.ConstantSheaf.isLocallyConstant_sheafPullback`, which holds for an arbitrary coefficient
category but only for the inverse image along a *morphism of sites*, i.e. along a continuous left
exact cover-preserving functor between the two sites; a morphism of topoi need not be induced by
one.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites Opposite
open Stacks.ConstantSheaf Stacks.ModuleCatLift

universe w r

/-! ### The side conditions on the coefficient category

Sheaves of `Λ`-modules need four things of the coefficient category which `AddCommGrpCat` gets
from Mathlib: that postcomposition with the forgetful functor to abelian groups carries sheaves
to sheaves and commutes with sheafification, and that presheaves of `Λ`-modules sheafify, on the
site and on its slice sites. All four are proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ModuleSheafSideConditions.lean` for an arbitrary
ring `Λ`, each with the single hypothesis `UnivLE.{max u v, w}` relating the universes of the
site to the universe of the modules. On the small sites of this file that inequality is
`UnivLE.{w, w}`, so marking the four as local instances discharges them outright and none of the
statements below carries any of them as a hypothesis. -/

attribute [local instance] Stacks.ModuleSheaf.hasSheafCompose_forget₂
  Stacks.ModuleSheaf.hasSheafify_moduleCat Stacks.ModuleSheaf.hasSheafify_over_moduleCat
  Stacks.ModuleSheaf.preservesSheafification_forget₂

section SideConditions

/-- Two commuting squares side by side commute. Used below both for the naturality and for the
`Λ`-equivariance of a comparison built as a composite of three factors: each is assembled out of
the corresponding property of the factors, with no composite ever unfolded. -/
private lemma comp_square {A : Type*} [Category A] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : A}
    {p : X₁ ⟶ X₂} (q : Y₁ ⟶ Y₂) {r : Z₁ ⟶ Z₂} {u₁ : X₁ ⟶ Y₁} {u₂ : X₂ ⟶ Y₂}
    {v₁ : Y₁ ⟶ Z₁} {v₂ : Y₂ ⟶ Z₂} (hu : p ≫ u₂ = u₁ ≫ q) (hv : q ≫ v₂ = v₁ ≫ r) :
    p ≫ u₂ ≫ v₂ = (u₁ ≫ v₁) ≫ r := by
  rw [reassoc_of% hu, hv, Category.assoc]

end SideConditions

namespace Stacks.ModuleCatLift

/-! ### The constant sheaf and the lift of an additive functor

The lift `Stacks.ModuleCatLift.moduleLift` of an additive functor `G` on abelian sheaves comes
with the identification of its underlying abelian sheaf with `G` of the underlying abelian sheaf;
what it does not come with is a comparison for *constant* sheaves, because `constantSheaf J
(ModuleCat Λ)` is not the lift of anything. This section supplies it: a natural isomorphism
identifying `G` of the constant abelian sheaf with the constant abelian sheaf lifts to one
identifying `moduleLift G` of the constant sheaf of `Λ`-modules with the constant sheaf of
`Λ`-modules.

The whole section is stated for an arbitrary additive `G` on purpose. Every crossing between
`ModuleCat Λ` and `AddCommGrpCat` below is an instance of an `rfl` lemma of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EndActionLift.lean`, and those are only cheap while
`G` is opaque: with `G` a definition that the elaborator may unfold — such as the abelian
relocalization along a section, which internalizes the group operations — the same crossings cost
more than a declaration's whole heartbeat budget. Specializing a statement proved here costs
nothing, since instantiating a variable needs no unfolding at all. -/

variable (Λ : Type r) [Ring Λ] {C₁ : Type w} [Category.{w} C₁] {C₂ : Type w} [Category.{w} C₂]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (G : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w}) [G.Additive]
  (e : constantSheaf J₁ AddCommGrpCat.{w} ⋙ G ≅ constantSheaf J₂ AddCommGrpCat.{w})

/-- **The abelian sheaf underlying the lift of `G` applied to a constant sheaf of `Λ`-modules is
the constant abelian sheaf.**

Three factors: the abelian sheaf underlying the lift is `G` of the underlying abelian sheaf
(`Stacks.ModuleCatLift.moduleLift_comp_sheafCompose`, the single crossing between `ModuleCat Λ`
and `AddCommGrpCat` made here), the abelian sheaf underlying a constant sheaf of `Λ`-modules is
the constant abelian sheaf (`Stacks.ModuleCatLift.constantSheafForget₂Iso`), and `G` carries the
constant abelian sheaf to the constant abelian sheaf, which is the hypothesis `e`. The
trivializing module is unchanged. -/
public def moduleLiftConstantSheafForgetIsoApp (E : ModuleCat.{w} Λ) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
        ((moduleLift Λ J₁ J₂ G).obj ((constantSheaf J₁ (ModuleCat.{w} Λ)).obj E)) ≅
      (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
        ((constantSheaf J₂ (ModuleCat.{w} Λ)).obj E) :=
  G.mapIso ((constantSheafForget₂Iso Λ J₁).app E) ≪≫
    (e.app ((forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).obj E) ≪≫
      ((constantSheafForget₂Iso Λ J₂).app E).symm)

/-- `Stacks.ModuleCatLift.moduleLiftConstantSheafForgetIsoApp` written out as the composite of its
three factors. -/
public lemma moduleLiftConstantSheafForgetIsoApp_hom (E : ModuleCat.{w} Λ) :
    (moduleLiftConstantSheafForgetIsoApp Λ J₁ J₂ G e E).hom =
      G.map ((constantSheafForget₂Iso Λ J₁).hom.app E) ≫
        (e.hom.app ((forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).obj E) ≫
          ((constantSheafForget₂Iso Λ J₂).app E).inv) :=
  rfl

/-- The square for `G` applied to `φ₁` and `φ₂` on the three factors of
`Stacks.ModuleCatLift.moduleLiftConstantSheafForgetIsoApp` commutes once `φ₁` and `φ₂` both
correspond to `ψ` under `Stacks.ModuleCatLift.constantSheafForget₂Iso`. -/
private lemma map_comp_forgetIsoApp_hom_eq {E₁ E₂ : ModuleCat.{w} Λ} {φ₁ φ₂ : _ ⟶ _}
    (ψ : (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).obj E₁ ⟶
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).obj E₂)
    (h₁ : φ₁ ≫ (constantSheafForget₂Iso Λ J₁).hom.app E₂ =
      (constantSheafForget₂Iso Λ J₁).hom.app E₁ ≫ (constantSheaf J₁ AddCommGrpCat.{w}).map ψ)
    (h₃ : φ₂ ≫ (constantSheafForget₂Iso Λ J₂).hom.app E₂ =
      (constantSheafForget₂Iso Λ J₂).hom.app E₁ ≫ (constantSheaf J₂ AddCommGrpCat.{w}).map ψ) :
    G.map φ₁ ≫ (moduleLiftConstantSheafForgetIsoApp Λ J₁ J₂ G e E₂).hom =
      (moduleLiftConstantSheafForgetIsoApp Λ J₁ J₂ G e E₁).hom ≫ φ₂ := by
  rw [moduleLiftConstantSheafForgetIsoApp_hom, moduleLiftConstantSheafForgetIsoApp_hom]
  refine comp_square _ ?_ (comp_square _ (e.hom.naturality ψ) ?_)
  · exact ((G.map_comp _ _).symm.trans (congrArg G.map h₁)).trans (G.map_comp _ _)
  · rw [← cancel_epi ((constantSheafForget₂Iso Λ J₂).hom.app E₁), ← Category.assoc, ← h₃]
    simp

/-- **`Stacks.ModuleCatLift.moduleLiftConstantSheafForgetIsoApp` is natural in the module**: each
of its three factors is, the first after applying `G`. -/
public lemma moduleLiftConstantSheafForgetIsoApp_naturality {E₁ E₂ : ModuleCat.{w} Λ}
    (g : E₁ ⟶ E₂) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        ((moduleLift Λ J₁ J₂ G).map ((constantSheaf J₁ (ModuleCat.{w} Λ)).map g)) ≫
        (moduleLiftConstantSheafForgetIsoApp Λ J₁ J₂ G e E₂).hom =
      (moduleLiftConstantSheafForgetIsoApp Λ J₁ J₂ G e E₁).hom ≫
        (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
          ((constantSheaf J₂ (ModuleCat.{w} Λ)).map g) := by
  rw [show (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        ((moduleLift Λ J₁ J₂ G).map ((constantSheaf J₁ (ModuleCat.{w} Λ)).map g)) = _ from
      sheafCompose_map_moduleLiftMap Λ J₁ J₂ G _]
  exact map_comp_forgetIsoApp_hom_eq Λ J₁ J₂ G e _
    ((constantSheafForget₂Iso Λ J₁).hom.naturality g)
    ((constantSheafForget₂Iso Λ J₂).hom.naturality g)

/-- **`Stacks.ModuleCatLift.moduleLiftConstantSheafForgetIsoApp` is `Λ`-equivariant.** Each of its
three factors is: the first because `G` is a functor and
`Stacks.ModuleCatLift.constantSheafForget₂Iso` is equivariant on `J₁`, the second by naturality
of `e` at multiplication by the scalar, and the third because
`Stacks.ModuleCatLift.constantSheafForget₂Iso` is equivariant on `J₂`. -/
public lemma moduleLiftConstantSheafForgetIsoApp_scalar (E : ModuleCat.{w} Λ) (a : Λ) :
    sheafScalarEnd Λ J₂
          ((moduleLift Λ J₁ J₂ G).obj ((constantSheaf J₁ (ModuleCat.{w} Λ)).obj E)) a ≫
        (moduleLiftConstantSheafForgetIsoApp Λ J₁ J₂ G e E).hom =
      (moduleLiftConstantSheafForgetIsoApp Λ J₁ J₂ G e E).hom ≫
        sheafScalarEnd Λ J₂ ((constantSheaf J₂ (ModuleCat.{w} Λ)).obj E) a := by
  rw [sheafScalarEnd_moduleLift_obj]
  exact map_comp_forgetIsoApp_hom_eq Λ J₁ J₂ G e ((ModuleCat.smulNatTrans Λ a).app E)
    (constantSheafForget₂Iso_hom_app_scalar Λ J₁ E a)
    (constantSheafForget₂Iso_hom_app_scalar Λ J₂ E a)

/-- **The lift of an additive functor carries the constant sheaf of `Λ`-modules on a module to
the constant sheaf of `Λ`-modules on the same module**, naturally in the module, as soon as the
functor does so for abelian groups.

The comparison of the underlying abelian sheaves is
`Stacks.ModuleCatLift.moduleLiftConstantSheafForgetIsoApp`, which is `Λ`-equivariant, so
`Stacks.ModuleCatLift.sheafIsoOfForget` reads it as an isomorphism of sheaves of `Λ`-modules; its
naturality is `Stacks.ModuleCatLift.moduleLiftConstantSheafForgetIsoApp_naturality`, the
forgetful functor on sheaves being faithful. -/
public def moduleLiftConstantSheafIso :
    constantSheaf J₁ (ModuleCat.{w} Λ) ⋙ moduleLift Λ J₁ J₂ G ≅
      constantSheaf J₂ (ModuleCat.{w} Λ) :=
  NatIso.ofComponents
    (fun E => sheafIsoOfForget Λ J₂ (moduleLiftConstantSheafForgetIsoApp Λ J₁ J₂ G e E)
      (moduleLiftConstantSheafForgetIsoApp_scalar Λ J₁ J₂ G e E))
    fun {_ _} g => (sheafCompose J₂
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
      rw [Functor.map_comp, Functor.map_comp, sheafCompose_map_sheafIsoOfForget_hom,
        sheafCompose_map_sheafIsoOfForget_hom]
      exact moduleLiftConstantSheafForgetIsoApp_naturality Λ J₁ J₂ G e g)

end Stacks.ModuleCatLift

namespace CategoryTheory.Sites

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) (Λ : Type r) [Ring Λ]

/-- **The inverse image of sheaves of `Λ`-modules attached to a morphism of topoi.** A sheaf of
`Λ`-modules is its underlying abelian sheaf together with multiplication by the scalars; the
abelian inverse image `CategoryTheory.Sites.abelianInverseImage` is additive, so it carries
multiplication by a scalar to multiplication by that scalar, and
`Stacks.ModuleCatLift.moduleLift` assembles the result. -/
public def moduleInverseImage : Sheaf K (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} Λ) :=
  moduleLift Λ K J (abelianInverseImage f)

/-- **Forgetting the `Λ`-module structure recovers the abelian inverse image**, naturally in the
sheaf. The isomorphism is the identity: the two composites are the same functor, by
`Stacks.ModuleCatLift.moduleLift_comp_sheafCompose`. -/
public def moduleInverseImage_forgetIso :
    moduleInverseImage f Λ ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      sheafCompose K (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙ abelianInverseImage f :=
  moduleLiftForgetIso Λ K J (abelianInverseImage f)

/-- **The faithfulness anchor: the sheaf of sets underlying the inverse image of a sheaf of
`Λ`-modules is `f⁻¹` of the sheaf of sets underlying it.** This is what makes the tag below a
statement about the inverse image of the morphism of topoi and not about some neighbouring
functor. Both halves are identities: forgetting the `Λ`-module structure of the lift is
`Stacks.ModuleCatLift.moduleLift_comp_sheafCompose`, an equality of functors, and forgetting the
abelian group operations of the abelian inverse image is
`CategoryTheory.Sites.abelianInverseImage_forgetIso`, which is `Iso.refl`. -/
public def moduleInverseImage_forgetTypesIso :
    (moduleInverseImage f Λ ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})) ⋙
        sheafCompose J (forget AddCommGrpCat.{w}) ≅
      sheafCompose K (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙
        sheafCompose K (forget AddCommGrpCat.{w}) ⋙ f.inverseImage :=
  Functor.isoWhiskerRight (moduleInverseImage_forgetIso f Λ)
      (sheafCompose J (forget AddCommGrpCat.{w})) ≪≫
    Functor.isoWhiskerLeft (sheafCompose K (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
      (abelianInverseImage_forgetIso f)

end CategoryTheory.Sites

namespace MorphismOfTopoi

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

section Relocalization

variable {V : C} {Y : D}
  (σ : (presheafToSheaf J (Type w)).obj (yoneda.obj V) ⟶
    f.inverseImage.obj ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)))
  (Λ : Type r) [Ring Λ]

/-- **The relocalization along a section, acting on sheaves of `Λ`-modules.** The abelian
relocalization `MorphismOfTopoi.abelianSectionRelocalization` is additive, so it carries
multiplication by a scalar on the underlying abelian sheaf to multiplication by that scalar, and
`Stacks.ModuleCatLift.moduleLift` assembles the result. -/
public def moduleSectionRelocalization :
    Sheaf (K.over Y) (ModuleCat.{w} Λ) ⥤ Sheaf (J.over V) (ModuleCat.{w} Λ) :=
  moduleLift Λ (K.over Y) (J.over V) (abelianSectionRelocalization J K f σ)

/-- Restricting a sheaf of `Λ`-modules to `Y` and then relocalizing is the lift of the composite
of the abelian restriction with the abelian relocalization: restriction commutes with the lift by
`Stacks.ModuleCatLift.moduleLift_overPullback` and composition by
`Stacks.ModuleCatLift.moduleLift_comp`, both on the nose. -/
public lemma overPullback_comp_moduleSectionRelocalization :
    K.overPullback (ModuleCat.{w} Λ) Y ⋙ moduleSectionRelocalization J K f σ Λ =
      moduleLift Λ K (J.over V)
        (K.overPullback AddCommGrpCat.{w} Y ⋙ abelianSectionRelocalization J K f σ) := by
  change moduleLift Λ K (K.over Y) (K.overPullback AddCommGrpCat.{w} Y) ⋙
    moduleLift Λ (K.over Y) (J.over V) (abelianSectionRelocalization J K f σ) = _
  rw [← moduleLift_comp]

/-- Taking the inverse image of a sheaf of `Λ`-modules and then restricting to `V` is the lift of
the composite of the abelian inverse image with the abelian restriction, for the same two
reasons. -/
public lemma moduleInverseImage_comp_overPullback :
    CategoryTheory.Sites.moduleInverseImage f Λ ⋙ J.overPullback (ModuleCat.{w} Λ) V =
      moduleLift Λ K (J.over V)
        (CategoryTheory.Sites.abelianInverseImage f ⋙ J.overPullback AddCommGrpCat.{w} V) := by
  change moduleLift Λ K J (CategoryTheory.Sites.abelianInverseImage f) ⋙
    moduleLift Λ J (J.over V) (J.overPullback AddCommGrpCat.{w} V) = _
  rw [← moduleLift_comp]

/-- **The relocalization carries the restriction of a sheaf of `Λ`-modules to `Y` to the
restriction of its inverse image to `V`**, naturally in the sheaf.

This is the lift of `MorphismOfTopoi.abelianSectionRelocalizationOverPullbackIso` by
`Stacks.ModuleCatLift.moduleLiftNatIso`, and nothing more: both sides of the statement are
already lifts of the two sides of the abelian isomorphism, by
`MorphismOfTopoi.overPullback_comp_moduleSectionRelocalization` and
`MorphismOfTopoi.moduleInverseImage_comp_overPullback`. -/
public def moduleSectionRelocalizationOverPullbackIso :
    K.overPullback (ModuleCat.{w} Λ) Y ⋙ moduleSectionRelocalization J K f σ Λ ≅
      CategoryTheory.Sites.moduleInverseImage f Λ ⋙ J.overPullback (ModuleCat.{w} Λ) V :=
  eqToIso (overPullback_comp_moduleSectionRelocalization J K f σ Λ) ≪≫
    moduleLiftNatIso Λ K (J.over V) (G := _) (G' := _)
      (abelianSectionRelocalizationOverPullbackIso J K f σ) ≪≫
    eqToIso (moduleInverseImage_comp_overPullback J K f Λ).symm

/-- **The relocalization carries the constant sheaf of `Λ`-modules on a module to the constant
sheaf of `Λ`-modules on the same module**, naturally in the module.

This is `Stacks.ModuleCatLift.moduleLiftConstantSheafIso` fed the abelian comparison
`MorphismOfTopoi.abelianSectionRelocalizationConstantSheafIso`. The trivializing module is
unchanged. -/
public def moduleSectionRelocalizationConstantSheafIso :
    constantSheaf (K.over Y) (ModuleCat.{w} Λ) ⋙ moduleSectionRelocalization J K f σ Λ ≅
      constantSheaf (J.over V) (ModuleCat.{w} Λ) :=
  moduleLiftConstantSheafIso Λ (K.over Y) (J.over V) (abelianSectionRelocalization J K f σ)
    (abelianSectionRelocalizationConstantSheafIso J K f σ)

/-- **A trivialization of a sheaf of `Λ`-modules survives the inverse image along a section, with
the same value.** If `G` restricted to `Y` is the constant sheaf of `Λ`-modules on a module `E`,
and `V` carries a section of `f⁻¹h_Y^#`, then the inverse image of `G` restricted to `V` is the
constant sheaf of `Λ`-modules on the same `E`.

Apply `MorphismOfTopoi.moduleSectionRelocalization` to the trivialization and read the two sides
with `MorphismOfTopoi.moduleSectionRelocalizationConstantSheafIso` and
`MorphismOfTopoi.moduleSectionRelocalizationOverPullbackIso`. -/
public def moduleConstantIsoOverPullbackInverseImageOfSection
    (G : Sheaf K (ModuleCat.{w} Λ)) (E : ModuleCat.{w} Λ)
    (c : (constantSheaf (K.over Y) (ModuleCat.{w} Λ)).obj E ≅
      (K.overPullback (ModuleCat.{w} Λ) Y).obj G) :
    (constantSheaf (J.over V) (ModuleCat.{w} Λ)).obj E ≅
      (J.overPullback (ModuleCat.{w} Λ) V).obj
        ((CategoryTheory.Sites.moduleInverseImage f Λ).obj G) :=
  ((moduleSectionRelocalizationConstantSheafIso J K f σ Λ).app E).symm ≪≫
    (moduleSectionRelocalization J K f σ Λ).mapIso c ≪≫
    (moduleSectionRelocalizationOverPullbackIso J K f σ Λ).app G

end Relocalization

/-- **Tag 093R for locally constant sheaves of modules over a fixed ring.** The inverse image of a
locally constant sheaf of `Λ`-modules along an arbitrary morphism of topoi between the topoi of
sheaves of sets on two small sites is locally constant.

No functor between the two sites, no final object in either, no commutativity of `Λ` and no
finiteness of the local values is assumed. The covering of an object `U` of `C` is the one
`Stacks.Topos.exists_cover_inverseImage_sections` produces for the family of sheaves represented
by the objects of `D` over which `G` is trivialized as a sheaf of `Λ`-modules, and on a member `V`
of it the section it carries trivializes the inverse image over `V`, with the same trivializing
module, by `MorphismOfTopoi.moduleConstantIsoOverPullbackInverseImageOfSection`. -/
@[stacks 093R "locally constant sheaves of modules over a fixed ring, for an arbitrary morphism \
  of topoi between the topoi of sheaves of sets on two small sites"]
public lemma isLocallyConstant_moduleInverseImage_of_smallSites (Λ : Type r) [Ring Λ]
    (G : Sheaf K (ModuleCat.{w} Λ)) [hG : IsLocallyConstant K G] :
    IsLocallyConstant J ((CategoryTheory.Sites.moduleInverseImage f Λ).obj G) where
  exists_cover U := by
    obtain ⟨T, hT⟩ := Stacks.Topos.exists_cover_inverseImage_sections f
      (Stacks.Topos.representedFamily K
        fun Y => Sheaf.IsConstant (K.over Y)
          ((K.overPullback (ModuleCat.{w} Λ) Y).obj G))
      (Stacks.Topos.jointlyLocallyInhabited_representedFamily K _
        fun W => by
          obtain ⟨I, Z, g, hg, hc⟩ := hG.exists_cover W
          exact ⟨I, Z, g, hg, hc⟩) U
    refine ⟨Σ V : C, {g : V ⟶ U // T.1.arrows g}, fun p => p.1, fun p => p.2.1,
      sieve_ofArrows_arrows_mem J _ T.2, fun p => ?_⟩
    obtain ⟨i, ⟨x⟩⟩ := hT p.1 p.2.1 p.2.2
    have := i.2
    obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant (K.over i.1)
      ((K.overPullback (ModuleCat.{w} Λ) i.1).obj G)
    exact ⟨E, ⟨moduleConstantIsoOverPullbackInverseImageOfSection J K f
      (Stacks.Topos.sectionHom J _ x) Λ G E c⟩⟩

end MorphismOfTopoi

end
