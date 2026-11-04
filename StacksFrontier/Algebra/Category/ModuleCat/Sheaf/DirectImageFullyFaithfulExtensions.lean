module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Triple
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fully faithful direct images of sheaves of modules

Let `f : C ⥤ D` be a continuous and cocontinuous functor of sites and `φ` a morphism from a
sheaf of rings `S` on `C` to the restriction along `f` of a sheaf of rings `O` on `D`. If
restriction of sheaves of modules along `φ` has a fully faithful right adjoint, then the unit of
any left adjoint of it is an isomorphism. When `f` is fully faithful and `φ` is invertible, such a
right adjoint is given by the direct image of sheaves of modules along the morphism of topoi of
`f`, at a module universe equal to the universe of the sheaves of rings.

## Main definitions

* `SheafOfModules.toposHom`: The morphism of topoi of a continuous and cocontinuous functor of
  sites.
* `SheafOfModules.toposDirectImage`: The direct image of sheaves of modules along `φ`, built
  through the morphism of topoi of `f`.
* `SheafOfModules.pushforwardToposDirectImageAdjunction`: Restriction along `φ` is left adjoint
  to `SheafOfModules.toposDirectImage`.
* `SheafOfModules.fullyFaithfulToposDirectImage`: `SheafOfModules.toposDirectImage` is fully
  faithful.

## Main results

* `SheafOfModules.isIso_unit_of_fullyFaithful_rightAdjoint`: If restriction along `φ` has a
  fully faithful right adjoint, the unit of any left adjoint of it is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe m r w vC vD uC uD v u

namespace Stacks.SheafOfModules.RestrictScalars

end Stacks.SheafOfModules.RestrictScalars

namespace PresheafOfModules

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) [f.Full] [f.Faithful] (R : Dᵒᵖ ⥤ RingCat.{r})

variable (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R))

end PresheafOfModules

namespace SheafOfModules

section Hinge

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {f : C ⥤ D} {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [f.IsContinuous J K] {O : Sheaf K RingCat.{r}} {S : Sheaf J RingCat.{r}}
  (φ : S ⟶ (f.sheafPushforwardContinuous RingCat.{r} J K).obj O)

/-- **`g^*g_! = id` on sheaves of modules, from a fully faithful direct image.** If restriction
of sheaves of modules along a structure morphism `φ` admits a fully faithful right adjoint, then
the unit `id ⟶ g^*L` of any left adjoint `L` of that restriction is an isomorphism. The module
universe `m` is arbitrary. -/
theorem isIso_unit_of_fullyFaithful_rightAdjoint
    {G : SheafOfModules.{m} S ⥤ SheafOfModules.{m} O} (adj₂ : pushforward.{m} φ ⊣ G)
    [G.Full] [G.Faithful]
    {P : SheafOfModules.{m} S ⥤ SheafOfModules.{m} O} (adj : P ⊣ pushforward.{m} φ) :
    IsIso adj.unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨adj, adj₂⟩).2
    (Adjunction.counit_isIso_of_R_fully_faithful adj₂)

end Hinge

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) [f.Full] [f.Faithful] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})

/-! ### The direct image through the morphism of topoi

The direct image of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DirectImage.lean` exists only
at a module universe dominating `max uC vD`, because its sections over `x` are the compatible
families indexed by the *objects* of `StructuredArrow x f.op`, an explicit product over a type in
`Type (max uC vD)`. The direct image built here, through the morphism of topoi of `f`, has no
such constraint: the universe-sensitive step of the Stacks 03D3 adjunction `g^{-1} ⊣ g_*` is
right Kan extension along `f.op` of presheaves of *sets*, which Mathlib takes as an abstract
limit and which therefore exists as soon as those comma categories are essentially small in the
module universe — and that is the content of the hypothesis
`[∀ F : Cᵒᵖ ⥤ Type r, f.op.HasPointwiseRightKanExtension F]`, discharged by
`CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` from `EssentiallySmall.{r} C` and
`LocallySmall.{r} D`. Nothing asks the module universe to dominate the universe of the objects or
of the morphisms of either site.

What is asked instead is that the module universe *agree* with the universe `r` of the sheaves of
rings: the inverse and direct images of sheaves of modules along a morphism of topoi read a sheaf
of modules as an internal module over an internal ring object of the topos `Sheaf K (Type r)`, so
the sections of the sheaf of rings live in the universe of the module sections. The two
constructions therefore cover different universe regimes, and neither is a generalisation of the
other; both discharge the hypothesis of
`SheafOfModules.isIso_unit_of_fullyFaithful_rightAdjoint`. -/

section ToposDirectImage

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) [f.Full] [f.Faithful] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [f.IsContinuous J K] [f.IsCocontinuous J K]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{r})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{r})]
  [∀ F : Cᵒᵖ ⥤ Type r, f.op.HasPointwiseRightKanExtension F]
  (O : Sheaf K RingCat.{r})

/-- **The morphism of topoi of a continuous and cocontinuous functor of sites**, with sheaves of
sets valued in the universe `r`: its inverse image is restriction along `f`, its direct image is
the cocontinuous partner of that restriction, and restriction is left exact
(`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`). -/
@[sga "4 III 2.4" "partial", sga "4 IV 4.9.1"]
def toposHom : MorphismOfTopoi (Sheaf J (Type r)) (Sheaf K (Type r)) where
  inverseImage := f.sheafPushforwardContinuous (Type r) J K
  pushforward := f.sheafPushforwardCocontinuous (Type r) J K
  adj := f.sheafAdjunctionCocontinuous (Type r) J K
  preservesFiniteLimits :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous J K f (Type r)

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{r})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{r})] in
/-- **Stacks 00XT for the morphism of topoi of `f`.** The counit `g^{-1}g_* ⟶ id` is an
isomorphism because `f` is continuous, cocontinuous and fully faithful. -/
instance isIso_toposHom_adj_counit : IsIso (toposHom.{r} f J K).adj.counit :=
  Functor.isIso_sheafAdjunctionCocontinuous_counit f (Type r) J K

/-- **The Stacks 03D3 direct image of sheaves of modules along the morphism of topoi of `f` is
fully faithful**, the counit `g^{-1}g_* ⟶ id` on sheaves of sets being an isomorphism. -/
def fullyFaithfulToposDirectImageModules :
    (directImageModules (toposHom.{r} f J K) O).FullyFaithful :=
  fullyFaithfulDirectImageModules _ _

/-- The direct image of sheaves of modules along the morphism of topoi of `f` is full. -/
instance full_toposDirectImageModules :
    (directImageModules (toposHom.{r} f J K) O).Full :=
  (fullyFaithfulToposDirectImageModules.{r} f J K O).full

/-- The direct image of sheaves of modules along the morphism of topoi of `f` is faithful. -/
instance faithful_toposDirectImageModules :
    (directImageModules (toposHom.{r} f J K) O).Faithful :=
  (fullyFaithfulToposDirectImageModules.{r} f J K O).faithful

/-- **Restriction of scalars along `Stacks.Sheaves.ToposPullback.restrictionRingIso`, as an
equivalence.** The comparison of the inverse image of a sheaf of rings along the morphism of
topoi of `f` with its restriction along `f` is an isomorphism, so restricting scalars along it
loses nothing. This is `Stacks.SheafOfModules.RestrictScalars.equivalence` at that isomorphism,
spelled with `Iso.hom` and `Iso.inv` rather than with `CategoryTheory.inv`. -/
def restrictScalarsRestrictionRingEquivalence :
    SheafOfModules.{r} (pullbackRingSheaf J (f.sheafPushforwardContinuous (Type r) J K) O) ≌
      SheafOfModules.{r} ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O) :=
  CategoryTheory.Equivalence.mk (restrictScalars.{r} (restrictionRingIso J K f O).inv)
    (restrictScalars.{r} (restrictionRingIso J K f O).hom)
    (Stacks.SheafOfModules.RestrictScalars.compIso.{r} (restrictionRingIso J K f O).inv
      (restrictionRingIso J K f O).hom (restrictionRingIso J K f O).hom_inv_id).symm
    (Stacks.SheafOfModules.RestrictScalars.compIso.{r} (restrictionRingIso J K f O).hom
      (restrictionRingIso J K f O).inv (restrictionRingIso J K f O).inv_hom_id)

variable {S : Sheaf J RingCat.{r}}
  (φ : S ⟶ (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) [IsIso φ]

/-- **The direct image of sheaves of modules right adjoint to restriction along `φ`**, built
through the morphism of topoi of `f` rather than through a comma category of the source site.

It is the Stacks 03D3 direct image of the morphism of topoi, precomposed with the two
restrictions of scalars which identify `SheafOfModules.pushforward φ` with the Stacks 03D2
inverse image of modules: along the inverse of `φ`, and along
`Stacks.Sheaves.ToposPullback.restrictionRingIso`, which compares the inverse image of the sheaf
of rings with its restriction. Both are equivalences, so this is fully faithful. -/
noncomputable abbrev toposDirectImage : SheafOfModules.{r} S ⥤ SheafOfModules.{r} O :=
  (restrictScalars.{r} (inv φ) ⋙ restrictScalars.{r} (restrictionRingIso J K f O).hom) ⋙
    directImageModules (toposHom.{r} f J K) O

/-- The Stacks 03D2 inverse image of sheaves of modules along the morphism of topoi of `f`,
followed by the two restrictions of scalars, is restriction of sheaves of modules along `φ`.

Both sides are restriction along `f` followed by a restriction of scalars; the comparison is
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`, which is the identity on sections, and the
two restrictions of scalars along `Stacks.Sheaves.ToposPullback.restrictionRingIso` cancel. That
`SheafOfModules.pushforward φ` is restriction of modules followed by restriction of scalars
along `φ` is true on the nose. -/
def inverseImageModulesCompIso :
    inverseImageModules (toposHom.{r} f J K) O ⋙
        (restrictScalars.{r} (restrictionRingIso J K f O).inv ⋙ restrictScalars.{r} φ) ≅
      pushforward.{r} φ :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (restrictionModuleIso J K f O)
        (restrictScalars.{r} (restrictionRingIso J K f O).inv) ≪≫
      Functor.isoWhiskerLeft (restrictionModules J K f O)
        (Stacks.SheafOfModules.RestrictScalars.compIso.{r} (restrictionRingIso J K f O).hom
          (restrictionRingIso J K f O).inv (restrictionRingIso J K f O).inv_hom_id) ≪≫
      (restrictionModules J K f O).rightUnitor)
    (restrictScalars.{r} φ)

/-- **Restriction of sheaves of modules along an invertible `φ` has a right adjoint at a module
universe equal to the universe of the sheaves of rings**, with no condition relating that
universe to the universes in which the objects or the morphisms of either site live.

This is the Stacks 03D3 adjunction `g^{-1} ⊣ g_*` of the morphism of topoi of `f` on sheaves of
modules, transported along `SheafOfModules.inverseImageModulesCompIso`; the two restrictions of
scalars it is transported across are equivalences. -/
def pushforwardToposDirectImageAdjunction :
    pushforward.{r} φ ⊣ toposDirectImage.{r} f J K O φ :=
  Adjunction.ofNatIsoLeft
    ((inverseImageAdjDirectImageModules (toposHom.{r} f J K) O).comp
      ((restrictScalarsRestrictionRingEquivalence.{r} f J K O).toAdjunction.comp
        (Stacks.SheafOfModules.RestrictScalars.equivalence.{r} φ).toAdjunction))
    (inverseImageModulesCompIso.{r} f J K O φ)

/-- **The direct image through the morphism of topoi is fully faithful.** It is the Stacks 03D3
direct image, which is fully faithful because `f` is fully faithful, composed with two
restrictions of scalars along isomorphisms, which are equivalences. -/
def fullyFaithfulToposDirectImage : (toposDirectImage.{r} f J K O φ).FullyFaithful :=
  have : (restrictScalars.{r} (inv φ)).IsEquivalence :=
    (Stacks.SheafOfModules.RestrictScalars.equivalence.{r} φ).isEquivalence_inverse
  have : (restrictScalars.{r} (restrictionRingIso J K f O).hom).IsEquivalence :=
    (restrictScalarsRestrictionRingEquivalence.{r} f J K O).isEquivalence_inverse
  Functor.FullyFaithful.comp
    (Functor.FullyFaithful.comp
      (Functor.FullyFaithful.ofFullyFaithful (restrictScalars.{r} (inv φ)))
      (Functor.FullyFaithful.ofFullyFaithful
        (restrictScalars.{r} (restrictionRingIso J K f O).hom)))
    (fullyFaithfulToposDirectImageModules.{r} f J K O)

/-- `SheafOfModules.toposDirectImage` is full. -/
instance full_toposDirectImage : (toposDirectImage.{r} f J K O φ).Full :=
  (fullyFaithfulToposDirectImage.{r} f J K O φ).full

/-- `SheafOfModules.toposDirectImage` is faithful. -/
instance faithful_toposDirectImage : (toposDirectImage.{r} f J K O φ).Faithful :=
  (fullyFaithfulToposDirectImage.{r} f J K O φ).faithful

end ToposDirectImage

end SheafOfModules

end
