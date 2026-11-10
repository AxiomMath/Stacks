module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensor
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportSectionMap

/-!
# Tensoring a section into the finite-support direct image

Let `f : X ⟶ Y` be a morphism of a big étale site, let `Λ` be a commutative ring, let `F` be a
sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. The projection formula of
[Stacks, Tag 0GKF] is built in the source from one recipe: a section `s` of `F` supported on a
locally closed `Z ⊂ X_V` and a section `t` of `G` over `V` are sent to `s ⊗ f^{-1}t`, which is
supported on the same `Z`. This file supplies that recipe.

Three things have to be in place for the recipe to typecheck at all. The tensor product of
sheaves of `Λ`-modules is a sheafification, so `s ⊗ t` is not a section of `F ⊗_Λ H` but only of
the presheaf `V ↦ F(V) ⊗_Λ H(V)`; the comparison is
`Stacks.ModuleSheafTensorSection.moduleToTensorSection`. The inverse image `f^{-1}` is the
abstract `Functor.sheafPullback`, which has no formula on sections; what the recipe uses is only
the unit, `AlgebraicGeometry.SmallEtale.modPullbackUnitSection`. And the support has to be
carried across, which is what `AlgebraicGeometry.SmallEtale.OpenSectionMap` was built for:
tensoring with a *fixed* section is natural over the Zariski opens of one object and over
nothing larger, and that is exactly the input that structure consumes.

Putting these together gives, for each test object `V` and each section `t` of `G` over `V`, the
map `f_{p!}F(V) ⟶ f_{p!}(F ⊗_Λ f^{-1}G)(V)` of the source, with its effect on a colimit
generator: `(Z, s) ↦ (Z, s ⊗ f^{-1}t)`. It is additive in `t` and `Λ`-balanced.

The same section-level data, for the *direct* image instead of the direct image with compact
support, assembles with no support argument at all into a morphism of sheaves
`f_*A ⊗_Λ G ⟶ f_*(A ⊗_Λ f^{-1}G)`, which is also given here.

The comparison map `can` of [Stacks, Tag 0GKF] itself is **not** constructed, and nothing in
this file carries a tag attribute; see "What is not done" for what is missing.

## Main definitions

* `Stacks.ModuleSheafTensorSection.moduleToTensorSection` — **the tensor product of sheaves of
  `Λ`-modules, on sections**: a morphism of presheaves `F.obj ⊗ G.obj ⟶ (F ⊗ G).obj`, where the
  left tensor product is the objectwise one of presheaves and the right is
  `CategoryTheory.Sheaf.monoidalCategory`.
* `AlgebraicGeometry.SmallEtale.modPullbackUnitSection` — **the inverse image of a section**,
  `G(V) ⟶ (f^{-1}G)(X_V)`, the unit of `AlgebraicGeometry.SmallEtale.modPullbackAdjunction` read
  on sections.
* `AlgebraicGeometry.SmallEtale.tensorSectionHom` — tensoring a section of `F` over a Zariski
  open of `W` with the restriction there of a fixed section of `H` over `W`.
* `AlgebraicGeometry.SmallEtale.tensorOpenSectionMap` — **the recipe as an
  `AlgebraicGeometry.SmallEtale.OpenSectionMap`**: the family above is compatible with
  restriction between the Zariski opens of `W`.
* `AlgebraicGeometry.SmallEtale.tensorSupportedSectionsHom` — the induced map on the groups
  `H_Z(F) ⟶ H_Z(F ⊗_Λ H)` of sections supported on a locally closed subset. Its existence is the
  statement that tensoring with a fixed section does not enlarge a support.
* `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom` — **the source's map on the
  finite-support direct image over one test object**, `f_{p!}F(V) ⟶ f_{p!}(F ⊗_Λ f^{-1}G)(V)`.
* `AlgebraicGeometry.SmallEtale.modPushforward`,
  `AlgebraicGeometry.SmallEtale.modPushforwardProjectionPresheaf` and
  `AlgebraicGeometry.SmallEtale.modPushforwardProjection` — the direct image of sheaves of
  `Λ`-modules, the recipe on its sections, and **the resulting projection formula morphism of
  sheaves** `f_*A ⊗_Λ G ⟶ f_*(A ⊗_Λ f^{-1}G)`.

## Main results

* `Stacks.ModuleSheafTensorSection.moduleToTensorSection_naturality_tmul` — the comparison on
  sections commutes with restriction on a pure tensor.
* `AlgebraicGeometry.SmallEtale.modPullbackUnitSection_naturality` — the inverse image of a
  section commutes with restriction along an arrow of `Y_étale`.
* `AlgebraicGeometry.SmallEtale.tensorSectionHom_add`,
  `AlgebraicGeometry.SmallEtale.tensorSectionHom_zero` and
  `AlgebraicGeometry.SmallEtale.tensorSectionHom_smul` — **the recipe is additive and
  `Λ`-balanced in the fixed section**, `(a • h) ⊗ s = h ⊗ (a • s)`. These are the facts that
  extend it over a tensor product of `Λ`-modules; the balancedness is where commutativity of
  `Λ` enters.
* `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom_ι` — **the pure-tensor formula**:
  on the colimit generator of a support `Z` carrying `s`, the map is `(Z, s) ↦ (Z, s ⊗ f^{-1}t)`,
  the support unchanged.
* `AlgebraicGeometry.SmallEtale.OpenSectionMap.finiteSupportSectionsHom_add` and
  `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom_add` — the induced map on
  finite-support sections is additive in the family of section maps, hence the formula is
  additive in `t`.
* `AlgebraicGeometry.SmallEtale.openObjectHomOfLE_comp_openObjectι` — including a Zariski open
  in a bigger one and then in the ambient object is including it in the ambient object. This is
  the functoriality of restricting the fixed section, which is all the naturality of
  `tensorOpenSectionMap` needs.

## Implementation notes

**Why the comparison on sections is not the sheafification unit.** `(F ⊗ G).obj` is *not*
definitionally the sheafification of the objectwise tensor product `F.obj ⊗ G.obj`: the monoidal
structure of `CategoryTheory.Sheaf.monoidalCategory` is obtained by localization, so its tensor
product is a lifted bifunctor and carries no formula, and `CategoryTheory.toSheafify` does not
typecheck at the required type. The comparison is therefore assembled as the sheafification unit
followed by `CategoryTheory.Functor.Monoidal.μIso` for sheafification — an isomorphism because
sheafification is monoidal — and the counit of the sheafification adjunction, which is an
isomorphism on sheaves. This is the same shape as
`Stacks.SectionTensorFormula.toTensorSection` one category over.

**Two spellings of the monoidal structure.** The general statements are made for
`CategoryTheory.Sheaf.monoidalCategory` and the small-étale ones for
`AlgebraicGeometry.SmallEtale.moduleSheafMonoidal`; the latter is that structure, so the two mix
with no transport. Both are activated with `attribute [local instance]`, as in Mathlib and in
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensor`.

**The coefficient universe.** Everything mentioning the tensor product carries `Λ` in the
coefficient universe `max (u + 1) v` of the small étale site, Mathlib equipping `ModuleCat.{w} Λ`
with a monoidal structure only for `Λ : Type w`. This matches
`AlgebraicGeometry.SmallEtale.moduleSheafMonoidal`.

**Local quasi-finiteness is not used.** The recipe and the map on finite-support sections make
sense for an arbitrary morphism `f` of the big étale site: the index of the colimit is the
supports which happen to be finite over the test object, and nothing here needs them to exist.
The hypotheses of [Stacks, Tag 0GKF] enter only where `f_!` itself does.

**Why the projection map for `f_*` is formal and the one for `f_!` is not.** For the direct
image the recipe needs no support argument and is natural in the test object for free, both
`moduleToTensorSection` and the unit being morphisms of (pre)sheaves; so
`modPushforwardProjection` is obtained by sheafifying a presheaf morphism assembled directly
from those two.
For `f_!` the recipe is only defined on sections *supported on a support finite over the test
object*, and that condition is not functorial in the test object on the nose.

## What is not done

No tag attribute appears in this file, and in particular that of [Stacks, Tag 0GKF] does not:
the comparison `can : f_!F ⊗_Λ G ⟶ f_!(F ⊗_Λ f^{-1}G)` is not constructed, so a fortiori it is
not shown to be an isomorphism and not shown to induce
`AlgebraicGeometry.SmallEtale.modShriekProjectionStalkIso` on stalks. Three obstacles are
recorded here.

*The `Λ`-linear finite-support direct image is missing.* To extend the formula `Λ`-linearly over
`f_{p!}F(V) ⊗_Λ G(V)` the group `f_{p!}F(V)` must first be a `Λ`-module, and it is not:
`AlgebraicGeometry.SmallEtale.fShriekMod` is `Stacks.ModuleCatLift.moduleLift` applied to the
already sheafified `AlgebraicGeometry.SmallEtale.fShriekFunctor`, and
`AlgebraicGeometry.SmallEtale.finiteSupportPresheaf` is a presheaf of abelian groups only. The
action is available in principle: `Stacks.ModuleCatLift.ofEndAction` applied to the image of
`Stacks.ModuleCatLift.sheafScalarEnd` under the functor
`AlgebraicGeometry.SmallEtale.finiteSupportPushforward` gives it, and identifying the
sheafification of the result with `fShriekMod` is what `CategoryTheory.sheafifyComposeIso` for
`forget₂ (ModuleCat Λ) AddCommGrpCat` is for. That identification, not the formula, is the next
piece of work.

*The route through the direct image is blocked by a condition the source does not impose.* With
`modPushforwardProjection` in hand it is tempting to obtain `can` by restricting it to the
subsheaf `f_! ⊆ f_*` of `AlgebraicGeometry.SmallEtale.fShriekSubsheaf`. That subsheaf
description of `f_!` is `AlgebraicGeometry.SmallEtale.finiteSupportPushforwardIso`, Stacks 0F6N,
which assumes `IsSeparated f`; [Stacks, Tag 0GKF] assumes only that `f` is locally
quasi-finite, and without separatedness a section supported on a support finite over `V` has no
extension by zero to `X_V`, so there is no map `f_! ⟶ f_*` to restrict. The route is therefore
not available for the tag.

*Naturality in the test object remains.* Turning the maps over each `V` into a morphism of
presheaves requires matching them against
`AlgebraicGeometry.SmallEtale.finiteSupportBaseChange`, whose own note records that the support
data is functorial only up to propositional equality with `HEq` transport. `OpenSectionMap`
absorbs the naturality over the opens of one `X_V`, which is what is done here, but not this.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 0F6E](https://stacks.math.columbia.edu/tag/0F6E)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace Stacks.ModuleSheafTensorSection

universe w v u

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
  [HasWeakSheafify J (ModuleCat.{w} Λ)] [(J.W (A := ModuleCat.{w} Λ)).IsMonoidal]

/-- **The tensor product of sheaves of `Λ`-modules, on sections.** -/
public def moduleToTensorSection (F G : Sheaf J (ModuleCat.{w} Λ)) :
    F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  toSheafify J (F.obj ⊗ G.obj) ≫
    (sheafToPresheaf J (ModuleCat.{w} Λ)).map
      ((Functor.Monoidal.μIso (presheafToSheaf J (ModuleCat.{w} Λ)) F.obj G.obj).inv ≫
        ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app F ⊗ₘ
          (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app G))

/-- The comparison commutes with restriction on a pure tensor. -/
public lemma moduleToTensorSection_naturality_tmul (F G : Sheaf J (ModuleCat.{w} Λ))
    {U U' : Cᵒᵖ} (m : U ⟶ U') (s : F.obj.obj U) (t : G.obj.obj U) :
    (moduleToTensorSection J Λ F G).app U' (F.obj.map m s ⊗ₜ[Λ] G.obj.map m t) =
      (F ⊗ G).obj.map m ((moduleToTensorSection J Λ F G).app U (s ⊗ₜ[Λ] t)) :=
  (moduleToTensorSection J Λ F G).naturality_apply m (s ⊗ₜ[Λ] t)

end Stacks.ModuleSheafTensorSection

namespace AlgebraicGeometry.SmallEtale

universe u v

section OpenObject

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Including a Zariski open in a bigger one and then including that in the ambient object is
including the smaller one in the ambient object. -/
public theorem openObjectHomOfLE_comp_openObjectι (W : SmallEtale B S hS)
    {U U' : ((SmallEtale.toScheme B S hS).obj W).Opens} (h : U' ≤ U) :
    openObjectHomOfLE B S hS W h ≫ openObjectι B S hS W U = openObjectι B S hS W U' := by
  apply (SmallEtale.inclusion B S hS).map_injective
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change (SmallEtale.toScheme B S hS).map
      (openObjectHomOfLE B S hS W h ≫ openObjectι B S hS W U) =
    (SmallEtale.toScheme B S hS).map (openObjectι B S hS W U')
  rw [Functor.map_comp, openObjectHomOfLE_map, openObjectι_map, openObjectι_map,
    Scheme.homOfLE_ι]

end OpenObject

section TensorSection

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}

attribute [local instance] moduleSheafMonoidal

/-- Tensoring a section of `F` over a Zariski open of `W` with the restriction there of a fixed
section `h` of `H` over `W`, as a `Λ`-linear map into the sections of `F ⊗_Λ H`. -/
public def tensorSectionHom (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (W : SmallEtale B X.obj X.property) (h : H.obj.obj (op W))
    (U : ((SmallEtale.toScheme B X.obj X.property).obj W).Opens) :
    F.obj.obj (op (openObject B X.obj X.property W U)) ⟶
      (F ⊗ H).obj.obj (op (openObject B X.obj X.property W U)) :=
  ModuleCat.ofHom
      (((TensorProduct.mk Λ (F.obj.obj (op (openObject B X.obj X.property W U)))
        (H.obj.obj (op (openObject B X.obj X.property W U)))).flip)
          (H.obj.map (openObjectι B X.obj X.property W U).op h)) ≫
    (Stacks.ModuleSheafTensorSection.moduleToTensorSection
      (SmallEtale.topology B X.obj X.property) Λ F H).app
        (op (openObject B X.obj X.property W U))

/-- `tensorSectionHom` sends a section `s` to the image of `s ⊗ₜ h|_U` under the comparison map
into the sections of `F ⊗_Λ H`, where `h|_U` is the restriction of `h` to `U`. -/
@[simp]
public lemma tensorSectionHom_apply (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (W : SmallEtale B X.obj X.property) (h : H.obj.obj (op W))
    (U : ((SmallEtale.toScheme B X.obj X.property).obj W).Opens)
    (s : F.obj.obj (op (openObject B X.obj X.property W U))) :
    tensorSectionHom B Λ F H W h U s =
      (Stacks.ModuleSheafTensorSection.moduleToTensorSection
        (SmallEtale.topology B X.obj X.property) Λ F H).app
          (op (openObject B X.obj X.property W U))
        (s ⊗ₜ[Λ] H.obj.map (openObjectι B X.obj X.property W U).op h) :=
  rfl

/-- Tensoring with a fixed section is additive in that section. -/
public lemma tensorSectionHom_add (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (W : SmallEtale B X.obj X.property) (h h' : H.obj.obj (op W))
    (U : ((SmallEtale.toScheme B X.obj X.property).obj W).Opens)
    (s : F.obj.obj (op (openObject B X.obj X.property W U))) :
    tensorSectionHom B Λ F H W (h + h') U s =
      tensorSectionHom B Λ F H W h U s + tensorSectionHom B Λ F H W h' U s := by
  rw [tensorSectionHom_apply, tensorSectionHom_apply, tensorSectionHom_apply, map_add,
    TensorProduct.tmul_add]
  exact map_add _ _ _

/-- Tensoring with the zero section is zero. -/
public lemma tensorSectionHom_zero (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (W : SmallEtale B X.obj X.property)
    (U : ((SmallEtale.toScheme B X.obj X.property).obj W).Opens)
    (s : F.obj.obj (op (openObject B X.obj X.property W U))) :
    tensorSectionHom B Λ F H W 0 U s = 0 := by
  rw [tensorSectionHom_apply, map_zero, TensorProduct.tmul_zero]
  exact map_zero _

/-- Tensoring is `Λ`-balanced: scaling the fixed section is scaling the varying one. This is
where commutativity of `Λ` is used. -/
public lemma tensorSectionHom_smul (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (W : SmallEtale B X.obj X.property) (a : Λ) (h : H.obj.obj (op W))
    (U : ((SmallEtale.toScheme B X.obj X.property).obj W).Opens)
    (s : F.obj.obj (op (openObject B X.obj X.property W U))) :
    tensorSectionHom B Λ F H W (a • h) U s =
      tensorSectionHom B Λ F H W h U (a • s) := by
  rw [tensorSectionHom_apply, tensorSectionHom_apply, map_smul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

/-- **Tensoring with a fixed section, as an `AlgebraicGeometry.SmallEtale.OpenSectionMap`.**
For a section `h` of `H` over an object `W` of the small étale site of `X`, the maps
`s ↦ s ⊗ h` on the sections of `F` over the Zariski opens of `W` are compatible with
restriction between those opens, because the comparison
`Stacks.ModuleSheafTensorSection.moduleToTensorSection` is a morphism of presheaves and
restricting `h` is functorial. -/
public def tensorOpenSectionMap (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (W : SmallEtale B X.obj X.property) (h : H.obj.obj (op W)) :
    OpenSectionMap.{u, max (u + 1) v} B ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj (F ⊗ H)) W where
  app U := ((forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
    (tensorSectionHom B Λ F H W h U)).hom
  naturality {U U'} hle s := by
    have hc : H.obj.map (openObjectι B X.obj X.property W U').op h =
        H.obj.map (openObjectHomOfLE B X.obj X.property W hle).op
          (H.obj.map (openObjectι B X.obj X.property W U).op h) := by
      rw [← CategoryTheory.comp_apply, ← H.obj.map_comp, ← op_comp,
        openObjectHomOfLE_comp_openObjectι]
    let t : F.obj.obj (op (openObject B X.obj X.property W U)) := s
    change (tensorSectionHom B Λ F H W h U')
        (F.obj.map (openObjectHomOfLE B X.obj X.property W hle).op t) =
      (F ⊗ H).obj.map (openObjectHomOfLE B X.obj X.property W hle).op
        (tensorSectionHom B Λ F H W h U t)
    rw [tensorSectionHom_apply, tensorSectionHom_apply, hc]
    exact Stacks.ModuleSheafTensorSection.moduleToTensorSection_naturality_tmul
      (SmallEtale.topology B X.obj X.property) Λ F H
      (openObjectHomOfLE B X.obj X.property W hle).op t
      (H.obj.map (openObjectι B X.obj X.property W U).op h)

/-- **Tensoring with a fixed section preserves the support condition.** A section of `F` on the
canonical open of a locally closed `Z` which is supported on `Z` has `s ⊗ h` supported on `Z`,
because `s ⊗ h` restricts to `0 ⊗ h = 0` off `Z`. -/
public def tensorSupportedSectionsHom (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (W : SmallEtale B X.obj X.property) (h : H.obj.obj (op W))
    (Z : Set ((SmallEtale.toScheme B X.obj X.property).obj W)) (hZ : IsLocallyClosed Z) :
    supportedSections B X.obj X.property
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) W Z hZ →+
      supportedSections B X.obj X.property
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj (F ⊗ H)) W Z hZ :=
  (tensorOpenSectionMap B Λ F H W h).supportedSectionsHom Z hZ

/-- The underlying section of the image of a supported section `s` under
`tensorSupportedSectionsHom` is `tensorSectionHom` applied to the underlying section of `s` on
the canonical open of `Z`. -/
@[simp]
public lemma tensorSupportedSectionsHom_val (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (W : SmallEtale B X.obj X.property) (h : H.obj.obj (op W))
    (Z : Set ((SmallEtale.toScheme B X.obj X.property).obj W)) (hZ : IsLocallyClosed Z)
    (s : supportedSections B X.obj X.property
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) W Z hZ) :
    (tensorSupportedSectionsHom B Λ F H W h Z hZ s).val =
      tensorSectionHom B Λ F H W h (supportOpen B X.obj X.property W Z hZ) s.val :=
  rfl

end TensorSection

section PullbackUnit

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **The inverse image on sections.** A section `t` of `G` over an object `V` of the small étale
site of `Y` has an inverse image `f^{-1}t`, a section of `f^{-1}G` over the base change `X_V`.
This is the unit of the adjunction `AlgebraicGeometry.SmallEtale.modPullbackAdjunction` read on
sections; the abstract `Functor.sheafPullback` supplies no formula for `f^{-1}G`, but the unit is
all the source's construction uses. -/
public def modPullbackUnitSection (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    (V : SmallEtale B Y.obj Y.property) :
    G.obj.obj (op V) ⟶ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.obj
      (op (baseChange B f V)) :=
  ((modPullbackAdjunction.{u, v, max (u + 1) v} B Λ f).unit.app G).hom.app (op V)

/-- Taking the inverse image of a section commutes with restriction along an arrow of the small
étale site of `Y`. -/
public lemma modPullbackUnitSection_naturality (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) (t : G.obj.obj (op V)) :
    modPullbackUnitSection B Λ f G V' (G.obj.map g.op t) =
      ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
        ((smallEtaleBaseChange B f).map g).op (modPullbackUnitSection B Λ f G V t) :=
  ((modPullbackAdjunction.{u, v, max (u + 1) v} B Λ f).unit.app G).hom.naturality_apply g.op t

end PullbackUnit

section FiniteSupport

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **The source's formula for the projection map, on the finite-support direct image over one
test object.** For a section `t` of `G` over `V`, the recipe `(Z, s) ↦ (Z, s ⊗ f^{-1}t)` of
[Stacks, Tag 0GKF] is a map `f_{p!}F(V) ⟶ f_{p!}(F ⊗_Λ f^{-1}G)(V)`: tensoring with the inverse
image of `t` does not enlarge the support, so it acts on each stage `H_Z` of the colimit, and it
commutes with the transition maps. -/
public def finiteSupportTensorSectionsHom (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t : G.obj.obj (op V)) :
    finiteSupportSections B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V ⟶
      finiteSupportSections B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V :=
  (tensorOpenSectionMap B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
    (baseChange B f V) (modPullbackUnitSection B Λ f G V t)).finiteSupportSectionsHom B f

/-- **The pure-tensor formula.** On the colimit generator of a support `Z` carrying a section `s`
supported on `Z`, the map of `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom` is the
source's `(Z, s) ⊗ t ↦ (Z, s ⊗ f^{-1}t)`: the same support `Z`, and the section tensored with the
inverse image of `t`. -/
public lemma finiteSupportTensorSectionsHom_ι (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t : G.obj.obj (op V)) (E : FiniteSupport B f V) :
    colimit.ι (finiteSupportDiagram B f
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) E ≫
        finiteSupportTensorSectionsHom B Λ f F G V t =
      AddCommGrpCat.ofHom
          (tensorSupportedSectionsHom B Λ F
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) (baseChange B f V)
            (modPullbackUnitSection B Λ f G V t) E.1
            (finiteSupport_isLocallyClosed B f V E)) ≫
        colimit.ι (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V) E :=
  (tensorOpenSectionMap B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
    (baseChange B f V) (modPullbackUnitSection B Λ f G V t)).finiteSupportSectionsHom_ι B f E

end FiniteSupport

section Additive

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}}
  {V : SmallEtale B Y.obj Y.property}

/-- The map induced on finite-support sections is additive in the family of section maps: if a
third family is the pointwise sum of two others, the maps it induces on the colimits add. -/
public lemma OpenSectionMap.finiteSupportSectionsHom_add [Small.{v} (FiniteSupport B f V)]
    (θ θ' θ'' : OpenSectionMap B F G (baseChange B f V))
    (hadd : ∀ (U : ((SmallEtale.toScheme B X.obj X.property).obj
        (baseChange B f V)).Opens)
      (s : F.obj.obj (op (openObject B X.obj X.property (baseChange B f V) U))),
      θ''.app U s = θ.app U s + θ'.app U s) :
    θ''.finiteSupportSectionsHom B f =
      θ.finiteSupportSectionsHom B f + θ'.finiteSupportSectionsHom B f := by
  refine colimit.hom_ext fun E => ?_
  have h : AddCommGrpCat.ofHom (θ''.supportedSectionsHom E.1
        (finiteSupport_isLocallyClosed B f V E)) =
      AddCommGrpCat.ofHom (θ.supportedSectionsHom E.1
          (finiteSupport_isLocallyClosed B f V E)) +
        AddCommGrpCat.ofHom (θ'.supportedSectionsHom E.1
          (finiteSupport_isLocallyClosed B f V E)) :=
    AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => Subtype.ext (hadd _ s.val))
  rw [θ''.finiteSupportSectionsHom_ι B f E, Preadditive.comp_add,
    θ.finiteSupportSectionsHom_ι B f E, θ'.finiteSupportSectionsHom_ι B f E, h]
  exact Preadditive.add_comp _ _ _ _ _ _

end Additive

section FiniteSupportAdditive

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **The pure-tensor formula is additive in the section of `G`.** This is the additivity in `t`
of `(Z, s) ⊗ t ↦ (Z, s ⊗ f^{-1}t)` which, together with
`AlgebraicGeometry.SmallEtale.tensorSectionHom_smul`, is what extends the formula `Λ`-linearly
over the tensor product `f_{p!}F(V) ⊗_Λ G(V)`. -/
public lemma finiteSupportTensorSectionsHom_add (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t t' : G.obj.obj (op V)) :
    finiteSupportTensorSectionsHom B Λ f F G V (t + t') =
      finiteSupportTensorSectionsHom B Λ f F G V t +
        finiteSupportTensorSectionsHom B Λ f F G V t' := by
  refine OpenSectionMap.finiteSupportSectionsHom_add.{u, max (u + 1) v} B f _ _ _ fun U s => ?_
  change tensorSectionHom B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
      (baseChange B f V) (modPullbackUnitSection B Λ f G V (t + t')) U s = _
  rw [map_add]
  exact tensorSectionHom_add B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
    (baseChange B f V) (modPullbackUnitSection B Λ f G V t)
    (modPullbackUnitSection B Λ f G V t') U s

end FiniteSupportAdditive

section Pushforward

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- The direct image of sheaves of `Λ`-modules along `f`, the right adjoint of
`AlgebraicGeometry.SmallEtale.modPullback`. -/
public abbrev modPushforward :
    ModuleSheaf.{u, v, max (u + 1) v} B X Λ ⥤ ModuleSheaf.{u, v, max (u + 1) v} B Y Λ :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v} Λ)
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- **The projection formula map for the direct image, on sections.** Over a test object `V` it
is `a ⊗ t ↦ a ⊗ f^{-1}t`, from `A(X_V) ⊗_Λ G(V)` to `(A ⊗_Λ f^{-1}G)(X_V)`. -/
public def modPushforwardProjectionPresheaf (A : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    ((modPushforward B Λ f).obj A).obj ⊗ G.obj ⟶
      ((modPushforward B Λ f).obj (A ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).obj where
  app V := (A.obj.obj (op (baseChange B f V.unop)) ◁
      modPullbackUnitSection B Λ f G V.unop) ≫
    (Stacks.ModuleSheafTensorSection.moduleToTensorSection
      (SmallEtale.topology B X.obj X.property) Λ A
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).app
      (op (baseChange B f V.unop))
  naturality V V' g := by
    apply ModuleCat.hom_ext
    refine TensorProduct.ext' fun a t => ?_
    change (Stacks.ModuleSheafTensorSection.moduleToTensorSection
          (SmallEtale.topology B X.obj X.property) Λ A
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).app
        (op (baseChange B f V'.unop))
        (A.obj.map ((smallEtaleBaseChange B f).map g.unop).op a ⊗ₜ[Λ]
          modPullbackUnitSection B Λ f G V'.unop (G.obj.map g.unop.op t)) = _
    rw [modPullbackUnitSection_naturality]
    exact Stacks.ModuleSheafTensorSection.moduleToTensorSection_naturality_tmul
      (SmallEtale.topology B X.obj X.property) Λ A
      ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
      ((smallEtaleBaseChange B f).map g.unop).op a
      (modPullbackUnitSection B Λ f G V.unop t)

/-- **The projection formula map for the direct image of sheaves of `Λ`-modules**,
`f_*A ⊗_Λ G ⟶ f_*(A ⊗_Λ f^{-1}G)`: the sheafification of `a ⊗ t ↦ a ⊗ f^{-1}t`. -/
public def modPushforwardProjection (A : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modPushforward B Λ f).obj A ⊗ G ⟶
      (modPushforward B Λ f).obj (A ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) :=
  (inv ((sheafificationAdjunction (SmallEtale.topology B Y.obj Y.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app ((modPushforward B Λ f).obj A)) ⊗ₘ
      inv ((sheafificationAdjunction (SmallEtale.topology B Y.obj Y.property)
        (ModuleCat.{max (u + 1) v} Λ)).counit.app G)) ≫
    (Functor.Monoidal.μIso
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
        (ModuleCat.{max (u + 1) v} Λ))
      ((modPushforward B Λ f).obj A).obj G.obj).hom ≫
    ((sheafificationAdjunction (SmallEtale.topology B Y.obj Y.property)
      (ModuleCat.{max (u + 1) v} Λ)).homEquiv _ _).symm
        (modPushforwardProjectionPresheaf B Λ f A G)

end Pushforward

end AlgebraicGeometry.SmallEtale

end
