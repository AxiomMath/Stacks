module

public import StacksFrontier.Deformation.RingedSpaceThickening.TrivializedFunctoriality
public import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningTrivialization
import StacksCore.Tactic.StacksAttribute

/-!
# The boundary of an extension class over a complex of thickenings (Stacks 08LF)

Let `(X, 𝒪_X)` be a ringed space and let

    (X'₁, 𝒪_{X'₁}) ⟶ (X'₂, 𝒪_{X'₂}) ⟶ (X'₃, 𝒪_{X'₃})

be a complex of first order thickenings of `(X, 𝒪_X)` in the sense of **Stacks 08LE**, so that
`ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁` is zero and `i₁` is canonically trivialized by a retraction `π` with
`π ≫ i₃ = f₁₂ ≫ f₂₃`. Fix an `𝒪_X`-module `ℱ`, pairs `(𝒦ᵢ, cᵢ)` with
`cᵢ : ℐᵢ ⊗_{𝒪_X} ℱ ⟶ 𝒦ᵢ`, and a short exact sequence `0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` compatible with
the `cᵢ` through the two squares of the remark. Given an extension `ℱ'₂` over `X'₂` as in
Tag 08L4 with `c_{ℱ'₂} = c₂`, Tag 08LC produces an extension `ℱ'₁` over `X'₁` with
`c_{ℱ'₁} = c₁`, and Tag 08LB turns `ℱ'₁` into a class
`ξ_{ℱ'₁} ∈ Ext¹_{𝒪_X}(ℱ, 𝒦₁)` using `π`.

This file proves the claim of the remark: the boundary map

    ∂ : Ext¹_{𝒪_X}(ℱ, 𝒦₁) ⟶ Ext²_{𝒪_X}(ℱ, 𝒦₃)

of the short exact sequence `0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` carries `ξ_{ℱ'₁}` to the obstruction class
`o(ℱ, 𝒦₃, c₃)` of **Stacks 08L8**.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.restrictedShortComplex` and
  `AlgebraicGeometry.RingedSpaceThickening.restrictedExtension`: an extension as in Tag 08L4
  across `i₂`, read across `i₃` by direct image along `h : X'₂ ⟶ X'₃` and the comparison
  `(i₂)_* ⋙ h_* ≅ (i₃)_*`. This is the source's "`ℰ'₃ = ℰ'₂` but viewed as an
  `𝒪_{X'₃}`-module via `𝒪_{X'₃} ⟶ 𝒪_{X'₂}`".

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.exists_descended_extensionHom`: the map of short
  exact sequences of `𝒪_X`-modules comparing the sequence underlying `ξ_{ℱ'₁}` with an
  extension of `ℱ` by `𝒬`.
* `AlgebraicGeometry.RingedSpaceThickening.exists_quotientExtension_obstructionClass`: the
  obstruction class of Tag 08L8 as the boundary of the class of an extension of `ℱ` by `𝒬`
  which receives a prescribed extension over the third thickening.
* `AlgebraicGeometry.RingedSpaceThickening.boundary_underlyingExtensionClass`:
  **Stacks 08LF**, the claim of the remark.

## Implementation notes

The boundary map of a short exact sequence `0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` on `Ext^n_{𝒪_X}(ℱ, -)` is
Yoneda composition with its class in `Ext¹_{𝒪_X}(𝒦₁, 𝒦₃)`: that is the connecting map of
`CategoryTheory.Abelian.covariantSequence`, namely `hK.extClass.postcomp ℱ`, so `∂ ξ` is
`ξ.comp hK.extClass`.

The source proof embeds `𝒦₃` in an injective `𝒪_X`-module `𝒥`, lifts the embedding to
`j' : 𝒦₂ ⟶ 𝒥` and forms the pushout `ℰ'₂` of `ℱ'₂` along `j'`. Here the order is reversed: the
extension `ℱ'₂` is first read over `X'₃` as `restrictedExtension`, and `ℰ'₃` is the pushout of
*that* along `j'`, formed over `X'₃` by
`AlgebraicGeometry.RingedSpaceThickening.pushoutExtension`. Pushing out and taking the direct
image along `h` commute, because `h_*` is exact, so this is the same extension; the gain is that
the canonical map of Tag 08L4 of the result is then computed by
`AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_pushoutExtension`, which is
Tag 08L5 part (1) over the single thickening `i₃`, rather than requiring a comparison of
extensions over two different thickenings.

The remaining pieces of the presentation are produced exactly as in
`AlgebraicGeometry.RingedSpaceThickening.exists_obstructionPresentation`: push `ℰ'₃` out along
`𝒥 ⟶ 𝒬`, observe that its canonical map is `c₃ ≫ (𝒦₃ ⟶ 𝒥) ≫ (𝒥 ⟶ 𝒬) = 0`, and descend the
result to `X` by **Stacks 08KS**.

The two naturality steps are both
`CategoryTheory.ShortComplex.ShortExact.extClass_naturality`: once for the map of short exact
sequences `(𝟙 𝒦₃, j', u)` from `0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` to `0 ⟶ 𝒦₃ ⟶ 𝒥 ⟶ 𝒬 ⟶ 0`, which
rewrites `∂` as the boundary of the latter precomposed with `u : 𝒦₁ ⟶ 𝒬`, and once for the map
`(u, descended, 𝟙 ℱ)` from the sequence underlying `ξ_{ℱ'₁}` to the quotient extension of the
presentation, which identifies the image of `ξ_{ℱ'₁}` under `u`.

`descended` is the only diagram chase. Over `X'₃` the middle term of `ℱ'₁` is a pushout — this
is the content of Tag 08LC, recorded as the hypothesis `hw` — so a map out of it is given by a
map out of `ℱ'₂` and a map out of `(i₂)_* 𝒦₁`, which is what `CategoryTheory.IsPushout.desc`
consumes. The resulting map over `X'₃` is then transported to a map of `𝒪_X`-modules by full
faithfulness of `(i₃)_*` (**Stacks 08KS**), using that reading `ℱ'₁` back along `π` and then
pushing forward along `i₃` is reading it along `f₁₂ ≫ f₂₃`, which is
`π ≫ i₃ = f₁₂ ≫ f₂₃`. The comparisons of the outer terms are composites of `eqToHom`s and
identity components, so they are compared through
`AlgebraicGeometry.RingedSpaceThickening.IsSectionIdentity`, as in Tag 08LD.

## Scope

One hypothesis of `AlgebraicGeometry.RingedSpaceThickening.boundary_underlyingExtensionClass`
is not derived here: `hrestrict`, which says that the canonical map of Tag 08L4 of
`restrictedExtension` is `c₂` read through the induced map `ℐ₃ ⟶ ℐ₂`. This is the module
structure half of Tag 08LC, which
`StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFunctoriality` explicitly does not
supply: the library does not identify the underlying spaces of `X`, `X'₂` and `X'₃`, and no
result of the library computes the canonical map of an extension read across a morphism of thickenings.
Everything else the remark asserts — both compatibility squares, the pushout description of
`ℱ'₁`, the construction of the presentation of the obstruction and the identity of classes — is
proved.

## References

* [Stacks Project, Tag 08LF](https://stacks.math.columbia.edu/tag/08LF)
* [Stacks Project, Tag 08LE](https://stacks.math.columbia.edu/tag/08LE)
* [Stacks Project, Tag 08L8](https://stacks.math.columbia.edu/tag/08L8)
* [Stacks Project, Tag 08LD](https://stacks.math.columbia.edu/tag/08LD)
* [Stacks Project, Tag 08LC](https://stacks.math.columbia.edu/tag/08LC)
* [Stacks Project, Tag 08LB](https://stacks.math.columbia.edu/tag/08LB)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local implicit_reducible] RingedSpaceModuleAdjunction.modulePushforward
  splitExtension pushoutExtensionPair IsFirstOrderThickening IsThickening

variable {X X₂ X₃ : RingedSpace.{u, u}}

/-! ### Reading an extension across the next thickening

A morphism `h : X'₂ ⟶ X'₃` of thickenings of `(X, 𝒪_X)` has an isomorphism on bases, so direct
image along it is exact and carries a short exact sequence of `𝒪_{X'₂}`-modules to one of
`𝒪_{X'₃}`-modules. Composing with the comparison `(i₂)_* ⋙ h_* ≅ (i₃)_*` on the outer terms
turns an extension as in Tag 08L4 across `i₂` into one across `i₃`.
-/

/-- The base map of a morphism of thickenings of `(X, 𝒪_X)` is an isomorphism: it is a left
inverse factor of the base map of `i₃`, which is one, after the base map of `i₂`, which is
one. -/
theorem isIso_base_of_thickeningMap (i₂ : X ⟶ X₂) (i₃ : X ⟶ X₃) (h : X₂ ⟶ X₃)
    (comm : i₂ ≫ h = i₃) (hb₂ : IsIso i₂.hom.base) (hb₃ : IsIso i₃.hom.base) :
    IsIso h.hom.base := by
  have hbase : i₂.hom.base ≫ h.hom.base = i₃.hom.base :=
    congrArg (fun m : X ⟶ X₃ => m.hom.base) comm
  have := hb₂
  have := hb₃
  have hcomp : IsIso (i₂.hom.base ≫ h.hom.base) := by rw [hbase]; infer_instance
  exact IsIso.of_isIso_comp_left i₂.hom.base h.hom.base

/-- A functor preserving zero morphisms carries a composite zero pair to a composite zero pair. -/
private theorem map_comp_eq_zero_of_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (G : C ⥤ D) [G.PreservesZeroMorphisms]
    {A B B' : C} {f : A ⟶ B} {g : B ⟶ B'} (hfg : f ≫ g = 0) : G.map f ≫ G.map g = 0 := by
  rw [← G.map_comp, hfg, G.map_zero]

variable (i₂ : X ⟶ X₂) (i₃ : X ⟶ X₃) (h : X₂ ⟶ X₃) (comm : i₂ ≫ h = i₃)
  (F K : SheafOfModules.{u} (structureSheafRing X))
  (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
    ((modulePushforward i₂).obj K) 0)

/-- The two maps of the short complex obtained by reading an extension across `i₃` compose to
zero: so do the two maps of the extension itself, and direct image is additive. -/
theorem restrictedShortComplex_comp_zero :
    ((thickeningPushforwardComp i₂ i₃ h comm).inv.app K ≫ (modulePushforward h).map E.f) ≫
        ((modulePushforward h).map E.g ≫
          (thickeningPushforwardComp i₂ i₃ h comm).hom.app F) = 0 := by
  have h0 := map_comp_eq_zero_of_comp_eq_zero (modulePushforward h)
    (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E)
  simp only [Category.assoc]
  rw [← Category.assoc ((modulePushforward h).map E.f), h0, zero_comp, comp_zero]

/-- The short complex `0 ⟶ (i₃)_* 𝒦 ⟶ h_* ℱ' ⟶ (i₃)_* ℱ ⟶ 0` obtained from an extension as in
Tag 08L4 across `i₂` by direct image along `h`, with the outer terms read through the comparison
`(i₂)_* ⋙ h_* ≅ (i₃)_*`. -/
noncomputable def restrictedShortComplex :
    ShortComplex (SheafOfModules.{u} (structureSheafRing X₃)) :=
  ShortComplex.mk
    ((thickeningPushforwardComp i₂ i₃ h comm).inv.app K ≫ (modulePushforward h).map E.f)
    ((modulePushforward h).map E.g ≫ (thickeningPushforwardComp i₂ i₃ h comm).hom.app F)
    (restrictedShortComplex_comp_zero i₂ i₃ h comm F K E)

/-- The first map of `AlgebraicGeometry.RingedSpaceThickening.restrictedShortComplex`, by
definition. -/
@[simp]
theorem restrictedShortComplex_f : (restrictedShortComplex i₂ i₃ h comm F K E).f =
    (thickeningPushforwardComp i₂ i₃ h comm).inv.app K ≫ (modulePushforward h).map E.f := rfl

/-- The second map of `AlgebraicGeometry.RingedSpaceThickening.restrictedShortComplex`, by
definition. -/
@[simp]
theorem restrictedShortComplex_g : (restrictedShortComplex i₂ i₃ h comm F K E).g =
    (modulePushforward h).map E.g ≫ (thickeningPushforwardComp i₂ i₃ h comm).hom.app F := rfl

/-- An extension across `i₂`, read across `i₃`, is again short exact: direct image along `h` is
exact because the base map of `h` is an isomorphism, and the outer terms are only reindexed by
isomorphisms. -/
theorem restrictedShortComplex_shortExact (hb : IsIso h.hom.base) :
    (restrictedShortComplex i₂ i₃ h comm F K E).ShortExact := by
  have := hb
  have hMap := (extensionShortComplex_shortExact i₂ F K E).map_of_exact (modulePushforward h)
  refine ShortComplex.shortExact_of_iso ?_ hMap
  refine ShortComplex.isoMk ((thickeningPushforwardComp i₂ i₃ h comm).app K) (Iso.refl _)
    ((thickeningPushforwardComp i₂ i₃ h comm).app F) ?_ ?_
  · exact (Iso.hom_inv_id_assoc ((thickeningPushforwardComp i₂ i₃ h comm).app K)
      ((modulePushforward h).map E.f)).trans (Category.comp_id _).symm
  · exact Category.id_comp _

/-- **The source's `ℰ'₃`.** An extension of `𝒪_{X'₂}`-modules as in Tag 08L4 across `i₂`, read
as one across `i₃` by direct image along `h` — the ringed-space form of "the same module, viewed
as an `𝒪_{X'₃}`-module via `𝒪_{X'₃} ⟶ 𝒪_{X'₂}`". -/
noncomputable def restrictedExtension (hb : IsIso h.hom.base) :
    CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₃).obj F)
      ((modulePushforward i₃).obj K) 0 :=
  CategoryTheory.Abelian.shortExactYonedaExtension
    (restrictedShortComplex_shortExact i₂ i₃ h comm F K E hb)

attribute [local implicit_reducible] restrictedShortComplex restrictedExtension

/-! ### The two readings of an `𝒪_X`-module over the last thickening

An `𝒪_X`-module can be read over `X'₃` in two ways once the thickenings are connected: directly
along `i₃`, or along `i₁` and then forward along `f₁₂` and `f₂₃`. The two readings are compared
by `doubleComparison`, and — in the presence of a trivialization `π` of `i₁` compatible with the
complex — reading back along `π` and then forward along `i₃` agrees with the composite reading.
Each of these comparisons is a composite of `eqToHom`s and identity components, so none of them
moves a section; that is how they are compared.
-/

section Comparisons

variable {X₁ : RingedSpace.{u, u}}

/-- The comparison `h_* ((i₂)_* ⋙ h'_*) ≅ (i₃)_*` of the two readings over `X'₃` of a module over
`X` pushed forward along `i₁`: first identify `(i₁)_* ⋙ (f₁₂)_*` with `(i₂)_*`, then
`(i₂)_* ⋙ (f₂₃)_*` with `(i₃)_*`. -/
noncomputable def doubleComparison (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (i₃ : X ⟶ X₃) (f₁₂ : X₁ ⟶ X₂)
    (f₂₃ : X₂ ⟶ X₃) (c₁₂ : i₁ ≫ f₁₂ = i₂) (c₂₃ : i₂ ≫ f₂₃ = i₃)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforward f₂₃).obj ((modulePushforward f₁₂).obj ((modulePushforward i₁).obj M)) ⟶
      (modulePushforward i₃).obj M :=
  (modulePushforward f₂₃).map ((thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).hom.app M) ≫
    (thickeningPushforwardComp i₂ i₃ f₂₃ c₂₃).hom.app M

/-- The comparison `r_* ⋙ (i₃)_* ≅ (f₁₂)_* ⋙ (f₂₃)_*` coming from `r ≫ i₃ = f₁₂ ≫ f₂₃`:
pushforward is multiplicative. For `r` the retraction of the canonical trivialization of a
complex of thickenings this is the identification used in Tag 08LF. -/
noncomputable def retractionPushforwardComp (r : X₁ ⟶ X) (i₃ : X ⟶ X₃) (f₁₂ : X₁ ⟶ X₂)
    (f₂₃ : X₂ ⟶ X₃) (hr : r ≫ i₃ = f₁₂ ≫ f₂₃) :
    modulePushforward r ⋙ modulePushforward i₃ ≅
      modulePushforward f₁₂ ⋙ modulePushforward f₂₃ :=
  RingedSpaceModuleAdjunction.modulePushforwardComp r i₃ ≪≫
    eqToIso (congrArg modulePushforward hr) ≪≫
      (RingedSpaceModuleAdjunction.modulePushforwardComp f₁₂ f₂₃).symm

/-- The comparison of direct images along a morphism of thickenings is the identity on
sections, in the direction opposite to
`AlgebraicGeometry.RingedSpaceThickening.isSectionIdentity_thickeningPushforwardComp_inv`. -/
theorem isSectionIdentity_thickeningPushforwardComp_hom (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂)
    (f₁₂ : X₁ ⟶ X₂) (c₁₂ : i₁ ≫ f₁₂ = i₂) (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsSectionIdentity ((thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).hom.app M) := by
  simp only [thickeningPushforwardComp, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom]
  exact isSectionIdentity_comp
    (isSectionIdentity_modulePushforwardComp_hom i₁ f₁₂ M)
    (isSectionIdentity_eqToHom_app (congrArg modulePushforward c₁₂) M)

/-- Both halves of `AlgebraicGeometry.RingedSpaceThickening.doubleComparison` leave sections
alone, so it does. -/
theorem isSectionIdentity_doubleComparison (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (i₃ : X ⟶ X₃)
    (f₁₂ : X₁ ⟶ X₂) (f₂₃ : X₂ ⟶ X₃) (c₁₂ : i₁ ≫ f₁₂ = i₂) (c₂₃ : i₂ ≫ f₂₃ = i₃)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsSectionIdentity (doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ M) :=
  isSectionIdentity_comp
    (isSectionIdentity_modulePushforward f₂₃
      (isSectionIdentity_thickeningPushforwardComp_hom i₁ i₂ f₁₂ c₁₂ M))
    (isSectionIdentity_thickeningPushforwardComp_hom i₂ i₃ f₂₃ c₂₃ M)

/-- The comparison of the two readings over `X'₃` is the identity on sections. -/
theorem isSectionIdentity_retractionPushforwardComp_hom (r : X₁ ⟶ X) (i₃ : X ⟶ X₃)
    (f₁₂ : X₁ ⟶ X₂) (f₂₃ : X₂ ⟶ X₃) (hr : r ≫ i₃ = f₁₂ ≫ f₂₃)
    (M : SheafOfModules.{u} (structureSheafRing X₁)) :
    IsSectionIdentity ((retractionPushforwardComp r i₃ f₁₂ f₂₃ hr).hom.app M) := by
  simp only [retractionPushforwardComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom]
  refine isSectionIdentity_comp (isSectionIdentity_modulePushforwardComp_hom r i₃ M) ?_
  exact isSectionIdentity_comp
    (isSectionIdentity_eqToHom_app (congrArg modulePushforward hr) M)
    (isSectionIdentity_modulePushforwardComp_inv f₁₂ f₂₃ M)

/-- **The coherence of the two readings.** Reading an `𝒪_X`-module back along a trivialization
`π` of `i₁`, pushing forward along `i₃` and comparing with the composite reading along
`f₁₂ ≫ f₂₃` is the direct image along `i₃` of the identification
`AlgebraicGeometry.RingedSpaceThickening.splitRestrictionIso`.

Both sides are composites of comparisons of direct images, so both are the identity on sections
and `AlgebraicGeometry.RingedSpaceThickening.eq_of_isSectionIdentity` applies. -/
theorem retractionPushforwardComp_doubleComparison (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (i₃ : X ⟶ X₃)
    (f₁₂ : X₁ ⟶ X₂) (f₂₃ : X₂ ⟶ X₃) (c₁₂ : i₁ ≫ f₁₂ = i₂) (c₂₃ : i₂ ≫ f₂₃ = i₃)
    (π : SplitMono i₁) (hr : π.retraction ≫ i₃ = f₁₂ ≫ f₂₃)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.app
          ((modulePushforward i₁).obj M) ≫
        doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ M =
      (modulePushforward i₃).map (splitRestrictionIso i₁ π M).hom := by
  refine eq_of_isSectionIdentity
    (isSectionIdentity_comp
      (isSectionIdentity_retractionPushforwardComp_hom π.retraction i₃ f₁₂ f₂₃ hr _)
      (isSectionIdentity_doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ M)) ?_
  exact isSectionIdentity_modulePushforward i₃
    (isSectionIdentity_splitRestrictionIso_hom π M)

/-- Precomposing the comparison of `retractionPushforwardComp` and `doubleComparison` with the
pushforward of the inverse of `splitRestrictionIso` gives the identity of the pushforward of
`M`. -/
theorem retractionPushforwardComp_doubleComparison_inv (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂)
    (i₃ : X ⟶ X₃) (f₁₂ : X₁ ⟶ X₂) (f₂₃ : X₂ ⟶ X₃) (c₁₂ : i₁ ≫ f₁₂ = i₂) (c₂₃ : i₂ ≫ f₂₃ = i₃)
    (π : SplitMono i₁) (hr : π.retraction ≫ i₃ = f₁₂ ≫ f₂₃)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforward i₃).map (splitRestrictionIso i₁ π M).inv ≫
        (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.app
            ((modulePushforward i₁).obj M) ≫
          doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ M =
      𝟙 ((modulePushforward i₃).obj M) := by
  rw [retractionPushforwardComp_doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ π hr M,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- `AlgebraicGeometry.RingedSpaceThickening.retractionPushforwardComp_doubleComparison_inv`
with a further map composed on, the form in which it is used. -/
theorem retractionPushforwardComp_doubleComparison_inv_assoc (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂)
    (i₃ : X ⟶ X₃) (f₁₂ : X₁ ⟶ X₂) (f₂₃ : X₂ ⟶ X₃) (c₁₂ : i₁ ≫ f₁₂ = i₂) (c₂₃ : i₂ ≫ f₂₃ = i₃)
    (π : SplitMono i₁) (hr : π.retraction ≫ i₃ = f₁₂ ≫ f₂₃)
    (M : SheafOfModules.{u} (structureSheafRing X)) {T : SheafOfModules.{u} (structureSheafRing X₃)}
    (x : (modulePushforward i₃).obj M ⟶ T) :
    (modulePushforward i₃).map (splitRestrictionIso i₁ π M).inv ≫
        (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.app
            ((modulePushforward i₁).obj M) ≫
          doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ M ≫ x =
      x := by
  rw [reassoc_of%
      (retractionPushforwardComp_doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ π hr M),
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Comparisons

/-! ### Descending the map of extensions to `X`

The claim of the remark compares the short exact sequence of `𝒪_X`-modules underlying
`ξ_{ℱ'₁}` with an extension of `ℱ` by `𝒬`. The comparison map is produced over `X'₃`, where both
`ℱ'₁` — read forward along `f₁₂` and `f₂₃` — and the direct image of the extension of `ℱ` by
`𝒬` live, and is then descended to `X` by full faithfulness of `(i₃)_*`.
-/

section Descent

variable {X₁ : RingedSpace.{u, u}}

/-- The map of short exact sequences of `𝒪_X`-modules underlying **Stacks 08LF**.

The hypothesis `hw` is the pushout description of `ℱ'₁` of Tag 08LC, read over `X'₃`; the
hypotheses `hml` and `hmr` say that `middle` is a map from `ℱ'₂`, read over `X'₃`, to the direct
image of the middle term of `D`, inducing `𝒦₂ ⟶ 𝒦₁ ⟶ 𝒬` on the kernels and the identity of `ℱ`
on the quotients. The map out of `ℱ'₁` is then the one the pushout provides, and it descends
because `(i₃)_*` is fully faithful (**Stacks 08KS**). -/
theorem exists_descended_extensionHom (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (i₃ : X ⟶ X₃)
    (f₁₂ : X₁ ⟶ X₂) (f₂₃ : X₂ ⟶ X₃) (c₁₂ : i₁ ≫ f₁₂ = i₂) (c₂₃ : i₂ ≫ f₂₃ = i₃)
    (hi₂ : IsFirstOrderThickening i₂) (hi₃ : IsFirstOrderThickening i₃)
    (π : SplitMono i₁) (hr : π.retraction ≫ i₃ = f₁₂ ≫ f₂₃)
    (F K₁ K₂ Q : SheafOfModules.{u} (structureSheafRing X)) (k₂₁ : K₂ ⟶ K₁) (u : K₁ ⟶ Q)
    (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K₂) 0)
    (E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₁).obj F)
      ((modulePushforward i₁).obj K₁) 0)
    (w : PushedExtension i₁ i₂ f₁₂ c₁₂ F K₁ K₂ k₂₁ E₂ E₁)
    (hw : IsPushout E₂.f ((modulePushforward i₂).map k₂₁ ≫
        (thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).inv.app K₁) w.hom
        ((modulePushforward f₁₂).map E₁.f))
    (D : CategoryTheory.Abelian.YonedaExtension F Q 0)
    (middle : (modulePushforward f₂₃).obj E₂.Z.left ⟶ (modulePushforward i₃).obj D.Z.left)
    (hml : (restrictedShortComplex i₂ i₃ f₂₃ c₂₃ F K₂ E₂).f ≫ middle =
      (modulePushforward i₃).map (k₂₁ ≫ u) ≫ (modulePushforward i₃).map D.f)
    (hmr : middle ≫ (modulePushforward i₃).map D.g =
      (restrictedShortComplex i₂ i₃ f₂₃ c₂₃ F K₂ E₂).g) :
    ∃ d : (splitRestriction i₁ π).obj E₁.Z.left ⟶ D.Z.left,
      (splitExtension i₁ π F K₁ E₁).f ≫ d = u ≫ D.f ∧
        d ≫ D.g = (splitExtension i₁ π F K₁ E₁).g := by
  have hb₂₃ : IsIso f₂₃.hom.base := isIso_base_of_thickeningMap i₂ i₃ f₂₃ c₂₃ hi₂.1.1 hi₃.1.1
  have := hb₂₃
  have hcolim : PreservesFiniteColimits (modulePushforward f₂₃) := inferInstance
  have hfull : (modulePushforward i₃).Full :=
    (closedQuotientOfIsThickening i₃ hi₃.1).full_modulePushforward
  have hfaith : (modulePushforward i₃).Faithful :=
    (closedQuotientOfIsThickening i₃ hi₃.1).faithful_modulePushforward
  have hwp := hw.map (modulePushforward f₂₃)
  -- the two hypotheses on `middle`, with the comparison of the outer terms made explicit
  have hml' : (modulePushforward f₂₃).map E₂.f ≫ middle =
      (thickeningPushforwardComp i₂ i₃ f₂₃ c₂₃).hom.app K₂ ≫
        (modulePushforward i₃).map (k₂₁ ≫ u) ≫ (modulePushforward i₃).map D.f := by
    have h1 : (modulePushforward f₂₃).map E₂.f =
        (thickeningPushforwardComp i₂ i₃ f₂₃ c₂₃).hom.app K₂ ≫
          (restrictedShortComplex i₂ i₃ f₂₃ c₂₃ F K₂ E₂).f :=
      (Iso.hom_inv_id_assoc ((thickeningPushforwardComp i₂ i₃ f₂₃ c₂₃).app K₂) _).symm
    rw [h1, Category.assoc, hml]
  have hmr' : middle ≫ (modulePushforward i₃).map D.g =
      (modulePushforward f₂₃).map E₂.g ≫
        (thickeningPushforwardComp i₂ i₃ f₂₃ c₂₃).hom.app F := hmr
  -- the two comparisons of the outer terms cancel
  have hcancel : ∀ M : SheafOfModules.{u} (structureSheafRing X),
      (modulePushforward f₂₃).map ((thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).inv.app M) ≫
        (modulePushforward f₂₃).map
          ((thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).hom.app M) = 𝟙 _ := by
    intro M
    exact ((modulePushforward f₂₃).mapIso
      ((thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).app M)).inv_hom_id
  have hnat : (modulePushforward f₂₃).map ((modulePushforward i₂).map k₂₁) ≫
      (thickeningPushforwardComp i₂ i₃ f₂₃ c₂₃).hom.app K₁ =
      (thickeningPushforwardComp i₂ i₃ f₂₃ c₂₃).hom.app K₂ ≫
        (modulePushforward i₃).map k₂₁ :=
    (thickeningPushforwardComp i₂ i₃ f₂₃ c₂₃).hom.naturality k₂₁
  -- the compatibility needed to descend `middle` through the pushout
  have hsq : (modulePushforward f₂₃).map E₂.f ≫ middle =
      (modulePushforward f₂₃).map ((modulePushforward i₂).map k₂₁ ≫
          (thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).inv.app K₁) ≫
        (doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ K₁ ≫
          (modulePushforward i₃).map u ≫ (modulePushforward i₃).map D.f) := by
    rw [hml']
    simp only [doubleComparison, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← Category.assoc ((modulePushforward f₂₃).map
        ((thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).inv.app K₁)), hcancel K₁, Category.id_comp,
      ← Category.assoc ((modulePushforward f₂₃).map ((modulePushforward i₂).map k₂₁)), hnat,
      Category.assoc]
  -- the map out of the pushout and its compatibility with the quotient maps
  have hdr : hwp.desc middle _ hsq ≫ (modulePushforward i₃).map D.g =
      (modulePushforward f₂₃).map ((modulePushforward f₁₂).map E₁.g) ≫
        doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ F := by
    refine hwp.hom_ext ?_ ?_
    · rw [← Category.assoc, hwp.inl_desc, hmr', ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, w.quotient_commutes]
      simp only [doubleComparison, CategoryTheory.Functor.map_comp, Category.assoc]
      rw [← Category.assoc ((modulePushforward f₂₃).map
        ((thickeningPushforwardComp i₁ i₂ f₁₂ c₁₂).inv.app F)), hcancel F, Category.id_comp]
    · rw [← Category.assoc, hwp.inr_desc]
      have hD := map_comp_eq_zero_of_comp_eq_zero (modulePushforward i₃)
        (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero D)
      have hE := map_comp_eq_zero_of_comp_eq_zero (modulePushforward f₂₃)
        (map_comp_eq_zero_of_comp_eq_zero (modulePushforward f₁₂)
          (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E₁))
      rw [← Category.assoc ((modulePushforward f₂₃).map ((modulePushforward f₁₂).map E₁.f)), hE,
        zero_comp]
      simp only [Category.assoc, hD, comp_zero]
  -- naturality of the comparison of the two readings, in the shape in which it is used
  have hnatf : (modulePushforward i₃).map ((modulePushforward π.retraction).map E₁.f) ≫
      (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.app E₁.Z.left =
      (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.app
          ((modulePushforward i₁).obj K₁) ≫
        (modulePushforward f₂₃).map ((modulePushforward f₁₂).map E₁.f) :=
    (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.naturality E₁.f
  have hnatg : (modulePushforward i₃).map ((modulePushforward π.retraction).map E₁.g) ≫
      (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.app
          ((modulePushforward i₁).obj F) =
      (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.app E₁.Z.left ≫
        (modulePushforward f₂₃).map ((modulePushforward f₁₂).map E₁.g) :=
    (retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.naturality E₁.g
  refine ⟨(modulePushforward i₃).preimage
    ((retractionPushforwardComp π.retraction i₃ f₁₂ f₂₃ hr).hom.app E₁.Z.left ≫
      hwp.desc middle _ hsq), ?_, ?_⟩
  · apply (modulePushforward i₃).map_injective
    rw [(modulePushforward i₃).map_comp, (modulePushforward i₃).map_preimage, splitExtension_f,
      (modulePushforward i₃).map_comp, (modulePushforward i₃).map_comp, Category.assoc,
      ← Category.assoc ((modulePushforward i₃).map
        ((modulePushforward π.retraction).map E₁.f)),
      hnatf, Category.assoc, hwp.inr_desc,
      retractionPushforwardComp_doubleComparison_inv_assoc i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ π hr K₁]
  · apply (modulePushforward i₃).map_injective
    rw [(modulePushforward i₃).map_comp, (modulePushforward i₃).map_preimage, splitExtension_g,
      (modulePushforward i₃).map_comp, Category.assoc, hdr, ← Category.assoc, ← hnatg,
      Category.assoc, retractionPushforwardComp_doubleComparison i₁ i₂ i₃ f₁₂ f₂₃ c₁₂ c₂₃ π hr]

end Descent

/-! ### The presentation of the obstruction attached to an extension over the last thickening -/

section Presentation

/-- Given an injective `𝒪_X`-module `𝒥` containing `𝒦₃` with quotient `𝒬` and an extension
`ℰ'₃` of `(i₃)_* ℱ` by `(i₃)_* 𝒥` as in Tag 08L4 whose canonical map is `c₃ ≫ (𝒦₃ ⟶ 𝒥)`, the
obstruction class `o(ℱ, 𝒦₃, c₃)` of **Stacks 08L8** is the boundary, along
`0 ⟶ 𝒦₃ ⟶ 𝒥 ⟶ 𝒬 ⟶ 0`, of the class of an extension `𝒟` of `ℱ` by `𝒬` which receives `ℰ'₃`.

This is the second and third step of the proof of Tag 08L8, run on a prescribed `ℰ'₃`: push
`ℰ'₃` out along `(i₃)_*(𝒥 ⟶ 𝒬)`, note that the canonical map of the result is
`c₃ ≫ (𝒦₃ ⟶ 𝒥) ≫ (𝒥 ⟶ 𝒬) = 0`, so its middle term lies in the essential image of `(i₃)_*`
(**Stacks 08KS**), and descend. -/
theorem exists_quotientExtension_obstructionClass (i₃ : X ⟶ X₃)
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi₃ : IsFirstOrderThickening i₃) (F K₃ J Q : SheafOfModules.{u} (structureSheafRing X))
    (hJinj : Injective J) (j : K₃ ⟶ J) (q : J ⟶ Q) (hz : j ≫ q = 0)
    (hex : (ShortComplex.mk j q hz).ShortExact)
    (c₃ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i₃))).obj (F)) ⟶ K₃)
    (E₃ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₃).obj F)
      ((modulePushforward i₃).obj J) 0)
    (hact : (firstOrderExtensionAction i₃ F J hi₃ E₃).val = c₃ ≫ j) :
    ∃ (D : CategoryTheory.Abelian.YonedaExtension F Q 0)
      (cmp : E₃.Z.left ⟶ (modulePushforward i₃).obj D.Z.left),
      ((modulePushforward i₃).map q ≫ (modulePushforward i₃).map D.f = E₃.f ≫ cmp) ∧
        (cmp ≫ (modulePushforward i₃).map D.g = E₃.g) ∧
          obstructionClass i₃ hi₃ F K₃ c₃ =
            (CategoryTheory.Abelian.YonedaExtension.shortExact D).extClass.comp hex.extClass
              (by decide) := by
  classical
  have hfull : (modulePushforward i₃).Full :=
    (closedQuotientOfIsThickening i₃ hi₃.1).full_modulePushforward
  have hfaith : (modulePushforward i₃).Faithful :=
    (closedQuotientOfIsThickening i₃ hi₃.1).faithful_modulePushforward
  have hlim : PreservesFiniteLimits (modulePushforward i₃) :=
    preservesFiniteLimits_modulePushforward i₃
  have hcolim : PreservesFiniteColimits (modulePushforward i₃) :=
    preservesFiniteColimits_modulePushforward i₃ hi₃.1
  have hmapzero : (modulePushforward i₃).map (firstOrderExtensionAction i₃ F Q hi₃
      (pushoutExtension i₃ F Q J q E₃)).val = 0 := by
    have hactQ : (firstOrderExtensionAction i₃ F Q hi₃
        (pushoutExtension i₃ F Q J q E₃)).val = c₃ ≫ j ≫ q :=
      (firstOrderExtensionAction_pushoutExtension i₃ F Q J hi₃ q E₃).trans
        ((congrArg (fun z => z ≫ q) hact).trans (Category.assoc c₃ j q))
    exact (congrArg (fun z => (modulePushforward i₃).map z) hactQ).trans
      (((modulePushforward i₃).map_comp c₃ (j ≫ q)).trans
        (((congrArg (fun z => (modulePushforward i₃).map c₃ ≫ (modulePushforward i₃).map z)
              hz).trans
            (congrArg (fun z => (modulePushforward i₃).map c₃ ≫ z)
              ((modulePushforward i₃).map_zero K₃ Q))).trans comp_zero))
  obtain ⟨D, e, hef, heg⟩ := CategoryTheory.Abelian.exists_yonedaExtension_descent
    (modulePushforward i₃) (pushoutExtension i₃ F Q J q E₃)
    (essImage_of_extensionAction_eq_zero i₃ hi₃ F Q _ hmapzero)
  have hker : E₃.f ≫ (pushoutCompatibleMap i₃ F Q J hi₃ q E₃).hom =
      (modulePushforward i₃).map q ≫ (pushoutExtension i₃ F Q J q E₃).f :=
    (pushoutCompatibleMap i₃ F Q J hi₃ q E₃).kernel_commutes
  have hquo : (pushoutCompatibleMap i₃ F Q J hi₃ q E₃).hom ≫
      (pushoutExtension i₃ F Q J q E₃).g =
      E₃.g ≫ (modulePushforward i₃).map (𝟙 F) :=
    (pushoutCompatibleMap i₃ F Q J hi₃ q E₃).quotient_commutes
  have hfinv : (pushoutExtension i₃ F Q J q E₃).f ≫ e.inv =
      (modulePushforward i₃).map D.f := by
    rw [← hef, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have heinv : e.inv ≫ (modulePushforward i₃).map D.g =
      (pushoutExtension i₃ F Q J q E₃).g := by
    rw [← heg, Iso.inv_hom_id_assoc]
  have hcl : (modulePushforward i₃).map q ≫ (modulePushforward i₃).map D.f =
      E₃.f ≫ (pushoutCompatibleMap i₃ F Q J hi₃ q E₃).hom ≫ e.inv := by
    rw [← Category.assoc, hker, Category.assoc, hfinv]
  have hcr : ((pushoutCompatibleMap i₃ F Q J hi₃ q E₃).hom ≫ e.inv) ≫
      (modulePushforward i₃).map D.g = E₃.g := by
    rw [Category.assoc, heinv, hquo, CategoryTheory.Functor.map_id, Category.comp_id]
  refine ⟨D, (pushoutCompatibleMap i₃ F Q J hi₃ q E₃).hom ≫ e.inv, hcl, hcr, ?_⟩
  · exact obstructionClass_eq i₃ hi₃ F K₃ c₃
      { J := J, Q := Q, injective := hJinj, j := j, q := q, zero := hz, exact := hex
        thickExtension := E₃, action := hact, quotientExtension := D
        comparison := (pushoutCompatibleMap i₃ F Q J hi₃ q E₃).hom ≫ e.inv
        comparison_left := hcl
        comparison_right := hcr }

end Presentation

/-! ### The claim of Stacks 08LF -/

section Boundary

/-- The extension `ℱ'₂` of a complex of first order thickenings, read over the third thickening:
`AlgebraicGeometry.RingedSpaceThickening.restrictedExtension` for the morphism `f₂₃` of the
sequence. This is the source's `ℰ'₂` read as an `𝒪_{X'₃}`-module. -/
noncomputable def sequenceRestrictedExtension (S : FirstOrderThickeningSequence.{u})
    (F K : SheafOfModules.{u} (structureSheafRing S.X))
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.i₂).obj F)
      ((modulePushforward S.i₂).obj K) 0) :
    CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.i₃).obj F)
      ((modulePushforward S.i₃).obj K) 0 :=
  restrictedExtension S.i₂ S.i₃ S.f₂₃ S.comm₂₃ F K E
    (isIso_base_of_thickeningMap S.i₂ S.i₃ S.f₂₃ S.comm₂₃ S.firstOrder₂.1.1 S.firstOrder₃.1.1)

attribute [local implicit_reducible] sequenceRestrictedExtension

/-- **Stacks 08LF** with a prescribed injective embedding of `𝒦₃` and a prescribed lift of it
along `𝒦₃ ⟶ 𝒦₂`.

The extension `ℰ'₃` of the source proof is the pushout, over `X'₃`, of `ℱ'₂` read over `X'₃`
along the lift `j' : 𝒦₂ ⟶ 𝒥`; its canonical map is `c₃ ≫ j` by Tag 08L5 part (1) and the second
compatibility square. The presentation of the obstruction attached to it, the induced map
`u : 𝒦₁ ⟶ 𝒬` and the descended map of extensions then give the identity of classes by two
applications of naturality of the class of a short exact sequence. -/
theorem boundary_underlyingExtensionClass_of_injective (S : FirstOrderThickeningSequence.{u})
    [HasExt (SheafOfModules.{u} (structureSheafRing S.X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))]
    (π : SplitMono S.i₁) (hπ : π.retraction ≫ S.i₃ = S.f₁₂ ≫ S.f₂₃)
    (F K₁ K₂ K₃ J Q : SheafOfModules.{u} (structureSheafRing S.X)) (hJinj : Injective J)
    (j : K₃ ⟶ J) (q : J ⟶ Q) (hz : j ≫ q = 0)
    (hex : (ShortComplex.mk j q hz).ShortExact) (lift : K₂ ⟶ J)
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (hk : k₃₂ ≫ k₂₁ = 0)
    (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact) (hlift : k₃₂ ≫ lift = j)
    (c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩).obj
      ((idealSheafPullback S.i₂))).obj (F)) ⟶ K₂)
    (c₃ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩).obj
      ((idealSheafPullback S.i₃))).obj (F)) ⟶ K₃)
    (hc₃₂ : c₃ ≫ k₃₂ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩)).map
        (((thickeningIdealMap S.i₂ S.i₃ S.f₂₃ S.comm₂₃), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₂)
    (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.i₂).obj F)
      ((modulePushforward S.i₂).obj K₂) 0)
    (E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.i₁).obj F)
      ((modulePushforward S.i₁).obj K₁) 0)
    (w : PushedExtension S.i₁ S.i₂ S.f₁₂ S.comm₁₂ F K₁ K₂ k₂₁ E₂ E₁)
    (hw : IsPushout E₂.f ((modulePushforward S.i₂).map k₂₁ ≫
        (thickeningPushforwardComp S.i₁ S.i₂ S.f₁₂ S.comm₁₂).inv.app K₁) w.hom
        ((modulePushforward S.f₁₂).map E₁.f))
    (hrestrict : (firstOrderExtensionAction S.i₃ F K₂ S.firstOrder₃
        (sequenceRestrictedExtension S F K₂ E₂)).val =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩)).map
        (((thickeningIdealMap S.i₂ S.i₃ S.f₂₃ S.comm₂₃), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₂) :
    (underlyingExtensionClass S.i₁ π S.firstOrder₁.1.1 F K₁ E₁).comp hK.extClass (by decide) =
      obstructionClass S.i₃ S.firstOrder₃ F K₃ c₃ := by
  classical
  -- `ℰ'₃`, the pushout over `X'₃` of `ℱ'₂` along the lift, and its canonical map
  have hactE₃ : (firstOrderExtensionAction S.i₃ F J S.firstOrder₃
      (pushoutExtension S.i₃ F J K₂ lift (sequenceRestrictedExtension S F K₂ E₂))).val =
      c₃ ≫ j := by
    rw [firstOrderExtensionAction_pushoutExtension, hrestrict]
    exact (congrArg (fun z => z ≫ lift) hc₃₂).symm.trans
      ((Category.assoc c₃ k₃₂ lift).trans (congrArg (fun z => c₃ ≫ z) hlift))
  obtain ⟨D, cmp, hcmpL, hcmpR, hobs⟩ := exists_quotientExtension_obstructionClass S.i₃
    S.firstOrder₃ F K₃ J Q hJinj j q hz hex c₃ _ hactE₃
  -- the map `u : 𝒦₁ ⟶ 𝒬` induced by the lift
  obtain ⟨u, hu⟩ : ∃ u : K₁ ⟶ Q, k₂₁ ≫ u = lift ≫ q :=
    ⟨hK.gIsCokernel.desc (CokernelCofork.ofπ (lift ≫ q)
        (by rw [← Category.assoc, hlift, hz])),
      hK.gIsCokernel.fac _ WalkingParallelPair.one⟩
  -- the map out of `ℱ'₂`, read over `X'₃`, into the direct image of the middle term of `𝒟`
  have hker : (sequenceRestrictedExtension S F K₂ E₂).f ≫
      (pushoutCompatibleMap S.i₃ F J K₂ S.firstOrder₃ lift
        (sequenceRestrictedExtension S F K₂ E₂)).hom =
      (modulePushforward S.i₃).map lift ≫
        (pushoutExtension S.i₃ F J K₂ lift (sequenceRestrictedExtension S F K₂ E₂)).f :=
    (pushoutCompatibleMap S.i₃ F J K₂ S.firstOrder₃ lift
      (sequenceRestrictedExtension S F K₂ E₂)).kernel_commutes
  have hquo : (pushoutCompatibleMap S.i₃ F J K₂ S.firstOrder₃ lift
        (sequenceRestrictedExtension S F K₂ E₂)).hom ≫
      (pushoutExtension S.i₃ F J K₂ lift (sequenceRestrictedExtension S F K₂ E₂)).g =
      (sequenceRestrictedExtension S F K₂ E₂).g ≫ (modulePushforward S.i₃).map (𝟙 F) :=
    (pushoutCompatibleMap S.i₃ F J K₂ S.firstOrder₃ lift
      (sequenceRestrictedExtension S F K₂ E₂)).quotient_commutes
  have hmiddleL : (sequenceRestrictedExtension S F K₂ E₂).f ≫
      ((pushoutCompatibleMap S.i₃ F J K₂ S.firstOrder₃ lift
        (sequenceRestrictedExtension S F K₂ E₂)).hom ≫ cmp) =
      (modulePushforward S.i₃).map (k₂₁ ≫ u) ≫ (modulePushforward S.i₃).map D.f := by
    rw [← Category.assoc, hker, Category.assoc, ← hcmpL,
      ← CategoryTheory.Functor.map_comp_assoc, ← hu]
  have hmiddleR : ((pushoutCompatibleMap S.i₃ F J K₂ S.firstOrder₃ lift
        (sequenceRestrictedExtension S F K₂ E₂)).hom ≫ cmp) ≫
      (modulePushforward S.i₃).map D.g = (sequenceRestrictedExtension S F K₂ E₂).g := by
    rw [Category.assoc, hcmpR, hquo, CategoryTheory.Functor.map_id, Category.comp_id]
  obtain ⟨d, hdl, hdr⟩ := exists_descended_extensionHom S.i₁ S.i₂ S.i₃ S.f₁₂ S.f₂₃ S.comm₁₂
    S.comm₂₃ S.firstOrder₂ S.firstOrder₃ π hπ F K₁ K₂ Q k₂₁ u E₂ E₁ w hw D _ hmiddleL hmiddleR
  -- the boundary of the short exact sequence of kernel modules, through `u`
  have hKclass : hK.extClass =
      (CategoryTheory.Abelian.Ext.mk₀ u).comp hex.extClass (zero_add 1) := by
    have hnat := hK.extClass_naturality hex
      ({ τ₁ := 𝟙 K₃, τ₂ := lift, τ₃ := u
         comm₁₂ := by simpa using hlift.symm
         comm₂₃ := hu.symm } : ShortComplex.mk k₃₂ k₂₁ hk ⟶ ShortComplex.mk j q hz)
    exact (CategoryTheory.Abelian.Ext.comp_mk₀_id hK.extClass).symm.trans hnat
  -- the image of `ξ_{ℱ'₁}` under `u` is the class of `𝒟`
  have hDclass : (underlyingExtensionClass S.i₁ π S.firstOrder₁.1.1 F K₁ E₁).comp
      (CategoryTheory.Abelian.Ext.mk₀ u) (add_zero 1) =
      (CategoryTheory.Abelian.YonedaExtension.shortExact D).extClass := by
    have hnat := (splitExtension_shortExact S.i₁ π S.firstOrder₁.1.1 F K₁ E₁).extClass_naturality
      (CategoryTheory.Abelian.YonedaExtension.shortExact D)
      ({ τ₁ := u, τ₂ := d, τ₃ := 𝟙 F
         comm₁₂ := hdl.symm
         comm₂₃ := hdr.trans (Category.comp_id _).symm } :
        splitExtension S.i₁ π F K₁ E₁ ⟶
          ShortComplex.mk D.f D.g (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero D))
    exact hnat.trans (CategoryTheory.Abelian.Ext.mk₀_id_comp _)
  rw [hobs, hKclass, ← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero, hDclass]

/-- **Stacks Project, Tag 08LF.** Let `(X, 𝒪_X)` be a ringed space, `ℱ` an `𝒪_X`-module, and let
`X'₁ ⟶ X'₂ ⟶ X'₃` be a complex of first order thickenings of `(X, 𝒪_X)`, with `π` the canonical
trivialization of `i₁` (Tag 08LE). Let `(𝒦ᵢ, cᵢ)` be pairs with `cᵢ : ℐᵢ ⊗_{𝒪_X} ℱ ⟶ 𝒦ᵢ` and
let `0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` be a short exact sequence of `𝒪_X`-modules making the two squares
`_hc₂₁` and `hc₃₂` of the remark commute. Let `ℱ'₂` be an extension as in Tag 08L4 over `X'₂`
with `c_{ℱ'₂} = c₂` and let `ℱ'₁` be the extension over `X'₁` that Tag 08LC produces from it,
exhibited by the map of extensions `w` and the pushout square `hw`.

Then the boundary map `∂ : Ext¹_{𝒪_X}(ℱ, 𝒦₁) ⟶ Ext²_{𝒪_X}(ℱ, 𝒦₃)` of
`0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` — Yoneda composition with the class of that sequence — carries
`ξ_{ℱ'₁}` of Tag 08LB to the obstruction class `o(ℱ, 𝒦₃, c₃)` of Tag 08L8.

The hypothesis `hrestrict` is not derived in this development; see the Scope section of the
module docstring. The hypotheses `_hS`, `_hc₂₁`, `_hE₂` and `_hE₁` are part of the situation of
the remark but are not used: the complex condition enters only through `hπ`, which is what the
canonical trivialization of Tag 08LE supplies, and the canonical maps of `ℱ'₂` and `ℱ'₁` enter
only through `hrestrict` and `w`. -/
@[stacks 08LF "the boundary of the extension class is the obstruction class"]
theorem boundary_underlyingExtensionClass (S : FirstOrderThickeningSequence.{u})
    [HasExt (SheafOfModules.{u} (structureSheafRing S.X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))]
    (_hS : IsComplex S) (π : SplitMono S.i₁)
    (hπ : π.retraction ≫ S.i₃ = S.f₁₂ ≫ S.f₂₃)
    (F K₁ K₂ K₃ : SheafOfModules.{u} (structureSheafRing S.X))
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (hk : k₃₂ ≫ k₂₁ = 0)
    (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact)
    (c₁ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩).obj
      ((idealSheafPullback S.i₁))).obj (F)) ⟶ K₁)
    (c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩).obj
      ((idealSheafPullback S.i₂))).obj (F)) ⟶ K₂)
    (c₃ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩).obj
      ((idealSheafPullback S.i₃))).obj (F)) ⟶ K₃)
    (_hc₂₁ : c₂ ≫ k₂₁ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩)).map
        (((thickeningIdealMap S.i₁ S.i₂ S.f₁₂ S.comm₁₂), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₁)
    (hc₃₂ : c₃ ≫ k₃₂ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩)).map
        (((thickeningIdealMap S.i₂ S.i₃ S.f₂₃ S.comm₂₃), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₂)
    (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.i₂).obj F)
      ((modulePushforward S.i₂).obj K₂) 0)
    (_hE₂ : (firstOrderExtensionAction S.i₂ F K₂ S.firstOrder₂ E₂).val = c₂)
    (E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.i₁).obj F)
      ((modulePushforward S.i₁).obj K₁) 0)
    (_hE₁ : (firstOrderExtensionAction S.i₁ F K₁ S.firstOrder₁ E₁).val = c₁)
    (w : PushedExtension S.i₁ S.i₂ S.f₁₂ S.comm₁₂ F K₁ K₂ k₂₁ E₂ E₁)
    (hw : IsPushout E₂.f ((modulePushforward S.i₂).map k₂₁ ≫
        (thickeningPushforwardComp S.i₁ S.i₂ S.f₁₂ S.comm₁₂).inv.app K₁) w.hom
        ((modulePushforward S.f₁₂).map E₁.f))
    (hrestrict : (firstOrderExtensionAction S.i₃ F K₂ S.firstOrder₃
        (sequenceRestrictedExtension S F K₂ E₂)).val =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩)).map
        (((thickeningIdealMap S.i₂ S.i₃ S.f₂₃ S.comm₂₃), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₂) :
    (underlyingExtensionClass S.i₁ π S.firstOrder₁.1.1 F K₁ E₁).comp hK.extClass (by decide) =
      obstructionClass S.i₃ S.firstOrder₃ F K₃ c₃ := by
  classical
  have hjm : Mono (Injective.ι K₃) := Injective.ι_mono K₃
  have hk₃₂ : Mono k₃₂ := hK.mono_f
  have hKJ : (ShortComplex.mk (Injective.ι K₃) (cokernel.π (Injective.ι K₃))
      (cokernel.condition (Injective.ι K₃))).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      hjm inferInstance
  exact boundary_underlyingExtensionClass_of_injective S π hπ F K₁ K₂ K₃ (Injective.under K₃)
    (cokernel (Injective.ι K₃)) (Injective.injective_under K₃) (Injective.ι K₃)
    (cokernel.π (Injective.ι K₃)) (cokernel.condition (Injective.ι K₃)) hKJ
    (Injective.factorThru (Injective.ι K₃) k₃₂) k₃₂ k₂₁ hk hK
    (Injective.comp_factorThru _ _) c₂ c₃ hc₃₂ E₂ E₁ w hw hrestrict

end Boundary

end AlgebraicGeometry.RingedSpaceThickening

end
