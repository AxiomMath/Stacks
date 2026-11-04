module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RefinementDatum

/-!
# The transition isomorphisms of Stacks 03DX (1) are compatible with pullback

`AlgebraicGeometry.BigFppfOver.transitionIso` assigns to an object `Z` of `(Sch/S)_fppf` with
morphisms `g₁ : Z ⟶ T₁` and `g₂ : Z ⟶ T₂` into two objects carrying local associated-module
data an isomorphism `g₁^*𝓕₁ ≅ g₂^*𝓕₂` of quasi-coherent modules on the scheme of `Z`.  A
descent datum asks more of such a family than the identity and composition laws already proved
in `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RefinementDatum.lean`: it asks that
the family be compatible with *further pullback*, that is, that restricting the transition at
`Z` along a morphism `g : Z' ⟶ Z` return the transition at `Z'`.

This file proves that compatibility, in the one spelling in which it is unconditional.  Along
`g` the local datum `(𝓕ᵢ, eᵢ)` at `Tᵢ` is transported to the local datum
`(gᵢ^*𝓕ᵢ, AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison …)` at `Z`, and
`AlgebraicGeometry.BigFppfOver.pullback_transitionIso` says that the pullback along `g` of the
transition at `Z` *is* the transition at `Z'` of the transported data.  The proof is the
naturality of Stacks 03DV in the module — the natural isomorphism
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` — together with the defining
property of the transition and the faithfulness half of Stacks 0GN7; no pseudofunctorial
coherence of the comparison enters, because nothing is reindexed along a composite.

What separates this from the `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` field of a
descent datum for `AlgebraicGeometry.modulePullbackPseudofunctor` is precisely that
reindexing, and it is stated in the implementation notes below as the one residue.

## Main results

* `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison_eq`,
  `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison_hom` and
  `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison_inv`: the comparison
  isomorphism of Stacks 03DV and its two directions as composites of their three factors.
* `AlgebraicGeometry.BigFppfOver.transitionIso_symm`: the inverse of a transition isomorphism is
  the transition isomorphism taken in the other order, which is what makes the two transition
  morphisms of a descent datum mutually inverse.
* `AlgebraicGeometry.BigFppfOver.associatedModule_map_transitionIso_pullback`: **the associated
  module of the pullback of a transition isomorphism** is the composite of the two comparison
  isomorphisms of the transported data.
* `AlgebraicGeometry.BigFppfOver.pullback_transitionIso`: **the transition isomorphisms of
  Stacks 03DX (1) are compatible with pullback along a morphism of the big fppf site** — the
  pullback along `g : Z' ⟶ Z` of the transition at `Z` is the transition at `Z'` of the local
  data transported along `g`.  Unconditional.
* `AlgebraicGeometry.BigFppfOver.pullHom_transitionIso_of_comparison_comp`: **the residue is all
  that is missing** — granted that the comparison of Stacks 03DV is compatible with composition
  in the big fppf site, the transition isomorphisms satisfy
  `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom`.  The two identifications of iterated
  pullbacks with pullbacks along composites are arbitrary isomorphisms there, so nothing about
  `AlgebraicGeometry.modulePullbackPseudofunctor` is used beyond the hypotheses.
* `AlgebraicGeometry.BigFppfOver.pullback_transitionIso_self` and
  `AlgebraicGeometry.BigFppfOver.pullback_transitionIso_trans`: the identity and composition
  laws survive the pullback, so the transported data again satisfy them.

## Implementation notes

Nothing here carries a `stacks` attribute: Stacks 03DX (1) is still a hypothesis, and a
hypothesis is part of a citation.

**The residue, stated.**  Let `g : Z' ⟶ Z` and `g₁ : Z ⟶ T₁` be morphisms of `(Sch/S)_fppf`,
let `𝓕₁` be a module on the scheme of `T₁` and `e₁ : 𝓕₁^a ≅ 𝒢|_{T₁}`, and let

    `μ : g^*(g₁^*𝓕₁) ≅ (g ≫ g₁)^*𝓕₁`

be the comparison of iterated pullbacks of modules on schemes, that is, the `mapComp`
isomorphism of `AlgebraicGeometry.modulePullbackPseudofunctor`.  What is *not* proved here, and
what the `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` field of a descent datum needs
beyond `AlgebraicGeometry.BigFppfOver.pullback_transitionIso`, is the single equation

    `(𝓕 ↦ 𝓕^a) μ⁻¹ ≫ localAssociatedModuleComparison g (g₁^*𝓕₁) (localAssociatedModuleComparison
      g₁ 𝓕₁ e₁) = localAssociatedModuleComparison (g ≫ g₁) 𝓕₁ e₁`

on the big fppf site of the scheme of `Z'`: the comparison of Stacks 03DV is compatible with
composition in the big fppf site, that is, it is a *pseudonatural* transformation and not merely
a family of isomorphisms indexed by the morphisms of the site.  Granting that equation for the
two indices, `AlgebraicGeometry.BigFppfOver.pullHom_transitionIso_of_comparison_comp` proves
`pullHom_hom`, so that equation is exactly the residue; it is also what the `pullHom'_hom_self`
and
`pullHom'_hom_comp` fields of `CategoryTheory.Pseudofunctor.DescentData'` reduce to, since both
of those compare transitions obtained through *different* binary fibre products over one and the
same scheme.

That equation splits, by the naturality of
`AlgebraicGeometry.BigFppfOver.objRestrictComp` at `e₁`, into two independent coherences, and
neither is available by unfolding: a square relating
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at `g`, at `g₁` and at
`g ≫ g₁`, whose constituents are assembled from `CategoryTheory.Adjunction.leftAdjointUniq`;
and a cocycle condition among the three isomorphisms
`AlgebraicGeometry.BigFppfOver.objRestrictComp` at `g`, at `g₁` and at `g ≫ g₁`, which is a
statement about pushforwards of sheaves of modules alone and should follow from
`SheafOfModules.pushforward_assoc` and the pentagon for `CategoryTheory.Over.mapComp`.

The transported local datum is spelled with the quasi-coherence witness
`Stacks.Modules.isQuasicoherent_pullback` rather than with an instance, because
`AlgebraicGeometry.BigFppfOver.transitionIso` takes its quasi-coherence hypotheses as explicit
arguments and the two occurrences must be literally the same term for the statements below to
be about one isomorphism.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison isomorphism, factor by factor -/

/-- **The three factors of the comparison isomorphism of Stacks 03DV along a morphism of the big
fppf site**: Stacks 03DV functorial in the object, the restriction of the given isomorphism `e`,
and the functoriality of restriction.  This is the definition, named so that the two directions
below can be read off it without unfolding anything at the enormous types involved. -/
public theorem localAssociatedModuleComparison_eq
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (F : (objScheme B S hS T).Modules)
    (e : (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F ≅
      (objRestrict B S hS T).obj G) :
    localAssociatedModuleComparison B S hS G g F e =
      (associatedModuleObjRestrictNatIso B (objScheme B S hS T)
          (contains_objScheme B S hS T) (Over.mk g.left)).app F ≪≫
        (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
          (Over.mk g.left)).mapIso e ≪≫
          (objRestrictComp B S hS g).app G :=
  rfl

/-- **The comparison isomorphism of Stacks 03DV along a morphism of the big fppf site, read as a
composite.**  Its three factors are Stacks 03DV functorial in the object, the restriction of the
given isomorphism `e`, and the functoriality of restriction. -/
public theorem localAssociatedModuleComparison_hom
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (F : (objScheme B S hS T).Modules)
    (e : (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F ≅
      (objRestrict B S hS T).obj G) :
    (localAssociatedModuleComparison B S hS G g F e).hom =
      (associatedModuleObjRestrictNatIso B (objScheme B S hS T)
          (contains_objScheme B S hS T) (Over.mk g.left)).hom.app F ≫
        (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
            (Over.mk g.left)).map e.hom ≫
          ((objRestrictComp B S hS g).app G).hom := by
  simp [localAssociatedModuleComparison_eq]

/-- **The inverse of the comparison isomorphism of Stacks 03DV, read as a composite**, the
three factors of `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison_hom` inverted
in the opposite order. -/
public theorem localAssociatedModuleComparison_inv
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (F : (objScheme B S hS T).Modules)
    (e : (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F ≅
      (objRestrict B S hS T).obj G) :
    (localAssociatedModuleComparison B S hS G g F e).inv =
      ((objRestrictComp B S hS g).app G).inv ≫
        (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
            (Over.mk g.left)).map e.inv ≫
          (associatedModuleObjRestrictNatIso B (objScheme B S hS T)
            (contains_objScheme B S hS T) (Over.mk g.left)).inv.app F := by
  simp [localAssociatedModuleComparison_eq]

/-! ### The transition isomorphisms under pullback -/

/-- **The inverse of a transition isomorphism is the transition isomorphism in the other
order.**  Both have the same associated module, the composite of the two comparisons of
Stacks 03DV in the opposite order, and Stacks 0GN7 is faithful.  This is what makes the two
transition morphisms `hom q f₁ f₂` and `hom q f₂ f₁` of a descent datum mutually inverse. -/
public theorem transitionIso_symm
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ Z : BigFppfOver B S hS}
    (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G) :
    (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).inv =
      (transitionIso B S hS G g₂ g₁ hF₂ e₂ hF₁ e₁).hom := by
  refine Iso.inv_ext (hom_ext_of_associatedModule_map B (objScheme B S hS Z)
    (contains_objScheme B S hS Z) (Stacks.Modules.isQuasicoherent_pullback _ F₁ hF₁)
    (Stacks.Modules.isQuasicoherent_pullback _ F₁ hF₁) ?_)
  rw [Functor.map_comp, associatedModule_map_transitionIso,
    associatedModule_map_transitionIso, CategoryTheory.Functor.map_id]
  simp

/-- **The associated module of the pullback of a transition isomorphism.**  Pulling the
transition at `Z` back along `g : Z' ⟶ Z` and forming its associated module on the scheme of
`Z'` returns the composite of the two comparison isomorphisms of Stacks 03DV of the *transported*
local data — the data `(gᵢ^*𝓕ᵢ, …)` that
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison` carries from `Tᵢ` to `Z`.

This is the naturality of `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at
the object `g` of the big fppf category over the scheme of `Z`, applied to the transition, read
through the defining property of the transition: after the naturality square the middle term is
the associated module of the transition at `Z`, which is the composite of the two comparisons at
`Z`, and reassembling the three factors on each side is exactly the comparison at `g` of the
transported datum. -/
public theorem associatedModule_map_transitionIso_pullback
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ Z Z' : BigFppfOver B S hS}
    (g : Z' ⟶ Z) (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G) :
    (associatedModule B (objScheme B S hS Z') (contains_objScheme B S hS Z')).map
        ((Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
          (contains_objScheme B S hS Z) (Over.mk g.left))).map
          (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom) =
      (localAssociatedModuleComparison B S hS G g _
            (localAssociatedModuleComparison B S hS G g₁ F₁ e₁)).hom ≫
        (localAssociatedModuleComparison B S hS G g _
          (localAssociatedModuleComparison B S hS G g₂ F₂ e₂)).inv := by
  rw [localAssociatedModuleComparison_hom, localAssociatedModuleComparison_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, ← associatedModule_map_transitionIso]
  exact (NatIso.naturality_2 (associatedModuleObjRestrictNatIso B (objScheme B S hS Z)
    (contains_objScheme B S hS Z) (Over.mk g.left))
    (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom).symm

/-- **The transition isomorphisms of Stacks 03DX (1) are compatible with pullback along a
morphism of the big fppf site.**  Let `g : Z' ⟶ Z` be a morphism of `(Sch/S)_fppf`.  The
pullback along `g` of the transition isomorphism at `Z` between the local data at `T₁` and at
`T₂` is the transition isomorphism at `Z'` between those data *transported to `Z`* along `g₁`
and `g₂` by `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison`.

Unconditional.  Both sides have the same associated module on the scheme of `Z'`, by
`AlgebraicGeometry.BigFppfOver.associatedModule_map_transitionIso_pullback` on the left and the
defining property of the transition on the right, and Stacks 0GN7 is faithful.

This is the pullback compatibility that a descent datum requires, in the spelling in which no
module is reindexed along a composite of morphisms of the site.  Rewriting the right-hand side
as the transition at `Z'` between the data at `T₁` and `T₂` themselves — that is, replacing the
transported datum `(g₁^*𝓕₁, …)` by `((g ≫ g₁)^*𝓕₁, …)` — is a further step, and it is exactly
the pseudonaturality of the comparison of Stacks 03DV discussed in the implementation notes of
this file. -/
public theorem pullback_transitionIso
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ Z Z' : BigFppfOver B S hS}
    (g : Z' ⟶ Z) (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G) :
    (Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
          (contains_objScheme B S hS Z) (Over.mk g.left))).map
        (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom =
      (transitionIso B S hS G g g
        (Stacks.Modules.isQuasicoherent_pullback _ F₁ hF₁)
        (localAssociatedModuleComparison B S hS G g₁ F₁ e₁)
        (Stacks.Modules.isQuasicoherent_pullback _ F₂ hF₂)
        (localAssociatedModuleComparison B S hS G g₂ F₂ e₂)).hom := by
  refine hom_ext_of_associatedModule_map B (objScheme B S hS Z')
    (contains_objScheme B S hS Z')
    (Stacks.Modules.isQuasicoherent_pullback _ _
      (Stacks.Modules.isQuasicoherent_pullback _ F₁ hF₁))
    (Stacks.Modules.isQuasicoherent_pullback _ _
      (Stacks.Modules.isQuasicoherent_pullback _ F₂ hF₂)) ?_
  rw [associatedModule_map_transitionIso_pullback, associatedModule_map_transitionIso]

/-- **The compatibility that a descent datum needs, granted that the comparison of Stacks 03DV
is compatible with composition.**  Let `g : Z' ⟶ Z`, let `g₁ : Z ⟶ T₁` and `g₂ : Z ⟶ T₂`, and
let `μᵢ : g^*(gᵢ^*𝓕ᵢ) ≅ (g ≫ gᵢ)^*𝓕ᵢ` be isomorphisms identifying the iterated pullback with
the pullback along the composite — the `mapComp` isomorphisms of
`AlgebraicGeometry.modulePullbackPseudofunctor`.  Suppose that reading the comparison of
Stacks 03DV at `g` of the datum transported along `gᵢ` through `μᵢ` returns the comparison at
the composite `g ≫ gᵢ`.  Then the transition isomorphism at `Z` conjugated by the `μᵢ` is the
transition isomorphism at `Z'` between the data at `T₁` and at `T₂` themselves.

This is `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` for
`AlgebraicGeometry.BigFppfOver.transitionIso`: the left-hand side is `pullHom` of the transition
at `Z` along `g`.  The hypotheses are exactly the residue described in the implementation notes
of this file, so this theorem is the statement that that residue is all that is missing.  Note
that the `μᵢ` are arbitrary isomorphisms here: nothing about the pseudofunctor is used, only the
two hypotheses. -/
public theorem pullHom_transitionIso_of_comparison_comp
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ Z Z' : BigFppfOver B S hS}
    (g : Z' ⟶ Z) (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G)
    (μ₁ : (Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
          (contains_objScheme B S hS Z) (Over.mk g.left))).obj
        ((Scheme.Modules.pullback (objHom B (objScheme B S hS T₁)
          (contains_objScheme B S hS T₁) (Over.mk g₁.left))).obj F₁) ≅
      (Scheme.Modules.pullback (objHom B (objScheme B S hS T₁)
        (contains_objScheme B S hS T₁) (Over.mk (g ≫ g₁).left))).obj F₁)
    (μ₂ : (Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
          (contains_objScheme B S hS Z) (Over.mk g.left))).obj
        ((Scheme.Modules.pullback (objHom B (objScheme B S hS T₂)
          (contains_objScheme B S hS T₂) (Over.mk g₂.left))).obj F₂) ≅
      (Scheme.Modules.pullback (objHom B (objScheme B S hS T₂)
        (contains_objScheme B S hS T₂) (Over.mk (g ≫ g₂).left))).obj F₂)
    (h₁ : localAssociatedModuleComparison B S hS G g _
          (localAssociatedModuleComparison B S hS G g₁ F₁ e₁) =
        (associatedModule B (objScheme B S hS Z')
            (contains_objScheme B S hS Z')).mapIso μ₁ ≪≫
          localAssociatedModuleComparison B S hS G (g ≫ g₁) F₁ e₁)
    (h₂ : localAssociatedModuleComparison B S hS G g _
          (localAssociatedModuleComparison B S hS G g₂ F₂ e₂) =
        (associatedModule B (objScheme B S hS Z')
            (contains_objScheme B S hS Z')).mapIso μ₂ ≪≫
          localAssociatedModuleComparison B S hS G (g ≫ g₂) F₂ e₂) :
    μ₁.inv ≫ (Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
          (contains_objScheme B S hS Z) (Over.mk g.left))).map
          (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom ≫ μ₂.hom =
      (transitionIso B S hS G (g ≫ g₁) (g ≫ g₂) hF₁ e₁ hF₂ e₂).hom := by
  refine hom_ext_of_associatedModule_map B (objScheme B S hS Z')
    (contains_objScheme B S hS Z')
    (Stacks.Modules.isQuasicoherent_pullback _ F₁ hF₁)
    (Stacks.Modules.isQuasicoherent_pullback _ F₂ hF₂) ?_
  rw [Functor.map_comp, Functor.map_comp, associatedModule_map_transitionIso_pullback,
    associatedModule_map_transitionIso, h₁, h₂]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- **The pullback of the transition isomorphism of a member with itself is the identity.**  The
transported local datum at `Z` is one datum, so
`AlgebraicGeometry.BigFppfOver.transitionIso_self` applies to it; this is that identity read
through `AlgebraicGeometry.BigFppfOver.pullback_transitionIso`. -/
public theorem pullback_transitionIso_self
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T Z Z' : BigFppfOver B S hS}
    (g : Z' ⟶ Z) (g₀ : Z ⟶ T)
    {F : (objScheme B S hS T).Modules} (hF : F.IsQuasicoherent)
    (e : (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F ≅
      (objRestrict B S hS T).obj G) :
    (Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
          (contains_objScheme B S hS Z) (Over.mk g.left))).map
        (transitionIso B S hS G g₀ g₀ hF e hF e).hom = 𝟙 _ := by
  rw [transitionIso_self, CategoryTheory.Functor.map_id]

/-- **The pullbacks of the transition isomorphisms compose.**  Over an object `Z` mapping into
three objects carrying local data, the pullback along `g : Z' ⟶ Z` of the transition from the
first to the second followed by that of the transition from the second to the third is the
pullback of the transition from the first to the third: a functor preserves composition, and
`AlgebraicGeometry.BigFppfOver.transitionIso_trans` is the composition law at `Z`. -/
public theorem pullback_transitionIso_trans
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ T₃ Z Z' : BigFppfOver B S hS}
    (g : Z' ⟶ Z) (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂) (g₃ : Z ⟶ T₃)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G)
    {F₃ : (objScheme B S hS T₃).Modules} (hF₃ : F₃.IsQuasicoherent)
    (e₃ : (associatedModule B (objScheme B S hS T₃) (contains_objScheme B S hS T₃)).obj F₃ ≅
      (objRestrict B S hS T₃).obj G) :
    (Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
            (contains_objScheme B S hS Z) (Over.mk g.left))).map
          (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom ≫
        (Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
            (contains_objScheme B S hS Z) (Over.mk g.left))).map
          (transitionIso B S hS G g₂ g₃ hF₂ e₂ hF₃ e₃).hom =
      (Scheme.Modules.pullback (objHom B (objScheme B S hS Z)
          (contains_objScheme B S hS Z) (Over.mk g.left))).map
        (transitionIso B S hS G g₁ g₃ hF₁ e₁ hF₃ e₃).hom := by
  rw [← Functor.map_comp, transitionIso_trans]

end AlgebraicGeometry.BigFppfOver

end
