module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.BaseChange
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ZariskiInclusion
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Reading the base-change formula on the affine opens of the base

Let `S` be a scheme, let `B` be a chosen big `τ`-site over `S`, and let `𝓖` be an adequate
`𝒪`-module on `B`. The proof of [Stacks, Tag 06VM] opens with a base-change formula on the site,
`𝓖(Spec A') = 𝓖(Spec A) ⊗_A A'` for a flat morphism `A → A'` of algebras of the site — this is
[Stacks, Tag 06UW] applied to [Stacks, Tag 06VI], available as
`Stacks.Adequate.bijective_affineSectionBaseChangeMap` — and then *reads it* on the affine opens
of `S`: for affine opens `U ⊆ V ⊆ S` it gives `𝓖(U) = 𝓖(V) ⊗_{𝒪(V)} 𝒪(U)`. This file carries out
that reading.

## Main results

* `Stacks.Adequate.BigSite.affineOpenBaseChange` — the base-change formula on the affine opens of
  `S` for every adequate `𝒪`-module, with no hypothesis: the restriction map on sections of
  `𝓖|_{S_Zar}` between affine opens `U ≤ V` of `S` exhibits `Γ(U, 𝓖|_{S_Zar})` as the base change
  of `Γ(V, 𝓖|_{S_Zar})` along `𝒪(V) → 𝒪(U)`.

Along the way:

* `Stacks.Adequate.overHom_ext_opensBelowObj` — two morphisms of a chosen big site into the site
  object of an open of `S` agree.
* `Stacks.Adequate.opensIsoSpecOver` — an object of a chosen big site whose structure morphism is
  the open immersion `Spec Γ(S, U) ⟶ S` of an affine open `U` is isomorphic, in the site, to `U`
  itself.
* `Stacks.Adequate.BigSite.sectionsCongr` — transport of sections of an `𝒪`-module along an
  isomorphism of site objects, as a linear equivalence over a ring acting through the structure
  sheaf on both sides.

## Implementation notes

The two presentations of an affine open `U ⊆ V ⊆ S` as an object of the site are
`Stacks.Adequate.opensBelowObj`, the open subscheme `U` with its open immersion into `S`, and
`Stacks.Adequate.affineSpecOver` applied to the `Γ(S, V)`-algebra `Γ(S, U)`, namely
`Spec Γ(S, U) ⟶ Spec Γ(S, V) ⟶ S`. The isomorphism between them is
`AlgebraicGeometry.IsAffineOpen.isoSpec`; that the structure morphism of the second is
`AlgebraicGeometry.IsAffineOpen.fromSpec` is `AlgebraicGeometry.IsAffineOpen.map_fromSpec`.

*The square commutes for free.* The inclusion `U ⊆ V` and the algebra map `Γ(S, V) → Γ(S, U)`
give two morphisms from the site object of `U` to the site object of `V`; they agree because the
structure morphism of the latter is a monomorphism, which is `overHom_ext_opensBelowObj`.

*Linearity is one ring identity.* Both presentations of `U` carry `Γ(S, U)` into the global
functions of the object — through `AlgebraicGeometry.Scheme.Opens.topIso` for the open subscheme
and through `AlgebraicGeometry.Scheme.ΓSpecIso` for the spectrum. That these agree after
transport along the isomorphism is `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop`, the
content of `structureSheaf_map_opensIsoSpecOver_inv`.

*Flatness.* The formula on the site applies to `Γ(S, V) → Γ(S, U)` because `Spec` of it is an open
immersion, which is `flat_presheaf_map_of_isAffineOpen`.

The sections of `𝓖|_{S_Zar}` over an open `W` of `S` are *definitionally* the sections of `𝓖`
over `Stacks.Adequate.opensBelowObj` of `W`, and the restriction maps agree too, because
`Stacks.Adequate.BigSite.zariskiRestrictModule` is a pushforward of sheaves of modules along a
continuous functor.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### Two presentations of an affine open of the base as an object of the site -/

/-- Two morphisms of a chosen big site over `S` into the site object of an open `W` of `S` agree:
both become the structure morphism of the source after composing with the open immersion of `W`,
which is a monomorphism. -/
public theorem overHom_ext_opensBelowObj {κ : Cardinal.{u}} {hS : schemeSizeBelow κ S}
    {Z : Over (⟨S, hS⟩ : SchemeBelow κ)} {W : S.Opens}
    (p q : Z ⟶ (opensBelowObj hS W : Over (⟨S, hS⟩ : SchemeBelow κ))) : p = q := by
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  rw [← cancel_mono W.ι]
  exact congrArg (fun k : Z.left ⟶ (⟨S, hS⟩ : SchemeBelow κ) => k.hom)
    ((Over.w p).trans (Over.w q).symm)

/-- The restriction map `𝒪(V) → 𝒪(U)` of the structure sheaf between affine opens `U ≤ V` of a
scheme is flat: its spectrum is an open immersion, by
`AlgebraicGeometry.IsAffineOpen.map_fromSpec`. -/
public theorem flat_presheaf_map_of_isAffineOpen {U V : S.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : U ≤ V) : RingHom.Flat (S.presheaf.map (homOfLE h).op).hom := by
  have : IsOpenImmersion (Spec.map (S.presheaf.map (homOfLE h).op) ≫ hV.fromSpec) := by
    rw [hV.map_fromSpec hU (homOfLE h).op]
    infer_instance
  have : IsOpenImmersion (Spec.map (S.presheaf.map (homOfLE h).op)) :=
    IsOpenImmersion.of_comp _ hV.fromSpec
  exact Flat.SpecMap_iff.mp inferInstance

/-- An object of a chosen big site over `S` whose structure morphism is the open immersion
`Spec Γ(S, U) ⟶ S` of an affine open `U` of `S` is isomorphic, in the site, to the open
subscheme `U` with its own open immersion. -/
public noncomputable def opensIsoSpecOver {κ : Cardinal.{u}} (hS : schemeSizeBelow κ S)
    {U : S.Opens} (hU : IsAffineOpen U) (hsz : schemeSizeBelow κ (Spec Γ(S, U)))
    (p : Spec Γ(S, U) ⟶ S) (hp : p = hU.fromSpec) :
    (opensBelowObj hS U : Over (⟨S, hS⟩ : SchemeBelow κ)) ≅
      Over.mk (ObjectProperty.homMk (X := (⟨Spec Γ(S, U), hsz⟩ : SchemeBelow κ)) p) :=
  Over.isoMk (ObjectProperty.isoMk _ hU.isoSpec)
    (ObjectProperty.hom_ext _ (by
      change hU.isoSpec.hom ≫ p = U.ι
      rw [hp, hU.isoSpec_hom_fromSpec]))

/-- The underlying morphism of schemes of the inverse of `opensIsoSpecOver` is the inverse of
`AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
@[simp]
public theorem opensIsoSpecOver_inv_left_hom {κ : Cardinal.{u}} (hS : schemeSizeBelow κ S)
    {U : S.Opens} (hU : IsAffineOpen U) (hsz : schemeSizeBelow κ (Spec Γ(S, U)))
    (p : Spec Γ(S, U) ⟶ S) (hp : p = hU.fromSpec) :
    (opensIsoSpecOver hS hU hsz p hp).inv.left.hom = hU.isoSpec.inv := rfl

/-- The two ways of reading `Γ(S, U)` inside the global functions of the spectrum of an affine
open `U` of `S` — restriction of `𝒪_S` followed by transport along `opensIsoSpecOver`, and the
canonical identification `AlgebraicGeometry.Scheme.ΓSpecIso` — agree. -/
public theorem structureSheaf_map_opensIsoSpecOver_inv (BB : BigSite τ S) {U : S.Opens}
    (hU : IsAffineOpen U) (hsz : schemeSizeBelow BB.cutoff (Spec Γ(S, U)))
    (p : Spec Γ(S, U) ⟶ S) (hp : p = hU.fromSpec) :
    (forget₂ CommRingCat RingCat).map (Scheme.Opens.topIso U).inv ≫
        BB.structureSheaf.obj.map (opensIsoSpecOver BB.base_mem hU hsz p hp).inv.op =
      (forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso Γ(S, U)).inv := by
  show (forget₂ CommRingCat RingCat).map
      ((Scheme.Opens.topIso U).inv ≫ hU.isoSpec.inv.appTop) = _
  rw [hU.isoSpec_inv_appTop, Iso.inv_hom_id_assoc]

/-! ### Transport of sections along an isomorphism of site objects -/

/-- Transport of sections of an `𝒪`-module along a morphism `k` of a chosen big site, as a linear
map over a ring `A` carried into the global functions of the two objects by `a` and `a'`. The
hypothesis `he` is the compatibility of `a` and `a'` with the restriction map of the structure
sheaf along `k`. -/
public noncomputable def BigSite.sectionsCongrₗ (BB : BigSite τ S)
    (G : SheafOfModules.{u} BB.structureSheaf) {T T' : BB.category} (k : T' ⟶ T) {A : Type u}
    [CommRing A] (a : RingCat.of A ⟶ BB.structureSheaf.obj.obj (op T))
    (a' : RingCat.of A ⟶ BB.structureSheaf.obj.obj (op T'))
    (he : a ≫ BB.structureSheaf.obj.map k.op = a') :
    ((ModuleCat.restrictScalars a.hom).obj (G.val.obj (op T))) →ₗ[A]
      ((ModuleCat.restrictScalars a'.hom).obj (G.val.obj (op T'))) where
  toFun x := G.val.map k.op x
  map_add' := map_add (G.val.map k.op).hom
  map_smul' r x := by
    have h2 : (BB.structureSheaf.obj.map k.op).hom (a.hom r) = a'.hom r :=
      congrArg (fun φ : RingCat.of A ⟶ _ => φ.hom r) he
    have h1 := G.val.map_smul k.op (a.hom r) x
    rwa [h2] at h1

/-- Transport of sections of an `𝒪`-module along an isomorphism of a chosen big site, as a linear
equivalence; see `Stacks.Adequate.BigSite.sectionsCongrₗ`. -/
public noncomputable def BigSite.sectionsCongr (BB : BigSite τ S)
    (G : SheafOfModules.{u} BB.structureSheaf) {T T' : BB.category} (k : T' ≅ T) {A : Type u}
    [CommRing A] (a : RingCat.of A ⟶ BB.structureSheaf.obj.obj (op T))
    (a' : RingCat.of A ⟶ BB.structureSheaf.obj.obj (op T'))
    (he : a ≫ BB.structureSheaf.obj.map k.hom.op = a') :
    ((ModuleCat.restrictScalars a.hom).obj (G.val.obj (op T))) ≃ₗ[A]
      ((ModuleCat.restrictScalars a'.hom).obj (G.val.obj (op T'))) :=
  LinearEquiv.ofBijective (BigSite.sectionsCongrₗ BB G k.hom a a' he)
    (ConcreteCategory.bijective_of_isIso (G.val.presheaf.map k.hom.op))

/-- `Stacks.Adequate.BigSite.sectionsCongr` sends a section to its restriction along the
morphism underlying the isomorphism. -/
@[simp]
public theorem BigSite.sectionsCongr_apply (BB : BigSite τ S)
    (G : SheafOfModules.{u} BB.structureSheaf) {T T' : BB.category} (k : T' ≅ T) {A : Type u}
    [CommRing A] (a : RingCat.of A ⟶ BB.structureSheaf.obj.obj (op T))
    (a' : RingCat.of A ⟶ BB.structureSheaf.obj.obj (op T'))
    (he : a ≫ BB.structureSheaf.obj.map k.hom.op = a') (x) :
    BigSite.sectionsCongr BB G k a a' he x = G.val.map k.hom.op x := rfl

/-! ### The base-change formula on the affine opens of the base -/

/-- **The base-change formula of the proof of [Stacks, Tag 06VM] on the affine opens of `S`.**
For every adequate `𝒪`-module `𝓖` on a chosen big `τ`-site over `S` and all affine opens
`U ≤ V` of `S`, the restriction map on sections of `𝓖|_{S_Zar}` exhibits `Γ(U, 𝓖|_{S_Zar})` as
the base change of `Γ(V, 𝓖|_{S_Zar})` along `𝒪(V) → 𝒪(U)`, that is
`𝓖(U) = 𝓖(V) ⊗_{𝒪(V)} 𝒪(U)`.

The formula on the site is [Stacks, Tag 06UW] applied to [Stacks, Tag 06VI],
`Stacks.Adequate.bijective_affineSectionBaseChangeMap`; it is read on the two presentations of
`U` and `V` as objects of the site and transported along `Stacks.Adequate.opensIsoSpecOver`. -/
public theorem BigSite.affineOpenBaseChange (B : BigSite τ S)
    (G : SheafOfModules.{u} B.structureSheaf) (hG : IsAdequate B G)
    (U V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    letI := algebraOfLE S h
    letI := moduleOfLE (B.zariskiRestrictModule.obj G) h
    letI := isScalarTowerOfLE (B.zariskiRestrictModule.obj G) h
    IsBaseChange Γ(S, U) (restrictₗ (B.zariskiRestrictModule.obj G) h) := by
  have hsz {W : S.Opens} (hW : IsAffineOpen W) : schemeSizeBelow B.cutoff (Spec Γ(S, W)) :=
    Scheme.size_lt_of_isOpenImmersion hW.fromSpec B.base_mem
  have hszV := hsz hV
  have hszU := hsz hU
  let instA : Algebra Γ(S, V) Γ(S, U) := algebraOfLE S h
  let instM : Module Γ(S, V) Γ(B.zariskiRestrictModule.obj G, U) :=
    moduleOfLE (B.zariskiRestrictModule.obj G) h
  have instT : IsScalarTower Γ(S, V) Γ(S, U) Γ(B.zariskiRestrictModule.obj G, U) :=
    isScalarTowerOfLE (B.zariskiRestrictModule.obj G) h
  let XV : AdequateFunctor.AlgebrasInSite Γ(S, V) (schemeSizeBelow B.cutoff) :=
    ⟨CommAlgCat.of Γ(S, V) Γ(S, V), hszV⟩
  let YU : AdequateFunctor.AlgebrasInSite Γ(S, V) (schemeSizeBelow B.cutoff) :=
    ⟨CommAlgCat.of Γ(S, V) Γ(S, U), hszU⟩
  let gUV : XV ⟶ YU := ObjectProperty.homMk (CommAlgCat.ofHom (Algebra.ofId Γ(S, V) Γ(S, U)))
  let aV : B.category := (affineSpecOver B Γ(S, V) hV.fromSpec).obj (op XV)
  let aU : B.category := (affineSpecOver B Γ(S, V) hV.fromSpec).obj (op YU)
  have haV : aV.hom.hom = hV.fromSpec := by
    show Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(S, V))) ≫ hV.fromSpec = _
    simp
  have haU : aU.hom.hom = hU.fromSpec := hV.map_fromSpec hU (homOfLE h).op
  let isoV := opensIsoSpecOver B.base_mem hV hszV aV.hom.hom haV
  let isoU := opensIsoSpecOver B.base_mem hU hszU aU.hom.hom haU
  let e {W : S.Opens} (hW : IsAffineOpen W) (p : Spec Γ(S, W) ⟶ S) (hp : p = hW.fromSpec) :=
    BigSite.sectionsCongr B G (opensIsoSpecOver B.base_mem hW (hsz hW) p hp).symm
      ((forget₂ CommRingCat RingCat).map (Scheme.Opens.topIso W).inv)
      ((forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso Γ(S, W)).inv)
      (structureSheaf_map_opensIsoSpecOver_inv B hW (hsz hW) p hp)
  let eM := e hV _ haV
  let eN := e hU _ haU
  let eBC : TensorProduct Γ(S, V) Γ(S, U)
      ((affineSectionFunctor B G Γ(S, V) hV.fromSpec).obj (op (op XV))) ≃ₗ[Γ(S, U)]
      ((affineSectionFunctor B G Γ(S, V) hV.fromSpec).obj (op (op YU))) :=
    LinearEquiv.ofBijective _ (bijective_affineSectionBaseChangeMap B G hG Γ(S, V) hV.fromSpec
      hszV gUV (flat_presheaf_map_of_isAffineOpen hU hV h))
  refine IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Γ(S, U) Γ(S, U)) eM ≪≫ₗ eBC ≪≫ₗ eN.symm) fun x ↦ ?_
  have key : (affineSectionFunctor B G Γ(S, V) hV.fromSpec).map gUV.op.op (eM x) =
      eN (restrictₗ (B.zariskiRestrictModule.obj G) h x) := by
    show G.val.map ((affineSpecOver B Γ(S, V) hV.fromSpec).map gUV.op).op
        (G.val.map isoV.inv.op x) =
      G.val.map isoU.inv.op (G.val.map (opensBelowHom B.base_mem h).op x)
    have e1 := G.val.map_comp_apply isoV.inv.op
      ((affineSpecOver B Γ(S, V) hV.fromSpec).map gUV.op).op x
    have e2 := G.val.map_comp_apply (opensBelowHom B.base_mem h).op isoU.inv.op x
    have e3 : isoV.inv.op ≫
        ((affineSpecOver B Γ(S, V) hV.fromSpec).map gUV.op).op =
        (opensBelowHom B.base_mem h).op ≫ isoU.inv.op :=
      congrArg Quiver.Hom.op (overHom_ext_opensBelowObj _ _)
    exact e1.symm.trans ((G.val.congr_map_apply e3 x).trans e2)
  show eN.symm ((1 : Γ(S, U)) •
    (affineSectionFunctor B G Γ(S, V) hV.fromSpec).map gUV.op.op (eM x)) = _
  rw [one_smul, key]
  exact eN.symm_apply_apply _

end Stacks.Adequate

end
