module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality

/-!
# The infinitesimal automorphisms of a trivial deformation commute

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` satisfying
(RS*), let `A` be an `S`-algebra whose spectrum lies in the site and let `x` be an object of
`𝒳` over `Spec A`. For a site module `M` the infinitesimal automorphisms `Inf_x(M)` are the
automorphisms of the trivial deformation of `x` over `Spec A[M]` which restrict to the
identity of `x`; they form a group under composition.

This file proves that that group is commutative. The argument is the Eckmann–Hilton half of
Stacks 06I6, carried out directly on the set-valued functor `Inf_x` of Stacks 07Y9: the
transition maps of that functor are restrictions of endomorphisms along a cartesian arrow, so
they preserve composition and the identity, and by (RS*) the functor turns the product
`M × M` of site modules into the product of sets. The codiagonal `M × M ⟶ M` therefore
induces a binary operation on `Inf_x(M)` which is a homomorphism for composition and has the
identity automorphism as a two-sided unit, and the Eckmann–Hilton argument makes composition
commutative.

No linear structure on `Inf_x(M)` is used: the statement is about the composition of
automorphisms, which is exactly what the transitions of Stacks 07YA on infinitesimal
automorphisms are expressed in.

## Main results

* `Deformation.Artin.fiberEndRestrict_id_endo` and `Deformation.Artin.fiberEndRestrict_comp_endo`
  — restriction of endomorphisms along a cartesian arrow is a homomorphism of monoids.
* `Deformation.Artin.infinitesimalAutomorphismSetFunctor_map_id_endo` and
  `Deformation.Artin.infinitesimalAutomorphismSetFunctor_map_comp_endo` — the transition maps
  of `Inf_x` are homomorphisms of monoids.
* `Deformation.Artin.comp_comm_infinitesimalAutomorphism` — **the infinitesimal automorphisms
  of the trivial deformation commute.**

## References

* [Stacks Project, Tag 06I6](https://stacks.math.columbia.edu/tag/06I6)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

universe u v w

namespace Deformation.Artin

/-! ### Restriction of endomorphisms is multiplicative -/

section FiberEndMonoid

open Functor

variable {C : Type*} [Category C] {Y : Type*} [Category Y]
  (q : Y ⥤ C) (hq : q.IsFiberedInGroupoids)
  {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b : q.Fiber V}
  (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ)

/-- Restriction of endomorphisms along a cartesian arrow carries the identity to the
identity. -/
public alias fiberEndRestrict_id_endo := fiberEndRestrict_map_id

/-- Restriction of endomorphisms along a cartesian arrow preserves composition. -/
public alias fiberEndRestrict_comp_endo := fiberEndRestrict_map_comp

end FiberEndMonoid

/-! ### The codiagonal of a site module -/

section Codiagonal

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
  (M : SiteModule A B)

include hA in
/-- The codiagonal `M × M ⟶ M` of a site module: addition of the two components. -/
public def siteModuleCodiag : siteModuleProd A B hA M M ⟶ M :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.coprod LinearMap.id LinearMap.id))

/-- The first inclusion followed by the codiagonal is the identity. -/
public theorem siteModuleInl_comp_codiag :
    siteModuleInl A B hA M M ≫ siteModuleCodiag A B hA M = 𝟙 M := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (m : M.obj) + (0 : M.obj) = m
  rw [add_zero]

/-- The second inclusion followed by the codiagonal is the identity. -/
public theorem siteModuleInr_comp_codiag :
    siteModuleInr A B hA M M ≫ siteModuleCodiag A B hA M = 𝟙 M := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (0 : M.obj) + (m : M.obj) = m
  rw [zero_add]

end Codiagonal

/-! ### Commutativity of the infinitesimal automorphisms -/

section Commute

open Functor

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)

include hp in
/-- The transition maps of the set-valued functor `Inf_x` carry the identity automorphism to
the identity automorphism. -/
public theorem infinitesimalAutomorphismSetFunctor_map_id_endo {M N : SiteModule A B}
    (f : M ⟶ N) :
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f
        (𝟙 (trivialDeformation A B S hS toS hA p x hx hp M)) =
      𝟙 (trivialDeformation A B S hS toS hA p x hx hp N) :=
  (infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp f
      (𝟙 (trivialDeformation A B S hS toS hA p x hx hp M))).trans
    (fiberEndRestrict_id_endo (Under.post p) (underPost_isFiberedInGroupoids p hp x) _ _)

include hp in
/-- The transition maps of the set-valued functor `Inf_x` preserve composition of
automorphisms. -/
public theorem infinitesimalAutomorphismSetFunctor_map_comp_endo {M N : SiteModule A B}
    (f : M ⟶ N)
    (θ θ' : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f (θ ≫ θ') =
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ ≫
        (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ' :=
  (infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp f (θ ≫ θ')).trans
    ((fiberEndRestrict_comp_endo (Under.post p) (underPost_isFiberedInGroupoids p hp x) _ _
        θ θ').trans
      (congrArg₂ (· ≫ ·)
        (infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp f θ).symm
        (infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp f θ').symm))

include hp in
/-- **The infinitesimal automorphisms of the trivial deformation commute.** This is the
Eckmann–Hilton half of Stacks 06I6: by (RS*) the functor `Inf_x` turns the product of two site
modules into the product of sets, so the codiagonal of `M` induces on `Inf_x(M)` a binary
operation which is a homomorphism for composition and has the identity as a two-sided unit. -/
public theorem comp_comm_infinitesimalAutomorphism (hRS : SatisfiesRSStar B S hS p hp)
    (M : SiteModule A B)
    (θ θ' : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    θ ≫ θ' = θ' ≫ θ := by
  have hbij := infinitesimalAutomorphismSetFunctor_product_bijective A B S hS toS hA p x hx hp
    hRS M M
  let G := infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp
  let u₁ : trivialDeformation A B S hS toS hA p x hx hp (siteModuleProd A B hA M M) ⟶
      trivialDeformation A B S hS toS hA p x hx hp (siteModuleProd A B hA M M) :=
    G.map (siteModuleInl A B hA M M) θ
  let u₂ : trivialDeformation A B S hS toS hA p x hx hp (siteModuleProd A B hA M M) ⟶
      trivialDeformation A B S hS toS hA p x hx hp (siteModuleProd A B hA M M) :=
    G.map (siteModuleInr A B hA M M) θ'
  have hfst : ∀ (e : M ⟶ siteModuleProd A B hA M M)
      (η : trivialDeformation A B S hS toS hA p x hx hp M ⟶
        trivialDeformation A B S hS toS hA p x hx hp M) (k : siteModuleProd A B hA M M ⟶ M)
      (_hk : e ≫ k = 𝟙 M),
      G.map k (G.map e η) = η := by
    intro e η k hk
    change (G.map e ≫ G.map k) η = η
    rw [← G.map_comp, hk, G.map_id]
    rfl
  have hzero : ∀ (e : M ⟶ siteModuleProd A B hA M M)
      (η : trivialDeformation A B S hS toS hA p x hx hp M ⟶
        trivialDeformation A B S hS toS hA p x hx hp M) (k : siteModuleProd A B hA M M ⟶ M)
      (_hk : e ≫ k = 0),
      G.map k (G.map e η) = 𝟙 (trivialDeformation A B S hS toS hA p x hx hp M) := by
    intro e η k hk
    change (G.map e ≫ G.map k) η = 𝟙 (trivialDeformation A B S hS toS hA p x hx hp M)
    rw [← G.map_comp, hk]
    exact infinitesimalAutomorphismSetFunctor_map_zero A B S hS toS hA p x hx hp M η
  have h₁ : G.map (siteModuleFst A B hA M M) u₁ = θ :=
    hfst _ θ _ (siteModuleInl_comp_fst A B hA M M)
  have h₂ : G.map (siteModuleSnd A B hA M M) u₁ =
      𝟙 (trivialDeformation A B S hS toS hA p x hx hp M) :=
    hzero _ θ _ (siteModuleInl_comp_snd A B hA M M)
  have h₃ : G.map (siteModuleFst A B hA M M) u₂ =
      𝟙 (trivialDeformation A B S hS toS hA p x hx hp M) :=
    hzero _ θ' _ (siteModuleInr_comp_fst A B hA M M)
  have h₄ : G.map (siteModuleSnd A B hA M M) u₂ = θ' :=
    hfst _ θ' _ (siteModuleInr_comp_snd A B hA M M)
  have hd₁ : G.map (siteModuleCodiag A B hA M) u₁ = θ :=
    hfst _ θ _ (siteModuleInl_comp_codiag A B hA M)
  have hd₂ : G.map (siteModuleCodiag A B hA M) u₂ = θ' :=
    hfst _ θ' _ (siteModuleInr_comp_codiag A B hA M)
  have hmul : ∀ (K : SiteModule A B) (k : siteModuleProd A B hA M M ⟶ K),
      G.map k (u₁ ≫ u₂) = G.map k u₁ ≫ G.map k u₂ := fun K k =>
    infinitesimalAutomorphismSetFunctor_map_comp_endo A B S hS toS hA p x hx hp k u₁ u₂
  have hmul' : ∀ (K : SiteModule A B) (k : siteModuleProd A B hA M M ⟶ K),
      G.map k (u₂ ≫ u₁) = G.map k u₂ ≫ G.map k u₁ := fun K k =>
    infinitesimalAutomorphismSetFunctor_map_comp_endo A B S hS toS hA p x hx hp k u₂ u₁
  have e₁ : G.map (siteModuleFst A B hA M M) (u₁ ≫ u₂) = θ :=
    (hmul _ (siteModuleFst A B hA M M)).trans
      ((congrArg₂ (· ≫ ·) h₁ h₃).trans (Category.comp_id θ))
  have e₂ : G.map (siteModuleFst A B hA M M) (u₂ ≫ u₁) = θ :=
    (hmul' _ (siteModuleFst A B hA M M)).trans
      ((congrArg₂ (· ≫ ·) h₃ h₁).trans (Category.id_comp θ))
  have e₃ : G.map (siteModuleSnd A B hA M M) (u₁ ≫ u₂) = θ' :=
    (hmul _ (siteModuleSnd A B hA M M)).trans
      ((congrArg₂ (· ≫ ·) h₂ h₄).trans (Category.id_comp θ'))
  have e₄ : G.map (siteModuleSnd A B hA M M) (u₂ ≫ u₁) = θ' :=
    (hmul' _ (siteModuleSnd A B hA M M)).trans
      ((congrArg₂ (· ≫ ·) h₄ h₂).trans (Category.comp_id θ'))
  have hcomm : u₁ ≫ u₂ = u₂ ≫ u₁ :=
    hbij.1 (Prod.ext (e₁.trans e₂.symm) (e₃.trans e₄.symm))
  have hc₁ : G.map (siteModuleCodiag A B hA M) (u₁ ≫ u₂) = θ ≫ θ' :=
    (hmul _ (siteModuleCodiag A B hA M)).trans (congrArg₂ (· ≫ ·) hd₁ hd₂)
  have hc₂ : G.map (siteModuleCodiag A B hA M) (u₂ ≫ u₁) = θ' ≫ θ :=
    (hmul' _ (siteModuleCodiag A B hA M)).trans (congrArg₂ (· ≫ ·) hd₂ hd₁)
  exact hc₁.symm.trans ((congrArg _ hcomm).trans hc₂)

end Commute

end Deformation.Artin
