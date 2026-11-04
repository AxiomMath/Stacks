module

public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BaseEquivalence

/-! # The isomorphism-class map of a gerbe is locally bijective

Let `(𝒞, J)` be a site, let `q : 𝒯 ⥤ 𝒞` and `p : 𝒮 ⥤ 𝒞` be categories fibred in groupoids over
it and let `G : 𝒮 ⥤ 𝒯` be a 1-morphism over `𝒞` making `𝒮` a gerbe over `𝒯`. Passing to
isomorphism classes of objects of the fibres turns `G` into a map of presheaves of sets
(`CategoryTheory.Functor.isoClassMap`), and the two local conditions of a gerbe say exactly that
this map is locally surjective and locally injective for `J`.

All names below are in the namespace `CategoryTheory`.

## Main results

* `IsGerbeOver.isLocallySurjective_isoClassMap`: the isomorphism-class map of a gerbe is locally
  surjective.
* `IsGerbeOver.isLocallyInjective_isoClassMap`: the isomorphism-class map of a gerbe is locally
  injective.
* `isGerbeOver_id`: a category fibred in groupoids is a gerbe over itself.
* `IsGerbeOver.of_equivalenceOver`: a 1-morphism which is an equivalence over the site makes its
  source a gerbe over its target.

## References

* [Stacks Project, Tag 04SC](https://stacks.math.columbia.edu/tag/04SC)
* [Stacks Project, Tag 06P0](https://stacks.math.columbia.edu/tag/06P0)
* [Stacks Project, Tag 06P2](https://stacks.math.columbia.edu/tag/06P2)
-/

@[expose] public section

open Opposite

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section Universes

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} {𝒯 : Type u₃} [Category.{v₂} 𝒮]
  [Category.{v₃} 𝒯]

/-- **A category fibred in groupoids is a gerbe over itself**, via the identity 1-morphism. -/
theorem isGerbeOver_id (J : GrothendieckTopology 𝒞) {q : 𝒯 ⥤ 𝒞}
    (hq : q.IsFiberedInGroupoids) : IsGerbeOver J q (𝟭 𝒯) where
  base_isFiberedInGroupoids := hq
  isFiberedInGroupoids := by rwa [Functor.id_comp]
  locally_essSurj := by
    intro U y hy
    exact ⟨⊤, J.top_mem U, fun V f _ => hq.exists_lift f y hy⟩
  locally_full := by
    intro U x x' b hb
    have hx : q.obj x = U := IsHomLift.domain_eq q (𝟙 U) b
    have hx' : q.obj x' = U := IsHomLift.codomain_eq q (𝟙 U) b
    refine ⟨⊤, J.top_mem U, fun V f _ => ?_⟩
    obtain ⟨x₁, ξ, hξ⟩ := hq.exists_lift f x hx
    obtain ⟨x₁', ξ', hξ'⟩ := hq.exists_lift f x' hx'
    have h₁ : q.obj x₁ = V := IsHomLift.domain_eq q f ξ
    have h₁' : q.obj x₁' = V := IsHomLift.domain_eq q f ξ'
    have hfac : eqToHom (h₁.trans h₁'.symm) ≫ q.map ξ' = q.map (ξ ≫ b) := by
      have := hξ
      have := hξ'
      have := hb
      rw [Functor.map_comp, IsHomLift.fac' q f ξ, IsHomLift.fac' q (𝟙 U) b,
        IsHomLift.fac' q f ξ']
      simp
    obtain ⟨a, ⟨hamap, hafac⟩, -⟩ := hq.unique_lift ξ' (ξ ≫ b) (eqToHom (h₁.trans h₁'.symm)) hfac
    have ha : q.IsHomLift (𝟙 V) a :=
      IsHomLift.of_fac' q (𝟙 V) a h₁ h₁' (by rw [hamap]; simp)
    have hcomp : (𝟭 𝒯) ⋙ q = q := Functor.id_comp q
    exact ⟨x₁, x₁', ξ, ξ', a, hcomp ▸ hξ, hcomp ▸ hξ', hcomp ▸ ha, hafac⟩

namespace IsGerbeOver

variable {J : GrothendieckTopology 𝒞} {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒯}

/-- **A 1-morphism which is an equivalence over the site makes its source a gerbe over its
target.** This is a degenerate case of Stacks 06P0. -/
theorem of_equivalenceOver (hq : q.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    IsGerbeOver J q e.hom.functor := by
  have hequiv : Functor.IsEquivalenceOver (e.hom.functor ⋙ q) ((𝟭 𝒯) ⋙ q) e.hom.functor := by
    rw [e.hom.w, Functor.id_comp]
    exact
      { inv := e.inv.functor
        inv_over := e.inv.w
        unitIso := e.unitIso.symm
        counitIso := e.counitIso
        unit_vertical := fun x => by
          have h := e.isHomLift_unitIso_inv_app x
          have hx : p.obj ((e.hom.functor ⋙ e.inv.functor).obj x) = p.obj x := by
            change ((e.hom.functor ⋙ e.inv.functor) ⋙ p).obj x = p.obj x
            rw [Functor.assoc, e.inv.w, e.hom.w]
          rw [hx]
          exact h
        counit_vertical := fun y => by
          have h := e.isHomLift_counitIso_hom_app y
          have hy : q.obj ((e.inv.functor ⋙ e.hom.functor).obj y) = q.obj y := by
            change ((e.inv.functor ⋙ e.hom.functor) ⋙ q).obj y = q.obj y
            rw [Functor.assoc, e.hom.w, e.inv.w]
          rw [hy]
          exact h }
  exact IsGerbeOver.of_isEquivalenceOver_base_symm (e.hom.functor.comp_id) hequiv
    (isGerbeOver_id J hq)

end IsGerbeOver

end Universes

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 𝒯 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₁} 𝒯]

namespace IsGerbeOver

variable {J : GrothendieckTopology 𝒞} {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒯}

variable [p.IsFibered] [q.IsFibered]

/-- Restricting the class of `x` along `f` gives the class of the source of any lift of `f`. -/
private theorem isoClassPresheaf_map_isoClassMk_eq_of_isHomLift {𝒮' : Type u₂} [Category.{v₁} 𝒮']
    {p' : 𝒮' ⥤ 𝒞} [p'.IsFibered] (hp : p'.IsFiberedInGroupoids) {U V : 𝒞} (f : V ⟶ U)
    (x : p'.Fiber U) (y : p'.Fiber V) (φ : y.1 ⟶ x.1) (hφ : p'.IsHomLift f φ) :
    p'.isoClassPresheaf.map f.op (Functor.isoClassMk p' x) = Functor.isoClassMk p' y := by
  have := hp.isStronglyCartesian_homLift f φ
  exact (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian f x y φ hφ inferInstance).symm

/-- **The isomorphism-class map of a gerbe is locally surjective.** Every isomorphism class of
objects of a fibre of `q` over `U` becomes, after restriction along the members of a covering of
`U`, the class of a `G`-image. -/
theorem isLocallySurjective_isoClassMap (hG : IsGerbeOver J q G)
    (hm : Functor.IsFibredOneMorphism p q G) :
    Presheaf.IsLocallySurjective J (Functor.isoClassMap hm) := by
  have hqg : q.IsFiberedInGroupoids := hG.base_isFiberedInGroupoids
  have hpg : p.IsFiberedInGroupoids := hm.comp_eq ▸ hG.isFiberedInGroupoids
  constructor
  intro U c
  obtain ⟨y, rfl⟩ := Functor.isoClassMk_surjective (p := q) c
  obtain ⟨S, hS, hcov⟩ := hG.locally_essSurj y.1 y.2
  refine J.superset_covering ?_ hS
  intro V f hf
  obtain ⟨x, ψ, hψ⟩ := hcov f hf
  have hxV : (G ⋙ q).obj x = V := IsHomLift.domain_eq q f ψ
  have hpx : p.obj x = V := by rwa [← hm.comp_eq]
  have hGx : q.obj (G.obj x) = V := hxV
  refine ⟨Functor.isoClassMk p (Functor.Fiber.mk hpx), ?_⟩
  rw [Functor.isoClassMap_app_isoClassMk]
  have hobj : (Functor.fiberFunctorOfCompEq hm.comp_eq V).obj (Functor.Fiber.mk hpx) =
      (Functor.Fiber.mk hGx : q.Fiber V) := Subtype.ext rfl
  rw [hobj]
  exact (isoClassPresheaf_map_isoClassMk_eq_of_isHomLift hqg f y (Functor.Fiber.mk hGx) ψ hψ).symm

/-- **The isomorphism-class map of a gerbe is locally injective.** Two objects of a fibre of `p`
over `U` whose `G`-images have the same class become isomorphic after restriction along the
members of a covering of `U`. -/
theorem isLocallyInjective_isoClassMap (hG : IsGerbeOver J q G)
    (hm : Functor.IsFibredOneMorphism p q G) :
    Presheaf.IsLocallyInjective J (Functor.isoClassMap hm) := by
  have hqg : q.IsFiberedInGroupoids := hG.base_isFiberedInGroupoids
  have hpg : p.IsFiberedInGroupoids := hm.comp_eq ▸ hG.isFiberedInGroupoids
  have hconv : ∀ {R T : 𝒞} (k : R ⟶ T) {a b : 𝒮} (φ : a ⟶ b),
      (G ⋙ q).IsHomLift k φ → p.IsHomLift k φ := by
    intro R T k a b φ h
    exact hm.comp_eq ▸ h
  constructor
  intro U c d hcd
  obtain ⟨U⟩ := U
  induction c using Quotient.inductionOn with
  | _ c =>
    induction d using Quotient.inductionOn with
    | _ d =>
      have hcd' : (Functor.isoClassMap hm).app (op U) (Functor.isoClassMk p c) =
          (Functor.isoClassMap hm).app (op U) (Functor.isoClassMk p d) := hcd
      rw [Functor.isoClassMap_app_isoClassMk, Functor.isoClassMap_app_isoClassMk] at hcd'
      obtain ⟨i⟩ := Functor.exists_iso_of_isoClassMk_eq hcd'
      have hb : q.IsHomLift (𝟙 U) (Functor.Fiber.fiberInclusion.map i.hom) := i.hom.2
      obtain ⟨S, hS, hcov⟩ := hG.locally_full (Functor.Fiber.fiberInclusion.map i.hom) hb
      refine J.superset_covering ?_ hS
      intro V f hf
      obtain ⟨x₁, x₂, ξ, ξ', α, hξ, hξ', hα, -⟩ := hcov f hf
      have hξp : p.IsHomLift f ξ := hconv f ξ hξ
      have hξ'p : p.IsHomLift f ξ' := hconv f ξ' hξ'
      have hαp : p.IsHomLift (𝟙 V) α := hconv (𝟙 V) α hα
      have := hαp
      have hres₁ := isoClassPresheaf_map_isoClassMk_eq_of_isHomLift hpg f c
        (Functor.Fiber.mk (IsHomLift.domain_eq p (𝟙 V) α)) ξ hξp
      have hres₂ := isoClassPresheaf_map_isoClassMk_eq_of_isHomLift hpg f d
        (Functor.Fiber.mk (IsHomLift.codomain_eq p (𝟙 V) α)) ξ' hξ'p
      have hgrp : IsGroupoid (p.Fiber V) := hpg.fiber_isGroupoid V
      have hiso : IsIso (Functor.Fiber.homMk p V α) := hgrp.all_isIso _
      have hsame : Functor.isoClassMk p (Functor.Fiber.mk (IsHomLift.domain_eq p (𝟙 V) α)) =
          Functor.isoClassMk p (Functor.Fiber.mk (IsHomLift.codomain_eq p (𝟙 V) α)) :=
        Functor.isoClassMk_eq_of_iso (asIso (Functor.Fiber.homMk p V α))
      exact hres₁.trans (hsame.trans hres₂.symm)

end IsGerbeOver

end CategoryTheory

end
