module

public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated

/-! # Gluing a morphism of a fibre from its restrictions to a covering

Let `p : 𝒳 ⥤ 𝒮` be a fibred category over a site `(𝒮, J)` and let `x`, `y` be objects of the
fibre over `U`. Condition (2) of Stacks 026F says that the presheaf `Mor(x, y)` of Stacks 02ZB
is a sheaf on `𝒮/U`. Under this condition, a family of morphisms `θ f : f^* x ⟶ f^* y` given
over the members of a covering sieve and compatible with base change comes from a morphism
`x ⟶ y` of the fibre, and the same holds for isomorphisms.

## Main results

* `CategoryTheory.Functor.morRestrict_eq_pullbackFiberHom`, the restriction map of `Mor(x, y)`
  expressed by base change and the canonical contractions of iterated chosen pullbacks;
* `CategoryTheory.Functor.exists_fiberHom_of_locally`, a compatible family of morphisms over a
  covering sieve comes from a morphism of the fibre;
* `CategoryTheory.Functor.exists_fiberIso_of_locally`, its form for isomorphisms.

## Implementation notes

The compatibility hypothesis names the base morphism `b` that the composite `γ ≫ f` equals,
rather than writing the composite, for the reason
`CategoryTheory.Functor.pullbackFiberCompIso'` does: the members of a sieve on `𝒮/U` are
objects `g` of `𝒮/U` whose structure morphism `g.hom` is *equal* to, but not the same morphism
as, the relevant composite, and a hypothesis stated at the composite could not be applied to
them.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}

/-- The restriction map of `Mor(x, y)` along `h : g₁ ⟶ g₂` of `𝒮/U` is base change along
`h.left`, conjugated by the canonical contractions of the iterated chosen pullbacks. -/
lemma morRestrict_eq_pullbackFiberHom (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom) :
    morRestrict p x y h m =
      (pullbackFiberCompIso' x g₂.hom h.left g₁.hom (Over.w h)).inv ≫
        pullbackFiberHom m h.left ≫
        (pullbackFiberCompIso' y g₂.hom h.left g₁.hom (Over.w h)).hom := by
  refine (morRestrict_uniq p x y h m _ ?_).symm
  simp only [Functor.map_comp, Category.assoc, pullbackFiberCompIso'_hom_fac,
    pullbackFiberHom_fac_assoc]
  rw [← Category.assoc, fiberInclusion_map_pullbackFiberCompIso'_inv_comp_pullbackMap p x h]

/-- If an arrow `k : g ⟶ Over.mk (𝟙 U)` of `𝒮/U` belongs to the sieve induced by a sieve `R`
on `U`, then `g.hom` belongs to `R`. -/
lemma mem_of_overEquiv_symm {R : Sieve U} {g : Over U} (k : g ⟶ Over.mk (𝟙 U))
    (hk : ((Sieve.overEquiv (Over.mk (𝟙 U))).symm R : Sieve (Over.mk (𝟙 U))).arrows k) :
    R.arrows g.hom := by
  rw [← show k.left = g.hom by simpa using Over.w k]
  exact hk

/-- If `Mor(x, y)` is a sheaf, a family of morphisms `θ f : f^* x ⟶ f^* y` of the fibres, given
over the members `f` of a covering sieve of `U` and compatible with base change, is the family
of base changes of a single morphism `x ⟶ y` of the fibre over `U`. -/
theorem exists_fiberHom_of_locally {J : GrothendieckTopology 𝒮} {x y : p.Fiber U}
    (hmor : IsMorSheaf p J U x y) {R : Sieve U} (hR : R ∈ J U)
    (θ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U), R.arrows f → (pullbackFiber p x f ⟶ pullbackFiber p y f))
    (hθ : ∀ ⦃V W : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U) (hb : γ ≫ f = b)
      (hb' : R.arrows b),
      θ b hb' = (pullbackFiberCompIso' x f γ b hb).inv ≫
        pullbackFiberHom (θ f hf) γ ≫ (pullbackFiberCompIso' y f γ b hb).hom) :
    ∃ m : x ⟶ y, ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), pullbackFiberHom m f = θ f hf := by
  have hSmem : (Sieve.overEquiv (Over.mk (𝟙 U))).symm R ∈ (J.over U) (Over.mk (𝟙 U)) :=
    J.overEquiv_symm_mem_over (Over.mk (𝟙 U)) R hR
  have hsheaf : Presieve.IsSheafFor (morPresheaf p x y)
      (((Sieve.overEquiv (Over.mk (𝟙 U))).symm R : Sieve (Over.mk (𝟙 U))) :
        Presieve (Over.mk (𝟙 U))) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hmor _ hSmem
  let fam : Presieve.FamilyOfElements (morPresheaf p x y)
      (((Sieve.overEquiv (Over.mk (𝟙 U))).symm R : Sieve (Over.mk (𝟙 U))) :
        Presieve (Over.mk (𝟙 U))) :=
    fun g k hk => θ g.hom (mem_of_overEquiv_symm k hk)
  have hcompat : fam.Compatible := by
    refine (Presieve.compatible_iff_sieveCompatible fam).2 fun Y Z k g hk => ?_
    have key (h₁ : R.arrows Z.hom) (h₂ : R.arrows Y.hom) :
        θ Z.hom h₁ = morRestrict p x y g (θ Y.hom h₂) := by
      rw [morRestrict_eq_pullbackFiberHom]
      exact hθ Y.hom h₂ g.left Z.hom (Over.w g) h₁
    exact key _ _
  obtain ⟨t, hamalg, -⟩ := hsheaf fam hcompat
  refine ⟨(pullbackFiberIdIso x).inv ≫ t ≫ (pullbackFiberIdIso y).hom, fun V f hf => ?_⟩
  let k : (Over.mk f : Over U) ⟶ Over.mk (𝟙 U) := Over.homMk f (by simp)
  have hk : (((Sieve.overEquiv (Over.mk (𝟙 U))).symm R : Sieve (Over.mk (𝟙 U))) :
      Presieve (Over.mk (𝟙 U))) k := hf
  have hres : morRestrict p x y k t = θ f (mem_of_overEquiv_symm k hk) := hamalg k hk
  rw [morRestrict_eq_pullbackFiberHom p x y k t] at hres
  rw [pullbackFiberHom_comp, pullbackFiberHom_comp,
    pullbackFiberHom_pullbackFiberIdIso_inv_eq x f]
  have hidhom : pullbackFiberHom (pullbackFiberIdIso y).hom f =
      (pullbackFiberCompIso' y (𝟙 U) f f (Category.comp_id f)).hom := by
    have h₂ := (pullbackFiberIso (pullbackFiberIdIso y) f).inv_hom_id
    rw [pullbackFiberIso_inv, pullbackFiberIso_hom,
      pullbackFiberHom_pullbackFiberIdIso_inv_eq y f] at h₂
    rw [← Category.id_comp (pullbackFiberHom (pullbackFiberIdIso y).hom f),
      ← Iso.hom_inv_id (pullbackFiberCompIso' y (𝟙 U) f f (Category.comp_id f)),
      Category.assoc, h₂, Category.comp_id]
  rwa [hidhom]

/-- If the presheaves `Mor(a, b)` of the fibre over `U` are sheaves, a family of isomorphisms
`θ f : f^* x ≅ f^* y` of the fibres, given over the members of a covering sieve of `U` and
compatible with base change, comes from an isomorphism `x ≅ y` of the fibre over `U`. -/
theorem exists_fiberIso_of_locally {J : GrothendieckTopology 𝒮} {x y : p.Fiber U}
    (hmor : ∀ (a b : p.Fiber U), IsMorSheaf p J U a b) {R : Sieve U} (hR : R ∈ J U)
    (θ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U), R.arrows f → (pullbackFiber p x f ≅ pullbackFiber p y f))
    (hθ : ∀ ⦃V W : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U) (hb : γ ≫ f = b)
      (hb' : R.arrows b),
      (θ b hb').hom = (pullbackFiberCompIso' x f γ b hb).inv ≫
        pullbackFiberHom (θ f hf).hom γ ≫ (pullbackFiberCompIso' y f γ b hb).hom) :
    ∃ e : x ≅ y,
      ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), pullbackFiberHom e.hom f = (θ f hf).hom := by
  have hθinv : ∀ ⦃V W : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U)
      (hb : γ ≫ f = b) (hb' : R.arrows b),
      (θ b hb').inv = (pullbackFiberCompIso' y f γ b hb).inv ≫
        pullbackFiberHom (θ f hf).inv γ ≫ (pullbackFiberCompIso' x f γ b hb).hom := by
    intro V W f hf γ b hb hb'
    have hiso : θ b hb' = (pullbackFiberCompIso' x f γ b hb).symm ≪≫
        pullbackFiberIso (θ f hf) γ ≪≫ pullbackFiberCompIso' y f γ b hb :=
      Iso.ext (by simpa using hθ f hf γ b hb hb')
    simp [hiso]
  obtain ⟨m, hm⟩ :=
    exists_fiberHom_of_locally p (hmor x y) hR (fun {_V} f hf => (θ f hf).hom) hθ
  obtain ⟨n, hn⟩ :=
    exists_fiberHom_of_locally p (hmor y x) hR (fun {_V} f hf => (θ f hf).inv) hθinv
  have hmn : m ≫ n = 𝟙 x := by
    refine eq_of_pullbackFiberHom_locally_eq p (hmor x x) hR fun V f hf => ?_
    rw [pullbackFiberHom_comp, hm f hf, hn f hf, Iso.hom_inv_id, pullbackFiberHom_id]
  have hnm : n ≫ m = 𝟙 y := by
    refine eq_of_pullbackFiberHom_locally_eq p (hmor y y) hR fun V f hf => ?_
    rw [pullbackFiberHom_comp, hn f hf, hm f hf, Iso.inv_hom_id, pullbackFiberHom_id]
  exact ⟨⟨m, n, hmn, hnm⟩, hm⟩

end Functor

end CategoryTheory
