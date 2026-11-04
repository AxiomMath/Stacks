module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Yoneda

/-!
# A base-change comparison is an isomorphism when it corepresents through global sections

Let `f : A →+* B` be a map of commutative rings, let `Γ_C : 𝒞 ⥤ ModuleCat A` and
`Γ_D : 𝒟 ⥤ ModuleCat B` be "global sections" functors and `G : 𝒟 ⥤ 𝒞` a functor compatible with
them, `G ⋙ Γ_C ≅ Γ_D ⋙ restrictScalars f`.  Given objects `N` of `𝒞` and `K` of `𝒟` and a map
`κ : N ⟶ G K`, its global sections give an `A`-linear map `n : Γ_C N ⟶ Γ_D K`, and hence a
`B`-linear base-change comparison `B ⊗_A Γ_C N ⟶ Γ_D K`.

This file proves that the comparison is an isomorphism as soon as

* `K` corepresents `L ↦ Hom(N, G L)` through `κ`;
* global sections are bijective on maps out of `N` and out of `K`; and
* some object `L₁` of `𝒟` has global sections isomorphic to `B ⊗_A Γ_C N`.

The three bijections compose, for every object `L` of `𝒟`, to the map `λ ↦ n ≫ λ` from
`B`-linear maps `Γ_D K ⟶ Γ_D L` to `A`-linear maps `Γ_C N ⟶ Γ_D L`, which is composition with the
comparison under the extension–restriction adjunction.  At `L₁` this produces a retraction of
the comparison, and at `L = K` injectivity shows that the retraction is a section.

This is the formal core of affine flat base change for sheaves of modules with the flat base
change property (Stacks 0762): `𝒞` and `𝒟` are the sheaves of modules on the small étale sites of
the two affine schemes, `Γ` is the evaluation at the final object, `G` the direct image, and `κ`
the comparison map of Stacks 06WC.

## Main results

* `ModuleCat.isIso_extendScalars_homEquiv_symm_of_corepresents`
-/

@[expose] public section

namespace ModuleCat

open CategoryTheory

universe u v₁ v₂ u₁ u₂

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
  {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  (ΓC : 𝒞 ⥤ ModuleCat.{u} A) (ΓD : 𝒟 ⥤ ModuleCat.{u} B) (G : 𝒟 ⥤ 𝒞)
  (γ : G ⋙ ΓC ≅ ΓD ⋙ ModuleCat.restrictScalars.{u} f)

/-- **A base-change comparison which corepresents through global sections is an isomorphism.**
See the module docstring.  Only two test objects of `𝒟` are needed: `K` itself, and one object
`L₁` whose global sections are abstractly isomorphic to the source `B ⊗_A Γ_C N` of the
comparison. -/
theorem isIso_extendScalars_homEquiv_symm_of_corepresents {N : 𝒞} {K L₁ : 𝒟}
    (κ : N ⟶ G.obj K)
    (h₁ : ∀ L : 𝒟, Function.Bijective (fun u : K ⟶ L => κ ≫ G.map u))
    (h₂ : ∀ L : 𝒟, Function.Bijective (fun u : N ⟶ G.obj L => ΓC.map u))
    (h₃ : ∀ L : 𝒟, Function.Bijective (fun u : K ⟶ L => ΓD.map u))
    (e : ΓD.obj L₁ ≅ (ModuleCat.extendScalars.{u, u, u} f).obj (ΓC.obj N)) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj.{u} f).homEquiv _ _).symm
      (ΓC.map κ ≫ γ.hom.app K)) := by
  set adj := ModuleCat.extendRestrictScalarsAdj.{u} f
  set n : ΓC.obj N ⟶ (ModuleCat.restrictScalars f).obj (ΓD.obj K) := ΓC.map κ ≫ γ.hom.app K
  set bc := (adj.homEquiv _ _).symm n
  -- composition with the comparison is `λ ↦ n ≫ λ` under the adjunction
  have hadj : ∀ {T : ModuleCat.{u} B} (x : ΓD.obj K ⟶ T),
      adj.homEquiv _ _ (bc ≫ x) = n ≫ (ModuleCat.restrictScalars f).map x := by
    intro T x
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  -- for every `L`, the map `λ ↦ n ≫ λ` out of `Hom(Γ_D K, Γ_D L)` is bijective
  have hΦ : ∀ L : 𝒟, Function.Bijective (fun x : ΓD.obj K ⟶ ΓD.obj L =>
      n ≫ (ModuleCat.restrictScalars f).map x) := by
    intro L
    have hcomp : (fun x : ΓD.obj K ⟶ ΓD.obj L => n ≫ (ModuleCat.restrictScalars f).map x) ∘
        (fun u : K ⟶ L => ΓD.map u) =
        (fun x : ΓC.obj N ⟶ ΓC.obj (G.obj L) => x ≫ γ.hom.app L) ∘
          (fun u : N ⟶ G.obj L => ΓC.map u) ∘ (fun u : K ⟶ L => κ ≫ G.map u) := by
      funext u
      have hγ := γ.hom.naturality u
      simp only [Functor.comp_map] at hγ
      simp only [Function.comp_apply, n, Functor.map_comp, Category.assoc]
      rw [hγ]
    have hpost : Function.Bijective (fun x : ΓC.obj N ⟶ ΓC.obj (G.obj L) =>
        x ≫ γ.hom.app L) :=
      ⟨fun x y hxy => (cancel_mono (γ.hom.app L)).1 hxy,
        fun y => ⟨y ≫ γ.inv.app L, by simp⟩⟩
    rw [← Function.Bijective.of_comp_iff _ (h₃ L), hcomp]
    exact hpost.comp ((h₂ L).comp (h₁ L))
  -- a retraction of the comparison, from the test object `L₁`
  obtain ⟨μ, hμ⟩ := (hΦ L₁).2 (adj.homEquiv _ _ e.inv)
  have hμ' : bc ≫ μ = e.inv := (adj.homEquiv _ _).injective ((hadj μ).trans hμ)
  have hret : bc ≫ μ ≫ e.hom = 𝟙 _ := by
    rw [← Category.assoc, hμ', Iso.inv_hom_id]
  -- the retraction is a section, by injectivity at the test object `K`
  have hsec : (μ ≫ e.hom) ≫ bc = 𝟙 _ := (hΦ K).1 <| by
    dsimp only
    rw [← hadj, ← hadj, ← Category.assoc, hret, Category.id_comp, Category.comp_id]
  exact ⟨⟨μ ≫ e.hom, hret, hsec⟩⟩

/-- **A base-change comparison which corepresents through global sections is an isomorphism**,
in the form with the global sections of the source given as a module.  Let `n : M ⟶ Γ_D K` be
`A`-linear.  If for every object `L` of `𝒟` the map `u ↦ n ≫ Γ_D u` from `Hom(K, L)` to `A`-linear
maps `M ⟶ Γ_D L` is bijective, if `Γ_D` is bijective on maps out of `K`, and if some object `L₁`
has global sections isomorphic to `B ⊗_A M`, then the comparison `B ⊗_A M ⟶ Γ_D K` is an
isomorphism. -/
theorem isIso_extendScalars_homEquiv_symm_of_corepresents' (M : ModuleCat.{u} A) {K L₁ : 𝒟}
    (n : M ⟶ (ModuleCat.restrictScalars f).obj (ΓD.obj K))
    (h₁ : ∀ L : 𝒟, Function.Bijective
      (fun u : K ⟶ L => n ≫ (ModuleCat.restrictScalars f).map (ΓD.map u)))
    (h₃ : ∀ L : 𝒟, Function.Bijective (fun u : K ⟶ L => ΓD.map u))
    (e : ΓD.obj L₁ ≅ (ModuleCat.extendScalars.{u, u, u} f).obj M) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj.{u} f).homEquiv _ _).symm n) := by
  set adj := ModuleCat.extendRestrictScalarsAdj.{u} f
  set bc := (adj.homEquiv _ _).symm n
  have hadj : ∀ {T : ModuleCat.{u} B} (x : ΓD.obj K ⟶ T),
      adj.homEquiv _ _ (bc ≫ x) = n ≫ (ModuleCat.restrictScalars f).map x := by
    intro T x
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  have hΦ : ∀ L : 𝒟, Function.Bijective (fun x : ΓD.obj K ⟶ ΓD.obj L =>
      n ≫ (ModuleCat.restrictScalars f).map x) := fun L =>
    (Function.Bijective.of_comp_iff _ (h₃ L)).1 (h₁ L)
  obtain ⟨μ, hμ⟩ := (hΦ L₁).2 (adj.homEquiv _ _ e.inv)
  have hμ' : bc ≫ μ = e.inv := (adj.homEquiv _ _).injective ((hadj μ).trans hμ)
  have hret : bc ≫ μ ≫ e.hom = 𝟙 _ := by
    rw [← Category.assoc, hμ', Iso.inv_hom_id]
  have hsec : (μ ≫ e.hom) ≫ bc = 𝟙 _ := (hΦ K).1 <| by
    dsimp only
    rw [← hadj, ← hadj, ← Category.assoc, hret, Category.id_comp, Category.comp_id]
  exact ⟨⟨μ ≫ e.hom, hret, hsec⟩⟩

end ModuleCat

end
