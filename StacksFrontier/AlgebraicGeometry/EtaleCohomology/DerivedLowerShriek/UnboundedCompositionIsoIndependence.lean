module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnboundedSquareMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoAssociativity

/-!
# The isomorphisms of [Stacks, Tag 0F7J] on `D(X_étale, Λ)` do not depend on the auxiliary
compactification

Let `Λ` be a torsion ring and let `f : X ⟶ Y`, `g : Y ⟶ Z` be separated morphisms of finite type
of quasi-compact and quasi-separated schemes. The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` on
unbounded derived categories, `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`, is
built from a compactification `i : Y ⟶ Ȳ` of `g` and a compactification `X ⟶ X̄` of `X` over `Ȳ`
chosen by Nagata's theorem. This file proves that every compactification `X ⟶ X̄` gives the same
isomorphism, as the proof of [Stacks, Tag 0F7J] asserts.

Through `X̄` the isomorphism is the Leray isomorphism for `X̄ ⟶ Ȳ ⟶ Z` followed by `Rḡ_*` of
`Ψ : R(f ≫ i)_! ≅ i_! ∘ Rf_!` (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedRestrictBaseIso`),
the open immersion case of [Stacks, Tag 0F7B]. Along a morphism `X̄ ⟶ X̄'` of compactifications
over `Ȳ`, the maps of [Stacks, Tag 0F7G] for `X ⟶ X̄ ⟶ X̄'` and for `X ⟶ X̄ ×_Ȳ Y ⟶ X̄' ×_Ȳ Y`
and the maps of [Stacks, Tag 0F7B] of the squares involved paste
([Stacks, Tags 0F7C and 0F7D]), which gives the naturality of `Ψ`.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedRestrictBaseIso_naturality`: `Ψ` is
  natural in the compactification of `X` over `Ȳ`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_eq_through`: the isomorphism of
  [Stacks, Tag 0F7J] through an arbitrary compactification of `X` over `Ȳ`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_hom_app_first` and
  `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_hom_app_third`: along the
  comparisons of [Stacks, Tag 0F7I] for `f` and for `g ∘ f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

variable (Λ : Type) [Ring Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-- The ambient morphism of a morphism of compactifications is proper. -/
instance isProper_compactificationOf_hom_map {S : Scheme.{u}} {X₀ : Over S}
    {j k : CompactificationOf X₀} (ψ : j ⟶ k) : IsProper (CompactificationOf.Hom.map ψ) := by
  have : IsProper (CompactificationOf.Hom.map ψ ≫ k.toBase) := by
    rw [CompactificationOf.map_comp_toBase]; infer_instance
  exact IsProper.of_comp _ k.toBase

/-- The comparison `Rf_!^k ⟶ Rf_!^j` of [Stacks, Tag 0F7I] along `ψ : j ⟶ k`: the map of
[Stacks, Tag 0F7G] followed by the inverse of the Leray isomorphism. -/
lemma derivedLowerShriekUnboundedHomUniv_app_eq_leray {X Y : Scheme.{u}} {f : X ⟶ Y}
    {j k : CompactificationOf (Over.mk f)} (ψ : j ⟶ k)
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ).app K =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ k.toBase).map
          ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ ψ).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map ψ)
          k.toBase j.toBase (CompactificationOf.map_comp_toBase ψ).symm).inv.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion).obj K) := by
  have hinv : inv (derivedBaseComparisonUnboundedUniv.{u, 0} Λ ψ) =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map ψ)
        k.toBase j.toBase (CompactificationOf.map_comp_toBase ψ).symm).inv :=
    IsIso.inv_eq_of_hom_inv_id (by
      rw [derivedBaseComparisonUnboundedUniv_eq_lerayIso_hom]
      exact Iso.hom_inv_id _)
  rw [derivedLowerShriekUnboundedHomUniv_app, hinv]

/-! ### The comparison of [Stacks, Tag 0F7I] along a pushed morphism of compactifications -/

section PushBase

variable {S S' X : Scheme.{u}} {p' : X ⟶ S'} (q : S' ⟶ S) (p : X ⟶ S)
  {j' k' : CompactificationOf (Over.mk p')} (ψ : j' ⟶ k') (bj : j'.space ⟶ S) [IsProper bj]
  (hbj : bj = j'.toBase ≫ q) (bk : k'.space ⟶ S) [IsProper bk] (hbk : bk = k'.toBase ≫ q)
  (hj : j'.immersion ≫ bj = p) (hk : k'.immersion ≫ bk = p)

/-- **The comparison of [Stacks, Tag 0F7I] along a pushed morphism of compactifications is the
derived direct image along `q` of the comparison over `S'`**, on unbounded derived categories,
read through the Leray isomorphisms. -/
theorem derivedLowerShriekUnboundedHomUniv_ofFactorHom
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ
        (CompactificationOf.ofFactorHom q p ψ bj hbj bk hbk hj hk)).app K =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ k'.toBase q bk hbk).hom.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ k'.immersion).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ j'.toBase q bj hbj).inv.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j'.immersion).obj K) := by
  let M := (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j'.immersion).obj K
  let θ := derivedRefinementComparisonUnboundedUniv.{u, 0} Λ ψ
  have hjb : bj = CompactificationOf.Hom.map ψ ≫ bk := by
    rw [hbj, hbk, ← Category.assoc, CompactificationOf.map_comp_toBase]
  have hA := etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ
    (CompactificationOf.Hom.map ψ) k'.toBase q j'.toBase
    (CompactificationOf.map_comp_toBase ψ).symm bk hbk bj hbj hjb M
  have hA' : (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
      (CompactificationOf.Hom.map ψ) bk bj hjb).inv.app M =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ k'.toBase q bk hbk).hom.app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map ψ)).obj M) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).map
          ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
            (CompactificationOf.Hom.map ψ) k'.toBase j'.toBase
            (CompactificationOf.map_comp_toBase ψ).symm).inv.app M) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ j'.toBase q bj hbj).inv.app M := by
    rw [← cancel_epi ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
      (CompactificationOf.Hom.map ψ) bk bj hjb).hom.app M), Iso.hom_inv_id_app, ← reassoc_of% hA]
    simp [← Functor.map_comp_assoc]
  have hn :=
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ k'.toBase q bk hbk).hom.naturality
      (θ.app K)
  simp only [Functor.comp_map] at hn
  have key : (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ bk).map (θ.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        (CompactificationOf.Hom.map ψ) bk bj hjb).inv.app M =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ k'.toBase q bk hbk).hom.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ k'.immersion).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).map
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ k'.toBase).map (θ.app K) ≫
            (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
              (CompactificationOf.Hom.map ψ) k'.toBase j'.toBase
              (CompactificationOf.map_comp_toBase ψ).symm).inv.app M) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ j'.toBase q bj hbj).inv.app M := by
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hn, hA']
    simp only [Category.assoc]
    rfl
  rw [derivedLowerShriekUnboundedHomUniv_app_eq_leray,
    derivedLowerShriekUnboundedHomUniv_app_eq_leray]
  exact key

end PushBase

/-! ### `Ψ : R(f ≫ i)_! ≅ i_! ∘ Rf_!` -/

section RestrictBase

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  [CompactSpace jg.space]

/-- **`Ψ : R(f ≫ i)_! ≅ i_! ∘ Rf_!` on `D(X_étale, Λ)`**, for a compactification `i : Y ⟶ Ȳ` of
`g` and a compactification `X ⟶ X̄` of `X` over `Ȳ`, with `R(f ≫ i)_!` computed through `X̄`
and `Rf_!` through `X̄ ×_Ȳ Y`: the open immersion case of [Stacks, Tag 0F7B] for the cartesian
square `X̄ ×_Ȳ Y`. -/
def derivedLowerShriekUnboundedRestrictBaseIso
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    derivedLowerShriekUnbounded.{u, 0} (f ≫ jg.immersion) (CompactificationOf.overBar jg jX) Λ ≅
      derivedLowerShriekUnbounded.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jg.immersion :=
  Functor.isoWhiskerRight (derivedExtensionByZeroUnboundedCompIso Λ
      (CompactificationOf.restrictBase jg jX).immersion
      (CompactificationOf.restrictBaseι jg jX)).symm
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase) ≪≫
    (Functor.isoWhiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
        (CompactificationOf.restrictBase jg jX).immersion)
      (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ jX.toBase
      jg.immersion (CompactificationOf.restrictBaseι jg jX)
      (CompactificationOf.restrictBase jg jX).toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion)) :
      etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion ⋙
        (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (CompactificationOf.restrictBaseι jg jX) ⋙
          etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase) ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion ⋙
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).toBase ⋙
          etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jg.immersion))

/-- The component of `Ψ`. -/
lemma derivedLowerShriekUnboundedRestrictBaseIso_hom_app
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jg jX).hom.app K =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
          ((derivedExtensionByZeroUnboundedCompIso Λ
            (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBaseι jg jX)).inv.app K) ≫
        (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ jX.toBase jg.immersion
          (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
          (IsPullback.of_hasPullback jX.toBase jg.immersion)).hom.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj K) :=
  rfl

/-- The chase behind `derivedLowerShriekUnboundedCompOverIso_hom_app`, over plain objects. -/
private lemma compOver_chain {𝒞' 𝒞 𝒟 : Type*} [Category* 𝒞'] [Category* 𝒞] [Category* 𝒟]
    (F : 𝒞' ⥤ 𝒞) (G : 𝒞 ⥤ 𝒟) {A₀ A₁ A₂ A₃ : 𝒞'} {c₂ c₃ c₄ : 𝒞} {d₀ d₁ : 𝒟}
    (Rι : d₀ ⟶ d₁) (L0 : d₁ ⟶ G.obj (F.obj A₁)) (L1 : d₀ ⟶ G.obj (F.obj A₀)) {A₀' : 𝒞'}
    (e1a : A₀ ⟶ A₀') (e1b : A₀' ⟶ A₁) (mb : A₁ ⟶ A₂) (ibi : A₂ ⟶ A₃) (ibh : A₃ ⟶ A₂)
    (β0 : F.obj A₁ ⟶ c₂) (mi : c₂ ⟶ c₃) (ιi : c₃ ⟶ c₄) (β1 : F.obj A₂ ⟶ c₃)
    (cinv : F.obj A₀ ⟶ F.obj A₃) (isoE : F.obj A₃ ⟶ c₄)
    (nL : Rι ≫ L0 = L1 ≫ G.map (F.map (e1a ≫ e1b)))
    (hcinv : cinv = F.map (e1a ≫ e1b ≫ mb ≫ ibi))
    (hisoE : isoE = F.map ibh ≫ β1 ≫ ιi) (hcan : ibi ≫ ibh = 𝟙 _)
    (nβ : F.map mb ≫ β1 = β0 ≫ mi) :
    Rι ≫ L0 ≫ G.map β0 ≫ G.map mi ≫ G.map ιi = L1 ≫ G.map (cinv ≫ isoE) := by
  have h1 : G.map (F.map ibi) ≫ G.map (F.map ibh) = 𝟙 _ := by
    rw [← G.map_comp, ← F.map_comp, hcan, F.map_id, G.map_id]
  have h2 : G.map (F.map mb) ≫ G.map β1 = G.map β0 ≫ G.map mi := by
    rw [← G.map_comp, nβ, G.map_comp]
  rw [hcinv, hisoE, reassoc_of% nL]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% h1, reassoc_of% h2]

/-- **The isomorphism of [Stacks, Tag 0F7J] through the compactifications of its proof is the
Leray isomorphism followed by `Rḡ_*` of `Ψ`.** -/
theorem derivedLowerShriekUnboundedCompOverIso_hom_app
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase jg.toBase
          (jX.toBase ≫ jg.toBase) rfl).hom.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (CompactificationOf.overBar jg jX).immersion).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase).map
          ((derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jg jX).hom.app K) := by
  have hco : (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K =
      ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jX.toBase ≫ jg.toBase)).map
          ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
              CompactificationOf.restrictBaseι jg jX)).hom.app K ≫
            (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
              (etaleModuleExtensionByZeroCompIso.{u, 0} Λ
                (CompactificationOf.restrictBase jg jX).immersion
                (CompactificationOf.restrictBaseι jg jX))).hom.app K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase jg.toBase
          (jX.toBase ≫ jg.toBase) rfl).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBaseι jg jX)).mapDerivedCategory.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K))) ≫
      ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase).map
          ((etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase jg.immersion
            (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
            (IsPullback.of_hasPullback jX.toBase jg.immersion)).hom.app
            ((etaleModuleExtensionByZero.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).immersion).mapDerivedCategory.obj K)) ≫
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jg.immersion).mapDerivedCategory.map
            ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).toBase).map
              ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
                (CompactificationOf.restrictBase jg jX).immersion).inv.app K))) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase).map
          ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ jg.immersion).inv.app
            ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).toBase).obj
              ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
                (CompactificationOf.restrictBase jg jX).immersion).obj K))))) :=
    rfl
  have nL := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase jg.toBase
    (jX.toBase ≫ jg.toBase) rfl).hom.naturality
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
          ((CompactificationOf.restrictBase jg jX).immersion ≫
            CompactificationOf.restrictBaseι jg jX)).hom.app K ≫
        (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBaseι jg jX))).hom.app K)
  have nβ := (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase jg.immersion
      (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion)).hom.naturality
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
        (CompactificationOf.restrictBase jg jX).immersion).inv.app K)
  rw [hco, Category.assoc, derivedLowerShriekUnboundedRestrictBaseIso_hom_app]
  exact compOver_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase)
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    nL rfl rfl (Iso.inv_hom_id_app (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
      (CompactificationOf.restrictBaseι jg jX)) _) nβ

end RestrictBase

/-! ### Naturality of `Ψ` in the compactification of `X` over `Ȳ` -/

section Naturality

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  [CompactSpace jg.space] {jX jX' : CompactificationOf (Over.mk (f ≫ jg.immersion))}
  (φ : jX ⟶ jX')

omit [CompactSpace jg.space] in
/-- The square `X̄ ×_Ȳ Y ⟶ X̄' ×_Ȳ Y` over `X̄ ⟶ X̄'` is cartesian. -/
theorem isPullback_restrictBaseHom :
    IsPullback (CompactificationOf.restrictBaseι jg jX)
      (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
      (CompactificationOf.Hom.map φ) (CompactificationOf.restrictBaseι jg jX') := by
  refine IsPullback.of_bot ?_ (CompactificationOf.baseChangeHom_map_fst _ φ).symm
    (IsPullback.of_hasPullback jX'.toBase jg.immersion)
  have h₁ : CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ) ≫
      pullback.snd jX'.toBase jg.immersion = pullback.snd jX.toBase jg.immersion :=
    CompactificationOf.map_comp_toBase (CompactificationOf.restrictBaseHom jg φ)
  have h₂ : CompactificationOf.Hom.map φ ≫ jX'.toBase = jX.toBase :=
    CompactificationOf.map_comp_toBase φ
  rw [h₁, h₂]
  exact IsPullback.of_hasPullback jX.toBase jg.immersion

/-- The chase behind `derivedLowerShriekUnboundedRestrictBaseIso_naturality`, over plain
objects. -/
private lemma naturality_chain' {𝒞₁ 𝒞₂ 𝒞₂' 𝒞₃ 𝒟 : Type*} [Category* 𝒞₁] [Category* 𝒞₂]
    [Category* 𝒞₂'] [Category* 𝒞₃] [Category* 𝒟] (R : 𝒞₂ ⥤ 𝒟) (R₀ : 𝒞₂' ⥤ 𝒟)
    (Ei : 𝒞₁ ⥤ 𝒟) (Rf : 𝒞₃ ⥤ 𝒞₁) (Eb : 𝒞₃ ⥤ 𝒞₂) (Rφ : 𝒞₂' ⥤ 𝒞₂)
    {a₀ a₁ : 𝒞₂} {x₀ x₁ x₂ : 𝒞₃} {w₀ w₁ : 𝒞₂'} {z₂ : 𝒞₁}
    (ρ1 : a₀ ⟶ a₁) (ρ2 : a₁ ⟶ Eb.obj x₁) (sA : x₁ ⟶ x₂) (sF : Eb.obj x₂ ⟶ Rφ.obj w₁)
    (cEh : w₁ ⟶ w₀) (cEi : w₀ ⟶ w₁) (l1 : R.obj (Rφ.obj w₀) ⟶ R₀.obj w₀)
    (l0 : R.obj (Rφ.obj w₁) ⟶ R₀.obj w₁) (ψS : R₀.obj w₁ ⟶ Ei.obj z₂)
    (ψR : R.obj (Eb.obj x₂) ⟶ Ei.obj (Rf.obj x₂)) (eL' : Rf.obj x₂ ⟶ z₂)
    (cE'i : a₀ ⟶ Eb.obj x₀) (ψ0 : R.obj (Eb.obj x₀) ⟶ Ei.obj (Rf.obj x₀)) (e1 : x₀ ⟶ x₁)
    (nL : R.map (Rφ.map cEh) ≫ l1 = l0 ≫ R₀.map cEh) (canc : R₀.map cEh ≫ R₀.map cEi = 𝟙 _)
    (hB : R.map sF ≫ l0 ≫ ψS = ψR ≫ Ei.map eL')
    (nΨ : R.map (Eb.map (e1 ≫ sA)) ≫ ψR = ψ0 ≫ Ei.map (Rf.map (e1 ≫ sA)))
    (nc : ρ1 ≫ ρ2 = cE'i ≫ Eb.map e1) :
    (R.map (ρ1 ≫ ρ2 ≫ Eb.map sA ≫ sF ≫ Rφ.map cEh) ≫ l1) ≫ R₀.map cEi ≫ ψS =
      (R.map cE'i ≫ ψ0) ≫ Ei.map (Rf.map (e1 ≫ sA) ≫ eL') := by
  have nΨ' : R.map (Eb.map e1) ≫ R.map (Eb.map sA) ≫ ψR =
      ψ0 ≫ Ei.map (Rf.map e1) ≫ Ei.map (Rf.map sA) := by
    simpa only [Functor.map_comp, Category.assoc] using nΨ
  have nc' : R.map ρ1 ≫ R.map ρ2 = R.map cE'i ≫ R.map (Eb.map e1) := by
    rw [← R.map_comp, nc, R.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nL, reassoc_of% canc, hB, ← reassoc_of% nΨ', ← reassoc_of% nc']

/-- The chase behind `derivedLowerShriekUnboundedCompOverIso_naturality`, over plain
objects. -/
private lemma compOverNat_chain {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (G : 𝒞 ⥤ 𝒟)
    {d₀ d₁ d₂ : 𝒟} {b₀ b₁ b₂ c₁ c₂ : 𝒞}
    (Rρ : d₀ ⟶ d₁) (Lci : d₁ ⟶ d₂) (L0h : d₂ ⟶ G.obj b₂) (Ψ : b₂ ⟶ c₁)
    (L1h : d₀ ⟶ G.obj b₀) (Ψ' : b₀ ⟶ c₂) (eh : c₂ ⟶ c₁) (Rρ' : b₀ ⟶ b₁) (Lφi : b₁ ⟶ b₂)
    (Lφh : b₂ ⟶ b₁) (Lch : d₂ ⟶ d₁) (L1h' : d₁ ⟶ G.obj b₁)
    (hY : (Rρ' ≫ Lφi) ≫ Ψ = Ψ' ≫ eh) (hA : L0h ≫ G.map Lφh = Lch ≫ L1h')
    (nL : Rρ ≫ L1h' = L1h ≫ G.map Rρ') (hci : Lci ≫ Lch = 𝟙 _) (hφ : Lφh ≫ Lφi = 𝟙 _) :
    (Rρ ≫ Lci) ≫ L0h ≫ G.map Ψ = (L1h ≫ G.map Ψ') ≫ G.map eh := by
  have hL0 : L0h = Lch ≫ L1h' ≫ G.map Lφi := by
    rw [← reassoc_of% hA, ← G.map_comp, hφ, G.map_id, Category.comp_id]
  have hY' : G.map Ψ' ≫ G.map eh = G.map Rρ' ≫ G.map Lφi ≫ G.map Ψ := by
    rw [← G.map_comp, ← hY]
    simp only [G.map_comp, Category.assoc]
  rw [hL0]
  simp only [Category.assoc]
  rw [hY', reassoc_of% hci, ← reassoc_of% nL]

omit [CompactSpace jg.space] in
/-- **[Stacks, Tag 0F7D] for the refinement `X ⟶ X̄ ⟶ X̄'`**: the map of [Stacks, Tag 0F7G] for
`X ⟶ X̄ ⟶ X̄'` is that for `X ⟶ X̄ ×_Ȳ Y ⟶ X̄' ×_Ȳ Y` followed by the map of
[Stacks, Tag 0F7B] of the square `X̄ ×_Ȳ Y ⟶ X̄` over `X̄' ×_Ȳ Y ⟶ X̄'`. -/
theorem derivedRefinementComparisonUnboundedUniv_overBarHom_app
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ
        (CompactificationOf.overBarHom jg φ)).app K =
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          ((CompactificationOf.restrictBase jg jX').immersion ≫
            CompactificationOf.restrictBaseι jg jX')).map
          ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv.app K) ≫
        (derivedExtensionByZeroUnboundedCompIso Λ
          (CompactificationOf.restrictBase jg jX').immersion
          (CompactificationOf.restrictBaseι jg jX')).inv.app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (𝟙 X)).obj K) ≫
        (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBaseι jg jX')).map
          ((derivedExtensionByZeroSquareMap Λ (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBase jg jX').immersion (𝟙 X)
            (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
            (refinementSquareIso Λ (CompactificationOf.restrictBaseHom jg φ))).app K) ≫
        (derivedExtensionByZeroSquareMap Λ (CompactificationOf.restrictBaseι jg jX)
          (CompactificationOf.restrictBaseι jg jX')
          (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
          (CompactificationOf.Hom.map φ)
          (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (CompactificationOf.Hom.map φ)
            (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBaseι jg jX)
            (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
            (isPullback_restrictBaseHom jg φ))).app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map φ)).map
          ((derivedExtensionByZeroUnboundedCompIso Λ
            (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBaseι jg jX)).hom.app K) := by
  have hpD : ∀ F, (etaleModuleExtensionByZeroCompIso.{u, 0} Λ
        (CompactificationOf.restrictBase jg jX').immersion
        (CompactificationOf.restrictBaseι jg jX')).inv.app
        ((etaleModuleDirectImage.{u, 0} Λ (𝟙 X)).obj F) ≫
        (refinementSquareIso Λ (CompactificationOf.overBarHom jg φ)).hom.app F =
      (etaleModuleExtensionByZero.{u, 0} Λ (CompactificationOf.restrictBaseι jg jX')).map
          ((refinementSquareIso Λ (CompactificationOf.restrictBaseHom jg φ)).hom.app F) ≫
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (CompactificationOf.Hom.map φ)
            (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBaseι jg jX)
            (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
            (isPullback_restrictBaseHom jg φ)).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map φ)).map
          ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBaseι jg jX)).inv.app F) := by
    intro F
    rw [refinementSquareIso_hom, refinementSquareIso_hom]
    exact IsExtensionByZeroBaseChange.horizontal_paste
      (isExtensionByZeroBaseChange_etaleModuleRefinementSquare Λ
        (CompactificationOf.immersion_comp_map (CompactificationOf.restrictBaseHom jg φ)))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
        (CompactificationOf.Hom.map φ) (CompactificationOf.restrictBaseι jg jX')
        (CompactificationOf.restrictBaseι jg jX)
        (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
        (isPullback_restrictBaseHom jg φ))
      (isExtensionByZeroBaseChange_etaleModuleRefinementSquare Λ
        (CompactificationOf.immersion_comp_map (CompactificationOf.overBarHom jg φ))) F
  have hD := NatTrans.congr_app (derivedExtensionByZeroSquareMap_horizontal_paste Λ
    (CompactificationOf.restrictBase jg jX).immersion (CompactificationOf.restrictBaseι jg jX)
    (CompactificationOf.restrictBase jg jX').immersion (CompactificationOf.restrictBaseι jg jX')
    (𝟙 X) (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
    (CompactificationOf.Hom.map φ) (refinementSquareIso Λ (CompactificationOf.restrictBaseHom jg φ))
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (CompactificationOf.Hom.map φ)
      (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBaseι jg jX)
      (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
      (isPullback_restrictBaseHom jg φ))
    (refinementSquareIso Λ (CompactificationOf.overBarHom jg φ)) hpD) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hD
  refine (NatTrans.congr_app (derivedRefinementComparisonUnboundedUniv_eq_squareMap Λ
    (CompactificationOf.overBarHom jg φ)) K).trans ?_
  refine (Category.id_comp _).trans ?_
  exact congrArg (fun t => _ ≫ t) hD

/-- A rearrangement of a square of isomorphisms, over plain objects. -/
private lemma rearrange_chain {𝒟 : Type*} [Category* 𝒟] {a b c d e : 𝒟}
    (sSi : a ⟶ b) (sSh : b ⟶ a) (Lh : b ⟶ c) (Li : c ⟶ b) (Eh : a ⟶ d) (Ei : d ⟶ a)
    (sS'i : d ⟶ e) (sS'h : e ⟶ d) (RF : e ⟶ c)
    (h : sSi ≫ Lh = Eh ≫ sS'i ≫ RF) (hS : sSi ≫ sSh = 𝟙 _) (hL : Lh ≫ Li = 𝟙 _)
    (hE : Ei ≫ Eh = 𝟙 _) (hS' : sS'h ≫ sS'i = 𝟙 _) :
    RF ≫ Li ≫ sSh = sS'h ≫ Ei := by
  have h' : RF = sS'h ≫ Ei ≫ sSi ≫ Lh := by rw [h, reassoc_of% hE, reassoc_of% hS']
  rw [h']
  simp only [Category.assoc]
  rw [reassoc_of% hL, hS, Category.comp_id]

/-- [Stacks, Tag 0F7C] for `X̄ ×_Ȳ Y ⟶ X̄` over `X̄' ×_Ȳ Y ⟶ X̄'` over `Y ⟶ Ȳ`, read through the
isomorphisms `Ψ`: the map of the square `X̄ ×_Ȳ Y ⟶ X̄` over `X̄' ×_Ȳ Y ⟶ X̄'`, the Leray
isomorphism of `X̄ ⟶ X̄' ⟶ Ȳ` and the open immersion case for `X̄` are the open immersion case for
`X̄'` and the Leray isomorphism of `X̄ ×_Ȳ Y ⟶ X̄' ×_Ȳ Y ⟶ Y`. -/
theorem restrictBase_vertical_paste
    (N : DerivedCategory (EtaleModules.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space)) :
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX'.toBase).map
        ((derivedExtensionByZeroSquareMap Λ (CompactificationOf.restrictBaseι jg jX)
          (CompactificationOf.restrictBaseι jg jX')
          (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
          (CompactificationOf.Hom.map φ)
          (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (CompactificationOf.Hom.map φ)
            (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBaseι jg jX)
            (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
            (isPullback_restrictBaseHom jg φ))).app N) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map φ)
        jX'.toBase jX.toBase (CompactificationOf.map_comp_toBase φ).symm).inv.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBaseι jg jX)).obj N) ≫
      (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ jX.toBase jg.immersion
        (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
        (IsPullback.of_hasPullback jX.toBase jg.immersion)).hom.app N =
    (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ jX'.toBase jg.immersion
        (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBase jg jX').toBase
        (IsPullback.of_hasPullback jX'.toBase jg.immersion)).hom.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
          (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))).obj N) ≫
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jg.immersion).map
        ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
          (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
          (CompactificationOf.restrictBase jg jX').toBase
          (CompactificationOf.restrictBase jg jX).toBase
          (CompactificationOf.map_comp_toBase
            (CompactificationOf.restrictBaseHom jg φ)).symm).inv.app N) := by
  have hpC : ∀ F, (etaleModuleExtensionByZero.{u, 0} Λ jg.immersion).map
        ((etaleModuleDirectImageComp.{u, 0} Λ
          (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
          (CompactificationOf.restrictBase jg jX').toBase
          (CompactificationOf.restrictBase jg jX).toBase
          (CompactificationOf.map_comp_toBase
            (CompactificationOf.restrictBaseHom jg φ)).symm).hom.app F) ≫
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase jg.immersion
          (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
          (IsPullback.of_hasPullback jX.toBase jg.immersion)).hom.app F =
      (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX'.toBase jg.immersion
          (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBase jg jX').toBase
          (IsPullback.of_hasPullback jX'.toBase jg.immersion)).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ
            (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))).obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ jX'.toBase).map
          ((etaleModuleDirectImageExtensionByZeroIso Λ hΛ (CompactificationOf.Hom.map φ)
            (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBaseι jg jX)
            (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
            (isPullback_restrictBaseHom jg φ)).hom.app F) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map φ) jX'.toBase jX.toBase
          (CompactificationOf.map_comp_toBase φ).symm).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ (CompactificationOf.restrictBaseι jg jX)).obj F) :=
    IsExtensionByZeroBaseChange.vertical_paste _ _
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
        (CompactificationOf.Hom.map φ) (CompactificationOf.restrictBaseι jg jX')
        (CompactificationOf.restrictBaseι jg jX)
        (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
        (isPullback_restrictBaseHom jg φ))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX'.toBase
        jg.immersion (CompactificationOf.restrictBaseι jg jX') _
        (IsPullback.of_hasPullback jX'.toBase jg.immersion))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase
        jg.immersion (CompactificationOf.restrictBaseι jg jX) _
        (IsPullback.of_hasPullback jX.toBase jg.immersion))
  have hC := NatTrans.congr_app (derivedExtensionByZeroSquareMap_vertical_paste Λ
    (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBaseι jg jX')
    jg.immersion (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
    (CompactificationOf.Hom.map φ) (CompactificationOf.restrictBase jg jX').toBase jX'.toBase
    (CompactificationOf.restrictBase jg jX).toBase jX.toBase
    (CompactificationOf.map_comp_toBase (CompactificationOf.restrictBaseHom jg φ)).symm
    (CompactificationOf.map_comp_toBase φ).symm _ _ _ hpC) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at hC
  rw [← etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv Λ hΛ jX.toBase jg.immersion
      (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion),
    ← etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv Λ hΛ jX'.toBase jg.immersion
      (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBase jg jX').toBase
      (IsPullback.of_hasPullback jX'.toBase jg.immersion)] at hC
  exact rearrange_chain _ _ _ _ _ _ _ _ _ hC (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jg.immersion).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
        (CompactificationOf.restrictBase jg jX').toBase
        (CompactificationOf.restrictBase jg jX).toBase
        (CompactificationOf.map_comp_toBase (CompactificationOf.restrictBaseHom jg φ)).symm).app
        N)).inv_hom_id
    (Iso.hom_inv_id_app _ _)

/-- **`Ψ : R(f ≫ i)_! ≅ i_! ∘ Rf_!` is natural in the compactification of `X` over `Ȳ`**: along a
morphism `φ : jX ⟶ jX'`, the comparisons of [Stacks, Tag 0F7I] for `f ≫ i` and for `f`
intertwine the two isomorphisms. The map of [Stacks, Tag 0F7G] for `X ⟶ X̄ ⟶ X̄'` is the pasting
of that for `X ⟶ X̄ ×_Ȳ Y ⟶ X̄' ×_Ȳ Y` with the map of [Stacks, Tag 0F7B] of the cartesian
square `X̄ ×_Ȳ Y ⟶ X̄` over `X̄' ×_Ȳ Y ⟶ X̄'` ([Stacks, Tag 0F7D]), and the map of the square
`X̄ ×_Ȳ Y ⟶ X̄` over `Y ⟶ Ȳ` is the pasting of the latter with that of `X̄' ×_Ȳ Y ⟶ X̄'` over
`Y ⟶ Ȳ` ([Stacks, Tag 0F7C]). -/
theorem derivedLowerShriekUnboundedRestrictBaseIso_naturality
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (CompactificationOf.overBarHom jg φ)).app K ≫
        (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jg jX).hom.app K =
      (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jg jX').hom.app K ≫
        (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jg.immersion).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ
            (CompactificationOf.restrictBaseHom jg φ)).app K) := by
  have hρ := derivedRefinementComparisonUnboundedUniv_overBarHom_app Λ hΛ jg φ K
  have hB := restrictBase_vertical_paste Λ hΛ jg φ
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      (CompactificationOf.restrictBase jg jX).immersion).obj K)
  have nL := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
    (CompactificationOf.Hom.map φ) jX'.toBase jX.toBase
    (CompactificationOf.map_comp_toBase φ).symm).inv.naturality
      ((derivedExtensionByZeroUnboundedCompIso Λ
        (CompactificationOf.restrictBase jg jX).immersion
        (CompactificationOf.restrictBaseι jg jX)).hom.app K)
  have canc := ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).mapIso
    ((derivedExtensionByZeroUnboundedCompIso Λ
      (CompactificationOf.restrictBase jg jX).immersion
      (CompactificationOf.restrictBaseι jg jX)).app K)).hom_inv_id
  have nΨ := (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ jX'.toBase jg.immersion
    (CompactificationOf.restrictBaseι jg jX') (CompactificationOf.restrictBase jg jX').toBase
    (IsPullback.of_hasPullback jX'.toBase jg.immersion)).hom.naturality
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX').immersion).map
          ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv.app K) ≫
        (derivedExtensionByZeroSquareMap Λ (CompactificationOf.restrictBase jg jX).immersion
          (CompactificationOf.restrictBase jg jX').immersion (𝟙 X)
          (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
          (refinementSquareIso Λ (CompactificationOf.restrictBaseHom jg φ))).app K)
  have nc := (derivedExtensionByZeroUnboundedCompIso Λ
      (CompactificationOf.restrictBase jg jX').immersion
      (CompactificationOf.restrictBaseι jg jX')).inv.naturality
        ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv.app K)
  have hob : (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ
      (CompactificationOf.overBarHom jg φ)).app K =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX'.toBase).map
          ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ
            (CompactificationOf.overBarHom jg φ)).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map φ)
          jX'.toBase jX.toBase (CompactificationOf.map_comp_toBase φ).symm).inv.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
              CompactificationOf.restrictBaseι jg jX)).obj K) :=
    derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ _ K
  have hρrb : (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ
      (CompactificationOf.restrictBaseHom jg φ)).app K =
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX').immersion).map
          ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv.app K) ≫
        (derivedExtensionByZeroSquareMap Λ (CompactificationOf.restrictBase jg jX).immersion
          (CompactificationOf.restrictBase jg jX').immersion (𝟙 X)
          (CompactificationOf.Hom.map (CompactificationOf.restrictBaseHom jg φ))
          (refinementSquareIso Λ (CompactificationOf.restrictBaseHom jg φ))).app K :=
    (NatTrans.congr_app (derivedRefinementComparisonUnboundedUniv_eq_squareMap Λ
      (CompactificationOf.restrictBaseHom jg φ)) K).trans (Category.id_comp _)
  rw [hob, derivedLowerShriekUnboundedHomUniv_app_eq_leray, hρrb, hρ,
    derivedLowerShriekUnboundedRestrictBaseIso_hom_app,
    derivedLowerShriekUnboundedRestrictBaseIso_hom_app]
  exact naturality_chain' (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX'.toBase)
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase)
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jg.immersion)
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ
      (CompactificationOf.restrictBase jg jX').toBase)
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      (CompactificationOf.restrictBaseι jg jX'))
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map φ))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ nL canc hB nΨ nc

/-- **The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of the compactifications of the proof of
[Stacks, Tag 0F7J] is natural in the compactification of `X` over `Ȳ`**, on `D(X_étale, Λ)`. -/
theorem derivedLowerShriekUnboundedCompOverIso_naturality
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (CompactificationOf.compOverHom jg φ)).app K ≫
        (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K =
      (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX').hom.app K ≫
        (derivedLowerShriekUnbounded.{u, 0} g jg Λ).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ
            (CompactificationOf.restrictBaseHom jg φ)).app K) := by
  have hc : (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ
      (CompactificationOf.compOverHom jg φ)).app K =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jX'.toBase ≫ jg.toBase)).map
          ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ
            (CompactificationOf.overBarHom jg φ)).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map φ)
          (jX'.toBase ≫ jg.toBase) (jX.toBase ≫ jg.toBase)
          (by rw [← Category.assoc, CompactificationOf.map_comp_toBase])).inv.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
              CompactificationOf.restrictBaseι jg jX)).obj K) :=
    derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ _ K
  have hob : (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ
      (CompactificationOf.overBarHom jg φ)).app K =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX'.toBase).map
          ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ
            (CompactificationOf.overBarHom jg φ)).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map φ)
          jX'.toBase jX.toBase (CompactificationOf.map_comp_toBase φ).symm).inv.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
              CompactificationOf.restrictBaseι jg jX)).obj K) :=
    derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ _ K
  have hY := derivedLowerShriekUnboundedRestrictBaseIso_naturality Λ hΛ jg φ K
  rw [hob] at hY
  have hA := etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ
    (CompactificationOf.Hom.map φ) jX'.toBase jg.toBase jX.toBase
    (CompactificationOf.map_comp_toBase φ).symm (jX'.toBase ≫ jg.toBase) rfl
    (jX.toBase ≫ jg.toBase) rfl (by rw [← Category.assoc, CompactificationOf.map_comp_toBase])
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      ((CompactificationOf.restrictBase jg jX).immersion ≫
        CompactificationOf.restrictBaseι jg jX)).obj K)
  have nL := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX'.toBase jg.toBase
    (jX'.toBase ≫ jg.toBase) rfl).hom.naturality
      ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ
        (CompactificationOf.overBarHom jg φ)).app K)
  rw [hc, derivedLowerShriekUnboundedCompOverIso_hom_app,
    derivedLowerShriekUnboundedCompOverIso_hom_app]
  exact compOverNat_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase) _ _ _ _ _ _
    _ _ _ _ _ _ hY hA nL (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)

end Naturality

/-! ### Independence of the auxiliary compactification -/

section CompactificationIso

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]

/-- The comparison of [Stacks, Tag 0F7I] from a compactification to itself is the identity. -/
lemma derivedLowerShriekUnboundedCompactificationIsoUniv_self
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnboundedCompactificationIsoUniv f j j Λ hΛ = Iso.refl _ := by
  have h := derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ j j j
  ext K
  have h' := congrArg (fun e => e.hom.app K) h
  simp only [Iso.trans_hom, NatTrans.comp_app] at h'
  simpa using (cancel_epi _).1 (h'.trans (Category.comp_id _).symm)

/-- The comparisons of [Stacks, Tag 0F7I] are inverse to each other. -/
lemma derivedLowerShriekUnboundedCompactificationIsoUniv_symm
    (j k : CompactificationOf (Over.mk f)) :
    (derivedLowerShriekUnboundedCompactificationIsoUniv f j k Λ hΛ).symm =
      derivedLowerShriekUnboundedCompactificationIsoUniv f k j Λ hΛ := by
  have h := derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ j k j
  rw [derivedLowerShriekUnboundedCompactificationIsoUniv_self] at h
  apply Iso.ext
  rw [Iso.symm_hom]
  refine Iso.inv_ext ?_
  have h' := congrArg Iso.hom h
  simpa using h'

/-- A comparison of [Stacks, Tag 0F7I], the second along a morphism of compactifications. -/
lemma derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_of_hom_comp
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) {j k l : CompactificationOf (Over.mk f)}
    (ψ : l ⟶ k) :
    (derivedLowerShriekUnboundedCompactificationIsoUniv f j l Λ hΛ).hom.app K =
      (derivedLowerShriekUnboundedCompactificationIsoUniv f j k Λ hΛ).hom.app K ≫
        (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ).app K := by
  rw [← derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ j k l,
    derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom f Λ hΛ ψ]
  rfl

/-- A comparison of [Stacks, Tag 0F7I] into the target of a morphism of compactifications. -/
lemma derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_of_hom_target
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) {j k l : CompactificationOf (Over.mk f)}
    (ψ : k ⟶ l) :
    (derivedLowerShriekUnboundedCompactificationIsoUniv f j l Λ hΛ).hom.app K =
      (derivedLowerShriekUnboundedCompactificationIsoUniv f j k Λ hΛ).hom.app K ≫
        (derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ ψ hΛ).inv.app K := by
  rw [← derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ j k l,
    ← derivedLowerShriekUnboundedCompactificationIsoUniv_symm Λ hΛ f l k,
    derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom f Λ hΛ ψ]
  rfl

/-- Two comparisons of [Stacks, Tag 0F7I] composing to that along a morphism of
compactifications. -/
lemma derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_comp_of_hom
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) {j k l : CompactificationOf (Over.mk f)}
    (ψ : l ⟶ j) :
    (derivedLowerShriekUnboundedCompactificationIsoUniv f j k Λ hΛ).hom.app K ≫
        (derivedLowerShriekUnboundedCompactificationIsoUniv f k l Λ hΛ).hom.app K =
      (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ).app K := by
  have e := derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ j k l
  rw [derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom f Λ hΛ ψ] at e
  exact NatTrans.congr_app (congrArg Iso.hom e) K

/-- A comparison of [Stacks, Tag 0F7I] out of the target of a morphism of compactifications. -/
lemma derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_of_hom_source
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) {j k l : CompactificationOf (Over.mk f)}
    (ψ : k ⟶ j) :
    (derivedLowerShriekUnboundedCompactificationIsoUniv f j l Λ hΛ).hom.app K =
      (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ).app K ≫
        (derivedLowerShriekUnboundedCompactificationIsoUniv f k l Λ hΛ).hom.app K := by
  rw [← derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ j k l,
    derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom f Λ hΛ ψ]
  rfl

/-- The comparison of [Stacks, Tag 0F7I] through a compactification dominating both. -/
lemma derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_span
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) {j k m : CompactificationOf (Over.mk f)}
    (ψ₁ : m ⟶ j) (ψ₂ : m ⟶ k) :
    (derivedLowerShriekUnboundedCompactificationIsoUniv f j k Λ hΛ).hom.app K =
      (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ₁).app K ≫
        (derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ ψ₂ hΛ).inv.app K := by
  rw [← derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ j m k,
    derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom f Λ hΛ ψ₁,
    ← derivedLowerShriekUnboundedCompactificationIsoUniv_symm Λ hΛ f k m,
    derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom f Λ hΛ ψ₂]
  rfl

end CompactificationIso

section Independence

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (jf : CompactificationOf (Over.mk f)) (jg : CompactificationOf (Over.mk g))
  (j : CompactificationOf (Over.mk (f ≫ g)))

/-- The space of a compactification over a quasi-compact scheme is quasi-compact. -/
lemma compactSpace_compactificationOf_space {S : Scheme.{u}} [CompactSpace S] {X₀ : Over S}
    (c : CompactificationOf X₀) : CompactSpace c.space := by
  have : UniversallyClosed c.toBase := IsProper.toUniversallyClosed
  have : QuasiCompact c.toBase := instQuasiCompactOfUniversallyClosed c.toBase
  exact QuasiCompact.compactSpace_of_compactSpace c.toBase

/-- The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` on `D(X_étale, Λ)` computed through a
compactification `jX` of `X` over `Ȳ`: the isomorphism of
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso`, transported to the
compactifications `j` and `jf` by the comparisons of [Stacks, Tag 0F7I]. -/
def derivedLowerShriekUnboundedCompIsoThrough
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    derivedLowerShriekUnbounded.{u, 0} (f ≫ g) j Λ ≅
      derivedLowerShriekUnbounded.{u, 0} f jf Λ ⋙ derivedLowerShriekUnbounded.{u, 0} g jg Λ :=
  haveI : QuasiCompact f := quasiCompact_of_compactSpace f
  haveI : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  haveI : CompactSpace jg.space := compactSpace_compactificationOf_space jg
  derivedLowerShriekUnboundedCompactificationIsoUniv (f ≫ g) j
      (CompactificationOf.compOver jg jX) Λ hΛ ≪≫
    derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX ≪≫
    Functor.isoWhiskerRight
      (derivedLowerShriekUnboundedCompactificationIsoUniv f
        (CompactificationOf.restrictBase jg jX) jf Λ hΛ)
      (derivedLowerShriekUnbounded.{u, 0} g jg Λ)

omit [QuasiSeparatedSpace X] in
/-- Along a morphism of auxiliary compactifications the two isomorphisms agree. -/
theorem derivedLowerShriekUnboundedCompIsoThrough_eq_of_hom
    {jX jX' : CompactificationOf (Over.mk (f ≫ jg.immersion))} (φ : jX ⟶ jX') :
    derivedLowerShriekUnboundedCompIsoThrough Λ hΛ f g jf jg j jX =
      derivedLowerShriekUnboundedCompIsoThrough Λ hΛ f g jf jg j jX' := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  have : CompactSpace jg.space := compactSpace_compactificationOf_space jg
  have hC : derivedLowerShriekUnboundedCompactificationIsoUniv (f ≫ g) j
      (CompactificationOf.compOver jg jX) Λ hΛ =
      derivedLowerShriekUnboundedCompactificationIsoUniv (f ≫ g) j
          (CompactificationOf.compOver jg jX') Λ hΛ ≪≫
        derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ (CompactificationOf.compOverHom jg φ)
          hΛ := by
    rw [← derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom,
      derivedLowerShriekUnboundedCompactificationIsoUniv_trans]
  have hR : derivedLowerShriekUnboundedCompactificationIsoUniv f
      (CompactificationOf.restrictBase jg jX) jf Λ hΛ =
      (derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ
          (CompactificationOf.restrictBaseHom jg φ) hΛ).symm ≪≫
        derivedLowerShriekUnboundedCompactificationIsoUniv f
          (CompactificationOf.restrictBase jg jX') jf Λ hΛ := by
    rw [← derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom,
      derivedLowerShriekUnboundedCompactificationIsoUniv_symm,
      derivedLowerShriekUnboundedCompactificationIsoUniv_trans]
  dsimp only [derivedLowerShriekUnboundedCompIsoThrough]
  rw [hC, hR]
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  have h := derivedLowerShriekUnboundedCompOverIso_naturality Λ hΛ jg φ K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, derivedLowerShriekUnboundedHomIsoUniv_hom,
    Category.assoc, Functor.map_comp]
  have hinv : (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ
      (CompactificationOf.restrictBaseHom jg φ)).app K ≫
      (derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ
        (CompactificationOf.restrictBaseHom jg φ) hΛ).inv.app K = 𝟙 _ :=
    (derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ
      (CompactificationOf.restrictBaseHom jg φ) hΛ).hom_inv_id_app K
  have e1 : (derivedLowerShriekUnbounded.{u, 0} g jg Λ).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ
          (CompactificationOf.restrictBaseHom jg φ)).app K) ≫
      (derivedLowerShriekUnbounded.{u, 0} g jg Λ).map
        ((derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ
          (CompactificationOf.restrictBaseHom jg φ) hΛ).inv.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, hinv, CategoryTheory.Functor.map_id]
  rw [reassoc_of% h]
  congr 2
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker e1 _).trans (Category.id_comp _))

/-- **The isomorphism of [Stacks, Tag 0F7J] on `D(X_étale, Λ)` through an arbitrary auxiliary
compactification**: `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso` is computed
through any compactification `jX` of `X` over the compactification `Ȳ` of `Y`, not only the one
chosen by Nagata's theorem. -/
theorem derivedLowerShriekUnboundedCompIso_eq_through
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg j =
      derivedLowerShriekUnboundedCompIsoThrough Λ hΛ f g jf jg j jX := by
  have : UniversallyClosed jg.toBase := IsProper.toUniversallyClosed
  have : QuasiCompact jg.toBase := instQuasiCompactOfUniversallyClosed jg.toBase
  have : IsSeparated jg.toBase := IsProper.toIsSeparated
  have : QuasiSeparated jg.toBase := IsSeparated.instQuasiSeparated jg.toBase
  have : CompactSpace jg.space := QuasiCompact.compactSpace_of_compactSpace jg.toBase
  have : QuasiSeparatedSpace jg.space := quasiSeparatedSpace_of_quasiSeparated jg.toBase
  have : QuasiCompact (f ≫ jg.immersion) := quasiCompact_of_compactSpace _
  let jX₀ := (nonempty_compactificationOf_comp_immersion f g jg).some
  change derivedLowerShriekUnboundedCompIsoThrough Λ hΛ f g jf jg j jX₀ = _
  exact (derivedLowerShriekUnboundedCompIsoThrough_eq_of_hom Λ hΛ f g jf jg j
    (IsCofiltered.minToLeft jX₀ jX)).symm.trans
      (derivedLowerShriekUnboundedCompIsoThrough_eq_of_hom Λ hΛ f g jf jg j
        (IsCofiltered.minToRight jX₀ jX))

/-- The components of the isomorphism of [Stacks, Tag 0F7J] on `D(X_étale, Λ)` through an
auxiliary compactification. -/
lemma derivedLowerShriekUnboundedCompIso_hom_app_eq
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    haveI : QuasiCompact f := quasiCompact_of_compactSpace f
    haveI : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
    haveI : CompactSpace jg.space := compactSpace_compactificationOf_space jg
    (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg j).hom.app K =
      (derivedLowerShriekUnboundedCompactificationIsoUniv (f ≫ g) j
          (CompactificationOf.compOver jg jX) Λ hΛ).hom.app K ≫
        (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K ≫
        (derivedLowerShriekUnbounded.{u, 0} g jg Λ).map
          ((derivedLowerShriekUnboundedCompactificationIsoUniv f
            (CompactificationOf.restrictBase jg jX) jf Λ hΛ).hom.app K) := by
  rw [derivedLowerShriekUnboundedCompIso_eq_through Λ hΛ f g jf jg j jX]
  rfl

/-- **The isomorphism of [Stacks, Tag 0F7J] along the comparisons of [Stacks, Tag 0F7I] for
`g ∘ f`**, on `D(X_étale, Λ)`. -/
theorem derivedLowerShriekUnboundedCompIso_hom_app_third (j' : CompactificationOf (Over.mk (f ≫ g)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    haveI : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
    (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg j').hom.app K =
      (derivedLowerShriekUnboundedCompactificationIsoUniv (f ≫ g) j' j Λ hΛ).hom.app K ≫
        (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg j).hom.app K := by
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion f g jg
  rw [derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g jf jg j' jX K,
    derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g jf jg j jX K,
    ← derivedLowerShriekUnboundedCompactificationIsoUniv_trans (f ≫ g) Λ hΛ j' j, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]

/-- **The isomorphism of [Stacks, Tag 0F7J] along the comparisons of [Stacks, Tag 0F7I] for
`f`**, on `D(X_étale, Λ)`. -/
theorem derivedLowerShriekUnboundedCompIso_hom_app_first (jf' : CompactificationOf (Over.mk f))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    haveI : QuasiCompact f := quasiCompact_of_compactSpace f
    (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf' jg j).hom.app K =
      (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg j).hom.app K ≫
        (derivedLowerShriekUnbounded.{u, 0} g jg Λ).map
          ((derivedLowerShriekUnboundedCompactificationIsoUniv f jf jf' Λ hΛ).hom.app K) := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion f g jg
  rw [derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g jf' jg j jX K,
    derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g jf jg j jX K,
    ← derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ _ jf jf']
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]

end Independence

end Stacks.EtaleCohomology

end
