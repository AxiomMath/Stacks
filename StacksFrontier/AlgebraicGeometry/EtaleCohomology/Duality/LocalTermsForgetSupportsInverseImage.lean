module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsForgetSupportsLAdic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CupPairingBounds

/-!
# Forgetting supports as the inverse image to the open part

Let `j' : U ⟶ Y` be an open immersion. The forget supports map
`Ext^n(A, j'_! F) → Ext^n(j'^{-1} A, F)`, `w ↦ extMap (w ∘ (j'_! F ↪ j'_* F))`, of
`Stacks.EtaleCohomology.forgetSupports_bounds_extensionByZero` is the restriction of `w` to `U`
followed by the inverse of the unit `F ≅ j'^{-1} j'_! F`
(`Stacks.EtaleCohomology.extMap_comp_etaleModuleExtensionByZeroToDirectImage`).

For an ℓ-adic sheaf `F` on `U` with a compactification `j : U ⟶ X̄` over `k`, `Y = X̄_k̄`,
`pr : Y ⟶ X̄`, `j' : U_k̄ ⟶ Y` and `M = pr^{-1}(j_! Fₙ)`, the base change
`pr^{-1} j_! ≅ j'_! pr_U^{-1}` identifies `M` with `j'_! (Fₙ|_{U_k̄})`, so the bounds of
`Stacks.EtaleCohomology.LAdicSheaf.forgetSupports_bounds_of_localTermsKilledBy` become bounds for
the inverse image `a ↦ j'^{-1} a` of classes `a ∈ H¹(Y, M)` out of the unit, which is how the
cup product sees forgetting supports (`Stacks.EtaleCohomology.mapUnit_bounds_of_forgetSupports`,
applied in `Stacks.EtaleCohomology.LAdicSheaf.levelCup_bounds_of_curve`). This is the
forgetting of supports in Poincaré duality on an affine curve over `k̄`, in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.extMap_comp_etaleModuleExtensionByZeroToDirectImage`.
* `Stacks.EtaleCohomology.mapUnit_bounds_of_forgetSupports`.
* `Stacks.EtaleCohomology.injective_mapExactFunctor_inverseImage_of_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- The class of morphisms of presheaves of `Λ`-modules on the small étale site of `S` that
become isomorphisms after sheafification is compatible with the monoidal structure. -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

section Restriction

variable (Λ : Type) [Ring Λ] {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- `j^{-1}` of the inclusion `j_! F ↪ j_* F`, followed by the counit `j^{-1} j_* F ⟶ F`, is the
inverse of the unit `F ≅ j^{-1} j_! F`. -/
theorem restriction_map_extensionByZeroToDirectImage_comp_counit
    (F : EtaleModules.{u, 0} Λ U) :
    (etaleModuleRestriction.{u, 0} Λ j).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app F) ≫
      (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).counit.app F =
      inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app F) := by
  rw [etaleModuleExtensionByZeroToDirectImage_app, Functor.map_comp, Category.assoc]
  have h := (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).counit.naturality
    (inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app F))
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h
  refine (congrArg (fun g => (etaleModuleRestriction.{u, 0} Λ j).map
    ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app
      ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F)) ≫ g) h).trans ?_
  rw [← Category.assoc]
  exact (congrArg (· ≫ inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app F))
    ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).left_triangle_components
      ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F))).trans (Category.id_comp _)

/-- **Forgetting supports is restriction to the open part.** For an open immersion `j`, the
class `extMap (w ∘ (j_! F ↪ j_* F)) ∈ Ext^n(j^{-1} A, F)` is `j^{-1} w` followed by the inverse
of the unit `F ≅ j^{-1} j_! F`. -/
theorem extMap_comp_etaleModuleExtensionByZeroToDirectImage
    [HasExt.{u + 1} (EtaleModules.{u, 0} Λ Y)] [HasExt.{u + 1} (EtaleModules.{u, 0} Λ U)]
    (A : EtaleModules.{u, 0} Λ Y) (F : EtaleModules.{u, 0} Λ U) (n : ℕ)
    (w : Ext.{u + 1} A ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F) n) :
    Stacks.ExtAdjunction.extMap (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j) A F n
        (w.comp (Ext.mk₀ ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app F))
          (add_zero n)) =
      (w.mapExactFunctor (etaleModuleRestriction.{u, 0} Λ j)).comp
        (Ext.mk₀ (inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app F))) (add_zero n) := by
  rw [Stacks.ExtAdjunction.extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    restriction_map_extensionByZeroToDirectImage_comp_counit]

/-- **The inverse image to the open part is injective on `Ext` out of an extension by zero**:
for an open immersion `j`, `G ≅ j_! A` and any `T`, `y ↦ j^{-1} y` on `Ext^i(G, T)` is
injective. -/
theorem injective_mapExactFunctor_inverseImage_of_iso
    [HasExt.{u + 1} (EtaleModules.{u, 0} Λ Y)] [HasExt.{u + 1} (EtaleModules.{u, 0} Λ U)]
    {G T : EtaleModules.{u, 0} Λ Y} (A : EtaleModules.{u, 0} Λ U)
    (e : G ≅ (etaleModuleExtensionByZero.{u, 0} Λ j).obj A) (i : ℕ) :
    Function.Injective (fun y : Ext.{u + 1} G T i =>
      y.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ j)) := by
  intro y₁ y₂ h
  let R := etaleModuleRestriction.{u, 0} Λ j
  let ι := etaleModuleInverseImageRestrictionIso.{u, 0} Λ j
  have hR : ∀ y : Ext.{u + 1} G T i, y.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ j) =
      (Ext.mk₀ (ι.hom.app G)).comp ((y.mapExactFunctor R).comp (Ext.mk₀ (ι.inv.app T))
        (add_zero i)) (zero_add i) := fun y => by
    rw [← Ext.comp_assoc_of_third_deg_zero,
      Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor ι.hom G i y,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app, Ext.comp_mk₀_id]
  have h' : y₁.mapExactFunctor R = y₂.mapExactFunctor R := by
    have h₀ : y₁.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ j) =
        y₂.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ j) := h
    rw [hR, hR] at h₀
    exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (ι.inv.app T) i).1
      ((Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (ι.hom.app G) i).1 h₀)
  have h'' : ((Ext.mk₀ e.inv).comp y₁ (zero_add i)).mapExactFunctor R =
      ((Ext.mk₀ e.inv).comp y₂ (zero_add i)).mapExactFunctor R := by
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, h']
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso e.inv i).1
    ((Stacks.ExtAdjunction.bijective_mapExactFunctor_of_isIso_unit
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) A T i).1 h'')

end Restriction

section MapUnit

variable (N : ℕ) {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- **Bounds for forgetting supports, read on the inverse image out of the unit.** Let `j` be an
open immersion, `G` a sheaf on `U` and `M ≅ j_! G`. If the forget supports map
`w ↦ extMap (w ∘ (j_! G ↪ j_* G))` on `Ext^n(ℤ/N, j_! G)` has kernel killed by `c₁` and image
containing `c₂ Ext^n(j^{-1} ℤ/N, G)`, then `a ↦ j^{-1} a` (read out of the unit,
`Stacks.ExtCup.mapUnit`) on `Ext^n(𝟙, M)` has kernel killed by `c₁` and image containing
`c₂ Ext^n(𝟙, j^{-1} M)`. -/
theorem mapUnit_bounds_of_forgetSupports
    [HasExt.{u + 1} (EtaleModules.{u, 0} (ZMod N) Y)]
    [HasExt.{u + 1} (EtaleModules.{u, 0} (ZMod N) U)]
    (G : EtaleModules.{u, 0} (ZMod N) U) (M : EtaleModules.{u, 0} (ZMod N) Y)
    (e : M ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj G) (c₁ c₂ n : ℕ)
    (h₁ : ∀ w : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj G) n,
      Stacks.ExtAdjunction.extMap (etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j) _ _ n
        (w.comp (Ext.mk₀ ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod N) j).app G))
          (add_zero n)) = 0 → c₁ • w = 0)
    (h₂ : ∀ x : Ext.{u + 1}
        ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y))) G n,
      ∃ w : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj G) n,
        Stacks.ExtAdjunction.extMap (etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j) _ _ n
          (w.comp (Ext.mk₀ ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod N) j).app G))
            (add_zero n)) = c₂ • x) :
    (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) M n,
      Stacks.ExtCup.mapUnit (etaleModuleInverseImage.{u, 0} (ZMod N) j) a = 0 → c₁ • a = 0) ∧
    ∀ z : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) U))
        ((etaleModuleInverseImage.{u, 0} (ZMod N) j).obj M) n,
      ∃ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) M n,
        Stacks.ExtCup.mapUnit (etaleModuleInverseImage.{u, 0} (ZMod N) j) a = c₂ • z := by
  let R := etaleModuleRestriction.{u, 0} (ZMod N) j
  let Φ := etaleModuleInverseImage.{u, 0} (ZMod N) j
  let ι := etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j
  let η := (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).unit.app G
  let d : 𝟙_ (EtaleModules.{u, 0} (ZMod N) U) ⟶ R.obj (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) :=
    Functor.LaxMonoidal.ε Φ ≫ ι.hom.app _
  let c : G ⟶ Φ.obj M := η ≫ R.map e.inv ≫ ι.inv.app M
  have : IsIso d := by
    dsimp only [d]
    infer_instance
  have : IsIso c := by
    dsimp only [c, η]
    infer_instance
  let β : Ext.{u + 1} (R.obj (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y))) G n →+
      Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) U)) (Φ.obj M) n :=
    ((Ext.mk₀ d).precomp _ (zero_add n)).comp ((Ext.mk₀ c).postcomp _ (add_zero n))
  have hβ : Function.Bijective β :=
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso d n).comp
      (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso c n)
  let fg := fun w : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y))
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj G) n =>
    Stacks.ExtAdjunction.extMap (etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j) _ _ n
      (w.comp (Ext.mk₀ ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod N) j).app G))
        (add_zero n))
  have key : ∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) M n,
      Stacks.ExtCup.mapUnit Φ a = β (fg (a.comp (Ext.mk₀ e.hom) (add_zero n))) := by
    intro a
    have hι := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor ι.hom
      (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) n a
    have hc : R.map e.hom ≫ inv η ≫ c = ι.inv.app M := by
      simp only [c, IsIso.inv_hom_id_assoc, ← R.map_comp_assoc, Iso.hom_inv_id, R.map_id,
        Category.id_comp]
    change (Ext.mk₀ (Functor.LaxMonoidal.ε Φ)).comp (a.mapExactFunctor Φ) (zero_add n) =
      (Ext.mk₀ d).comp ((fg (a.comp (Ext.mk₀ e.hom) (add_zero n))).comp (Ext.mk₀ c) (add_zero n))
        (zero_add n)
    rw [show fg (a.comp (Ext.mk₀ e.hom) (add_zero n)) =
        ((a.comp (Ext.mk₀ e.hom) (add_zero n)).mapExactFunctor R).comp (Ext.mk₀ (inv η))
          (add_zero n) from extMap_comp_etaleModuleExtensionByZeroToDirectImage _ j _ G n _,
      Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, hc,
      show d = Functor.LaxMonoidal.ε Φ ≫ ι.hom.app _ from rfl, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc_of_second_deg_zero, ← Ext.comp_assoc_of_third_deg_zero, hι,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app, Ext.comp_mk₀_id]
  have hinv : ∀ {X X' : EtaleModules.{u, 0} (ZMod N) Y} (e : X ≅ X')
      (w : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) X n),
      (w.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) = w :=
    fun e w => by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.comp_mk₀_id]
  refine ⟨fun a ha => ?_, fun z => ?_⟩
  · have hw : fg (a.comp (Ext.mk₀ e.hom) (add_zero n)) = 0 :=
      hβ.1 (by rw [← key, ha, map_zero])
    rw [← hinv e a, ← Stacks.ExtAdjunction.postcomp_apply, ← map_nsmul,
      Stacks.ExtAdjunction.postcomp_apply, h₁ _ hw, Ext.zero_comp]
  · obtain ⟨x, rfl⟩ := hβ.2 z
    obtain ⟨w, hw⟩ := h₂ x
    refine ⟨w.comp (Ext.mk₀ e.inv) (add_zero n), ?_⟩
    rw [key, ← map_nsmul]
    exact (congrArg (fun v => β (fg v)) (hinv e.symm w)).trans (congrArg β hw)

end MapUnit

end Stacks.EtaleCohomology

end
