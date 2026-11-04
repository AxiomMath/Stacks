module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveExtensionByZeroSheafTrace

/-!
# Naturality of the trace of `H²(C, j_! G)` and of `H²(C, H)`

Let `C` be a smooth proper curve over an algebraically closed field `K`, `j : U ⟶ C` an open
immersion with finite complement, `Λ` a finite ring with `#Λ` invertible in `K` and `ζ ∈ K` a
primitive `#Λ`-th root of unity.

* The trace `τ_G : H²(C, j_! G) ≅ Γ(U, G)` of a sheaf `G` constant on its global sections
  (`Stacks.EtaleCohomology.curveExtensionByZeroSheafTrace`) is natural in `G`.
* The trace `H²(C, H) ≅ Γ(U, G)` through an identification `l : j^{-1} H ≅ G`
  (`Stacks.EtaleCohomology.curveExtensionByZeroRestrictionTrace`) is natural in `(H, G, l)`:
  for `α : H ⟶ H'` and `β : G ⟶ G'` with `j^{-1}(α) ≫ l' = l ≫ β`, it carries `H²(α)` to `Γ(β)`.

## Main results

* `Stacks.EtaleCohomology.curveExtensionByZeroSheafTrace_naturality`.
* `Stacks.EtaleCohomology.curveExtensionByZeroRestrictionTrace_naturality`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high] Stacks.EtaleCohomology.etaleModules_hasSheafify

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModulesEnoughInjectivesZeroTraceTwist
  moduleCatHasColimitsOfSizeSmallEtale hasGlobalSectionsFunctorSmallEtaleModuleCat

section Trace

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  {U : Scheme.{u}} (jC : U ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

/-- If `g ≫ b = a ≫ f` with `a` and `b` invertible, then `f ≫ inv b = inv a ≫ g`. -/
private theorem comp_inv_eq_inv_comp_of_comp_eq {D : Type*} [Category D] {X Y X' Y' : D}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y) [IsIso a] [IsIso b]
    (h : g ≫ b = a ≫ f) : f ≫ inv b = inv a ≫ g := by
  rw [IsIso.comp_inv_eq, Category.assoc, h, IsIso.inv_hom_id_assoc]

/-- **`τ_G : H²(C, j_! G) ≅ Γ(U, G)` is natural in `G`.** -/
theorem curveExtensionByZeroSheafTrace_naturality {G G' : EtaleModules.{u, 0} Λ U} (β : G ⟶ G')
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hG' : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G'))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))
    (hE' : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G'))
    (w : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj G)) :
    curveExtensionByZeroSheafTrace q Λ hn hζ jC hfin G' hG' hE'
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map β)).hom w) =
      ((etaleModuleGlobalSections.{u, 0} Λ U).map β).hom
        (curveExtensionByZeroSheafTrace q Λ hn hζ jC hfin G hG hE w) := by
  have := hG
  have := hG'
  have := hE
  have := hE'
  have hε : (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        ((etaleModuleGlobalSections.{u, 0} Λ U).map β) ≫
        (constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G' =
      (constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G ≫ β :=
    (constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.naturality β
  have hinv := comp_inv_eq_inv_comp_of_comp_eq β _ _ _ hε
  have hR := congrArg (fun φ => (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus
      ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZero.{u, 0} Λ jC).map φ)).hom w) hinv
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hR
  rw [curveExtensionByZeroSheafTrace_apply, curveExtensionByZeroSheafTrace_apply, hR]
  have h := curveExtensionByZeroConstantTrace_naturality q Λ hn hζ jC hfin
    ((etaleModuleGlobalSections.{u, 0} Λ U).map β)
    ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)))).hom w)
  convert h using 3

/-- **The trace `H²(C, H) ≅ Γ(U, G)` through `l : j^{-1} H ≅ G` is natural in `(H, G, l)`.** For
`α : H ⟶ H'` and `β : G ⟶ G'` with `j^{-1}(α) ≫ l' = l ≫ β`, it carries `H²(α)` to `Γ(β)`. -/
theorem curveExtensionByZeroRestrictionTrace_naturality {H H' : EtaleModules.{u, 0} Λ C}
    {G G' : EtaleModules.{u, 0} Λ U} (l : (etaleModuleRestriction.{u, 0} Λ jC).obj H ≅ G)
    (l' : (etaleModuleRestriction.{u, 0} Λ jC).obj H' ≅ G')
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hG' : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G'))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))
    (hE' : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G')) (α : H ⟶ H') (β : G ⟶ G')
    (hαβ : (etaleModuleRestriction.{u, 0} Λ jC).map α ≫ l'.hom = l.hom ≫ β)
    (z : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj H) :
    curveExtensionByZeroRestrictionTrace q Λ hn hζ jC hfin H' G' l' hG' hE'
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map α).hom z) =
      ((etaleModuleGlobalSections.{u, 0} Λ U).map β).hom
        (curveExtensionByZeroRestrictionTrace q Λ hn hζ jC hfin H G l hG hE z) := by
  have := isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H
  have := isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H'
  have hc := (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.naturality α
  have hRc := comp_inv_eq_inv_comp_of_comp_eq
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map α)
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((etaleModuleRestriction.{u, 0} Λ jC).map α)))
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H'))
    (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ hc)
  have hl : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
          ((etaleModuleRestriction.{u, 0} Λ jC).map α)) ≫
        ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map l'.hom) =
      ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map l.hom) ≫
        ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map β) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hαβ, Functor.map_comp, Functor.map_comp]
  have h₁ := congrArg (fun φ => φ.hom z) hRc
  have h₂ := congrArg (fun φ => φ.hom
    ((inv (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus
      ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))).hom z)) hl
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
  rw [curveExtensionByZeroRestrictionTrace_apply, curveExtensionByZeroRestrictionTrace_apply, h₁,
    h₂]
  exact curveExtensionByZeroSheafTrace_naturality q Λ hn hζ jC hfin β hG hG' hE hE' _

end Trace

end Stacks.EtaleCohomology

end
