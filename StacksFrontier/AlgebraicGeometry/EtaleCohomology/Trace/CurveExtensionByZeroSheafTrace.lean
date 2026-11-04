module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantModuleTraceGaloisTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCounitTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceRootChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralTwistRestriction

/-!
# The trace of `H²(C, j_! G)` for a sheaf `G` which is constant on its global sections

Let `C` be a smooth proper curve over an algebraically closed field `K`, `j : U ⟶ C` an open
immersion with finite complement, `Λ` a finite ring with `#Λ` invertible in `K` and `ζ ∈ K` a
primitive `#Λ`-th root of unity. For a sheaf `G` of `Λ`-modules on `U` whose counit
`ε : Γ(U, G)_U ⟶ G` is an isomorphism and whose global sections are finite, the trace

  `τ_{G,ζ} : H²(C, j_! G) ≅ H²(C, j_!(Γ(U, G)_U)) ≅ Γ(U, G)`

is `Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace` after `ε⁻¹`.

Let `s : C ⟶ C` be an automorphism lying over `Spec τ`, `τ` a field automorphism of `K`, which
preserves `U` (`s_U ≫ j = j ≫ s` cartesian), and `β : G ⟶ s_{U,*} G` a twist. Then `s` acts on
`H²(C, j_! G)` through `j_!(β) ≫ (j_! s_{U,*} ⟶ s_* j_!)`, and on `Γ(U, G)` by
`a = Γ(β) ≫ (Γ(U, s_{U,*} -) = Γ(U, -))`. The main result is
`τ_{G,τ(ζ)}(s^* w) = a(τ_{G,ζ}(w))`.

In [Stacks, Tag 03VK] this is the trace on the smooth projective model of `X_k̄`, applied to the
restriction of a sheaf `ℱ_ρ` with `π₁(X_k̄)` acting trivially, and `a` the Galois action on
`Γ(X_k̄, ℱ_ρ) = M`.

## Main definitions

* `Stacks.EtaleCohomology.curveExtensionByZeroSheafTrace`.

## Main results

* `Stacks.EtaleCohomology.integralSelfMapCohomologyEndo_comp_directImage_map`.
* `Stacks.EtaleCohomology.curveExtensionByZeroSheafTrace_integralSelfMapCohomologyEndo_of_twist`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high] Stacks.EtaleCohomology.etaleModules_hasSheafify

namespace Stacks.EtaleCohomology

section Endo

variable (Λ : Type r) [Ring Λ] {Y : Scheme.{u}} (φ : Y ⟶ Y) [IsIntegralHom φ]

/-- **A twist followed by the direct image of an endomorphism.** The pullback action through
`α ≫ φ_* ψ` is the pullback action through `α` followed by `H^i(ψ)`. -/
theorem integralSelfMapCohomologyEndo_comp_directImage_map (N : EtaleModules.{u, r} Λ Y)
    (α : N ⟶ (etaleModuleDirectImage.{u, r} Λ φ).obj N) (ψ : N ⟶ N) (i : ℤ) :
    integralSelfMapCohomologyEndo Λ φ N (α ≫ (etaleModuleDirectImage.{u, r} Λ φ).map ψ) i =
      integralSelfMapCohomologyEndo Λ φ N α i ≫
        ((etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedPlus i).map ψ := by
  rw [integralSelfMapCohomologyEndo, integralSelfMapCohomologyEndo, Functor.map_comp,
    Category.assoc, integralDirectImageCohomologyIso_hom_naturality, Category.assoc]

end Endo

attribute [local instance] etaleModulesEnoughInjectivesZeroTraceTwist
  moduleCatHasColimitsOfSizeSmallEtale hasGlobalSectionsFunctorSmallEtaleModuleCat

section Trace

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  {U : Scheme.{u}} (jC : U ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

/-- **The trace `H²(C, j_! G) ≅ Γ(U, G)`** for a sheaf `G` on `U` whose counit
`Γ(U, G)_U ⟶ G` is an isomorphism and whose global sections are finite: `ε⁻¹`, then
`Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace`. -/
def curveExtensionByZeroSheafTrace (G : EtaleModules.{u, 0} Λ U)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)) :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj G) ≃ₗ[Λ]
      (etaleModuleGlobalSections.{u, 0} Λ U).obj G :=
  haveI := hG
  haveI := hE
  ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).mapIso
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).mapIso
        (asIso ((constantSheafΓAdj U.smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).counit.app G)).symm)).toLinearEquiv).trans
    (curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin
      ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))

omit [IsCurve K q] [Smooth q] [IsProper q] in
/-- `Stacks.EtaleCohomology.curveExtensionByZeroSheafTrace` is the trace of the constant sheaf
after `ε⁻¹`. -/
theorem curveExtensionByZeroSheafTrace_apply [IsCurve K q] [Smooth q] [IsProper q]
    (G : EtaleModules.{u, 0} Λ U) (hG : IsIso
      ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))
    (w : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj G)) :
    haveI := hE
    curveExtensionByZeroSheafTrace q Λ hn hζ jC hfin G hG hE w =
      curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin
        ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
          (@inv _ _ _ _ ((constantSheafΓAdj U.smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).counit.app G) hG))).hom w) := by
  have := hE
  simp only [curveExtensionByZeroSheafTrace, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    Functor.mapIso_hom, Iso.symm_hom, asIso_inv]

omit [Fintype Λ] [IsCurve K q] [IsProper q] in
include q hfin in
/-- `H²(C, j_! j^{-1} H) ⟶ H²(C, H)`, induced by the counit, is an isomorphism. -/
theorem isIso_rightDerivedPlus_two_counit_of_finite_compl' (H : EtaleModules.{u, 0} Λ C) :
    IsIso (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H)) :=
  isIso_rightDerivedPlus_two_counit_of_finite_compl q Λ jC hfin H

/-- **The trace `H²(C, H) ≅ Γ(U, G)`** for a sheaf `H` on `C` and an identification
`l : j^{-1} H ≅ G` with a sheaf `G` on `U` constant on its global sections: the boundary does not
contribute (`H²(C, j_! j^{-1} H) ≅ H²(C, H)`), then `j_! l` and
`Stacks.EtaleCohomology.curveExtensionByZeroSheafTrace`. -/
def curveExtensionByZeroRestrictionTrace (H : EtaleModules.{u, 0} Λ C)
    (G : EtaleModules.{u, 0} Λ U) (l : (etaleModuleRestriction.{u, 0} Λ jC).obj H ≅ G)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)) :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj H ≃ₗ[Λ]
      (etaleModuleGlobalSections.{u, 0} Λ U).obj G :=
  haveI := isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H
  ((asIso
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))).symm ≪≫
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).mapIso
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).mapIso l)).toLinearEquiv.trans
    (curveExtensionByZeroSheafTrace q Λ hn hζ jC hfin G hG hE)

omit [IsCurve K q] [Smooth q] [IsProper q] in
/-- `Stacks.EtaleCohomology.curveExtensionByZeroRestrictionTrace` is
`Stacks.EtaleCohomology.curveExtensionByZeroSheafTrace` after the inverse of the counit
`H²(C, j_! j^{-1} H) ⟶ H²(C, H)` and `j_! l`. -/
theorem curveExtensionByZeroRestrictionTrace_apply [IsCurve K q] [Smooth q] [IsProper q]
    (H : EtaleModules.{u, 0} Λ C) (G : EtaleModules.{u, 0} Λ U)
    (l : (etaleModuleRestriction.{u, 0} Λ jC).obj H ≅ G)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))
    (z : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj H) :
    curveExtensionByZeroRestrictionTrace q Λ hn hζ jC hfin H G l hG hE z =
      curveExtensionByZeroSheafTrace q Λ hn hζ jC hfin G hG hE
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map l.hom)).hom
          ((@inv _ _ _ _ (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus
            ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))
            (isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H)).hom z)) := by
  simp only [curveExtensionByZeroRestrictionTrace, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply]

omit [IsCurve K q] [Smooth q] [IsProper q] in
/-- **`τ_G` for `ζ^b` is `b` times `τ_G` for `ζ`.** -/
theorem curveExtensionByZeroSheafTrace_of_pow_eq [IsCurve K q] [Smooth q] [IsProper q]
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' (Fintype.card Λ)) {b : ℕ} (hb : ζ ^ b = ζ')
    (G : EtaleModules.{u, 0} Λ U)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))
    (w : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj G)) :
    curveExtensionByZeroSheafTrace q Λ hn hζ' jC hfin G hG hE w =
      b • curveExtensionByZeroSheafTrace q Λ hn hζ jC hfin G hG hE w := by
  have := hE
  rw [curveExtensionByZeroSheafTrace_apply, curveExtensionByZeroSheafTrace_apply]
  exact curveExtensionByZeroConstantTrace_of_pow_eq q Λ hn hζ hζ' hb jC hfin _ _

omit [IsCurve K q] [Smooth q] [IsProper q] in
/-- **The trace `H²(C, H) ≅ Γ(U, G)` for `ζ^b` is `b` times the one for `ζ`.** -/
theorem curveExtensionByZeroRestrictionTrace_of_pow_eq [IsCurve K q] [Smooth q] [IsProper q]
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' (Fintype.card Λ)) {b : ℕ} (hb : ζ ^ b = ζ')
    (H : EtaleModules.{u, 0} Λ C) (G : EtaleModules.{u, 0} Λ U)
    (l : (etaleModuleRestriction.{u, 0} Λ jC).obj H ≅ G)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))
    (z : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj H) :
    curveExtensionByZeroRestrictionTrace q Λ hn hζ' jC hfin H G l hG hE z =
      b • curveExtensionByZeroRestrictionTrace q Λ hn hζ jC hfin H G l hG hE z := by
  rw [curveExtensionByZeroRestrictionTrace_apply, curveExtensionByZeroRestrictionTrace_apply]
  exact curveExtensionByZeroSheafTrace_of_pow_eq q Λ hn hζ jC hfin hζ' hb G hG hE _

variable (sU : U ⟶ U) (s : C ⟶ C) [IsIso s] (sq : IsPullback sU jC jC s) (τ : K ≃+* K)
  (hs : s ≫ q = q ≫ Spec.map (CommRingCat.ofHom τ.toRingHom))

include hs in
/-- **The trace of `H²(C, j_! G)` under a semilinear automorphism of the curve.** Let
`s : C ⟶ C` lie over `Spec τ` and preserve `U`, and let `β : G ⟶ s_{U,*} G`. Then the trace
through `τ(ζ)` of the pullback of `w` through `j_!(β) ≫ (j_! s_{U,*} ⟶ s_* j_!)` is
`a = Γ(β) ≫ (Γ(U, s_{U,*} -) = Γ(U, -))` applied to the trace through `ζ` of `w`. -/
theorem curveExtensionByZeroSheafTrace_integralSelfMapCohomologyEndo_of_twist
    (G : EtaleModules.{u, 0} Λ U) (hG : IsIso
      ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))
    (β : G ⟶ (etaleModuleDirectImage.{u, 0} Λ sU).obj G)
    (w : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj G)) :
    curveExtensionByZeroSheafTrace q Λ hn (hζ.map_of_injective τ.injective) jC hfin G hG hE
        ((integralSelfMapCohomologyEndo Λ s ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj G)
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map β ≫
            extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq G)
          ((2 : ℕ) : ℤ)).hom w) =
      ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
        (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G).hom
        (curveExtensionByZeroSheafTrace q Λ hn hζ jC hfin G hG hE w) := by
  have := hG
  have := hE
  have h3a := constantSheafΓCounit_comp_twist Λ sU G β
  have hext := extensionByZeroIntegralDirectImageMap_naturality Λ jC jC sU s sq
    ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
          (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G) ≫
      (constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)
  have hsq : (((etaleModuleExtensionByZero.{u, 0} Λ jC).map
    (constantSelfMapTwist.{u, 0} Λ ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) sU) ≫
        extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq
          (etaleModuleConstantSheaf Λ ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) U)) ≫
        (etaleModuleDirectImage.{u, 0} Λ s).map ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
              (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G)))) ≫
        (etaleModuleDirectImage.{u, 0} Λ s).map ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
          ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)) =
      (etaleModuleExtensionByZero.{u, 0} Λ jC).map ((constantSheafΓAdj U.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).counit.app G) ≫ ((etaleModuleExtensionByZero.{u, 0} Λ jC).map β ≫
        extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq G) := by
    rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, Category.assoc, ← hext,
      ← Functor.map_comp_assoc, ← h3a, Functor.map_comp_assoc]
    rfl
  have hnat := integralSelfMapCohomologyEndo_naturality Λ s
    (N := (etaleModuleExtensionByZero.{u, 0} Λ jC).obj (etaleModuleConstantSheaf Λ
      ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) U))
      (N' := (etaleModuleExtensionByZero.{u, 0} Λ jC).obj G) _ _ _ hsq
    ((2 : ℕ) : ℤ)
  rw [integralSelfMapCohomologyEndo_comp_directImage_map] at hnat
  have hinv : ∀ z, (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
    (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)))).hom
      ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))).hom
        z) = z := by
    intro z
    rw [Functor.map_inv, Functor.map_inv]
    exact IsIso.hom_inv_id_apply _ z
  have hinv' : ∀ z, (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
    ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))).hom
      ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)))).hom
        z) = z := by
    intro z
    rw [Functor.map_inv, Functor.map_inv]
    exact IsIso.inv_hom_id_apply _ z
  have hx := congrArg (fun f => f.hom ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus
    ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
    (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)))).hom
    w)) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  rw [hinv'] at hx
  have hy := congrArg (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
    (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)))).hom hx
  rw [hinv] at hy
  have hy' : (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
    (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)))).hom
        ((integralSelfMapCohomologyEndo Λ s ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj G)
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map β ≫
            extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq G)
          ((2 : ℕ) : ℤ)).hom w) =
      (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
          ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
            (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G)))).hom
        ((integralSelfMapCohomologyEndo Λ s
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
            (etaleModuleConstantSheaf Λ ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) U))
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
            (constantSelfMapTwist.{u, 0} Λ ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) sU) ≫
            extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq
              (etaleModuleConstantSheaf Λ
                ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) U)) ((2 : ℕ) : ℤ)).hom
          ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
            (inv ((constantSheafΓAdj U.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).counit.app G)))).hom w)) :=
    hy.symm
  refine (curveExtensionByZeroSheafTrace_apply q Λ hn (hζ.map_of_injective τ.injective) jC hfin G
    hG hE _).trans ?_
  refine Eq.trans ?_ (congrArg ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
    (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G).hom
    (curveExtensionByZeroSheafTrace_apply q Λ hn hζ jC hfin G hG hE w)).symm
  refine (congrArg (curveExtensionByZeroConstantTrace q Λ hn (hζ.map_of_injective τ.injective) jC
    hfin ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)) hy').trans ?_
  have h1 := curveExtensionByZeroConstantTrace_integralSelfMapCohomologyEndo_of_twist q Λ hn hζ jC
    hfin sU s sq τ hs ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)
      ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
      (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)))).hom w)
  have hN := curveExtensionByZeroConstantTrace_naturality q Λ hn (hζ.map_of_injective τ.injective)
    jC hfin ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
      (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G)
      ((integralSelfMapCohomologyEndo Λ s
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
            (etaleModuleConstantSheaf Λ ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) U))
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
            (constantSelfMapTwist.{u, 0} Λ ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) sU) ≫
            extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq
              (etaleModuleConstantSheaf Λ
                ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)
                U)) ((2 : ℕ) : ℤ)).hom ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus
                ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
                (inv ((constantSheafΓAdj U.smallEtaleTopology
                (ModuleCat.{u + 1} Λ)).counit.app G)))).hom w))
  convert hN.trans (congrArg ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
    (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G).hom h1) using 2

include hs in
/-- **The trace of `H²(C, H)` under a semilinear automorphism of the curve.** Let `s : C ⟶ C` lie
over `Spec τ` and preserve `U`, `tw : H ⟶ s_* H` a twist and `β : G ⟶ s_{U,*} G` a twist that
`l : j^{-1} H ≅ G` intertwines with the restriction of `tw`. Then the trace through `τ(ζ)` of
the pullback of `z` through `tw` is `a = Γ(β) ≫ (Γ(U, s_{U,*} -) = Γ(U, -))` applied to the trace
through `ζ` of `z`. -/
theorem curveExtensionByZeroRestrictionTrace_integralSelfMapCohomologyEndo_of_twist
    (H : EtaleModules.{u, 0} Λ C) (G : EtaleModules.{u, 0} Λ U)
    (l : (etaleModuleRestriction.{u, 0} Λ jC).obj H ≅ G)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))
    (tw : H ⟶ (etaleModuleDirectImage.{u, 0} Λ s).obj H)
    (β : G ⟶ (etaleModuleDirectImage.{u, 0} Λ sU).obj G)
    (hl : (etaleModuleRestriction.{u, 0} Λ jC).map tw ≫
      (restrictionIntegralDirectImageIso Λ jC jC sU s sq).inv.app H ≫
        (etaleModuleDirectImage.{u, 0} Λ sU).map l.hom = l.hom ≫ β)
    (z : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj H) :
    curveExtensionByZeroRestrictionTrace q Λ hn
      (hζ.map_of_injective τ.injective) jC hfin H G l hG hE
        ((integralSelfMapCohomologyEndo Λ s H tw ((2 : ℕ) : ℤ)).hom z) =
      ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
        (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G).hom
        (curveExtensionByZeroRestrictionTrace q Λ hn hζ jC hfin H G l hG hE z) := by
  have := isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H
  have n1 := integralSelfMapCohomologyEndo_naturality Λ s
    (N := (etaleModuleExtensionByZero.{u, 0} Λ jC).obj ((etaleModuleRestriction.{u, 0} Λ jC).obj H))
    (N' := H)
    (extensionByZeroIntegralTwist Λ jC sU s sq H tw) tw
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H)
    (extensionByZeroIntegralTwist_comp_counit Λ jC sU s sq H tw) ((2 : ℕ) : ℤ)
  have n2 := integralSelfMapCohomologyEndo_naturality Λ s
    (N := (etaleModuleExtensionByZero.{u, 0} Λ jC).obj ((etaleModuleRestriction.{u, 0} Λ jC).obj H))
    (N' := (etaleModuleExtensionByZero.{u, 0} Λ jC).obj G) (extensionByZeroIntegralTwist Λ jC
      sU s sq H tw) ((etaleModuleExtensionByZero.{u, 0} Λ jC).map β ≫
      extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq G)
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).map l.hom)
    (extensionByZeroIntegralTwist_comp_map_of_restriction Λ jC sU s sq H tw G β l.hom hl)
    ((2 : ℕ) : ℤ)
  have hinv : ∀ y,
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H)).hom
    ((@inv _ _ _ _ (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))
    (isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H)).hom y) = y := by
    intro y
    exact IsIso.inv_hom_id_apply _ y
  have hinv' : ∀ y,
    (@inv _ _ _ _
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))
    (isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H)).hom
    ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H)).hom y) = y := by
    intro y
    exact IsIso.hom_inv_id_apply _ y
  have h1 := congrArg
    (fun f => f.hom ((@inv _ _ _ _ (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus
    ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))
    (isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H)).hom z)) n1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [hinv] at h1
  have h1' := congrArg (@inv _ _ _ _ (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus
    ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))
    (isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H)).hom h1
  rw [hinv'] at h1'
  have h2 := congrArg
    (fun f => f.hom ((@inv _ _ _ _ (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus
    ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H))
    (isIso_rightDerivedPlus_two_counit_of_finite_compl' q Λ jC hfin H)).hom z)) n2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  refine (curveExtensionByZeroRestrictionTrace_apply q Λ hn (hζ.map_of_injective τ.injective) jC
    hfin H G l hG hE _).trans ?_
  refine Eq.trans ?_ (congrArg ((etaleModuleGlobalSections.{u, 0} Λ U).map β ≫
    (etaleModuleGlobalSectionsDirectImageIso.{u, 0} sU Λ).hom.app G).hom
    (curveExtensionByZeroRestrictionTrace_apply q Λ hn hζ jC hfin H G l hG hE z)).symm
  refine (congrArg (fun t => curveExtensionByZeroSheafTrace q Λ hn (hζ.map_of_injective τ.injective)
    jC hfin G hG hE ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).map l.hom)).hom t)) h1'.symm).trans ?_
  convert (congrArg (curveExtensionByZeroSheafTrace q Λ hn (hζ.map_of_injective τ.injective)
    jC hfin G hG hE) h2).trans
      (curveExtensionByZeroSheafTrace_integralSelfMapCohomologyEndo_of_twist q Λ hn hζ jC hfin
        sU s sq τ hs G hG hE β _) using 2

end Trace

end Stacks.EtaleCohomology

end
