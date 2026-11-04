module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.FieldSpaceSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.TwistedEulerMixedDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The Euler characteristic of the structure sheaf of the spectrum of a field

The algebraic space `Spec k` over the base `Spec k` has `χ(Spec k, 𝒪) = 1`: its higher
cohomology vanishes because it is affine, and its global sections are `k`, the base ring acting
through the structure morphism of the terminal chart `Spec k = Spec k`.

## Main results

* `AlgebraicGeometry.Space.bijective_baseRingHom_baseObject`: the map from `k` to the global
  sections of the structure sheaf of `Spec k` is bijective.
* `AlgebraicGeometry.Space.twistedEulerMixedDifference_unit_baseObject`: `χ(Spec k, 𝒪) = 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- **The global functions of `Spec k` are `k`**: the map from the base ring `k` to the global
sections of the structure sheaf of the algebraic space `Spec k` is bijective. -/
theorem bijective_baseRingHom_baseObject :
    Function.Bijective (baseRingHom k B hk (yoneda.obj (baseObject k B hk))
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk))) := by
  let P : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨yoneda.obj (baseObject k B hk),
      isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
  let V := etaleChartOfIso B (Spec (.of k)) hk (Iso.refl P.1)
  have hV := isTerminalEtaleChartOfIso B (Spec (.of k)) hk (Iso.refl P.1)
  have hev := bijective_globalSectionsChartEval_of_isTerminal B (Spec (.of k)) hk P hV
  have b1 : Function.Bijective (Scheme.ΓSpecIso (.of k)).inv :=
    ConcreteCategory.bijective_of_isIso _
  have b2 : Function.Bijective (Scheme.Γ.map
      (B.inclusion.map ((SmallEtale.toOver B (Spec (.of k)) hk P.1).obj V).hom).op) :=
    haveI : IsIso ((SmallEtale.toOver B (Spec (.of k)) hk P.1).obj V).hom :=
      inferInstanceAs (IsIso (𝟙 _))
    ConcreteCategory.bijective_of_isIso _
  exact (Function.Bijective.of_comp_iff' hev _).1 (b2.comp b1)

/-- **`χ(Spec k, 𝒪) = 1`**, as the mixed difference of `𝒪` along the empty family. -/
theorem twistedEulerMixedDifference_unit_baseObject
    (L : Fin 0 → Modules.{u, u} B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)))
    [∀ j, Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk)))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk
        (yoneda.obj (baseObject k B hk))
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk))).O).property (L j)]
    (hO : IsCoherent B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B
        (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk))).O))) :
    twistedEulerMixedDifference.{u, w} k B hk
      ⟨yoneda.obj (baseObject k B hk),
        isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
      (𝟙 _) (isProper_id_baseObject k B hk) _ hO L = 1 := by
  set P : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨yoneda.obj (baseObject k B hk),
      isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
  unfold twistedEulerMixedDifference
  rw [Finset.sum_eq_single (∅ : Finset (Fin 0)) (fun T _ hT => absurd (Subsingleton.elim T ∅) hT)
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Finset.card_empty, Nat.sub_self, pow_zero, one_mul]
  rw [eulerCharacteristic_eq_finsum]
  have := enoughInjectives_modules B (Spec (.of k)) hk P.1 P.2
  set M := twistedModule B (Spec (.of k)) hk P.1 P.2 (SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk P.1 P.2).O))
    L (fun j => if j ∈ (∅ : Finset (Fin 0)) then 1 else 0) with hM
  have hfr : ∀ i, Module.finrank k (cohomologyOverBase.{u, w} k B hk P.1 P.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk P.1 P.2 _ L
        (fun j => if j ∈ (∅ : Finset (Fin 0)) then 1 else 0)) i) =
      Module.finrank k ((ModuleCat.restrictScalars (baseRingHom k B hk P.1 P.2)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk P.1 P.2).O)).rightDerived i).obj M)) :=
    fun i => finrank_cohomologyOverBase_uliftForPresentation.{u, w} B k hk P.1 P.2 M i
  rw [finsum_eq_single _ 0 ?_]
  · set R := Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of k)) hk P.1 P.2).O with hR
    have hTw : twistedModuleUlift.{u, w} B (Spec (.of k)) hk P.1 P.2 (SheafOfModules.unit R) L
        (fun j => if j ∈ (∅ : Finset (Fin 0)) then 1 else 0) =
        unitULift.{u + 1, u, u, max (u + 1) w} R := by
      unfold twistedModuleUlift twistedModule
      simp only [List.finRange_zero, List.foldl_nil]
      rfl
    rw [hTw]
    let f := baseRingHom k B hk P.1 P.2
    let e1 := cohomologyZeroUnitLinearEquiv.{u + 1, u, u, max (u + 1) w} R
    let N : ModuleCat.{u + 1} k :=
      (ModuleCat.restrictScalars f).obj (ModuleCat.of (GlobalSectionRing R) (GlobalSectionRing R))
    let e2 : cohomologyOverBase.{u, w} k B hk P.1 P.2
        (unitULift.{u + 1, u, u, max (u + 1) w} R) 0 ≃ₗ[k] N :=
      { e1.toAddEquiv with map_smul' := fun a x => e1.map_smul (f a) x }
    let g : k →ₗ[k] N :=
      { toFun := fun a => (show N from f a)
        map_add' := fun a b => map_add f a b
        map_smul' := fun a b => map_mul f a b }
    let e3 : k ≃ₗ[k] N := LinearEquiv.ofBijective g (bijective_baseRingHom_baseObject k B hk)
    rw [e2.finrank_eq, ← e3.finrank_eq, Module.finrank_self]
    simp
  · intro i hi
    rw [hfr i]
    have hMq : M.IsQuasicoherentOnSite :=
      inferInstanceAs (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk P.1 P.2).O)).IsQuasicoherentOnSite
    have hz := isZero_rightDerived_globalSections_of_isAffineSpace B (Spec (.of k)) hk P
      (isAffineSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)
        (inferInstanceAs (IsAffine (Spec (.of k))))) M hMq i (Nat.pos_of_ne_zero hi)
    have hsub := ModuleCat.isZero_iff_subsingleton.1 hz
    have : Subsingleton ((ModuleCat.restrictScalars (baseRingHom k B hk P.1 P.2)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk P.1 P.2).O)).rightDerived i).obj M)) := hsub
    rw [Module.finrank_zero_of_subsingleton]
    simp

end AlgebraicGeometry.Space

end
