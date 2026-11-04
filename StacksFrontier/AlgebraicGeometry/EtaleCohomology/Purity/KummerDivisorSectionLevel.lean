module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerDivisorSection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerUnitClassReduction

/-!
# The fundamental class of a divisor under change of the level

Let `j : U₀ ⟶ U` be a morphism of schemes and `N = e N'` with `N` and `N'` invertible on `U₀`.
The `e`-th power map `μ_N ⟶ μ_{N'}`, the `e`-th power map of `𝐆_m` and the identity of `𝐆_m` form
a morphism from the Kummer sequence at level `N` to the Kummer sequence at level `N'`
(`Stacks.Kummer.kummerSequencePowHom`). By the naturality of the connecting morphisms of the
`δ`-functor `R^• j_*`, the Kummer coboundary `∂_N : j_* 𝐆_m ⟶ R¹ j_* μ_N` followed by the power
map is `∂_{N'}`
(`Stacks.EtaleCohomology.Purity.kummerDirectImageδ_comp_map_rootsOfUnityPowMap`). Hence the local
Kummer classes and the glued fundamental class of a divisor `Z` in `R¹ j_* μ_N` go to those in
`R¹ j_* μ_{N'}` (`Stacks.EtaleCohomology.Purity.map_rootsOfUnityPowMap_kummerDivisorSection`).

This is the compatibility of the classes `s_N ∈ Γ(U, R¹ j_* μ_N)` with the transition maps of the
tower `n ↦ μ_{ℓⁿ⁺¹}`, which the tower form of cohomological purity of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) needs.

## Main results

* `Stacks.EtaleCohomology.Purity.kummerDirectImageδ_comp_map_rootsOfUnityPowMap`.
* `Stacks.EtaleCohomology.Purity.map_rootsOfUnityPowMap_localKummerClass`.
* `Stacks.EtaleCohomology.Purity.map_rootsOfUnityPowMap_kummerDivisorSection`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  TopologicalSpace Opposite

universe w u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U)
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})] {e N' N : ℕ}
  (hN : e * N' = N) (hN'0 : N' ≠ 0) (hN0 : N ≠ 0) (hN' : IsUnit ((N' : ℕ) : Γ(U₀, ⊤)))
  (hNu : IsUnit ((N : ℕ) : Γ(U₀, ⊤)))

/-- **The Kummer coboundary is compatible with the change of level**: `∂_N` followed by the
`e`-th power map `R¹ j_* μ_N ⟶ R¹ j_* μ_{N'}` is `∂_{N'}`, for `N = e N'`. -/
theorem kummerDirectImageδ_comp_map_rootsOfUnityPowMap :
    kummerDirectImageδ j hN0 hNu ≫
        ((smallEtalePushforwardAb j).rightDerived 1).map
          (rootsOfUnityPowMap.{u, 0} U₀ e N' N hN) =
      kummerDirectImageδ j hN'0 hN' := by
  have h := (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb j)).δ_naturality (kummerSequence_shortExact.{u, 0} U₀ hN0 hNu)
    (kummerSequence_shortExact.{u, 0} U₀ hN'0 hN') (kummerSequencePowHom.{u, 0} U₀ e N' N hN) 0
  have h' : (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb j)).δ (kummerSequence_shortExact.{u, 0} U₀ hN0 hNu) 0 ≫
      ((smallEtalePushforwardAb j).rightDerived 1).map
        (rootsOfUnityPowMap.{u, 0} U₀ e N' N hN) =
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb j)).δ (kummerSequence_shortExact.{u, 0} U₀ hN'0 hN') 0 := by
    refine h.symm.trans ?_
    show ((smallEtalePushforwardAb j).rightDerived 0).map (𝟙 _) ≫ _ = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  rw [kummerDirectImageδ_eq, kummerDirectImageδ_eq]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h')

/-- **The local Kummer class is compatible with the change of level**: the `e`-th power map
carries `∂_N t` to `∂_{N'} t`. -/
theorem map_rootsOfUnityPowMap_localKummerClass (V : U.Opens) (t : Γ(U, V))
    (ht : IsUnit (puncturedFunction j V t)) :
    (((smallEtalePushforwardAb j).rightDerived 1).map
        (rootsOfUnityPowMap.{u, 0} U₀ e N' N hN)).hom.app (op ((opensToEtale U).obj V))
        (localKummerClass j hN0 hNu V t ht) =
      localKummerClass j hN'0 hN' V t ht := by
  have h := congrArg (fun φ => φ.hom.app (op ((opensToEtale U).obj V))
      (ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) ht.unit))
    (kummerDirectImageδ_comp_map_rootsOfUnityPowMap j hN hN'0 hN0 hN' hNu)
  exact h

/-- **The fundamental class of a divisor is compatible with the change of level**: the `e`-th
power map `R¹ j_* μ_N ⟶ R¹ j_* μ_{N'}` carries the fundamental class at level `N` to the one at
level `N'`. -/
theorem map_rootsOfUnityPowMap_kummerDivisorSection (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
    (hNU' : IsUnit ((N' : ℕ) : Γ(U, ⊤))) {Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]
    (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
    (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t) :
    (((smallEtalePushforwardAb j).rightDerived 1).map
        (rootsOfUnityPowMap.{u, 0} U₀ e N' N hN)).hom.app (op ((opensToEtale U).obj ⊤))
        (kummerDivisorSection j hN0 hNu hNU i hj hcov) =
      kummerDivisorSection j hN'0 hN' hNU' i hj hcov := by
  refine eq_kummerDivisorSection j hN'0 hN' hNU' i hj hcov _ fun V t ht => ?_
  have hnat := NatTrans.naturality_apply (((smallEtalePushforwardAb j).rightDerived 1).map
      (rootsOfUnityPowMap.{u, 0} U₀ e N' N hN)).hom
    ((opensToEtale U).map (homOfLE (le_top : V ≤ ⊤))).op
    (kummerDivisorSection j hN0 hNu hNU i hj hcov)
  refine hnat.symm.trans ?_
  rw [kummerDivisorSection_restrict j hN0 hNu hNU i hj hcov V t ht]
  exact map_rootsOfUnityPowMap_localKummerClass j hN hN'0 hN0 hN' hNu V t _

end Stacks.EtaleCohomology.Purity

end
