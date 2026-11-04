module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerClassMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerDivisorSectionLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneTransition

/-!
# The purity map and the change of level

Let `N' = ℓ N`. The `ℓ`-th power map `p : μ_{N'} ⟶ μ_N` commutes with the identification
`j⁻¹ μ_N ≅ μ_N` (`Stacks.EtaleCohomology.Purity.pullbackRootsOfUnityIso_hom_naturality`), so it
carries the fundamental class of a divisor at level `N'`, read in `R¹ j_*(j⁻¹ μ_{N'})`, to the one
at level `N` (`Stacks.EtaleCohomology.Purity.map_kummerDivisorPullbackSection`). Hence the purity
map `α ↦ α_* s_N` at level `N` is the purity map at level `N'` after precomposition with `p`
(`Stacks.EtaleCohomology.Purity.kummerClassMapAb_eq_precompPow_comp`), and the purity maps commute
with the transition maps `𝓗om(μ_{N'}, G') ⟶ 𝓗om(μ_N, G)` of the Tate twist
(`Stacks.EtaleCohomology.Purity.twistNegOneModuleTransition_comp_kummerClassMapAb`): these are
the squares of the tower form of purity
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.Purity.map_kummerDivisorPullbackSection`.
* `Stacks.EtaleCohomology.Purity.kummerClassMapAb_eq_precompPow_comp`.
* `Stacks.EtaleCohomology.Purity.twistNegOneModuleTransition_comp_kummerClassMapAb`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe w u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

section PowMap

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (ℓ N N' : ℕ) (hN : ℓ * N = N')

/-- **The comparison `π⁻¹ μ_N ⟶ μ_N` commutes with the `ℓ`-th power maps.** -/
theorem rootsOfUnityInverseImageComparison_comp_rootsOfUnityPowMap :
    (etaleAbelianInverseImage.{u, 0} π).map (rootsOfUnityPowMap.{u, 0} Y ℓ N N' hN) ≫
        rootsOfUnityInverseImageComparison.{u, 0} π N =
      rootsOfUnityInverseImageComparison.{u, 0} π N' ≫ rootsOfUnityPowMap.{u, 0} X ℓ N N' hN := by
  rw [← cancel_mono (rootsOfUnityι.{u, 0} X N), Category.assoc, Category.assoc,
    rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, rootsOfUnityPowMap_comp_ι,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, rootsOfUnityPowMap_comp_ι,
    CategoryTheory.Functor.map_comp, Category.assoc,
    multiplicativeInverseImageComparison_comm_powMap, ← Category.assoc, ← Category.assoc,
    rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, Category.assoc]

/-- **The identification `π⁻¹ μ_N ≅ μ_N` commutes with the `ℓ`-th power maps.** -/
theorem pullbackRootsOfUnityIso_hom_naturality (hNY : IsUnit ((N : ℕ) : Γ(Y, ⊤)))
    (hN'Y : IsUnit ((N' : ℕ) : Γ(Y, ⊤))) :
    (smallEtalePullbackAb π).map (rootsOfUnityPowMap.{u, 0} Y ℓ N N' hN) ≫
        (pullbackRootsOfUnityIso π N hNY).hom =
      (pullbackRootsOfUnityIso π N' hN'Y).hom ≫ rootsOfUnityPowMap.{u, 0} X ℓ N N' hN := by
  simp only [pullbackRootsOfUnityIso, Iso.trans_hom, Iso.app_hom, rootsOfUnityInverseImageIso_hom]
  rw [← Category.assoc, NatTrans.naturality, Category.assoc, Category.assoc,
    rootsOfUnityInverseImageComparison_comp_rootsOfUnityPowMap]

/-- The inverse form of `Stacks.EtaleCohomology.Purity.pullbackRootsOfUnityIso_hom_naturality`. -/
theorem pullbackRootsOfUnityIso_inv_naturality (hNY : IsUnit ((N : ℕ) : Γ(Y, ⊤)))
    (hN'Y : IsUnit ((N' : ℕ) : Γ(Y, ⊤))) :
    (pullbackRootsOfUnityIso π N' hN'Y).inv ≫
        (smallEtalePullbackAb π).map (rootsOfUnityPowMap.{u, 0} Y ℓ N N' hN) =
      rootsOfUnityPowMap.{u, 0} X ℓ N N' hN ≫ (pullbackRootsOfUnityIso π N hNY).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← pullbackRootsOfUnityIso_hom_naturality π ℓ N N' hN hNY
    hN'Y, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end PowMap

/-- The `ℓ`-th power map `μ_{ℓN} ⟶ μ_N`, between the underlying abelian sheaves of `μ` as
sheaves of `ℤ/ℓN`- and `ℤ/N`-modules. -/
abbrev rootsOfUnityPowMapForget (U : Scheme.{u}) (ℓ N N' : ℕ) (hN : ℓ * N = N') [NeZero N]
    [NeZero N'] :
    smallEtaleModuleSheafForgetAb (ZMod N') (rootsOfUnityModule.{u, 0} U N') ⟶
      smallEtaleModuleSheafForgetAb (ZMod N) (rootsOfUnityModule.{u, 0} U N) :=
  rootsOfUnityPowMap.{u, 0} U ℓ N N' hN

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U) [IsOpenImmersion j]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})] (ℓ N N' : ℕ)
  (hN : ℓ * N = N') [NeZero N] [NeZero N']
  (hN₀ : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
  (hN'₀ : IsUnit ((N' : ℕ) : Γ(U₀, ⊤))) (hN'U : IsUnit ((N' : ℕ) : Γ(U, ⊤))) {Z : Scheme.{u}}
  (i : Z ⟶ U) [IsClosedImmersion i] (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
  (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t)

omit [IsOpenImmersion j] in
/-- **The fundamental class is compatible with the change of level**, in `R¹ j_*(j⁻¹ μ)`: the
`ℓ`-th power map carries the class at level `N' = ℓ N` to the class at level `N`. -/
theorem map_kummerDivisorPullbackSection :
    (((smallEtalePushforwardAb j).rightDerived 1).map ((smallEtalePullbackAb j).map
        (rootsOfUnityPowMapForget U ℓ N N' hN))).hom.app
        (op ((opensToEtale U).obj ⊤)) (kummerDivisorPullbackSection j N' hN'₀ hN'U i hj hcov) =
      kummerDivisorPullbackSection j N hN₀ hNU i hj hcov := by
  have h1 := map_rootsOfUnityPowMap_kummerDivisorSection j hN (NeZero.ne N) (NeZero.ne N') hN₀
    hN'₀ hN'U hNU i hj hcov
  have h2 := congrArg (fun φ => (((smallEtalePushforwardAb j).rightDerived 1).map φ).hom.app
      (op ((opensToEtale U).obj ⊤)) (kummerDivisorSection j (NeZero.ne N') hN'₀ hN'U i hj hcov))
    (pullbackRootsOfUnityIso_inv_naturality j ℓ N N' hN hNU hN'U)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h2
  have h3 : (((smallEtalePushforwardAb j).rightDerived 1).map ((smallEtalePullbackAb j).map
        (rootsOfUnityPowMap.{u, 0} U ℓ N N' hN))).hom.app (op ((opensToEtale U).obj ⊤))
        (kummerDivisorPullbackSection j N' hN'₀ hN'U i hj hcov) =
      (((smallEtalePushforwardAb j).rightDerived 1).map
          (pullbackRootsOfUnityIso j N hNU).inv).hom.app (op ((opensToEtale U).obj ⊤))
        ((((smallEtalePushforwardAb j).rightDerived 1).map
          (rootsOfUnityPowMap.{u, 0} U₀ ℓ N N' hN)).hom.app (op ((opensToEtale U).obj ⊤))
          (kummerDivisorSection j (NeZero.ne N') hN'₀ hN'U i hj hcov)) := h2
  refine h3.trans ?_
  rw [h1]
  rfl

variable (G : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} (ZMod N)))

omit [IsOpenImmersion j] in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The purity map at level `N` is the purity map at level `N' = ℓ N` after precomposition with
the `ℓ`-th power map**: `α_* s_N = (α ∘ p)_* s_{N'}`. -/
theorem kummerClassMapAb_eq_precompPow_comp :
    kummerClassMapAb j N hN₀ hNU i hj hcov G =
      (sheafCompose (smallEtaleTopology U) (forget₂ (ModuleCat.{u + 1} (ZMod N'))
          AddCommGrpCat.{u + 1})).map (twistNegOnePrecompPow.{u, 0} U ℓ N N' hN G) ≫
        kummerClassMapAb j N' hN'₀ hN'U i hj hcov
          ((sheafCompose (smallEtaleTopology U) (zmodRestrict.{u, 0} ℓ N N' hN)).obj G) := by
  apply Sheaf.hom_ext
  ext V : 2
  refine AddCommGrpCat.ext (fun α => ?_)
  let α' : ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} (ZMod N)) V.unop).obj
      (rootsOfUnityModule.{u, 0} U N) ⟶
      ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} (ZMod N)) V.unop).obj G := α
  have hsl : moduleSheafHomForgetSliceHom V.unop
      (show ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} (ZMod N')) V.unop).obj
          (rootsOfUnityModule.{u, 0} U N') ⟶
        ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} (ZMod N')) V.unop).obj
          ((sheafCompose (smallEtaleTopology U) (zmodRestrict.{u, 0} ℓ N N' hN)).obj G) from
        (twistNegOnePrecompPow.{u, 0} U ℓ N N' hN G).hom.app V α) =
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V.unop).map
          (rootsOfUnityPowMapForget U ℓ N N' hN) ≫
        moduleSheafHomForgetSliceHom (Λ := ZMod N) (F := rootsOfUnityModule.{u, 0} U N) (G := G)
          V.unop α' := by
    apply Sheaf.hom_ext
    ext P : 2
    rfl
  have h2 := (congrArg (fun φ => higherDirectImageInverseImageSectionMap j 1 V.unop φ) hsl).trans
    (higherDirectImageInverseImageSectionMap_map_comp j 1 V.unop _ _)
  have hnat := NatTrans.naturality_apply (((smallEtalePushforwardAb j).rightDerived 1).map
    ((smallEtalePullbackAb j).map (rootsOfUnityPowMapForget U ℓ N N' hN))).hom
    ((isTerminal_opensToEtale_top U).from V.unop).op
    (kummerDivisorPullbackSection j N' hN'₀ hN'U i hj hcov)
  rw [map_kummerDivisorPullbackSection j ℓ N N' hN hN₀ hNU hN'₀ hN'U i hj hcov] at hnat
  refine Eq.trans ?_ (congrArg (fun φ : (((smallEtalePushforwardAb j).rightDerived 1).obj
      ((smallEtalePullbackAb j).obj (smallEtaleModuleSheafForgetAb (ZMod N')
        (rootsOfUnityModule.{u, 0} U N')))).obj.obj (op V.unop) ⟶
      (((smallEtalePushforwardAb j).rightDerived 1).obj ((smallEtalePullbackAb j).obj
        (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj.obj
        (op V.unop) => ConcreteCategory.hom φ
    ((((smallEtalePushforwardAb j).rightDerived 1).obj ((smallEtalePullbackAb j).obj
      (smallEtaleModuleSheafForgetAb (ZMod N') (rootsOfUnityModule.{u, 0} U N')))).obj.map
        ((isTerminal_opensToEtale_top U).from V.unop).op
      (kummerDivisorPullbackSection j N' hN'₀ hN'U i hj hcov))) h2).symm
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
  exact (congrArg (ConcreteCategory.hom (higherDirectImageInverseImageSectionMap j 1 V.unop
    (moduleSheafHomForgetSliceHom V.unop α'))) hnat).symm

omit [IsOpenImmersion j] in
/-- **The purity maps commute with the transitions of the Tate twist**: for `t : G' ⟶ G` from a
sheaf of `ℤ/N'`-modules to a sheaf of `ℤ/N`-modules (`N' = ℓ N`), the transition
`𝓗om(μ_{N'}, G') ⟶ 𝓗om(μ_N, G)` followed by the purity map at level `N` is the purity map at
level `N'` followed by `R¹ j_*(j⁻¹ t)`. -/
theorem twistNegOneModuleTransition_comp_kummerClassMapAb {k : Type u} [Field k]
    (f : U ⟶ Spec (.of k)) [NeZero ((N' : ℕ) : k)]
    (G' : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} (ZMod N')))
    (t : G' ⟶ (sheafCompose (smallEtaleTopology U) (zmodRestrict.{u, 0} ℓ N N' hN)).obj G) :
    (sheafCompose (smallEtaleTopology U) (forget₂ (ModuleCat.{u + 1} (ZMod N'))
          AddCommGrpCat.{u + 1})).map (twistNegOneModuleTransition.{u, 0} U ℓ N N' hN G f G' t) ≫
        kummerClassMapAb j N hN₀ hNU i hj hcov G =
      kummerClassMapAb j N' hN'₀ hN'U i hj hcov G' ≫
        ((smallEtalePushforwardAb j).rightDerived 1).map ((smallEtalePullbackAb j).map
          ((sheafCompose (smallEtaleTopology U) (forget₂ (ModuleCat.{u + 1} (ZMod N'))
            AddCommGrpCat.{u + 1})).map t)) := by
  have e1 := congrArg (sheafCompose (smallEtaleTopology U) (forget₂ (ModuleCat.{u + 1} (ZMod N'))
      AddCommGrpCat.{u + 1})).map (twistNegOneModuleTransition_comp_precompPow.{u, 0} U ℓ N N' hN G
        f G' t)
  rw [CategoryTheory.Functor.map_comp] at e1
  refine (congrArg (_ ≫ ·) (kummerClassMapAb_eq_precompPow_comp j ℓ N N' hN hN₀ hNU hN'₀ hN'U i
    hj hcov G)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ kummerClassMapAb j N' hN'₀ hN'U i hj hcov
    ((sheafCompose (smallEtaleTopology U) (zmodRestrict.{u, 0} ℓ N N' hN)).obj G)) e1).trans ?_
  exact moduleSheafHomMap_comp_higherDirectImageClassMap j 1 (isTerminal_opensToEtale_top U)
    (kummerDivisorPullbackSection j N' hN'₀ hN'U i hj hcov) t

end Stacks.EtaleCohomology.Purity

end
