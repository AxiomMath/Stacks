module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BottomHomologyEdge
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedEquivalence

/-!
# The Gysin edge morphism is faithful on sheaves supported on the closed subset

Let `Z` be a closed subset of a ringed space `X`, `i` the inclusion, `ℱ` an `𝒪_X`-module with
`ℋ^j_Z(ℱ) = 0` for `j < c`, and `edge : i_*ℋ^c_Z(ℱ)[-c] ⟶ ℱ` the Gysin edge morphism of
[Stacks, Tag 0G8A] (`Stacks.DeRham.CohomologicalGysin.supportedGysinEdge`). For an
`𝒪_X`-module `𝒜` supported on `Z` and a morphism of sheaves `γ : 𝒜 ⟶ i_*ℋ^c_Z(ℱ)`,

`γ[-c] ≫ edge = 0` in `D(𝒪_X)` only if `γ = 0`.

So a nonzero sheaf-level Gysin map gives a nonzero morphism `𝒜[-c] ⟶ ℱ` of the derived category.

## Implementation notes

`𝒜[-c]` is supported on `Z`, so the counit `ε : i_*Rℋ_Z(𝒜[-c]) ⟶ 𝒜[-c]` is invertible
([Stacks, Tag 0AEF], `isIso_derivedPushforwardAdjunction_counit_app_of_supported`), and `i_*` is
fully faithful on derived categories (its unit is invertible). Hence `ε ≫ γ[-c]` is `i_*(f')` for
a unique `f'`, and `ε ≫ γ[-c] ≫ edge` is the transpose of `f' ≫ L` under `i_* ⊣ Rℋ_Z`, where
`L : ℋ^c_Z(ℱ)[-c] ⟶ Rℋ_Z(ℱ)` is the comparison of the vanishing hypothesis. That `L` induces an
isomorphism on `H^c` (`Stacks.BottomHomologyEdge.homologyMap_eq`), so `f' ≫ L = 0` forces
`H^c(f') = 0`; as `i_*` is exact, `H^c(i_*(f')) = i_*(H^c(f')) = 0`, and reading `H^c` of
`ε ≫ γ[-c]` gives `γ = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace DerivedCategory
open RingedSpaceModuleAdjunction Stacks.Cohomology.SupportedComplexes

namespace Stacks.DeRham.CohomologicalGysin

universe u

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance] moduleSheavesHasDerivedCategory

/-- **The comparison `H^c(K)[-c] ⟶ K` of an object with no cohomology below `c` induces the
canonical identification on `H^c`.** -/
theorem homologyFunctor_map_singleHomologyToOfIsGE {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C) (c : ℤ) (hK : TStructure.t.IsGE K c) :
    (homologyFunctor C c).map (singleHomologyToOfIsGE K c hK) =
      (singleFunctorCompHomologyFunctorIso C c).hom.app ((homologyFunctor C c).obj K) := by
  have : K.IsGE c := hK
  exact Stacks.BottomHomologyEdge.homologyMap_eq c K

/-- **Transposing a vanishing composite across an adjunction with invertible unit.** If
`g₀ ≫ P(L) ≫ ε_K = 0` and the counit is invertible at `M`, then `ε_M ≫ g₀ = P(f')` for some
`f'` with `f' ≫ L = 0`. -/
theorem exists_map_eq_counit_comp_and_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {P : D ⥤ C} {R : C ⥤ D} [P.PreservesZeroMorphisms]
    (adj : P ⊣ R) [IsIso adj.unit] {M K : C} {N : D} [IsIso (adj.counit.app M)]
    (g₀ : M ⟶ P.obj N) (L : N ⟶ R.obj K) (h : g₀ ≫ P.map L ≫ adj.counit.app K = 0) :
    ∃ f' : R.obj M ⟶ N, P.map f' = adj.counit.app M ≫ g₀ ∧ f' ≫ L = 0 := by
  let hff : P.FullyFaithful := adj.fullyFaithfulLOfIsIsoUnit
  refine ⟨hff.preimage (adj.counit.app M ≫ g₀), hff.map_preimage _, ?_⟩
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, P.map_comp, hff.map_preimage,
    Functor.map_zero, zero_comp, Category.assoc, Category.assoc, h, comp_zero]

/-- **An exact functor carries a morphism killed by `H^c` to one killed by `H^c`, read through an
isomorphism.** If `F(f') = e ≫ g₀` with `e` invertible and `H^c(f') = 0`, then `H^c(g₀) = 0`. -/
theorem homologyFunctor_map_eq_zero_of_mapDerivedCategory {C D : Type*} [Category C]
    [Category D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : D ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (c : ℤ)
    {Y N : DerivedCategory D} {M : DerivedCategory C} (f' : Y ⟶ N)
    (e : F.mapDerivedCategory.obj Y ≅ M) (g₀ : M ⟶ F.mapDerivedCategory.obj N)
    (hf' : F.mapDerivedCategory.map f' = e.hom ≫ g₀)
    (h : (homologyFunctor D c).map f' = 0) :
    (homologyFunctor C c).map g₀ = 0 := by
  let θ := StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F c
  have hn : (homologyFunctor C c).map (F.mapDerivedCategory.map f') ≫ θ.hom.app N =
      θ.hom.app Y ≫ F.map ((homologyFunctor D c).map f') := θ.hom.naturality f'
  rw [h, F.map_zero, comp_zero, hf', Functor.map_comp] at hn
  exact zero_of_epi_comp _ (zero_of_comp_mono (θ.hom.app N) hn)

variable {X : RingedSpace.{u, u}} (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The Gysin edge morphism detects nonzero sheaf-level Gysin maps out of a sheaf supported on
`Z`.** If `γ[-c] ≫ edge = 0` for `γ : 𝒜 ⟶ i_*ℋ^c_Z(ℱ)` and `𝒜[-c]` supported on `Z`, then
`γ = 0`. -/
theorem eq_zero_of_singleFunctor_map_comp_supportedGysinEdge_eq_zero (c : ℤ)
    (A F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hA : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z
      ((singleFunctor _ c).obj A))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (γ : A ⟶ (modulePushforward (closedSubsetInclusion X Z)).obj
      (localCohomologySheafOfComplex X Z hZ c ((singleFunctor _ (0 : ℤ)).obj F)))
    (h : (singleFunctor _ c).map γ ≫
      supportedGysinEdge Z hZ c ((singleFunctor _ (0 : ℤ)).obj F) hvan = 0) :
    γ = 0 := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := isIso_unit_derivedPushforwardAdjunction X Z hZ
  let adj := derivedPushforwardAdjunction X Z hZ
  let K := (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (0 : ℤ)).obj F
  let H := localCohomologySheafOfComplex X Z hZ c K
  let M := (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) c).obj A
  have : IsIso (adj.counit.app M) :=
    isIso_derivedPushforwardAdjunction_counit_app_of_supported X Z hZ M hA
  let ι :=
    ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategorySingleFunctor c).inv.app H
  let L := localCohomologySingleToDerived Z hZ c K hvan
  obtain ⟨f', hf', h2⟩ := exists_map_eq_counit_comp_and_comp_eq_zero adj
    ((singleFunctor _ c).map γ ≫ ι) L (by rwa [Category.assoc])
  -- `H^c(L)` is invertible, so `H^c(f') = 0`
  let HZ := homologyFunctor
    (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) c
  have hL : IsIso (HZ.map L) := by
    rw [show L = singleHomologyToOfIsGE _ c ((DerivedCategory.isGE_iff _ c).2 hvan) from rfl,
      homologyFunctor_map_singleHomologyToOfIsGE]
    infer_instance
  have h3 : HZ.map f' = 0 :=
    zero_of_comp_mono (HZ.map L) (by rw [← HZ.map_comp, h2, HZ.map_zero])
  have h5 := homologyFunctor_map_eq_zero_of_mapDerivedCategory
    (modulePushforward (closedSubsetInclusion X Z)) c f' (asIso (adj.counit.app M)) _ hf' h3
  rw [Functor.map_comp] at h5
  have h6 : (homologyFunctor _ c).map ((singleFunctor _ c).map γ) = 0 :=
    zero_of_comp_mono _ h5
  have hn := (singleFunctorCompHomologyFunctorIso
    (_root_.SheafOfModules.{u} (structureSheafRing X)) c).hom.naturality γ
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [h6, zero_comp] at hn
  exact zero_of_epi_comp _ hn.symm

end Stacks.DeRham.CohomologicalGysin
