module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale

/-!
# Isomorphisms in the derived category of an algebraic space are étale local

Let `Y` be an algebraic space and `(Vᵢ ⟶ Y)` a family of étale scheme charts covering `Y`.  A
morphism `φ` of `D(𝒪_Y)` is an isomorphism as soon as every derived pullback `L(Vᵢ ⟶ Y)^*φ` is
one.  This is the reduction "we may work étale locally on `Y`" used throughout the chapter on
derived categories of spaces.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace`: the
  criterion, for a family of charts covering the final object of the small étale site.

## Implementation notes

An étale derived pullback is the exact restriction functor read on derived categories
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoEtale`), so it commutes with the
cohomology sheaves; restriction to a chart is restriction to the slice at that chart followed by
an equivalence (`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`); and restriction to the
slices at a covering family is jointly conservative
(`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of `𝒪_Y`-modules is an isomorphism as soon as its restrictions to a family of
étale scheme charts covering `Y` are. -/
theorem isIso_of_isIso_modulePullback_chartToSpace {Y : AlgebraicSpaces B S hS} {ι : Type*}
    {V : ι → SmallEtale B S hS Y.1} (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((modulePullback B S hS (chartToSpace B S hS Y (V i))).map φ)) :
    IsIso φ := by
  refine Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map hV φ fun i => ?_
  have hi : IsIso ((chartModuleRestriction B S hS Y (V i)).map φ) := h i
  have h₁ : IsIso ((SheafOfModules.overFunctor (structureRingSheaf B S hS Y) (V i) ⋙
      chartModuleSliceReindex B S hS Y (V i)).map φ) :=
    (NatIso.isIso_map_iff (chartModuleRestrictionSliceIso B S hS Y (V i)) φ).1 hi
  have : (chartModuleSliceReindex B S hS Y (V i)).ReflectsIsomorphisms := by
    rw [← chartModuleSliceEquiv_functor]
    infer_instance
  have : IsIso ((chartModuleSliceReindex B S hS Y (V i)).map
      ((SheafOfModules.overFunctor (structureRingSheaf B S hS Y) (V i)).map φ)) := h₁
  exact isIso_of_reflects_iso ((SheafOfModules.overFunctor (structureRingSheaf B S hS Y)
    (V i)).map φ) (chartModuleSliceReindex B S hS Y (V i))

/-- **Isomorphisms of `D(𝒪_Y)` are étale local.**  A morphism `φ` of `D(𝒪_Y)` is an isomorphism
as soon as its derived pullbacks along a family of étale scheme charts covering `Y` are. -/
theorem isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace {Y : AlgebraicSpaces B S hS}
    {ι : Type*} {V : ι → SmallEtale B S hS Y.1}
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (φ : K ⟶ L)
    (h : ∀ i, IsIso ((smallEtaleDerivedModulePullback B S hS
      (chartToSpace B S hS Y (V i))).map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_modulePullback_chartToSpace B S hS hV _ fun i => ?_
  let a := chartToSpace B S hS Y (V i)
  let ha := isEtale_chartToSpace B S hS Y (V i)
  have : (etaleModulePullback.{u, u} B S hS a ha).Additive :=
    etaleModulePullback_additive B S hS a ha
  have : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteLimits_etaleModulePullback B S hS a ha
  have : PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteColimits_etaleModulePullback B S hS a ha
  have h₁ : IsIso ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.map φ) :=
    (NatIso.isIso_map_iff (smallEtaleDerivedModulePullbackIsoEtale B S hS a ha) φ).1 (h i)
  rw [DerivedCategory.isIso_iff] at h₁
  let φ' : (show DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) from K) ⟶
      (show DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) from L) := φ
  have h₂ : IsIso ((etaleModulePullback.{u, u} B S hS a ha).map
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).map φ')) :=
    (Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff
      (C₁ := Modules.{u, u} B S hS Y.1 Y.2)
      (C₂ := Modules.{u, u} B S hS (chartSpace B S hS Y (V i)).1 (chartSpace B S hS Y (V i)).2)
      (etaleModulePullback.{u, u} B S hS a ha) φ' n).1 (h₁ n)
  exact (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS a ha) _).2 h₂

/-- A sheaf of `𝒪_Y`-modules is zero as soon as its restrictions to a family of étale scheme
charts covering `Y` are. -/
theorem isZero_of_isZero_modulePullback_chartToSpace {Y : AlgebraicSpaces B S hS} {ι : Type*}
    {V : ι → SmallEtale B S hS Y.1} (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (h : ∀ i, IsZero ((modulePullback B S hS (chartToSpace B S hS Y (V i))).obj M)) :
    IsZero M := by
  have hiso : IsIso (0 : M ⟶ M) := by
    refine isIso_of_isIso_modulePullback_chartToSpace B S hS hV _ fun i => ?_
    rw [(h i).eq_of_src ((modulePullback B S hS (chartToSpace B S hS Y (V i))).map 0) (𝟙 _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  have h0 : 𝟙 M = (0 : M ⟶ M) ≫ inv (0 : M ⟶ M) := (IsIso.hom_inv_id _).symm
  rw [zero_comp] at h0
  exact h0

/-- **Cohomological amplitude in `D(𝒪_Y)` is étale local.** An object of `D(𝒪_Y)` whose derived
pullbacks along a family of étale scheme charts covering `Y` have vanishing cohomology sheaves in
degrees `> n` has itself vanishing cohomology sheaves in degrees `> n`. -/
theorem isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace {Y : AlgebraicSpaces B S hS}
    {ι : Type*} {V : ι → SmallEtale B S hS Y.1}
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (h : ∀ i, ((smallEtaleDerivedModulePullback B S hS
      (chartToSpace B S hS Y (V i))).obj K).IsLE n) :
    K.IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro m hm
  refine isZero_of_isZero_modulePullback_chartToSpace B S hS hV _ fun i => ?_
  let a := chartToSpace B S hS Y (V i)
  let ha := isEtale_chartToSpace B S hS Y (V i)
  have : (etaleModulePullback.{u, u} B S hS a ha).Additive :=
    etaleModulePullback_additive B S hS a ha
  have : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteLimits_etaleModulePullback B S hS a ha
  have : PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteColimits_etaleModulePullback B S hS a ha
  let K' : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) := K
  have h₂ : IsZero ((DerivedCategory.homologyFunctor _ m).obj
      ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj K')) :=
    ((DerivedCategory.isLE_iff _ n).1 (h i) m hm).of_iso
      ((DerivedCategory.homologyFunctor _ m).mapIso
        ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K).symm)
  have h₃ : IsZero ((etaleModulePullback.{u, u} B S hS a ha).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) m).obj K')) :=
    h₂.of_iso (((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategoryHomologyIso m).app
      K').symm
  exact h₃.of_iso ((modulePullbackIsoEtaleModulePullback B S hS a ha).app _)

/-- **Cohomological amplitude from below in `D(𝒪_Y)` is étale local.** An object of
`D(𝒪_Y)` whose derived pullbacks along a family of étale scheme charts covering `Y` have vanishing
cohomology sheaves in degrees `< n` has itself vanishing cohomology sheaves in degrees `< n`. -/
theorem isGE_of_isGE_smallEtaleDerivedModulePullback_chartToSpace {Y : AlgebraicSpaces B S hS}
    {ι : Type*} {V : ι → SmallEtale B S hS Y.1}
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (h : ∀ i, ((smallEtaleDerivedModulePullback B S hS
      (chartToSpace B S hS Y (V i))).obj K).IsGE n) :
    K.IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro m hm
  refine isZero_of_isZero_modulePullback_chartToSpace B S hS hV _ fun i => ?_
  let a := chartToSpace B S hS Y (V i)
  let ha := isEtale_chartToSpace B S hS Y (V i)
  have : (etaleModulePullback.{u, u} B S hS a ha).Additive :=
    etaleModulePullback_additive B S hS a ha
  have : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteLimits_etaleModulePullback B S hS a ha
  have : PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteColimits_etaleModulePullback B S hS a ha
  let K' : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) := K
  have h₂ : IsZero ((DerivedCategory.homologyFunctor _ m).obj
      ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj K')) :=
    ((DerivedCategory.isGE_iff _ n).1 (h i) m hm).of_iso
      ((DerivedCategory.homologyFunctor _ m).mapIso
        ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K).symm)
  have h₃ : IsZero ((etaleModulePullback.{u, u} B S hS a ha).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) m).obj K')) :=
    h₂.of_iso (((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategoryHomologyIso m).app
      K').symm
  exact h₃.of_iso ((modulePullbackIsoEtaleModulePullback B S hS a ha).app _)

end AlgebraicGeometry.Space

end
