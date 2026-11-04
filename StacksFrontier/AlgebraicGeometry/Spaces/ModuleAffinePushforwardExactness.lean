module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramIsoDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image along an affine morphism on quasi-coherent modules

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` of a big fppf site
`B`.  This file proves the properties of `f_*` on quasi-coherent modules which the proof of
Stacks 0CW8 uses: on a map `v : F ⟶ G` of quasi-coherent `𝒪_X`-modules it preserves and
reflects isomorphisms, monomorphisms, epimorphisms and vanishing.  The quasi-coherence of `f_*F`
itself (the first assertion of Stacks 07U8) is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional`.

In the source these properties come from Stacks 08AI: `f_*` is an equivalence of quasi-coherent
`𝒪_X`-modules with quasi-coherent `f_*𝒪_X`-modules, hence "a faithful, exact functor reflecting
isomorphisms, injective maps, and surjective maps".  Here they are proved directly on the
sections over affine charts, without the equivalence.

## Main results

* `AlgebraicGeometry.Space.exists_affine_chart_bijective_modulePushforwardCounitApp`: over an
  affine chart `V` of `Y`, the sections of `f_*F` are the sections of `F` over the affine chart
  `V ×_Y X` of `X`.
* `AlgebraicGeometry.Space.epi_of_surjective_affineChartDiagram` and
  `AlgebraicGeometry.Space.eq_zero_of_affineChartDiagram`: surjectivity and vanishing of a map of
  modules are checked on the source charts of the affine chart diagrams over a morphism.
* `AlgebraicGeometry.Space.mono_modulePushforward_map_iff_of_isAffineHom`,
  `.epi_modulePushforward_map_iff_of_isAffineHom`,
  `.isIso_modulePushforward_map_iff_of_isAffineHom` and
  `.modulePushforward_map_eq_zero_iff_of_isAffineHom`: `f_*v` is a monomorphism, an
  epimorphism, an isomorphism or zero exactly when `v` is.
* `AlgebraicGeometry.Space.nonempty_arrowIso_modulePullback_map_modulePushforward_map`: the base
  change clause of Stacks 07U8 at a morphism `u`: `g^*f_*u ≅ f'_*(g')^*u` as arrows.

## Proof

For an affine étale chart `V` of `Y`, the algebraic space `V ×_Y X` is an affine étale chart `W`
of `X` (`AlgebraicGeometry.Space.exists_affine_chart_isIso_chartLift`), and the sections of
`f_*F` over `V` are the sections of `F` over `W`.  Every source chart `U` of an affine chart
diagram `U ⟶ V` over `f` maps to `W`, and for quasi-coherent `F` the sections over `U` are the
base change of those over `W` (Stacks 03DX,
`isCartesianOnAffineCharts_of_isQuasicoherentOnSite`).  So vanishing of `v` over `U` follows
from vanishing of `f_*v` over `V`, and those charts `U` cover `X` (Stacks 03G2).  Hence `f_*`
reflects vanishing of maps out of a quasi-coherent module; it reflects monomorphisms because the
kernel inclusion vanishes after `f_*`, and epimorphisms because the cokernel projection does.
In the other direction, an epimorphism of quasi-coherent modules is surjective over every affine
chart (`surjective_val_app_of_epi_of_isQuasicoherentOnSite`), so `f_*v` is surjective over every
affine chart of `Y`.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 0CW8](https://stacks.math.columbia.edu/tag/0CW8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The affine chart above an affine chart of the target -/

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The sections of a direct image along an affine morphism over an affine chart.**  For an
affine `f : X ⟶ Y` and an affine étale chart `V` of `Y` there is an affine étale chart `W` of `X`
with a chart diagram `W ⟶ V` over `f` such that the canonical map
`(f_*F)(V) ⟶ F(W)` of `AlgebraicGeometry.Space.modulePushforwardCounitApp` is bijective for every
`𝒪_X`-module `F`, and the source chart of every chart diagram over `f` with target `V` maps to
`W`. -/
theorem exists_affine_chart_bijective_modulePushforwardCounitApp (hf : IsAffineHom B S hS f.hom)
    (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V)) :
    ∃ (W : SmallEtale B S hS X.1)
      (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom),
      IsAffine (chartScheme W) ∧
      (∀ F : Modules.{u, u} B S hS X.1 X.2,
        Function.Bijective (modulePushforwardCounitApp B S hS f F ⟨W, V, b, hb⟩)) ∧
      ∀ (U : SmallEtale B S hS X.1)
        (g : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V),
        U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom → Nonempty (U ⟶ W) := by
  obtain ⟨W, b, hb, hWa, hiso⟩ := exists_affine_chart_isIso_chartLift f hf V hV
  let e : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨W, V, b, hb⟩
  have hsurj : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map
      (chartLift B S hS f e)).hom :=
    isSurjective_of_isIso B S hS ((SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _).map
      (chartLift B S hS f e))
  have hpbW : IsPullback ((comparisonFunctor B S hS X).map (𝟙 W))
      ((comparisonFunctor B S hS X).map (𝟙 W)) (chartLift B S hS f e) (chartLift B S hS f e) := by
    rw [CategoryTheory.Functor.map_id]
    exact IsKernelPair.id_of_mono _
  have hk : IsSurjective B S hS
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map (𝟙 W))).hom := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact isSurjective_of_isIso B S hS (𝟙 _)
  refine ⟨W, b, hb, hWa, fun F => ⟨injective_modulePushforwardCounitApp f F e hsurj, fun p =>
    exists_modulePushforwardCounitApp_eq f F e hsurj (𝟙 W) (𝟙 W) hpbW (𝟙 W) hk p rfl⟩, ?_⟩
  intro U g comm
  have := comparisonFunctor_full B S hS X
  exact ⟨(comparisonFunctor B S hS X).preimage
    (chartLift B S hS f ⟨U, V, g, comm⟩ ≫ inv (chartLift B S hS f e))⟩

end Chart

/-! ### Transfer of a property of a map of modules to a smaller chart -/

section Transfer

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  {M N : Modules.{u, u} B S hS F hF} (v : M ⟶ N) {U W : SmallEtale B S hS F} (i : U ⟶ W)

/-- If the sections of `M` over `U` are generated by those over `W`, vanishing of a map of
modules over `W` passes to `U`. -/
theorem val_app_eq_zero_of_surjective_sectionsBaseChange
    (hM : Function.Surjective (sectionsBaseChange M i)) (hv : v.val.app (op W) = 0) :
    v.val.app (op U) = 0 := by
  let := chartAlgebra (hF := hF) i
  ext x
  obtain ⟨z, rfl⟩ := hM x
  rw [app_sectionsBaseChange v i z, hv, ModuleCat.hom_zero, LinearMap.lTensor_zero,
    LinearMap.zero_apply, map_zero]
  rfl

end Transfer

/-! ### Properties checked on the affine chart diagrams -/

section ChartDiagram

variable {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) {M N : Modules.{u, u} B S hS X.1 X.2}
  (φ : M ⟶ N)

/-- **A morphism of `𝒪_X`-modules surjective on the sections over the source chart of every
affine chart diagram over `g` is an epimorphism**: those charts generate a covering sieve of
every étale chart (Stacks 03G2), so the morphism is locally surjective. -/
theorem epi_of_surjective_affineChartDiagram
    (h : ∀ d : ChartDiagram B S hS X.1 Y.1 g.hom, IsAffine (chartScheme d.U) →
      IsAffine (chartScheme d.V) → Function.Surjective (φ.val.app (op d.U))) :
    Epi φ := by
  have hcov := generate_affineChartDiagram_mem_topology B S hS g (fun _ => True)
    (fun _ _ => trivial)
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective φ ⟨fun {U} s => ?_⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ (hcov U)
  rintro W b ⟨Z, l, a, ⟨hZ, d, rfl, hV, -⟩, rfl⟩
  refine (Presheaf.imageSieve _ s).downward_closed ?_ l
  obtain ⟨t, ht⟩ := h d hZ hV (((PresheafOfModules.toPresheaf _).obj N.val).map a.op s)
  exact ⟨t, ht⟩

/-- **A morphism of `𝒪_X`-modules vanishing on the sections over the source chart of every
affine chart diagram over `g` is zero**: those charts generate a covering sieve of every étale
chart (Stacks 03G2), and the target is separated. -/
theorem eq_zero_of_affineChartDiagram
    (h : ∀ d : ChartDiagram B S hS X.1 Y.1 g.hom, IsAffine (chartScheme d.U) →
      IsAffine (chartScheme d.V) → φ.val.app (op d.U) = 0) :
    φ = 0 := by
  have hcov := generate_affineChartDiagram_mem_topology B S hS g (fun _ => True)
    (fun _ _ => trivial)
  ext ⟨U⟩ x
  refine (Presheaf.IsSheaf.isSeparated N.isSheaf) U _ (hcov U) _ 0 ?_
  rintro W b ⟨Z, l, a, ⟨hZ, d, rfl, hV, -⟩, rfl⟩
  have e := congrArg (fun ψ => (ConcreteCategory.hom ψ) (φ.val.app (op U) x))
    (N.val.presheaf.map_comp a.op l.op)
  refine (e.trans ?_).trans (map_zero _).symm
  have hnat := PresheafOfModules.naturality_apply φ.val a.op x
  have h0 : φ.val.app (op d.U) (M.val.map a.op x) = 0 := by
    rw [h d hZ hV]
    rfl
  exact (congrArg (fun y => (ConcreteCategory.hom (N.val.presheaf.map l.op)) y)
    (hnat.symm.trans h0)).trans (map_zero _)

end ChartDiagram

/-! ### The direct image along an affine morphism -/

section Pushforward

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The canonical map of sections into the direct image sends zero to zero. -/
theorem modulePushforwardCounitApp_zero (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    modulePushforwardCounitApp B S hS f F d 0 = 0 := by
  simpa using modulePushforwardCounitApp_add B S hS f F d 0 0

variable (hf : IsAffineHom B S hS f.hom) {M N : Modules.{u, u} B S hS X.1 X.2}
include hf

/-- **The direct image along an affine morphism reflects vanishing** of a map out of a module
cartesian on affine charts, in particular out of a quasi-coherent module. -/
theorem eq_zero_of_modulePushforward_map_eq_zero (hM : IsCartesianOnAffineCharts M)
    (φ : M ⟶ N) (h : (modulePushforward B S hS f).map φ = 0) : φ = 0 := by
  refine eq_zero_of_affineChartDiagram f φ fun d hU hV => ?_
  obtain ⟨W, b, hb, hWa, hbij, hmap⟩ :=
    exists_affine_chart_bijective_modulePushforwardCounitApp f hf d.V hV
  obtain ⟨i⟩ := hmap d.U d.g d.comm
  refine val_app_eq_zero_of_surjective_sectionsBaseChange φ i (hM W d.U hWa hU i).2 ?_
  ext y
  obtain ⟨z, rfl⟩ := (hbij M).2 y
  have h0 : ((modulePushforward B S hS f).map φ).val.app (op d.V) z = 0 := by
    rw [h]
    rfl
  rw [ModuleCat.hom_zero, LinearMap.zero_apply]
  exact (modulePushforwardCounitApp_map B S hS f φ ⟨W, d.V, b, hb⟩ z).symm.trans
    ((congrArg (modulePushforwardCounitApp B S hS f N ⟨W, d.V, b, hb⟩) h0).trans
      (modulePushforwardCounitApp_zero f N _))

/-- **The direct image along an affine morphism preserves epimorphisms of quasi-coherent
modules.**  Over an affine chart `V` of `Y` the map `f_*v` is the map `v` over the affine chart
`V ×_Y X` of `X`, which is surjective by Stacks 03DW. -/
theorem epi_modulePushforward_map_of_isAffineHom (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) [Epi φ] :
    Epi ((modulePushforward B S hS f).map φ) := by
  refine epi_of_surjective_affineChartDiagram (𝟙 Y) _ fun d hU _ z => ?_
  obtain ⟨W, b, hb, hWa, hbij, -⟩ :=
    exists_affine_chart_bijective_modulePushforwardCounitApp f hf d.U hU
  obtain ⟨m, hm⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite φ inferInstance hM hN W hWa
    (modulePushforwardCounitApp B S hS f N ⟨W, d.U, b, hb⟩ z)
  obtain ⟨z', rfl⟩ := (hbij M).2 m
  exact ⟨z', (hbij N).1 ((modulePushforwardCounitApp_map B S hS f φ _ z').trans hm)⟩

/-- **The direct image along an affine morphism reflects monomorphisms of quasi-coherent
modules**: the kernel is again cartesian on affine charts, and its inclusion vanishes after
direct image. -/
theorem mono_of_mono_modulePushforward_map (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) [Mono ((modulePushforward B S hS f).map φ)] :
    Mono φ := by
  refine Preadditive.mono_of_kernel_zero (eq_zero_of_modulePushforward_map_eq_zero f hf
    (isCartesianOnAffineCharts_kernel φ
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 N hN)) _ ?_)
  rw [← cancel_mono ((modulePushforward B S hS f).map φ), ← Functor.map_comp, kernel.condition,
    Functor.map_zero, zero_comp]

/-- **The direct image along an affine morphism reflects epimorphisms of quasi-coherent
modules**: the cokernel projection vanishes after direct image. -/
theorem epi_of_epi_modulePushforward_map (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    [Epi ((modulePushforward B S hS f).map φ)] :
    Epi φ := by
  refine Preadditive.epi_of_cokernel_zero (eq_zero_of_modulePushforward_map_eq_zero f hf
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 N hN) _ ?_)
  rw [← cancel_epi ((modulePushforward B S hS f).map φ), ← Functor.map_comp, cokernel.condition,
    Functor.map_zero, comp_zero]

/-- The direct image along an affine morphism detects monomorphisms of quasi-coherent
modules. -/
theorem mono_modulePushforward_map_iff_of_isAffineHom (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    Mono ((modulePushforward B S hS f).map φ) ↔ Mono φ :=
  ⟨fun _ => mono_of_mono_modulePushforward_map f hf hM hN φ, fun _ => inferInstance⟩

/-- The direct image along an affine morphism detects epimorphisms of quasi-coherent
modules. -/
theorem epi_modulePushforward_map_iff_of_isAffineHom (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    Epi ((modulePushforward B S hS f).map φ) ↔ Epi φ :=
  ⟨fun _ => epi_of_epi_modulePushforward_map f hf hN φ,
    fun _ => epi_modulePushforward_map_of_isAffineHom f hf hM hN φ⟩

/-- The direct image along an affine morphism detects isomorphisms of quasi-coherent
modules. -/
theorem isIso_modulePushforward_map_iff_of_isAffineHom (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    IsIso ((modulePushforward B S hS f).map φ) ↔ IsIso φ := by
  rw [isIso_iff_mono_and_epi_modules B S hS, isIso_iff_mono_and_epi_modules B S hS,
    mono_modulePushforward_map_iff_of_isAffineHom f hf hM hN,
    epi_modulePushforward_map_iff_of_isAffineHom f hf hM hN]

/-- The direct image along an affine morphism detects vanishing of maps of quasi-coherent
modules. -/
theorem modulePushforward_map_eq_zero_iff_of_isAffineHom (hM : M.IsQuasicoherentOnSite)
    (φ : M ⟶ N) :
    (modulePushforward B S hS f).map φ = 0 ↔ φ = 0 := by
  refine ⟨eq_zero_of_modulePushforward_map_eq_zero f hf
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM) φ, ?_⟩
  rintro rfl
  exact Functor.map_zero _ _ _

end Pushforward

/-! ### Affine base change of a map of modules -/

section BaseChange

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- **Affine base change of a map of quasi-coherent modules** (the base change clause of
Stacks 07U8, at a morphism).  For a cartesian square whose right morphism `f` is affine and a map
`u : F ⟶ G` of quasi-coherent `𝒪_X`-modules, the base change maps identify `g^*f_*u` with
`f'_*(g')^*u` as arrows. -/
theorem nonempty_arrowIso_modulePullback_map_modulePushforward_map (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) {F G : Modules.{u, u} B S hS X.1 X.2} (u : F ⟶ G)
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) :
    Nonempty (Arrow.mk ((modulePullback B S hS g).map ((modulePushforward B S hS f).map u)) ≅
      Arrow.mk ((modulePushforward B S hS f').map ((modulePullback B S hS g').map u))) :=
  ⟨Arrow.isoMk (@asIso _ _ _ _ _ (isIso_moduleBaseChangeMap_app_of_isAffineHom sq hf F hF))
    (@asIso _ _ _ _ _ (isIso_moduleBaseChangeMap_app_of_isAffineHom sq hf G hG))
    ((moduleBaseChangeMap f g f' g' sq.w).naturality u).symm⟩

end BaseChange

end AlgebraicGeometry.Space

end
