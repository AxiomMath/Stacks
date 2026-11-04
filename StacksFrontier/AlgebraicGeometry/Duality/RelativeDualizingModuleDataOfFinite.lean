module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CompactOpenLocalization.OpenImmersion
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebraLiftedPresentation
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.BasisSectionExtension
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartFactorization
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleData0BVG

/-!
# Relative dualizing module data from a trace on a finite morphism

Let `f = i ≫ g : Y ⟶ X` with `i : Y ⟶ Y'` an open immersion and `g : Y' ⟶ X` finite, let `M` be
a quasi-coherent `𝒪_{Y'}`-module and `t : g_*M ⟶ 𝒪_X`. If for every affine open `U = Spec A`
of `X`, with `g⁻¹U = Spec B'`, the map `Γ(g⁻¹U, M) → Hom_A(B', A)`, `s ↦ (b ↦ t(b • s))`, is
bijective, then every `N ≅ M|_Y` carries the chart data of the relative dualizing module of `f`
(Tag 0BVG): on a chart `Spec B = V ⊆ f⁻¹U` its sections are `Hom_A(B', A) ⊗_{B'} B = ω_{B/A}`,
compatibly with Tags 0BT1 and 0BT2.

## Main definitions

* `Stacks.Discriminant.traceDual`: the map `s ↦ (b ↦ t(b • s))`.
* `Stacks.Discriminant.chartFactorization`: the finite-open factorization `A → B' → B` of a chart.
* `Stacks.Discriminant.chartEquiv`: the identification `ω_{A → B' → B} ≅ Γ(V, N)`.
* `Stacks.Discriminant.RelativeDualizingModuleData.ofFiniteTrace`: the chart data on `N`.

## Main results

* `Stacks.Discriminant.RelativeDualizingModuleData.ofFiniteTrace_localEquiv` and
  `Stacks.Discriminant.RelativeDualizingModuleData.ofFiniteTrace_localEquiv_selfFactorization`:
  the affine identifications send the section induced by `s` to `(b ↦ t(b • s)) ⊗ 1`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

section OpenRestriction

variable {Z : Scheme.{u}} {V W : Z.Opens}

/-- The restriction map between two nested affine opens induces an open embedding on prime
spectra. -/
theorem isOpenEmbedding_comap_restrict (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W) :
    IsOpenEmbedding (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom) := by
  have hcomp : Spec.map (Z.presheaf.map (homOfLE h).op) ≫ hW.fromSpec = hV.fromSpec :=
    hW.map_fromSpec hV (homOfLE h).op
  have : IsOpenImmersion (Spec.map (Z.presheaf.map (homOfLE h).op) ≫ hW.fromSpec) := by
    rw [hcomp]
    infer_instance
  have : IsOpenImmersion (Spec.map (Z.presheaf.map (homOfLE h).op)) :=
    IsOpenImmersion.of_comp _ hW.fromSpec
  exact (Spec.map (Z.presheaf.map (homOfLE h).op)).isOpenEmbedding

/-- The range of the map on prime spectra induced by restriction between nested affine opens is
the preimage of the smaller open. -/
theorem range_comap_restrict (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W) :
    Set.range (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom) =
      hW.fromSpec ⁻¹' (V : Set Z) := by
  have hcomp : Spec.map (Z.presheaf.map (homOfLE h).op) ≫ hW.fromSpec = hV.fromSpec :=
    hW.map_fromSpec hV (homOfLE h).op
  have e : ∀ q, (Spec.map (Z.presheaf.map (homOfLE h).op) ≫ hW.fromSpec) q = hV.fromSpec q :=
    fun q => by rw [hcomp]
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    show (Spec.map (Z.presheaf.map (homOfLE h).op) ≫ hW.fromSpec) q ∈ (V : Set Z)
    rw [e q, ← hV.range_fromSpec]
    exact ⟨q, rfl⟩
  · intro hp
    obtain ⟨q, hq⟩ : hW.fromSpec p ∈ Set.range hV.fromSpec := by
      rwa [hV.range_fromSpec]
    refine ⟨q, hW.fromSpec.isOpenEmbedding.injective ?_⟩
    show (Spec.map (Z.presheaf.map (homOfLE h).op) ≫ hW.fromSpec) q = _
    rw [e q, hq]

/-- For a basic open `D(g)` of `Spec Γ(Z, W)` inside the range of the restriction to `V`, the
induced map of localizations away from `g` is bijective. -/
theorem bijective_awayMap_restrict (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W)
    (g : Γ(Z, W))
    (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Γ(Z, W))) ⊆
      Set.range (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom)) :
    Function.Bijective (Localization.awayMap (Z.presheaf.map (homOfLE h).op).hom g) := by
  refine hW.bijective_awayMap_res hV.isCompact h ?_
  intro x hx
  obtain ⟨p, rfl⟩ : x ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    exact Z.basicOpen_le g hx
  have hp : p ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Γ(Z, W))) := by
    change p ∈ hW.fromSpec ⁻¹ᵁ Z.basicOpen g at hx
    rwa [hW.fromSpec_preimage_basicOpen g] at hx
  have := hg hp
  rwa [range_comap_restrict hV hW h] at this

/-- The restriction map between nested affine opens, followed by an isomorphism of rings,
satisfies the two conditions on the second map of a finite-open factorization. -/
theorem isOpenEmbedding_and_bijective_awayMap_restrict_comp (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : V ≤ W) {B : CommRingCat.{u}} (σ : Γ(Z, V) ≅ B) :
    IsOpenEmbedding (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op ≫ σ.hom).hom) ∧
      ∀ g : Γ(Z, W),
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Γ(Z, W))) ⊆
          Set.range (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op ≫ σ.hom).hom) →
        Function.Bijective
          (Localization.awayMap (Z.presheaf.map (homOfLE h).op ≫ σ.hom).hom g) := by
  let e : Γ(Z, V) ≃+* B := σ.commRingCatIsoToRingEquiv
  have he : (Z.presheaf.map (homOfLE h).op ≫ σ.hom).hom =
      (e : Γ(Z, V) →+* B).comp (Z.presheaf.map (homOfLE h).op).hom := by
    rw [CommRingCat.hom_comp]
    rfl
  have hc : PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op ≫ σ.hom).hom =
      PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom ∘
        PrimeSpectrum.comap (e : Γ(Z, V) →+* B) := by
    rw [he, PrimeSpectrum.comap_comp]
  have hhomeo := PrimeSpectrum.isHomeomorph_comap_of_bijective (f := (e : Γ(Z, V) →+* B))
    e.bijective
  have hr : Set.range (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op ≫ σ.hom).hom) =
      Set.range (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom) := by
    rw [hc, Set.range_comp, hhomeo.surjective.range_eq, Set.image_univ]
  refine ⟨?_, fun g hg => ?_⟩
  · rw [hc]
    exact (isOpenEmbedding_comap_restrict hV hW h).comp hhomeo.isOpenEmbedding
  · rw [he, Localization.bijective_awayMap_comp_ringEquiv]
    exact bijective_awayMap_restrict hV hW h g (hr ▸ hg)

end OpenRestriction

section TraceDual

variable {X Y' : Scheme.{u}} (g : Y' ⟶ X) {M : Y'.Modules}
  (t : (Scheme.Modules.pushforward g).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- The sections of a morphism `t : g_*M ⟶ 𝒪_X` over `U`, valued in `Γ(X, U)`. -/
def traceApp (U : X.Opens) : Γ(M, g ⁻¹ᵁ U) →+ Γ(X, U) :=
  (t.app U).hom

/-- A morphism `g_*M ⟶ 𝒪_X` is linear over `Γ(X, U)` acting through `g`. -/
theorem traceApp_smul (U : X.Opens) (a : Γ(X, U)) (s : Γ(M, g ⁻¹ᵁ U)) :
    traceApp g t U ((g.appLE U (g ⁻¹ᵁ U) le_rfl).hom a • s) = a * traceApp g t U s := by
  rw [Scheme.Hom.appLE_eq_app]
  exact Scheme.Modules.Hom.app_smul t a s

/-- A morphism of sheaves commutes with restriction of sections. -/
theorem traceApp_restrict {U U' : X.Opens} (h : U' ≤ U) (x : Γ(M, g ⁻¹ᵁ U)) :
    traceApp g t U' (M.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g h)).op x) =
      X.presheaf.map (homOfLE h).op (traceApp g t U x) :=
  congrArg (fun φ => φ x) (t.mapPresheaf.naturality (homOfLE h).op)

/-- The functional `b ↦ t(b • s)` attached to a section `s` of `M` over `g⁻¹U` by a morphism
`t : g_*M ⟶ 𝒪_X`, as a `Γ(Y', g⁻¹U)`-linear map to `Hom_{Γ(X,U)}(Γ(Y', g⁻¹U), Γ(X, U))`. -/
def traceDual (U : X.Opens) :
    letI : Algebra Γ(X, U) Γ(Y', g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    Γ(M, g ⁻¹ᵁ U) →ₗ[Γ(Y', g ⁻¹ᵁ U)] Module.Dual Γ(X, U) Γ(Y', g ⁻¹ᵁ U) :=
  letI : Algebra Γ(X, U) Γ(Y', g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  { toFun := fun s =>
      { toFun := fun b => traceApp g t U (b • s)
        map_add' := fun b c => by rw [add_smul, map_add]
        map_smul' := fun a b => by
          change traceApp g t U (((g.appLE U (g ⁻¹ᵁ U) le_rfl).hom a * b) • s) = a * _
          rw [mul_smul]
          exact traceApp_smul g t U a (b • s) }
    map_add' := fun s s' => by
      ext b
      change traceApp g t U (b • (s + s')) = traceApp g t U (b • s) + traceApp g t U (b • s')
      rw [smul_add, map_add]
    map_smul' := fun c s => by
      ext b
      change traceApp g t U (b • c • s) = traceApp g t U ((c * b) • s)
      rw [smul_smul, mul_comm] }

/-- The value of `traceDual` at `b` is `t(b • s)`. -/
theorem traceDual_apply (U : X.Opens) (s : Γ(M, g ⁻¹ᵁ U)) (b : Γ(Y', g ⁻¹ᵁ U)) :
    traceDual g t U s b = traceApp g t U (b • s) :=
  rfl

/-- The functionals `traceDual` are compatible with shrinking the open of the base. -/
theorem traceDual_restrict {U U' : X.Opens} (h : U' ≤ U) (s : Γ(M, g ⁻¹ᵁ U))
    (b : Γ(Y', g ⁻¹ᵁ U)) :
    traceDual g t U' (M.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g h)).op s)
        (Y'.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g h)).op b) =
      X.presheaf.map (homOfLE h).op (traceDual g t U s b) := by
  rw [traceDual_apply, traceDual_apply, ← traceApp_restrict g t h, M.map_smul]

end TraceDual

/-! ### Sections of a restriction to an open immersion -/

section Chart

variable {Y Y' : Scheme.{u}} {i : Y ⟶ Y'} [IsOpenImmersion i]

/-- An open lying over `W` has its image inside `W`. -/
theorem image_le_of_le_preimage {W : Y'.Opens} {V : Y.Opens} (h : V ≤ i ⁻¹ᵁ W) :
    i ''ᵁ V ≤ W :=
  (Scheme.Hom.image_mono _ h).trans (Scheme.Hom.image_preimage_le _ _)

/-- For an open immersion, `appLE` is restriction followed by the identification of the
sections over an open with the sections over its image. -/
theorem appLE_eq_map_comp_appIso {W : Y'.Opens} {V : Y.Opens} (h : V ≤ i ⁻¹ᵁ W) :
    i.appLE W V h = Y'.presheaf.map (homOfLE (image_le_of_le_preimage h)).op ≫
      (i.appIso V).hom := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

variable (M : Y'.Modules) {N : Y.Modules} (e : N ≅ M.restrict i)

/-- The identification of the sections of `M|_Y` over `V` with those of `M` over `i(V)` is
linear along `Γ(Y', i(V)) ≅ Γ(Y, V)`. -/
theorem restrictAppIso_inv_smul (V : Y.Opens) (r : Γ(Y', i ''ᵁ V)) (x : Γ(M, i ''ᵁ V)) :
    (M.restrictAppIso i V).inv (r • x) =
      (i.appIso V).hom.hom r • (M.restrictAppIso i V).inv x := by
  simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
    Scheme.Modules.smul_apply] using congr($(Scheme.Modules.smul_restrictAppIso_inv i M V r).hom x)

/-- The restriction of a section of `M` over `W` to a section of `N` over an open `V` with
`i(V) ⊆ W`, through `N ≅ M|_Y`. -/
def chartRestrict {W : Y'.Opens} {V : Y.Opens} (h : V ≤ i ⁻¹ᵁ W) : Γ(M, W) →+ Γ(N, V) :=
  ((e.inv.app V).hom.comp ((M.restrictAppIso i V).inv.hom)).comp
    (M.presheaf.map (homOfLE (image_le_of_le_preimage h)).op).hom

/-- The value of `chartRestrict`. -/
theorem chartRestrict_apply {W : Y'.Opens} {V : Y.Opens} (h : V ≤ i ⁻¹ᵁ W) (m : Γ(M, W)) :
    chartRestrict M e h m = e.inv.app V ((M.restrictAppIso i V).inv
      (M.presheaf.map (homOfLE (image_le_of_le_preimage h)).op m)) :=
  rfl

/-- `chartRestrict` is semilinear along `appLE`. -/
theorem chartRestrict_smul {W : Y'.Opens} {V : Y.Opens} (h : V ≤ i ⁻¹ᵁ W) (b : Γ(Y', W))
    (m : Γ(M, W)) :
    chartRestrict M e h (b • m) = (i.appLE W V h).hom b • chartRestrict M e h m := by
  rw [chartRestrict_apply, chartRestrict_apply, M.map_smul, restrictAppIso_inv_smul,
    Scheme.Modules.Hom.app_smul, appLE_eq_map_comp_appIso h]
  rfl

/-- The restriction of sections `chartRestrict`, as a linear map over `Γ(Y', W)` acting on
`Γ(N, V)` through `appLE`. -/
def chartRestrictₗ {W : Y'.Opens} {V : Y.Opens} (h : V ≤ i ⁻¹ᵁ W) :
    letI : Module Γ(Y', W) Γ(N, V) := Module.compHom _ (i.appLE W V h).hom
    Γ(M, W) →ₗ[Γ(Y', W)] Γ(N, V) :=
  letI : Module Γ(Y', W) Γ(N, V) := Module.compHom _ (i.appLE W V h).hom
  { chartRestrict M e h with map_smul' := chartRestrict_smul M e h }

/-- **Sections of a quasi-coherent module over nested affine opens.** For affine opens
`V ⊆ Y` and `W ⊆ Y'` with `i(V) ⊆ W`, the restriction `Γ(M, W) → Γ(N, V)` is a base change
along `Γ(Y', W) → Γ(Y, V)`. -/
theorem isBaseChange_chartRestrictₗ [M.IsQuasicoherent] {W : Y'.Opens} {V : Y.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ i ⁻¹ᵁ W) :
    letI : Algebra Γ(Y', W) Γ(Y, V) := (i.appLE W V h).hom.toAlgebra
    letI : Module Γ(Y', W) Γ(N, V) := Module.compHom _ (i.appLE W V h).hom
    letI : IsScalarTower Γ(Y', W) Γ(Y, V) Γ(N, V) := IsScalarTower.of_compHom _ _ _
    IsBaseChange Γ(Y, V) (chartRestrictₗ M e h) := by
  have hle := image_le_of_le_preimage h
  let : Algebra Γ(Y', W) Γ(Y, V) := (i.appLE W V h).hom.toAlgebra
  let : Module Γ(Y', W) Γ(N, V) := Module.compHom _ (i.appLE W V h).hom
  let : IsScalarTower Γ(Y', W) Γ(Y, V) Γ(N, V) := IsScalarTower.of_compHom _ _ _
  let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.algebraOfLE Y' hle
  let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE M hle
  let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isScalarTowerOfLE M hle
  have hf := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ M
    (hV.image_of_isOpenImmersion i) hW hle
  let : Algebra Γ(Y', i ''ᵁ V) Γ(Y, V) := (i.appIso V).hom.hom.toAlgebra
  let : Module Γ(Y', i ''ᵁ V) Γ(N, V) := Module.compHom _ (i.appIso V).hom.hom
  let : IsScalarTower Γ(Y', i ''ᵁ V) Γ(Y, V) Γ(N, V) := IsScalarTower.of_compHom _ _ _
  have htow : ∀ r : Γ(Y', W), (i.appIso V).hom.hom (Y'.presheaf.map (homOfLE hle).op r) =
      (i.appLE W V h).hom r := fun r => by
    rw [appLE_eq_map_comp_appIso h]
    rfl
  let : IsScalarTower Γ(Y', W) Γ(Y', i ''ᵁ V) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun r => (htow r).symm
  let : IsScalarTower Γ(Y', W) Γ(Y', i ''ᵁ V) Γ(N, V) :=
    ⟨fun r c n => by
      show ((i.appIso V).hom.hom (Y'.presheaf.map (homOfLE hle).op r * c)) • n =
        (i.appLE W V h).hom r • ((i.appIso V).hom.hom c • n)
      rw [map_mul, htow, mul_smul]⟩
  let : IsScalarTower Γ(Y', W) Γ(Y, V) Γ(N, V) := IsScalarTower.of_compHom _ _ _
  let σ : Γ(M, i ''ᵁ V) →ₗ[Γ(Y', i ''ᵁ V)] Γ(N, V) :=
    { toFun := fun x => e.inv.app V ((M.restrictAppIso i V).inv x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun c x => by
        rw [restrictAppIso_inv_smul, Scheme.Modules.Hom.app_smul]
        rfl }
  have hσ : Function.Bijective σ := by
    have h1 : Function.Bijective (M.restrictAppIso i V).inv :=
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso i V).inv)
    have h2 : Function.Bijective (e.inv.app V) :=
      (ConcreteCategory.bijective_of_isIso (e.inv.app V))
    exact h2.comp h1
  have hg : IsBaseChange Γ(Y, V) σ :=
    IsBaseChange.of_bijective_of_surjective_algebraMap
      (ConcreteCategory.bijective_of_isIso (i.appIso V).hom).2 hσ
  rw [show chartRestrictₗ M e h = (σ.restrictScalars Γ(Y', W)).comp
      (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ M hle) from
    LinearMap.ext fun _ => rfl]
  exact hf.comp hg

end Chart

/-! ### The finite-open factorization of a chart -/

section Factorization

variable {X Y Y' : Scheme.{u}} {f : Y ⟶ X} {g : Y' ⟶ X} {i : Y ⟶ Y'} [IsOpenImmersion i]
  (hig : i ≫ g = f)

omit [IsOpenImmersion i] in
include hig in
/-- An open of `Y` over `U` lies over `g⁻¹U` in `Y'`. -/
theorem le_preimage_preimage {U : X.Opens} {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U) :
    V ≤ i ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  subst hig
  exact hVU

omit [IsOpenImmersion i] in
include hig in
/-- `Γ(X, U) → Γ(Y', g⁻¹U) → Γ(Y, V)` is `Γ(X, U) → Γ(Y, V)`. -/
theorem appLE_comp_appLE_preimage {U : X.Opens} {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U) :
    g.appLE U (g ⁻¹ᵁ U) le_rfl ≫ i.appLE (g ⁻¹ᵁ U) V (le_preimage_preimage hig hVU) =
      f.appLE U V hVU := by
  subst hig
  rw [Scheme.Hom.appLE_comp_appLE]

variable [IsFinite g]

/-- **The finite-open factorization of a chart.** For affine opens `U ⊆ X` and `V ⊆ f⁻¹U`, the
map `Γ(X, U) → Γ(Y, V)` factors as `Γ(X, U) → Γ(Y', g⁻¹U) → Γ(Y, V)`, the first map finite and
the second the restriction along the open immersion `V → g⁻¹U`. -/
def chartFactorization (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) := (g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  letI : Algebra Γ(Y', g ⁻¹ᵁ U.1) Γ(Y, V.1) :=
    (i.appLE (g ⁻¹ᵁ U.1) V.1 (le_preimage_preimage hig hVU)).hom.toAlgebra
  have hle := le_preimage_preimage hig hVU
  have hφ : (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom =
      (Y'.presheaf.map (homOfLE (image_le_of_le_preimage hle)).op ≫ (i.appIso V.1).hom).hom := by
    rw [appLE_eq_map_comp_appIso hle]
  have hopen := isOpenEmbedding_and_bijective_awayMap_restrict_comp
    (V.2.image_of_isOpenImmersion i) (U.2.preimage g) (image_le_of_le_preimage hle) (i.appIso V.1)
  { middle := Γ(Y', g ⁻¹ᵁ U.1)
    commRingMiddle := inferInstance
    algebraMiddle := inferInstance
    algebraTarget := inferInstance
    scalarTower := IsScalarTower.of_algebraMap_eq fun a => by
      change (f.appLE U V hVU).hom a = (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom
        ((g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom a)
      rw [← appLE_comp_appLE_preimage hig hVU]
      rfl
    finite_middle := by
      have h := g.finite_app U.1 U.2
      rw [Scheme.Hom.app_eq_appLE] at h
      exact h
    isOpenEmbedding_comap := by
      change IsOpenEmbedding (PrimeSpectrum.comap (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom)
      rw [hφ]
      exact hopen.1
    awayMap_bijective := fun b hb => by
      change Function.Bijective (Localization.awayMap (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom b)
      change _ ⊆ Set.range (PrimeSpectrum.comap (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom) at hb
      rw [hφ] at hb ⊢
      exact hopen.2 b hb }

variable (M : Y'.Modules) [M.IsQuasicoherent]
  (t : (Scheme.Modules.pushforward g).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
  (hbij : ∀ U : X.affineOpens, Function.Bijective (traceDual g t U.1))
  {N : Y.Modules} (e : N ≅ M.restrict i)

/-- The identification `Γ(M, g⁻¹U) ≅ Hom_{Γ(X,U)}(Γ(Y', g⁻¹U), Γ(X, U))` given by the trace. -/
def traceDualEquiv (U : X.affineOpens) :
    letI : Algebra Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) := (g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
    Γ(M, g ⁻¹ᵁ U.1) ≃ₗ[Γ(Y', g ⁻¹ᵁ U.1)] Module.Dual Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) :=
  LinearEquiv.ofBijective (traceDual g t U.1) (hbij U)

/-- **The chart identification.** For affine opens `U ⊆ X`, `V ⊆ f⁻¹U`, the sections of `N` over
`V` are the algebraic relative dualizing module `Hom_A(B', A) ⊗_{B'} B` of the chart
factorization, through the trace. -/
def chartEquiv (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    dualizingModule (chartFactorization hig U V hVU) ≃ₗ[Γ(Y, V.1)] Γ(N, V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) := (g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hle := le_preimage_preimage hig hVU
  letI : Algebra Γ(Y', g ⁻¹ᵁ U.1) Γ(Y, V.1) := (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom.toAlgebra
  letI : Module Γ(Y', g ⁻¹ᵁ U.1) Γ(N, V.1) :=
    Module.compHom _ (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom
  letI : IsScalarTower Γ(Y', g ⁻¹ᵁ U.1) Γ(Y, V.1) Γ(N, V.1) := IsScalarTower.of_compHom _ _ _
  have hρ := isBaseChange_chartRestrictₗ M e V.2 (U.2.preimage g) hle
  (dualizingModuleCommEquiv (chartFactorization hig U V hVU)).trans
    (((traceDualEquiv M t hbij U).symm.baseChange Γ(Y', g ⁻¹ᵁ U.1) Γ(Y, V.1) _ _).trans
      hρ.equiv)

/-- The chart identification sends `φ ⊗ b` to `b` times the section induced by `φ`. -/
theorem chartEquiv_tmul (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ (φ : Module.Dual Γ(X, U.1) (chartFactorization hig U V hVU).middle) (b : Γ(Y, V.1)),
    chartEquiv hig M t hbij e U V hVU (dualizingModule.tmul _ φ b) =
      b • chartRestrict M e (le_preimage_preimage hig hVU)
        ((traceDualEquiv M t hbij U).symm φ) := by
  intro φ b
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) := (g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hle := le_preimage_preimage hig hVU
  let : Algebra Γ(Y', g ⁻¹ᵁ U.1) Γ(Y, V.1) := (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom.toAlgebra
  let : Module Γ(Y', g ⁻¹ᵁ U.1) Γ(N, V.1) :=
    Module.compHom _ (i.appLE (g ⁻¹ᵁ U.1) V.1 hle).hom
  let : IsScalarTower Γ(Y', g ⁻¹ᵁ U.1) Γ(Y, V.1) Γ(N, V.1) := IsScalarTower.of_compHom _ _ _
  have hρ := isBaseChange_chartRestrictₗ M e V.2 (U.2.preimage g) hle
  show hρ.equiv (((traceDualEquiv M t hbij U).symm.baseChange Γ(Y', g ⁻¹ᵁ U.1) Γ(Y, V.1) _ _)
    (b ⊗ₜ[Γ(Y', g ⁻¹ᵁ U.1)] φ)) = _
  exact hρ.equiv_tmul b ((traceDualEquiv M t hbij U).symm φ)

/-- The chart identification composed with the comparison of Tag 0BT1: the affine
identification `Γ(N, V) ≅ ω_F` for an arbitrary finite-open factorization `F`. -/
def ofFiniteTraceLocalEquiv [IsLocallyNoetherian X] (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      Γ(N, V.1) ≃ₗ[Γ(Y, V.1)] dualizingModule F :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  fun F => (chartEquiv hig M t hbij e U V hVU).symm.trans
    (dualizingModuleEquiv (chartFactorization hig U V hVU) F)

include hig t hbij e in
/-- The sections of `N` over the source chart of a chart pair form a finite module. -/
theorem moduleFinite_sections_of_chart [IsLocallyNoetherian X] (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) : Module.Finite Γ(Y, V.1) Γ(N, V.1) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := finite_dualizingModule (chartFactorization hig U V hVU)
  exact Module.Finite.equiv (chartEquiv hig M t hbij e U V hVU)

include e in
/-- A module isomorphic to the restriction of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_of_iso_restrict : N.IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent Y.ringCatSheaf) e.symm
    (inferInstanceAs (M.restrict i).IsQuasicoherent)

include hig t hbij e in
/-- `N` is coherent: its sections over the source charts are finite. -/
theorem isCoherent_ofFiniteTrace [IsLocallyNoetherian X] [IsLocallyNoetherian Y] :
    N.IsCoherent := by
  have := isQuasicoherent_of_iso_restrict M e
  obtain ⟨-, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn N
    ⟨AffineChartPair f, fun p => ((p.1).2).1,
      TopologicalSpace.IsOpenCover.mk (iSup_affineChartPair_eq_top f),
      fun p => ⟨((p.1).2).2,
        Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections
          N (p.1).2 (moduleFinite_sections_of_chart hig M t hbij e (p.1).1 (p.1).2 p.2)⟩⟩
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType N

omit [M.IsQuasicoherent] in
/-- `chartRestrict` after restricting the source section. -/
theorem chartRestrict_restrict_target {W W' : Y'.Opens} {V : Y.Opens} (hW : W' ≤ W)
    (h : V ≤ i ⁻¹ᵁ W') (m : Γ(M, W)) :
    chartRestrict M e h (M.presheaf.map (homOfLE hW).op m) =
      chartRestrict M e (h.trans (Scheme.Hom.preimage_mono i hW)) m := by
  rw [chartRestrict_apply, chartRestrict_apply, Stacks.Modules.res_comp]

/-- **Compatibility with shrinking the base chart.** -/
theorem ofFiniteTraceLocalEquiv_baseBasicOpen [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyQuasiFinite f] (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (a : Γ(X, U.1)) (hVa : V.1 ≤ f ⁻¹ᵁ (X.basicOpen a)) :
      let Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) :=
        (f.appLE U V hVU).hom.toAlgebra
      letI : Algebra Γ(X, Ua.1) Γ(Y, V.1) :=
        (f.appLE Ua V hVa).hom.toAlgebra
      letI : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
      letI : IsNoetherianRing Γ(X, U.1) :=
        IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(Y, V.1) :=
        IsLocallyNoetherian.component_noetherian V
      letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
        (RingHom.quasiFinite_algebraMap).mp
          (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
      letI : IsLocalization.Away a Γ(X, Ua.1) :=
        U.2.isLocalization_basicOpen a
      letI : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
        IsScalarTower.of_algebraMap_eq' (by
          change (f.appLE U V hVU).hom =
            ((f.appLE Ua V hVa).hom).comp
              (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
          rw [← CommRingCat.hom_comp, f.map_appLE hVa
            (homOfLE (X.basicOpen_le a)).op])
      ∀ (F : FiniteOpenFactorization.{u, u, u}
          Γ(X, U.1) Γ(Y, V.1))
        (G : FiniteOpenFactorization.{u, u, u}
          Γ(X, Ua.1) Γ(Y, V.1)) (s : Γ(N, V.1)),
        ofFiniteTraceLocalEquiv hig M t hbij e Ua V hVa G s =
          dualizingModule_equiv_of_isLocalization_away a F G
            (ofFiniteTraceLocalEquiv hig M t hbij e U V hVU F s) := by
  intro Ua F G s
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, Ua.1) Γ(Y, V.1) := (f.appLE Ua V hVa).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    (RingHom.quasiFinite_algebraMap).mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : IsLocalization.Away a Γ(X, Ua.1) := U.2.isLocalization_basicOpen a
  let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (f.appLE U V hVU).hom =
        ((f.appLE Ua V hVa).hom).comp (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
      rw [← CommRingCat.hom_comp, f.map_appLE hVa (homOfLE (X.basicOpen_le a)).op])
  let : IsNoetherianRing Γ(X, Ua.1) := IsLocallyNoetherian.component_noetherian Ua
  have hUa : Ua.1 ≤ U.1 := X.basicOpen_le a
  set F0 := chartFactorization hig U V hVU
  set F0' := chartFactorization hig Ua V hVa
  let : Algebra Γ(X, U.1) F0'.middle :=
    ((algebraMap Γ(X, Ua.1) F0'.middle).comp (algebraMap Γ(X, U.1) Γ(X, Ua.1))).toAlgebra
  let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) F0'.middle :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let r : F0.middle →ₐ[Γ(X, U.1)] F0'.middle :=
    { toRingHom := (Y'.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g hUa)).op).hom
      commutes' := fun c => by
        show (Y'.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g hUa)).op).hom
            ((g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom c) =
          (g.appLE Ua.1 (g ⁻¹ᵁ Ua.1) le_rfl).hom ((X.presheaf.map (homOfLE hUa).op).hom c)
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
          Scheme.Hom.map_appLE] }
  have hrloc : let := r.toRingHom.toAlgebra
      IsLocalization.Away (algebraMap Γ(X, U.1) F0.middle a) F0'.middle := by
    have h1 : algebraMap Γ(X, U.1) F0.middle a = (g.app U.1).hom a := by
      show (g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom a = _
      rw [Scheme.Hom.appLE_eq_app]
    rw [h1]
    exact (U.2.preimage g).isLocalization_of_eq_basicOpen ((g.app U.1).hom a)
      (homOfLE (Scheme.Hom.preimage_mono g hUa)) (Scheme.preimage_basicOpen g a)
  have hr : ∀ c : F0.middle,
      F0'.algebraTarget.algebraMap (r c) = F0.algebraTarget.algebraMap c := fun c => by
    show (i.appLE (g ⁻¹ᵁ Ua.1) V.1 _).hom
        ((Y'.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g hUa)).op).hom c) =
      (i.appLE (g ⁻¹ᵁ U.1) V.1 _).hom c
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) c) (Scheme.Hom.map_appLE i
      (le_preimage_preimage hig hVa) (homOfLE (Scheme.Hom.preimage_mono g hUa)).op)
  have key : ∀ x : dualizingModule F0,
      dualizingModule_equiv_of_isLocalization_away a F0 F0' x =
        (chartEquiv hig M t hbij e Ua V hVa).symm (chartEquiv hig M t hbij e U V hVU x) := by
    intro x
    induction x using dualizingModule.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul φ b =>
      set m := (traceDualEquiv M t hbij U).symm φ
      let ψ : Module.Dual Γ(X, Ua.1) F0'.middle :=
        traceDual g t Ua.1 (M.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g hUa)).op m)
      have hψ : ∀ c : F0.middle, ψ (r c) = algebraMap Γ(X, U.1) Γ(X, Ua.1) (φ c) := by
        intro c
        rw [show φ = traceDual g t U.1 m from
          ((traceDualEquiv M t hbij U).apply_symm_apply φ).symm]
        exact traceDual_restrict g t hUa m c
      rw [dualizingModule_equiv_of_isLocalization_away_tmul a F0 F0' r hrloc hr φ ψ hψ b,
        LinearEquiv.eq_symm_apply, chartEquiv_tmul, chartEquiv_tmul]
      congr 1
      have hψm : (traceDualEquiv M t hbij Ua).symm ψ =
          M.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g hUa)).op m :=
        (traceDualEquiv M t hbij Ua).symm_apply_apply _
      rw [hψm, chartRestrict_restrict_target]
  show dualizingModuleEquiv F0' G ((chartEquiv hig M t hbij e Ua V hVa).symm s) =
    dualizingModule_equiv_of_isLocalization_away a F G
      (dualizingModuleEquiv F0 F ((chartEquiv hig M t hbij e U V hVU).symm s))
  rw [← dualizingModule_equiv_of_isLocalization_away_natural a F0 F F0' G, key,
    LinearEquiv.apply_symm_apply]

omit [IsFinite g] [M.IsQuasicoherent] in
/-- `chartRestrict` followed by restriction of the target section. -/
theorem chartRestrict_restrict_source {W : Y'.Opens} {V V' : Y.Opens} (hV : V' ≤ V)
    (h : V ≤ i ⁻¹ᵁ W) (m : Γ(M, W)) :
    N.presheaf.map (homOfLE hV).op (chartRestrict M e h m) =
      chartRestrict M e (hV.trans h) m := by
  rw [chartRestrict_apply, chartRestrict_apply]
  have hnat := congrArg (fun φ => φ ((M.restrictAppIso i V).inv
    (M.presheaf.map (homOfLE (image_le_of_le_preimage h)).op m)))
    (e.inv.mapPresheaf.naturality (homOfLE hV).op)
  refine hnat.symm.trans ?_
  show e.inv.app V' (M.presheaf.map (homOfLE (Scheme.Hom.image_mono i hV)).op
      (M.presheaf.map (homOfLE (image_le_of_le_preimage h)).op m)) =
    e.inv.app V' (M.presheaf.map (homOfLE (image_le_of_le_preimage (hV.trans h))).op m)
  rw [Stacks.Modules.res_comp]

/-- **Compatibility with shrinking the source chart.** -/
theorem ofFiniteTraceLocalEquiv_basicOpen [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyQuasiFinite f] (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (b : Γ(Y, V.1)) :
      let W : Y.affineOpens := ⟨Y.basicOpen b, V.2.basicOpen b⟩
      let hWU : W.1 ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le b).trans hVU
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) :=
        (f.appLE U V hVU).hom.toAlgebra
      letI : Algebra Γ(X, U.1) Γ(Y, W.1) :=
        (f.appLE U W hWU).hom.toAlgebra
      letI : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
        (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
      letI : IsNoetherianRing Γ(X, U.1) :=
        IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(Y, V.1) :=
        IsLocallyNoetherian.component_noetherian V
      letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
        (RingHom.quasiFinite_algebraMap).mp
          (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
      letI : IsLocalization.Away b Γ(Y, W.1) :=
        V.2.isLocalization_basicOpen b
      letI : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
        IsScalarTower.of_algebraMap_eq' (by
          change (f.appLE U W hWU).hom =
            ((Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom).comp
              (f.appLE U V hVU).hom
          rw [← CommRingCat.hom_comp, ← f.appLE_map hVU
            (homOfLE (Y.basicOpen_le b)).op])
      ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
        (G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, W.1)),
        letI : Module Γ(Y, V.1) (dualizingModule G) :=
          Module.compHom (dualizingModule G)
            (algebraMap Γ(Y, V.1) Γ(Y, W.1))
        letI : IsScalarTower Γ(Y, V.1) Γ(Y, W.1)
            (dualizingModule G) :=
          IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
        ∃ (r : dualizingModule F →ₗ[Γ(Y, V.1)]
            dualizingModule G)
          (hr : IsLocalizedModule (Submonoid.powers b) r),
          (∀ s : Γ(N, V.1),
              ofFiniteTraceLocalEquiv hig M t hbij e U W hWU G
                ((Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ N
                  (Y.basicOpen_le b)) s) =
                r (ofFiniteTraceLocalEquiv hig M t hbij e U V hVU F s)) ∧
            (∀ m : dualizingModule G,
              localizedModule_dualizingModule_equiv b F G r hr m = m) := by
  intro W hWU F G
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    (RingHom.quasiFinite_algebraMap).mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : IsLocalization.Away b Γ(Y, W.1) := V.2.isLocalization_basicOpen b
  let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (f.appLE U W hWU).hom =
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom).comp (f.appLE U V hVU).hom
      rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE (Y.basicOpen_le b)).op])
  let : Module Γ(Y, V.1) (dualizingModule G) :=
    Module.compHom (dualizingModule G) (algebraMap Γ(Y, V.1) Γ(Y, W.1))
  let : IsScalarTower Γ(Y, V.1) Γ(Y, W.1) (dualizingModule G) :=
    IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
  have hWV : W.1 ≤ V.1 := Y.basicOpen_le b
  let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE N hWV
  let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isScalarTowerOfLE N hWV
  set eV := ofFiniteTraceLocalEquiv hig M t hbij e U V hVU F
  set eW := ofFiniteTraceLocalEquiv hig M t hbij e U W hWU G
  set res := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ N hWV
  let eWB : Γ(N, W.1) ≃ₗ[Γ(Y, V.1)] dualizingModule G := eW.restrictScalars Γ(Y, V.1)
  let r : dualizingModule F →ₗ[Γ(Y, V.1)] dualizingModule G :=
    (eWB.toLinearMap.comp res).comp eV.symm.toLinearMap
  have : N.IsQuasicoherent := isQuasicoherent_of_iso_restrict M e
  have hres_loc : IsLocalizedModule (Submonoid.powers b) res :=
    Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ N V.2 b rfl hWV
  have hr1 : IsLocalizedModule (Submonoid.powers b) (eWB.toLinearMap.comp res) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers b) res eWB
  have hr : IsLocalizedModule (Submonoid.powers b) r :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers b) _ eV.symm
  refine ⟨r, hr, fun s => ?_, ?_⟩
  · show eW (res s) = eW (res (eV.symm (eV s)))
    rw [LinearEquiv.symm_apply_apply]
  · have heVsymm : ∀ z, eV.symm (dualizingModuleEquiv (chartFactorization hig U V hVU) F z) =
        chartEquiv hig M t hbij e U V hVU z := fun z => by
      simp [eV, ofFiniteTraceLocalEquiv]
    have heW : ∀ z, eW (chartEquiv hig M t hbij e U W hWU z) =
        dualizingModuleEquiv (chartFactorization hig U W hWU) G z :=
      fun z => by simp [eW, ofFiniteTraceLocalEquiv]
    let r0 : dualizingModule (chartFactorization hig U V hVU) →ₗ[Γ(Y, V.1)] dualizingModule G :=
      r.comp (dualizingModuleEquiv (chartFactorization hig U V hVU) F).toLinearMap
    have hr0 : IsLocalizedModule (Submonoid.powers b) r0 :=
      IsLocalizedModule.of_linearEquiv_right (Submonoid.powers b) r
        (dualizingModuleEquiv (chartFactorization hig U V hVU) F)
    have hr0_tmul : ∀ (φ : Module.Dual Γ(X, U.1) (chartFactorization hig U V hVU).middle)
        (c : Γ(Y, V.1)), r0 (dualizingModule.tmul (chartFactorization hig U V hVU) φ c) =
          dualizingModuleEquiv (chartFactorization hig U W hWU) G
            (dualizingModule.tmul (chartFactorization hig U W hWU) φ
              (algebraMap _ Γ(Y, W.1) c)) := by
      intro φ c
      show eW (res (eV.symm (dualizingModuleEquiv (chartFactorization hig U V hVU) F
        (dualizingModule.tmul (chartFactorization hig U V hVU) φ c)))) = _
      rw [heVsymm, chartEquiv_tmul, map_smul, ← heW,
        chartEquiv_tmul hig M t hbij e U W hWU φ (algebraMap _ Γ(Y, W.1) c),
        show ∀ y : Γ(N, W.1), c • y = algebraMap Γ(Y, V.1) Γ(Y, W.1) c • y from fun _ => rfl]
      congr 2
      exact chartRestrict_restrict_source M e hWV _ _
    have hloc0 : ∀ y, localizedModule_dualizingModule_equiv b (chartFactorization hig U V hVU)
        (chartFactorization hig U W hWU) r0 hr0 (r0 y) =
        (dualizingModuleEquiv (chartFactorization hig U W hWU) G).symm (r0 y) := by
      intro y
      induction y using dualizingModule.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
      | tmul φ c =>
        have hr' : ∀ c' : (chartFactorization hig U W hWU).middle,
            algebraMap Γ(Y, V.1) Γ(Y, W.1)
              ((chartFactorization hig U V hVU).algebraTarget.algebraMap
                ((AlgEquiv.refl : (chartFactorization hig U V hVU).middle ≃ₐ[Γ(X, U.1)]
                  (chartFactorization hig U V hVU).middle) c')) =
              (chartFactorization hig U W hWU).algebraTarget.algebraMap c' := fun c' =>
          congrArg (fun φ => (CommRingCat.Hom.hom φ) c') (Scheme.Hom.appLE_map i
            (le_preimage_preimage hig hVU) (homOfLE hWV).op)
        rw [localizedModule_dualizingModule_equiv_tmul b (chartFactorization hig U V hVU)
            (chartFactorization hig U W hWU) r0 hr0 AlgEquiv.refl hr' φ c,
          hr0_tmul, LinearEquiv.symm_apply_apply]
        rfl
    have hfix : ∀ x, localizedModule_dualizingModule_equiv b F G r hr (r x) = r x := by
      intro x
      obtain ⟨y, rfl⟩ := (dualizingModuleEquiv (chartFactorization hig U V hVU) F).surjective x
      have hnat := localizedModule_dualizingModule_equiv_natural_in_source b
        (chartFactorization hig U V hVU) F (chartFactorization hig U W hWU) G r0 hr0
        r hr LinearMap.id (fun _ => rfl) (r0 y)
      show localizedModule_dualizingModule_equiv b F G r hr (r0 y) = r0 y
      rw [LinearMap.id_apply] at hnat
      rw [← hnat, hloc0, LinearEquiv.apply_symm_apply]
    have hext : ((localizedModule_dualizingModule_equiv b F G r hr).toLinearMap.restrictScalars
        Γ(Y, V.1)).comp r = (LinearMap.id).comp r :=
      LinearMap.ext hfix
    exact fun m =>
      LinearMap.congr_fun (IsLocalizedModule.linearMap_ext (Submonoid.powers b) r r hext) m

/-- **Relative dualizing module data from a trace on a finite morphism.** Let `f = i ≫ g` with
`i : Y ⟶ Y'` an open immersion and `g : Y' ⟶ X` finite, let `M` be a quasi-coherent
`𝒪_{Y'}`-module with a morphism `t : g_*M ⟶ 𝒪_X` such that on every affine open `U ⊆ X` the map
`Γ(M, g⁻¹U) → Hom_{Γ(X,U)}(Γ(Y', g⁻¹U), Γ(X, U))`, `s ↦ (b ↦ t(b • s))`, is bijective, and let
`N ≅ M|_Y`. Then `N` carries the chart data of the relative dualizing module of `f`
(Tag 0BVG): on a chart `V ⊆ f⁻¹U` its sections are `Hom_A(B', A) ⊗_{B'} B` with
`B' = Γ(Y', g⁻¹U)`. -/
def RelativeDualizingModuleData.ofFiniteTrace [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyQuasiFinite f] : RelativeDualizingModuleData f where
  sheaf := N
  isQuasicoherent := isQuasicoherent_of_iso_restrict M e
  isCoherent := isCoherent_ofFiniteTrace hig M t hbij e
  factorization U V hVU := ⟨chartFactorization hig U V hVU⟩
  localEquiv := ofFiniteTraceLocalEquiv hig M t hbij e
  localEquiv_natural U V hVU := by
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    intro F G s
    exact (congrArg (fun φ => φ ((chartEquiv hig M t hbij e U V hVU).symm s))
      (dualizingModuleEquiv_trans (chartFactorization hig U V hVU) F G)).symm
  localEquiv_baseBasicOpen := ofFiniteTraceLocalEquiv_baseBasicOpen hig M t hbij e
  localEquiv_basicOpen := ofFiniteTraceLocalEquiv_basicOpen hig M t hbij e

/-- **The affine identification of `ofFiniteTrace`.** The section of `N` over `V` obtained from a
section `s` of `M` over `g⁻¹U` by restriction is carried to the image under the comparison of
Tag 0BT1 of `t_s ⊗ 1`, where `t_s = (b ↦ t(b • s))`. -/
theorem RelativeDualizingModuleData.ofFiniteTrace_localEquiv [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [LocallyQuasiFinite f] (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) (s : Γ(M, g ⁻¹ᵁ U.1)),
      (RelativeDualizingModuleData.ofFiniteTrace hig M t hbij e).localEquiv U V hVU F
          (chartRestrict M e (le_preimage_preimage hig hVU) s) =
        dualizingModuleEquiv (chartFactorization hig U V hVU) F
          (dualizingModule.tmul (chartFactorization hig U V hVU) (traceDual g t U.1 s) 1) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  intro F s
  show dualizingModuleEquiv (chartFactorization hig U V hVU) F
      ((chartEquiv hig M t hbij e U V hVU).symm _) = _
  congr 1
  rw [LinearEquiv.symm_apply_eq, chartEquiv_tmul hig M t hbij e U V hVU (traceDual g t U.1 s) 1,
    one_smul]
  congr 1
  exact ((traceDualEquiv M t hbij U).symm_apply_apply s).symm

end Factorization

section Self

variable {X Y' : Scheme.{u}} {g : Y' ⟶ X} [IsFinite g] (M : Y'.Modules) [M.IsQuasicoherent]
  (t : (Scheme.Modules.pushforward g).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
  (hbij : ∀ U : X.affineOpens, Function.Bijective (traceDual g t U.1))
  {N : Y'.Modules} (e : N ≅ M.restrict (𝟙 Y'))

omit [IsFinite g] in
/-- `appLE` of the identity is the identity on sections. -/
theorem id_appLE_apply {W : Y'.Opens} (h : W ≤ (𝟙 Y') ⁻¹ᵁ W) (c : Γ(Y', W)) :
    (Scheme.Hom.appLE (𝟙 Y') W W h).hom c = c := by
  show (Y'.presheaf.map (homOfLE h).op).hom c = c
  exact congrArg (fun φ : Γ(Y', W) ⟶ Γ(Y', W) => φ.hom c) (Y'.presheaf.map_id (op W))

/-- **The affine identification of `ofFiniteTrace` for `g` itself on `g⁻¹U`.** For the finite
morphism `g` (with `i = 𝟙`), on the chart `g⁻¹U ⊆ g⁻¹U` and the factorization `A → B → B`, the
section of `N` corresponding to `s ∈ Γ(M, g⁻¹U)` is carried to `t_s ⊗ 1`, `t_s = (b ↦ t(b • s))`.
-/
theorem RelativeDualizingModuleData.ofFiniteTrace_localEquiv_selfFactorization
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y'] [LocallyQuasiFinite g]
    (U : X.affineOpens) :
    letI : Algebra Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) := (g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
    letI : Module.Finite Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) := by
      have h := g.finite_app U.1 U.2
      rw [Scheme.Hom.app_eq_appLE] at h
      exact h
    ∀ s : Γ(M, g ⁻¹ᵁ U.1),
      (RelativeDualizingModuleData.ofFiniteTrace (Category.id_comp g) M t hbij e).localEquiv U
          ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩ le_rfl (selfFactorization Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1))
          (chartRestrict M e (le_preimage_preimage (Category.id_comp g) le_rfl) s) =
        dualizingModule.tmul (selfFactorization Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1))
          (traceDual g t U.1 s) 1 := by
  let : Algebra Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) := (g.appLE U.1 (g ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  let : Module.Finite Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1) := by
    have h := g.finite_app U.1 U.2
    rwa [Scheme.Hom.app_eq_appLE] at h
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  intro s
  let V : Y'.affineOpens := ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩
  let F0 := chartFactorization (Category.id_comp g) U V le_rfl
  let S := selfFactorization Γ(X, U.1) Γ(Y', g ⁻¹ᵁ U.1)
  rw [RelativeDualizingModuleData.ofFiniteTrace_localEquiv]
  let rF : F0.middle →ₐ[Γ(X, U.1)] S.middle :=
    IsScalarTower.toAlgHom Γ(X, U.1) F0.middle Γ(Y', V.1)
  have hrF : ∀ c : Γ(Y', g ⁻¹ᵁ U.1), (rF c : Γ(Y', g ⁻¹ᵁ U.1)) = c := fun c =>
    id_appLE_apply _ c
  have hφ : (traceDual g t U.1 s : Module.Dual Γ(X, U.1) F0.middle) =
      (traceDual g t U.1 s : Module.Dual Γ(X, U.1) S.middle).comp rF.toLinearMap :=
    LinearMap.ext fun c => (congrArg (traceDual g t U.1 s) (hrF c)).symm
  have h := dualizingModuleEquiv_tmul F0 S S (Function.injective_id)
    rF (AlgHom.id Γ(X, U.1) S.middle) (fun c => hrF c ▸ (hrF c).symm ▸ rfl) (fun _ => rfl)
    (traceDual g t U.1 s : Module.Dual Γ(X, U.1) S.middle) 1
  refine (congrArg (dualizingModuleEquiv F0 S)
    (congrArg (fun φ => dualizingModule.tmul F0 φ 1) hφ)).trans (h.trans ?_)
  rfl

end Self

end Stacks.Discriminant
