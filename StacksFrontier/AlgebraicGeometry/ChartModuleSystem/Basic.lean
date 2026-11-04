module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Modules on affine charts with localization restriction maps

This file sets up the data from which `AlgebraicGeometry.ChartModuleSystem.sheaf` glues a sheaf
of modules on a scheme `Y`: an index of affine charts of `Y` with a refinement relation, and a
module on each chart with restriction maps along refinements which are localizations.

The restriction maps are semilinear maps along the restriction of functions, and the localization
condition is stated as a base change condition (`LinearMap.IsBaseChangeAlong`): for `c'` refining
`c`, `ρ : M c → M c'` induces a bijection `Γ(Y, V c') ⊗[Γ(Y, V c)] M c ≃ M c'`. Since
`Γ(Y, V c')` is the localization of `Γ(Y, V c)` at the function `g` with `V c' = D(g)`, this is the
same as asking `ρ` to be the localization away from `g`
(`LinearMap.isBaseChangeAlong_iff_isLocalizedModule`); the base change form is the one that is
uniform with the morphisms along a morphism of schemes
(`AlgebraicGeometry.ChartModuleSystem.MapData`), whose maps are asked to be base changes too.

## Main definitions

* `LinearMap.restrictScalarsAlong`: a semilinear map along `σ : R →+* S`, read `R`-linearly.
* `LinearMap.IsBaseChangeAlong`: a semilinear map exhibits its target as the base change of its
  source along `σ`.
* `AlgebraicGeometry.Scheme.AffineChartIndex`: an index of affine charts of a scheme with a
  refinement relation, satisfying the covering axioms needed for gluing.
* `AlgebraicGeometry.ChartModuleSystem`: a module on each chart with restriction maps along
  refinements which are base changes.

## Main results

* `LinearMap.isBaseChangeAlong_iff_isLocalizedModule`: along a localization away from `g`, base
  change is localization away from `g`.
* `AlgebraicGeometry.Scheme.AffineChartIndex.isBasis`: the charts form a basis of the topology.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace LinearMap

section restrictScalarsAlong

variable {R S M N : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module S N] {σ : R →+* S}

/-- A `σ`-semilinear map read as an `R`-linear map, `N` being an `R`-module by restriction of
scalars along `σ`. -/
@[ega "II 1.7.2" "partial"]
def restrictScalarsAlong (f : M →ₛₗ[σ] N) :
    letI : Module R N := Module.compHom N σ
    M →ₗ[R] N :=
  letI : Module R N := Module.compHom N σ
  { toFun := f, map_add' := f.map_add, map_smul' := f.map_smulₛₗ }

/-- `LinearMap.restrictScalarsAlong` does not change the underlying function. -/
@[simp] theorem restrictScalarsAlong_apply (f : M →ₛₗ[σ] N) (m : M) :
    f.restrictScalarsAlong m = f m :=
  rfl

end restrictScalarsAlong

variable {R S M N : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N] {σ : R →+* S}

/-- A `σ`-semilinear map `f : M → N` *exhibits `N` as the base change of `M` along `σ`*: with `S`
an `R`-algebra through `σ`, the induced `S`-linear map `S ⊗[R] M → N` is bijective. -/
def IsBaseChangeAlong (f : M →ₛₗ[σ] N) : Prop :=
  letI := σ.toAlgebra
  letI : Module R N := Module.compHom N σ
  haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  IsBaseChange S f.restrictScalarsAlong

namespace IsBaseChangeAlong

variable {f : M →ₛₗ[σ] N} {Q : Type*} [AddCommGroup Q] [Module S Q]

/-- The universal property of a base change: a `σ`-semilinear map out of `M` into an `S`-module
extends uniquely to an `S`-linear map out of `N`. -/
noncomputable def lift (h : f.IsBaseChangeAlong) (g : M →ₛₗ[σ] Q) : N →ₗ[S] Q :=
  letI := σ.toAlgebra
  letI : Module R N := Module.compHom N σ
  letI : Module R Q := Module.compHom Q σ
  haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  IsBaseChange.lift h g.restrictScalarsAlong

/-- The lift of `g` extends `g`. -/
theorem lift_apply (h : f.IsBaseChangeAlong) (g : M →ₛₗ[σ] Q) (m : M) :
    h.lift g (f m) = g m :=
  let := σ.toAlgebra
  let : Module R N := Module.compHom N σ
  let : Module R Q := Module.compHom Q σ
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R S Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  IsBaseChange.lift_eq h g.restrictScalarsAlong m

/-- Two semilinear maps out of a base change agreeing on the image of `f` are equal. -/
theorem ext (h : f.IsBaseChangeAlong) {T : Type*} [Semiring T] {σ' : S →+* T} {P : Type*}
    [AddCommGroup P] [Module T P] {φ₁ φ₂ : N →ₛₗ[σ'] P} (hφ : ∀ m, φ₁ (f m) = φ₂ (f m)) :
    φ₁ = φ₂ := by
  let := σ.toAlgebra
  let : Module R N := Module.compHom N σ
  let : Module S P := Module.compHom P σ'
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have := IsBaseChange.algHom_ext (Q := P) h φ₁.restrictScalarsAlong φ₂.restrictScalarsAlong hφ
  exact LinearMap.ext fun n => LinearMap.congr_fun this n

end IsBaseChangeAlong

/-- **Along a localization, base change is localization.** If `σ : R → S` makes `S` a
localization of `R` away from `g`, a `σ`-semilinear map exhibits its target as the base change of
its source exactly when, read `R`-linearly, it is a localization away from `g`. -/
theorem isBaseChangeAlong_iff_isLocalizedModule (g : R)
    (hσ : letI := σ.toAlgebra; IsLocalization.Away g S) (f : M →ₛₗ[σ] N) :
    f.IsBaseChangeAlong ↔
      letI : Module R N := Module.compHom N σ
      IsLocalizedModule (Submonoid.powers g) f.restrictScalarsAlong := by
  let := σ.toAlgebra
  let : Module R N := Module.compHom N σ
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) S f.restrictScalarsAlong).symm


end LinearMap

namespace AlgebraicGeometry

/-- **An index of affine charts of a scheme `Y`.** A family `V` of affine opens of `Y`, indexed by
a type `ι`, with a refinement relation `Refines c' c` (read: `c'` refines `c`) such that

* a refinement of `c` is a basic open of `V c`;
* refinement is reflexive and transitive;
* the charts cover `Y`;
* every chart can be shrunk by refinement into any neighbourhood of any of its points;
* two charts have, near each point of their intersection, a common refinement.

These are the axioms under which a family of modules on the charts, with restriction maps along
refinements that are localizations, glues to a sheaf of modules on `Y`
(`AlgebraicGeometry.ChartModuleSystem`). -/
structure Scheme.AffineChartIndex (Y : Scheme.{u}) where
  /-- The index type of the charts. -/
  ι : Type u
  /-- The affine open of `Y` attached to a chart. -/
  V : ι → Y.affineOpens
  /-- `Refines c' c`: the chart `c'` refines the chart `c`. -/
  Refines : ι → ι → Prop
  /-- A refinement of `c` is a basic open of `V c`. -/
  exists_eq_basicOpen : ∀ {c' c : ι}, Refines c' c → ∃ g : Γ(Y, (V c).1), (V c').1 = Y.basicOpen g
  /-- Refinement is reflexive. -/
  refines_refl : ∀ c, Refines c c
  /-- Refinement is transitive. -/
  refines_trans : ∀ {c'' c' c : ι}, Refines c'' c' → Refines c' c → Refines c'' c
  /-- The charts cover `Y`. -/
  exists_mem : ∀ y : Y, ∃ c, y ∈ (V c).1
  /-- A chart can be shrunk by refinement into any neighbourhood of any of its points. -/
  exists_refines_le : ∀ {c : ι} {y : Y}, y ∈ (V c).1 → ∀ {W : Y.Opens}, y ∈ W →
    ∃ c', Refines c' c ∧ y ∈ (V c').1 ∧ (V c').1 ≤ W
  /-- Two charts have a common refinement near each point of their intersection. -/
  exists_refines_refines : ∀ {c₁ c₂ : ι} {y : Y}, y ∈ (V c₁).1 → y ∈ (V c₂).1 →
    ∃ c₃, Refines c₃ c₁ ∧ Refines c₃ c₂ ∧ y ∈ (V c₃).1

namespace Scheme.AffineChartIndex

variable {Y : Scheme.{u}} (I : Y.AffineChartIndex)

/-- The open of a chart is affine. -/
theorem isAffineOpen (c : I.ι) : IsAffineOpen (I.V c).1 :=
  (I.V c).2

/-- A refinement of a chart is contained in it. -/
theorem le_of_refines {c' c : I.ι} (h : I.Refines c' c) : (I.V c').1 ≤ (I.V c).1 := by
  obtain ⟨g, hg⟩ := I.exists_eq_basicOpen h
  rw [hg]
  exact Y.basicOpen_le g

/-- The restriction of functions from a chart to a refinement of it. -/
abbrev res {c' c : I.ι} (h : I.Refines c' c) : Γ(Y, (I.V c).1) →+* Γ(Y, (I.V c').1) :=
  (Y.presheaf.map (homOfLE (I.le_of_refines h)).op).hom

/-- Restricting functions along two successive refinements is restricting along the composite
refinement. -/
theorem res_res {c'' c' c : I.ι} (h' : I.Refines c'' c') (h : I.Refines c' c)
    (a : Γ(Y, (I.V c).1)) : I.res h' (I.res h a) = I.res (I.refines_trans h' h) a := by
  simp only [res, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Every neighbourhood of a point contains a chart around that point. -/
theorem exists_mem_le {y : Y} {W : Y.Opens} (hy : y ∈ W) : ∃ c, y ∈ (I.V c).1 ∧ (I.V c).1 ≤ W := by
  obtain ⟨c, hc⟩ := I.exists_mem y
  obtain ⟨c', -, hyc', hc'W⟩ := I.exists_refines_le hc hy
  exact ⟨c', hyc', hc'W⟩

/-- The charts form a basis of the topology of `Y`. -/
theorem isBasis : Opens.IsBasis (Set.range fun c => (I.V c).1) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {W y} hy => ?_
  obtain ⟨c, hyc, hcW⟩ := I.exists_mem_le hy
  exact ⟨_, ⟨c, rfl⟩, hyc, hcW⟩

end Scheme.AffineChartIndex

open Scheme

/-- **A system of modules on the affine charts of an index `I`, with localization restriction
maps.** For each chart `c` a `Γ(Y, V c)`-module `M c`; for each refinement `c'` of `c` a map
`ρ : M c → M c'`, semilinear along the restriction `Γ(Y, V c) → Γ(Y, V c')`; these are the
identity on a chart and compose along refinements, and each of them exhibits `M c'` as the base
change of `M c` along `Γ(Y, V c) → Γ(Y, V c')`.

Since `V c'` is a basic open `D(g)` of `V c` and `Γ(Y, D(g))` is the localization of
`Γ(Y, V c)` away from `g`, the last condition says that `ρ` is the localization of `M c` away from
`g` (`AlgebraicGeometry.ChartModuleSystem.isLocalizedModule_ρ`); conversely the base change
condition can be verified from that localization condition with
`AlgebraicGeometry.Scheme.AffineChartIndex.isBaseChangeAlong_iff_isLocalizedModule`. -/
structure ChartModuleSystem {Y : Scheme.{u}} (I : Y.AffineChartIndex) where
  /-- The module on a chart. -/
  M : I.ι → Type u
  /-- The additive structure of the module on a chart. -/
  [addCommGroup : ∀ c, AddCommGroup (M c)]
  /-- The `Γ(Y, V c)`-module structure of the module on a chart. -/
  [module : ∀ c, Module Γ(Y, (I.V c).1) (M c)]
  /-- The restriction map along a refinement. -/
  ρ : ∀ {c' c : I.ι} (h : I.Refines c' c), M c →ₛₗ[I.res h] M c'
  /-- Restriction to the chart itself is the identity. -/
  ρ_refl : ∀ (c : I.ι) (x : M c), ρ (I.refines_refl c) x = x
  /-- Restrictions compose along refinements. -/
  ρ_ρ : ∀ {c'' c' c : I.ι} (h' : I.Refines c'' c') (h : I.Refines c' c) (x : M c),
    ρ h' (ρ h x) = ρ (I.refines_trans h' h) x
  /-- Each restriction map is a base change along the restriction of functions. -/
  isBaseChangeAlong_ρ : ∀ {c' c : I.ι} (h : I.Refines c' c), (ρ h).IsBaseChangeAlong

attribute [instance] ChartModuleSystem.addCommGroup ChartModuleSystem.module

end AlgebraicGeometry
