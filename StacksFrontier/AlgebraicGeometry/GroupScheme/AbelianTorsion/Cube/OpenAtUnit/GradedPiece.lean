module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.GradedPieceAlgebra
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.LiftingCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientDerivedLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Cokernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplitting
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicArtinRees

/-!
# The graded piece `Iⁿ⁺¹ℱ / Iⁿ⁺²ℱ` of a module flat over the base

Let `g : X ⟶ Spec R` be a morphism of schemes, `I ⊆ R` an ideal and `ℱ` a quasi-coherent
`𝒪_X`-module whose sections over every affine open are flat `R`-modules. Choose
`r₁, …, r_d ∈ Iⁿ⁺¹` whose images form a basis of `Iⁿ⁺¹ / Iⁿ⁺²` over `R / I` (in the sense of
`Stacks.CubeOpenAtUnit.mem_smul_top_of_sum_smul_mem`). Then the sequence

`0 → (ℱ / Iℱ)ᵈ → ℱ / Iⁿ⁺²ℱ → ℱ / Iⁿ⁺¹ℱ → 0`,

whose first map is `(xₖ) ↦ ∑ rₖ xₖ`, is short exact.

## Main definitions

* `Stacks.CubeOpenAtUnit.quo`: `ℱ / Iᵏℱ` for the ideal sheaf `I · 𝒪_X`.
* `Stacks.CubeOpenAtUnit.mulMap`: multiplication by `rₖ`, `ℱ / Iℱ ⟶ ℱ / Iⁿ⁺²ℱ`.
* `Stacks.CubeOpenAtUnit.gradedShortComplex`: the sequence above.

## Main results

* `Stacks.CubeOpenAtUnit.gradedShortComplex_shortExact`: it is short exact.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open Stacks.Coherent (baseSectionHom baseIdealSheaf_ideal_eq_map)

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

universe u

namespace Stacks.CubeOpenAtUnit

/-- `𝒪_X`-modules have finite biproducts (`X.Modules` is abelian); a local instance, as in
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessResolution/Basic.lean`. -/
local instance hasFiniteBiproducts_modules (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-! ### Generalities on morphisms of modules on a scheme -/

section General

variable {X : Scheme.{u}}

/-- The sections of a composite of morphisms of `𝒪_X`-modules. -/
theorem comp_app_apply {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (U : X.Opens)
    (x : Γ(M, U)) : (f ≫ g).app U x = g.app U (f.app U x) := rfl

/-- Two morphisms of `𝒪_X`-modules agreeing on the sections over every affine open are equal. -/
theorem hom_ext_affine {M N : X.Modules} (φ ψ : M ⟶ N)
    (h : ∀ U : X.affineOpens, φ.app U.1 = ψ.app U.1) : φ = ψ := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  let N' : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  exact TopCat.Sheaf.hom_ext M.presheaf N' (B := fun U : X.affineOpens => U.1)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens)
    h

/-- The value of a finite sum of morphisms on a section. -/
theorem sum_app_apply {M N : X.Modules} {ι : Type*} (s : Finset ι) (φ : ι → (M ⟶ N))
    (U : X.Opens) (x : Γ(M, U)) : (∑ i ∈ s, φ i).app U x = ∑ i ∈ s, (φ i).app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    exact congrArg _ ih

/-- A section of a finite biproduct is the sum of its components. -/
theorem biproduct_app_eq_sum {d : ℕ} (f : Fin d → X.Modules) (U : X.Opens) (y : Γ(⨁ f, U)) :
    y = ∑ i, (biproduct.ι f i).app U ((biproduct.π f i).app U y) := by
  have h := congrArg (fun φ => φ.app U y) (biproduct.total (f := f))
  simp only [sum_app_apply, comp_app_apply] at h
  exact h.symm

/-- The components of a sum of sections of the summands of a biproduct. -/
theorem biproduct_π_app_sum {d : ℕ} (Q : X.Modules) (U : X.Opens) (z : Fin d → Γ(Q, U))
    (j : Fin d) :
    (biproduct.π (fun _ : Fin d => Q) j).app U
      (∑ i, (biproduct.ι (fun _ : Fin d => Q) i).app U (z i)) = z j := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [← comp_app_apply, biproduct.ι_π_self]
    rfl
  · intro i _ hij
    rw [← comp_app_apply, biproduct.ι_π_ne _ hij]
    rfl
  · simp

end General

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (.of R)) (I : Ideal R)

/-- The ring map `R ⟶ Γ(X, ⊤)` along `g`. -/
abbrev baseTop : R →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop).hom

/-- The restriction to `U` of the image of `a` under `baseTop g` is `baseSectionHom R g U a`. -/
theorem restrictTop_baseTop (a : R) (U : X.Opens) :
    AlgebraicGeometry.restrictTop (baseTop g a) U = baseSectionHom R g U a := rfl

variable (G : X.Modules)

/-- `ℱ / Iᵏℱ` for the ideal sheaf `I · 𝒪_X`. -/
abbrev quo (k : ℕ) : X.Modules := idealPowerQuotient (baseIdealSheaf R I g) k G

/-- The projection `ℱ ⟶ ℱ / Iᵏℱ`. -/
abbrev quoπ (k : ℕ) : G ⟶ quo g I G k :=
  cokernel.π (C := X.Modules) (idealPowerMultiple (baseIdealSheaf R I g) k G).ι

/-- Lowering the exponent, `ℱ / Iᵏ⁺¹ℱ ⟶ ℱ / Iᵏℱ`. -/
abbrev quoDrop (k : ℕ) : quo g I G (k + 1) ⟶ quo g I G k :=
  idealPowerQuotientDrop (baseIdealSheaf R I g) (Nat.le_succ k) G

/-- The projection to `ℱ / Iᵏ⁺¹ℱ` followed by `quoDrop` is the projection to `ℱ / Iᵏℱ`. -/
@[reassoc]
theorem quoπ_quoDrop (k : ℕ) : quoπ g I G (k + 1) ≫ quoDrop g I G k = quoπ g I G k :=
  idealPowerQuotientDrop_π _ _ _

/-- On sections, multiplication by `a` followed by the projection to `ℱ / Iᵏℱ` is the projection of
`baseSectionHom R g U a • y`. -/
private theorem globalSmul_comp_quoπ_app (k : ℕ) (a : R) (U : X.Opens) (y : Γ(G, U)) :
    (AlgebraicGeometry.globalSmul (baseTop g a) G ≫ quoπ g I G k).app U y =
      (quoπ g I G k).app U (baseSectionHom R g U a • y) := by
  rw [comp_app_apply, AlgebraicGeometry.globalSmul_app, restrictTop_baseTop]

variable [G.IsQuasicoherent]

/-- Over an affine open `U`, a section of `ℱ` maps to zero in `ℱ / Iᵏℱ` if and only if it lies in
`(I · Γ(X, U))ᵏ · Γ(ℱ, U)`. -/
theorem quoπ_app_eq_zero_iff (k : ℕ) (U : X.affineOpens) (s : Γ(G, U.1)) :
    (quoπ g I G k).app U.1 s = 0 ↔
      s ∈ (I.map (baseSectionHom R g U.1)) ^ k • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)) := by
  rw [cokernel_π_idealPowerMultiple_app_eq_zero_iff, baseIdealSheaf_ideal_eq_map]

/-- Over an affine open, the projection `ℱ ⟶ ℱ / Iᵏℱ` is surjective on sections. -/
theorem surjective_quoπ_app (k : ℕ) (U : X.affineOpens) :
    Function.Surjective ((quoπ g I G k).app U.1) :=
  AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen _ U.2

/-- The image of an element of `Iᵐ` in `Γ(X, U)` lies in the `m`-th power of the extended ideal. -/
theorem baseSectionHom_mem_pow (U : X.Opens) {a : R} {m : ℕ} (ha : a ∈ I ^ m) :
    baseSectionHom R g U a ∈ (I.map (baseSectionHom R g U)) ^ m := by
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

/-- Multiplication by an element `a` of `Iᵐ` kills `ℱ / Iᵐℱ`: `a · ℱ ⊆ Iᵐℱ`. -/
theorem globalSmul_comp_quoπ_eq_zero {a : R} {m : ℕ} (ha : a ∈ I ^ m) :
    AlgebraicGeometry.globalSmul (baseTop g a) G ≫ quoπ g I G m = 0 := by
  refine hom_ext_affine _ _ fun U => ?_
  ext y
  change (AlgebraicGeometry.globalSmul (baseTop g a) G ≫ quoπ g I G m).app U.1 y = 0
  rw [globalSmul_comp_quoπ_app, quoπ_app_eq_zero_iff]
  exact Submodule.smul_mem_smul (baseSectionHom_mem_pow g I U.1 ha) Submodule.mem_top

variable {n : ℕ}

/-- **Multiplication by `a ∈ Iⁿ⁺¹`**, `ℱ / Iℱ ⟶ ℱ / Iⁿ⁺²ℱ`: well defined because
`a · Iℱ ⊆ Iⁿ⁺²ℱ`. -/
def mulMap {a : R} (ha : a ∈ I ^ (n + 1)) : quo g I G 1 ⟶ quo g I G (n + 2) :=
  cokernel.desc (C := X.Modules) (idealPowerMultiple (baseIdealSheaf R I g) 1 G).ι
    (AlgebraicGeometry.globalSmul (baseTop g a) G ≫ quoπ g I G (n + 2)) (by
      refine Stacks.Coherent.idealPowerMultiple_ι_comp_eq_zero_of_app_smul _ _ _
        fun U b hb y => ?_
      change (quoπ g I G (n + 2)).app U.1
        ((AlgebraicGeometry.globalSmul (baseTop g a) G).app U.1 (b • y)) = 0
      rw [AlgebraicGeometry.globalSmul_app, restrictTop_baseTop, quoπ_app_eq_zero_iff, smul_smul]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [pow_succ]
      refine Ideal.mul_mem_mul (baseSectionHom_mem_pow g I U.1 ha) ?_
      rwa [baseIdealSheaf_ideal_eq_map, pow_one] at hb)

/-- On `ℱ`, `mulMap` is multiplication by `a` followed by the projection to `ℱ / Iⁿ⁺²ℱ`. -/
@[reassoc]
theorem quoπ_mulMap {a : R} (ha : a ∈ I ^ (n + 1)) :
    quoπ g I G 1 ≫ mulMap g I G ha =
      AlgebraicGeometry.globalSmul (baseTop g a) G ≫ quoπ g I G (n + 2) :=
  cokernel.π_desc _ _ _

/-- `mulMap` sends the class of a section `y` to the class of `a • y`. -/
theorem mulMap_app_quoπ_app {a : R} (ha : a ∈ I ^ (n + 1)) (U : X.Opens) (y : Γ(G, U)) :
    (mulMap g I G ha).app U ((quoπ g I G 1).app U y) =
      (quoπ g I G (n + 2)).app U (baseSectionHom R g U a • y) := by
  rw [← comp_app_apply, quoπ_mulMap, globalSmul_comp_quoπ_app]

/-- The image of `mulMap` lies in the kernel of `ℱ / Iⁿ⁺²ℱ ⟶ ℱ / Iⁿ⁺¹ℱ`. -/
theorem mulMap_quoDrop {a : R} (ha : a ∈ I ^ (n + 1)) :
    mulMap g I G ha ≫ quoDrop g I G (n + 1) = 0 := by
  refine (cancel_epi (quoπ g I G 1)).1 ?_
  rw [quoπ_mulMap_assoc, quoπ_quoDrop, comp_zero, globalSmul_comp_quoπ_eq_zero g I G ha]

/-- The kernel `Iⁿ⁺¹ℱ / Iⁿ⁺²ℱ` of `ℱ / Iⁿ⁺²ℱ ⟶ ℱ / Iⁿ⁺¹ℱ`. -/
abbrev gradedKer (n : ℕ) : X.Modules := kernel (C := X.Modules) (quoDrop g I G (n + 1))

/-- Multiplication by `a ∈ Iⁿ⁺¹` as a map `ℱ / Iℱ ⟶ Iⁿ⁺¹ℱ / Iⁿ⁺²ℱ`. -/
def mulKer {a : R} (ha : a ∈ I ^ (n + 1)) : quo g I G 1 ⟶ gradedKer g I G n :=
  kernel.lift (C := X.Modules) _ (mulMap g I G ha) (mulMap_quoDrop g I G ha)

/-- `mulKer` followed by the kernel inclusion is `mulMap`. -/
@[reassoc (attr := simp)]
theorem mulKer_ι {a : R} (ha : a ∈ I ^ (n + 1)) :
    mulKer g I G ha ≫ kernel.ι (C := X.Modules) _ = mulMap g I G ha :=
  kernel.lift_ι _ _ _

variable {d : ℕ} (r : Fin d → R) (hr : ∀ k, r k ∈ I ^ (n + 1))

/-- **The graded piece as a direct sum.** The map `(ℱ / Iℱ)ᵈ ⟶ Iⁿ⁺¹ℱ / Iⁿ⁺²ℱ`,
`(xₖ) ↦ ∑ rₖ xₖ`. -/
def gradedDesc : (⨁ fun _ : Fin d => quo g I G 1) ⟶ gradedKer g I G n :=
  biproduct.desc fun k => mulKer g I G (hr k)

/-- The value of `gradedDesc` on a section is the sum of `mulKer` applied to its components. -/
theorem gradedDesc_app (U : X.Opens) (w : Γ(⨁ fun _ : Fin d => quo g I G 1, U)) :
    (gradedDesc g I G r hr).app U w =
      ∑ k, (mulKer g I G (hr k)).app U
        ((biproduct.π (fun _ : Fin d => quo g I G 1) k).app U w) := by
  conv_lhs => rw [biproduct_app_eq_sum _ U w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← comp_app_apply, gradedDesc, biproduct.ι_desc]

/-- **The graded piece of a flat module is a direct sum of copies of `ℱ / Iℱ`.** If the sections
of `ℱ` over every affine open are flat over `R`, and the `rₖ ∈ Iⁿ⁺¹` form a basis of
`Iⁿ⁺¹ / Iⁿ⁺²` over `R / I`, the map `(ℱ / Iℱ)ᵈ ⟶ Iⁿ⁺¹ℱ / Iⁿ⁺²ℱ`, `(xₖ) ↦ ∑ rₖ xₖ`, is an
isomorphism. -/
theorem isIso_gradedDesc
    (hflat : ∀ U : X.affineOpens, (baseSectionHom R g U.1).Flat ∧
      Module.Flat Γ(X, U.1) Γ(G, U.1))
    (hspan : I ^ (n + 1) ≤ Ideal.span (Set.range r) ⊔ I ^ (n + 2))
    (hind : ∀ a : Fin d → R, ∑ k, a k * r k ∈ I ^ (n + 2) → ∀ k, a k ∈ I) :
    IsIso (gradedDesc g I G r hr) := by
  refine isIso_of_affine_sections_bijective _ fun U => ?_
  change Function.Bijective ((gradedDesc g I G r hr).app U.1)
  let A := Γ(X, U.1)
  let φU := baseSectionHom R g U.1
  let : Algebra R A := φU.toAlgebra
  let : Module R Γ(G, U.1) := Module.compHom Γ(G, U.1) φU
  have : IsScalarTower R A Γ(G, U.1) := ⟨fun a b m => by
    change (φU a * b) • m = φU a • b • m
    rw [mul_smul]⟩
  have : Module.Flat R A := (hflat U).1
  have : Module.Flat A Γ(G, U.1) := (hflat U).2
  have : Module.Flat R Γ(G, U.1) := Module.Flat.trans R A Γ(G, U.1)
  have hπι : Function.Injective ((kernel.ι (C := X.Modules) (quoDrop g I G (n + 1))).app U.1) :=
    Stacks.Algebraization.app_injective_of_mono _ inferInstance U.1
  let P := fun _ : Fin d => quo g I G 1
  -- the element of the biproduct with components the classes of `y k`
  let σ (y : Fin d → Γ(G, U.1)) : Γ(⨁ P, U.1) :=
    ∑ k, (biproduct.ι P k).app U.1 ((quoπ g I G 1).app U.1 (y k))
  -- the value of `gradedDesc` composed with the kernel inclusion
  have hval (y : Fin d → Γ(G, U.1)) :
      (kernel.ι (C := X.Modules) (quoDrop g I G (n + 1))).app U.1
          ((gradedDesc g I G r hr).app U.1 (σ y)) =
        (quoπ g I G (n + 2)).app U.1 (∑ k, algebraMap R A (r k) • y k) := by
    rw [gradedDesc_app, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [biproduct_π_app_sum, ← comp_app_apply, mulKer_ι, mulMap_app_quoπ_app]
    rfl
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, fun z => ?_⟩
  · choose y hy using fun k => surjective_quoπ_app g I G 1 U ((biproduct.π P k).app U.1 w)
    have hw' : w = σ y := by
      conv_lhs => rw [biproduct_app_eq_sum P U.1 w]
      simp only [σ, hy]
    have h0 := hval y
    rw [← hw', hw, map_zero, eq_comm, quoπ_app_eq_zero_iff] at h0
    have hk : ∀ k, (quoπ g I G 1).app U.1 (y k) = 0 := fun k => by
      rw [quoπ_app_eq_zero_iff, pow_one]
      exact mem_smul_top_of_sum_smul_mem I n r hind y h0 k
    simp only [hw', σ, hk, map_zero, Finset.sum_const_zero]
  · obtain ⟨y, hy⟩ := surjective_quoπ_app g I G (n + 2) U
      ((kernel.ι (C := X.Modules) (quoDrop g I G (n + 1))).app U.1 z)
    have hdrop : (quoπ g I G (n + 1)).app U.1 y = 0 := by
      rw [← quoπ_quoDrop, comp_app_apply, hy, ← comp_app_apply, kernel.condition]
      rfl
    rw [quoπ_app_eq_zero_iff] at hdrop
    obtain ⟨x, hx⟩ := exists_sub_sum_smul_mem I n r hspan y hdrop
    refine ⟨σ x, hπι ?_⟩
    rwa [hval, ← hy, eq_comm, ← sub_eq_zero, ← map_sub, quoπ_app_eq_zero_iff]

end Stacks.CubeOpenAtUnit

end
