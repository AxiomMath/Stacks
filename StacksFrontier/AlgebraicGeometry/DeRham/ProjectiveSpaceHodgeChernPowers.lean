module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineFormsMapSections
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeChernClassCech
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderBiproducts
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationLeibniz
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupBoundary

/-!
# The Hodge cohomology of projective space is free on the powers of `c₁^{Hodge}(𝒪(1))`

Let `A` be a commutative ring, `n = m + 1` and `ℙⁿ_A = Proj A[T₀, …, Tₙ]`. This file proves the
basis assertion of [Stacks, Tag 0FMI]: for `0 ≤ p ≤ n` the `A`-module `Hᵖ(ℙⁿ_A, Ωᵖ)` is free of
rank one with basis element `c₁^{Hodge}(𝒪(1))ᵖ`. (Its vanishing assertion, quoted from
[Stacks, Tag 0FUK], is `isZero_hodgeCohomology_of_ne_or_gt`.)

The powers are actual cup powers. The Hodge first Chern class `c₁^{Hodge}(𝒪(1))` of
[Stacks, Tag 0FLE] lives in the cohomology of `Ω` as a sheaf of abelian groups; it is read in the
cohomology of `Ω` as a sheaf of modules through the identification of first cohomology computed on
Čech cocycles (`Stacks.Cech.Hypercohomology.abelianToModuleH1`, [Stacks, Tag 03FD] in degree
one), giving `hodgeFirstChernClassModule`. Then `c⁰ = 1 ∈ H⁰(ℙⁿ_A, Ω⁰)` and
`c^{p+1} = cᵖ ∪ c₁^{Hodge}(𝒪(1))`, for the cup product of [Stacks, Section 01FP] attached to the
wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}` (`chernPowR2`, `hodgeChernPow`).

The proof is the source's. On the standard covering the boundary of `1 ∈ H⁰(ℙⁿ_A, 𝒪)` along the
Euler sequence is the Čech class of `d log(T_{i₁}/T_{i₀})`, which is `c₁^{Hodge}(𝒪(1))`
(`boundary_euler_one`). [Stacks, Tag 07MC], applied to the filtration sequence
`0 ⟶ Ω^{p+1} ⟶ ⋀^{p+1}(𝒪(-1)^{⊕ (n+1)}) ⟶ Ωᵖ ⟶ 0` and the Euler sequence, with the scalar
action, the product `⋀^{p+1} E × E ⟶ Ω^{p+1}` and the wedge product as pairings, shows that the
boundary of the filtration sequence is `x ↦ ±(x ∪ c₁^{Hodge}(𝒪(1)))` (`boundary_wedgeSC`); the
squares commute by the Leibniz rule for the Koszul contraction. The middle term is acyclic, so
that boundary is an isomorphism carrying `cᵖ` to `±c^{p+1}`, and the induction starts from
`H⁰(ℙⁿ_A, 𝒪) = A`, of which `1` is a basis because it is a unit for the cup product.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.wedgePairing`: the wedge product
  `Ωᵖ × Ω ⟶ Ω^{p+1}` as a pairing of sheaves placed in degree zero.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.chernPowR2`: the powers
  `c₁^{Hodge}(𝒪(1))ᵖ`, in hypercohomology.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.hodgeChernPow`: the powers, in `Hᵖ(ℙⁿ_A, Ωᵖ)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.boundary_wedgeSC`: the boundary of the
  filtration sequence is, up to sign, the cup product with `c₁^{Hodge}(𝒪(1))`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.exists_basis_chernPow`: [Stacks, Tag 0FMI], the
  basis.

## References

* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Tag 0FUK](https://stacks.math.columbia.edu/tag/0FUK)
* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.Hypercohomology
open Stacks.Cech.LinearCupProduct (tensorPresheafModules)
open Stacks.Cohomology.CechSheaf (SectionRing)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.ProjectiveSpace.Cohomology

variable (A : Type u) [CommRing A] (m : ℕ)

/-! ### Čech cohomology computes the cohomology of the sheaves involved -/

section CechComputes

/-- The sheaves `Ωᵖ` of differential forms on `ℙⁿ_A` are quasi-coherent. -/
theorem isQuasicoherent_forms (p : ℕ) :
    SheafOfModules.IsQuasicoherent.{u, u, u} (R := (projSpace A m).ringCatSheaf) (forms A m p) :=
  (inferInstance : (Scheme.Modules.exteriorPower (X := projSpace A m)
    (Scheme.Hom.relativeDifferentials (projToSpecCoeff A (m + 1))) (p : ℤ)).IsQuasicoherent)

/-- `𝒪(-1)^{⊕ (n+1)}` is quasi-coherent. -/
theorem isQuasicoherent_twistMinusOneSum :
    SheafOfModules.IsQuasicoherent.{u, u, u} (R := (projSpace A m).ringCatSheaf)
      (twistMinusOneSum A (m + 1)) :=
  have : ∀ j, SheafOfModules.IsQuasicoherent.{u, u, u} (R := (projSpace A m).ringCatSheaf)
      (twistMinusOneFamily A (m + 1) j) := fun _ =>
    Stacks.ProjectiveCohomology.isQuasicoherent_twistingSheaf A (m + 1) (-1)
  Scheme.Modules.isQuasicoherent_biproduct (X := projSpace A m) (twistMinusOneFamily A (m + 1))

/-- The exterior powers of `𝒪(-1)^{⊕ (n+1)}` are quasi-coherent. -/
theorem isQuasicoherent_wedge (p : ℕ) :
    SheafOfModules.IsQuasicoherent.{u, u, u} (R := (projSpace A m).ringCatSheaf)
      (Scheme.Modules.exteriorPower (X := projSpace A m) (twistMinusOneSum A (m + 1)) (p : ℤ)) :=
  have := isQuasicoherent_twistMinusOneSum A m
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorPower (X := projSpace A m)
    (twistMinusOneSum A (m + 1)) p

/-- Čech cohomology computes the cohomology of `Ωᵖ` on `ℙⁿ_A`. -/
theorem cechComputesSheaf_forms (p : ℕ) :
    CechComputesSheaf (projSpace A m).sheaf (forms A m p) :=
  have := isQuasicoherent_forms A m p
  cechComputesSheaf_of_isQuasicoherent (projSpace A m) (forms A m p)

/-- Čech cohomology computes the cohomology of `Ω` on `ℙⁿ_A`. -/
theorem cechComputesSheaf_differentials :
    CechComputesSheaf (projSpace A m).sheaf (projDifferentials A (m + 1)) :=
  cechComputesSheaf_of_isQuasicoherent (projSpace A m) (projDifferentials A (m + 1))

/-- Čech cohomology computes the cohomology of `𝒪(-1)^{⊕ (n+1)}` on `ℙⁿ_A`. -/
theorem cechComputesSheaf_twistMinusOneSum :
    CechComputesSheaf (projSpace A m).sheaf (twistMinusOneSum A (m + 1)) :=
  have := isQuasicoherent_twistMinusOneSum A m
  cechComputesSheaf_of_isQuasicoherent (projSpace A m) (twistMinusOneSum A (m + 1))

/-- Čech cohomology computes the cohomology of `⋀ᵖ(𝒪(-1)^{⊕ (n+1)})` on `ℙⁿ_A`. -/
theorem cechComputesSheaf_wedge (p : ℕ) :
    CechComputesSheaf (projSpace A m).sheaf
      (Scheme.Modules.exteriorPower (X := projSpace A m) (twistMinusOneSum A (m + 1)) (p : ℤ)) :=
  have := isQuasicoherent_wedge A m p
  cechComputesSheaf_of_isQuasicoherent (projSpace A m) _

/-- Čech cohomology computes the cohomology of `𝒪` on `ℙⁿ_A`. -/
theorem cechComputesSheaf_unit :
    CechComputesSheaf (projSpace A m).sheaf
      (SheafOfModules.unit (ringSheaf (projSpace A m).sheaf)) :=
  cechComputesSheaf_of_isQuasicoherent (projSpace A m) (SheafOfModules.unit _)

end CechComputes

/-! ### The filtration sequences -/

section Filtration

/-- The sign `(-1)^{p+1}`. -/
abbrev wedgeSign (p : ℕ) : ℤ := (((p : ℤ) + 1).negOnePow : ℤ)

/-- **The filtration sequence `0 ⟶ Ω^{p+1} ⟶ ⋀^{p+1}(𝒪(-1)^{⊕ (n+1)}) ⟶ Ωᵖ ⟶ 0`** of the
Euler sequence, with its first arrow multiplied by the sign `(-1)^{p+1}`. -/
abbrev wedgeSC (p : ℕ) : ShortComplex (SheafOfModules.{u} (ringSheaf (projSpace A m).sheaf)) :=
  ShortComplex.mk (wedgeSign p • (ShortComplex.mk (C := SheafOfModules.{u} (ringSheaf _)) _ _
      (exteriorPowerMap_comp_eulerWedgeQuotient A (m + 1) p)).f)
    (ShortComplex.mk (C := SheafOfModules.{u} (ringSheaf _)) _ _
      (exteriorPowerMap_comp_eulerWedgeQuotient A (m + 1) p)).g
    (by rw [Preadditive.zsmul_comp, ShortComplex.zero, smul_zero])

/-- Multiplication by a unit of `ℤ`, as an automorphism. -/
def unitSMulIso {C : Type*} [Category* C] [Preadditive C] (X : C) (ε : ℤˣ) : X ≅ X where
  hom := (ε : ℤ) • 𝟙 X
  inv := (ε : ℤ) • 𝟙 X
  hom_inv_id := by rw [Preadditive.zsmul_comp, Category.id_comp, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]
  inv_hom_id := by rw [Preadditive.zsmul_comp, Category.id_comp, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]

/-- Multiplying twice by a unit of `ℤ` is the identity. -/
theorem zsmul_zsmul_unit {C : Type*} [Category* C] [Preadditive C] {X Y : C} (ε : ℤˣ)
    (f : X ⟶ Y) : (ε : ℤ) • (ε : ℤ) • f = f := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

/-- The filtration sequence `0 ⟶ Ω^{p+1} ⟶ ⋀^{p+1}(𝒪(-1)^{⊕ (n+1)}) ⟶ Ωᵖ ⟶ 0`, with its first arrow
multiplied by `(-1)^{p+1}`, is short exact. -/
theorem shortExact_wedgeSC (p : ℕ) : (wedgeSC A m p).ShortExact := by
  have h := shortExact_eulerWedgeFiltration A (m + 1) p
  refine ShortComplex.shortExact_of_iso ?_ h
  refine ShortComplex.isoMk (unitSMulIso _ (((p : ℤ) + 1).negOnePow)) (Iso.refl _) (Iso.refl _)
    ?_ (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
  refine (Preadditive.zsmul_comp _ _ _).trans ?_
  refine (congrArg (wedgeSign p • ·) (Category.id_comp _)).trans ?_
  exact (zsmul_zsmul_unit _ _).trans (Category.comp_id _).symm

end Filtration

/-! ### The pairings -/

section Pairings

/-- **The wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}`**, `(x, ω) ↦ x ∧ ω`. -/
def wedgeBilinear (p : ℕ) : Stacks.BilinearMap (forms A m p).val
    (projDifferentials A (m + 1)).val (forms A m (p + 1)).val :=
  ((Scheme.Modules.exteriorAlgebra (X := projSpace A m) (projDifferentials A (m + 1))).mul
    (p : ℤ) 1).compRight
      (Scheme.Modules.exteriorGenerator (X := projSpace A m) (projDifferentials A (m + 1))).val

/-- **The wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}`**, as a pairing of the sheaves placed in degree
zero; the cup product it induces is `x ∪ c ∈ H^{p+1}(ℙⁿ_A, Ω^{p+1})` for `x ∈ Hᵖ(ℙⁿ_A, Ωᵖ)` and
`c ∈ H¹(ℙⁿ_A, Ω)`. -/
def wedgePairing (p : ℕ) : Pairing (projSpace A m).sheaf
    (singlePlus (projSpace A m).sheaf (forms A m p) 0)
    (singlePlus (projSpace A m).sheaf (projDifferentials A (m + 1)) 0)
    (singlePlus (projSpace A m).sheaf (forms A m (p + 1)) 0) :=
  singlePairing (bilinearPairing (wedgeBilinear A m p))

/-- The product `⋀^{p+1} E × E ⟶ Ω^{p+1}`, `(g, e) ↦ q_{p+1}(g ∧ e)`, for
`E = 𝒪(-1)^{⊕ (n+1)}`. -/
def middleBilinear (p : ℕ) : Stacks.BilinearMap
    (Scheme.Modules.exteriorPower (X := projSpace A m) (twistMinusOneSum A (m + 1))
      ((p + 1 : ℕ) : ℤ)).val (twistMinusOneSum A (m + 1)).val (forms A m (p + 1)).val :=
  (((Scheme.Modules.exteriorAlgebra (X := projSpace A m) (twistMinusOneSum A (m + 1))).mul
    ((p + 1 : ℕ) : ℤ) 1).compRight
      (Scheme.Modules.exteriorGenerator (X := projSpace A m)
          (twistMinusOneSum A (m + 1))).val).postcomp
    (eulerWedgeQuotient A (m + 1) (p + 1)).val

/-- The product `⋀^{p+1} E × E ⟶ Ω^{p+1}` as a pairing of the sheaves placed in degree zero. -/
def middlePairing (p : ℕ) : Pairing (projSpace A m).sheaf
    (singlePlus (projSpace A m).sheaf
      (Scheme.Modules.exteriorPower (X := projSpace A m) (twistMinusOneSum A (m + 1))
        ((p + 1 : ℕ) : ℤ)) 0)
    (singlePlus (projSpace A m).sheaf (twistMinusOneSum A (m + 1)) 0)
    (singlePlus (projSpace A m).sheaf (forms A m (p + 1)) 0) :=
  singlePairing (bilinearPairing (middleBilinear A m p))

end Pairings

/-! ### The boundary of the filtration sequence is the cup product with `c₁^{Hodge}(𝒪(1))` -/

section Boundary

/-- The scalar action on `Ω^{p+1}` and the product `⋀^{p+1} E × E ⟶ Ω^{p+1}` are compatible with
the first arrow of the filtration sequence and the Euler surjection: the first square of
[Stacks, Tag 07MC]. -/
theorem compat_scalar_middle (p : ℕ) (a b n : ℤ) (hn : a + b = n) :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf (projSpace A m).sheaf) ⊤)).obj
        (((Stacks.Cech.Refinement.sectionsComplex (projSpace A m).sheaf).obj
          (singlePlus (projSpace A m).sheaf (forms A m (p + 1)) 0).obj).X a)).map
        (((Stacks.Cech.Refinement.sectionsComplex (projSpace A m).sheaf).map
          (singlePlusMap (projSpace A m).sheaf (eulerSurjection A (m + 1))).hom).f b) ≫
        (scalarPairing (projSpace A m).sheaf (forms A m (p + 1))).μ a b n hn =
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf (projSpace A m).sheaf) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex (projSpace A m).sheaf).map
            (singlePlusMap (projSpace A m).sheaf (wedgeSC A m p).f).hom).f a)).app
          (((Stacks.Cech.Refinement.sectionsComplex (projSpace A m).sheaf).obj
            (singlePlus (projSpace A m).sheaf (twistMinusOneSum A (m + 1)) 0).obj).X b) ≫
        (middlePairing A m p).μ a b n hn :=
  singlePairing_compat (wedgeSC A m p).f (eulerSurjection A (m + 1)) _ _ (fun Z x y => by
    refine Eq.trans ?_ (congrArg (fun w => (eulerWedgeQuotient A (m + 1) (p + 1)).val.app Z
      (((Scheme.Modules.exteriorAlgebra (X := projSpace A m) (twistMinusOneSum A (m + 1))).mul
        ((p + 1 : ℕ) : ℤ) 1).app Z w ((Scheme.Modules.exteriorGenerator (X := projSpace A m)
          (twistMinusOneSum A (m + 1))).val.app Z y)))
      (SheafOfModules.zsmul_val_app (wedgeSign p) (Scheme.Modules.exteriorPowerMap
        (X := projSpace A m) (eulerFirstArrow A (m + 1)) ((p + 1 : ℕ) : ℤ)) Z x)).symm
    exact (eulerWedgeQuotient_mul_exteriorPowerMap A (m + 1) p Z.unop x y).symm) a b n hn

/-- The product `⋀^{p+1} E × E ⟶ Ω^{p+1}` and the wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}` are compatible
with the second arrow of the filtration sequence and the first arrow of the Euler sequence: the
second square of [Stacks, Tag 07MC]. -/
theorem compat_middle_wedge (p : ℕ) (a b n : ℤ) (hn : a + b = n) :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf (projSpace A m).sheaf) ⊤)).obj
        (((Stacks.Cech.Refinement.sectionsComplex (projSpace A m).sheaf).obj
          (singlePlus (projSpace A m).sheaf (Scheme.Modules.exteriorPower (X := projSpace A m)
            (twistMinusOneSum A (m + 1)) ((p + 1 : ℕ) : ℤ)) 0).obj).X a)).map
        (((Stacks.Cech.Refinement.sectionsComplex (projSpace A m).sheaf).map
          (singlePlusMap (projSpace A m).sheaf (eulerFirstArrow A (m + 1))).hom).f b) ≫
        (middlePairing A m p).μ a b n hn =
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf (projSpace A m).sheaf) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex (projSpace A m).sheaf).map
            (singlePlusMap (projSpace A m).sheaf (wedgeSC A m p).g).hom).f a)).app
          (((Stacks.Cech.Refinement.sectionsComplex (projSpace A m).sheaf).obj
            (singlePlus (projSpace A m).sheaf (projDifferentials A (m + 1)) 0).obj).X b) ≫
        (wedgePairing A m p).μ a b n hn :=
  singlePairing_compat (wedgeSC A m p).g (eulerFirstArrow A (m + 1)) _ _ (fun Z w z =>
    eulerWedgeQuotient_mul_eulerFirstArrow A (m + 1) p Z.unop w z) a b n hn

/-- **The boundary of the filtration sequence is, up to the sign `(-1)^{p+1}`, the cup product
with `c₁^{Hodge}(𝒪(1))`**: for `x ∈ Hᵖ(ℙⁿ_A, Ωᵖ)`,
`∂ x = (-1)^{p+1} (x ∪ c₁^{Hodge}(𝒪(1)))` in `H^{p+1}(ℙⁿ_A, Ω^{p+1})`. This is [Stacks, Tag 07MC]
for the filtration sequence and the Euler sequence, with the unit `1 ∈ H⁰(ℙⁿ_A, 𝒪)`, whose
boundary along the Euler sequence is `c₁^{Hodge}(𝒪(1))` (`boundary_euler_one`). -/
theorem boundary_wedgeSC (p : ℕ)
    (x : hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m p) 0)
      p) :
    boundary (projSpace A m).sheaf (singlePlusSC (projSpace A m).sheaf (wedgeSC A m p))
        (shortExact_singlePlusSC (projSpace A m).sheaf (shortExact_wedgeSC A m p)) p (p + 1) rfl
        x =
      wedgeSign p • cup (projSpace A m).sheaf (cechComputesSheaf_forms A m p)
        (cechComputesSheaf_differentials A m) (wedgePairing A m p) p (0 + 1) (p + 0 + 1)
        (by omega) x (hodgeFirstChernClassModule A m) := by
  have key := cup_boundary_of_cechComputes (projSpace A m).sheaf
    (singlePlusSC (projSpace A m).sheaf (wedgeSC A m p))
    (shortExact_singlePlusSC (projSpace A m).sheaf (shortExact_wedgeSC A m p))
    (singlePlusSC (projSpace A m).sheaf (eulerSC A m))
    (shortExact_singlePlusSC (projSpace A m).sheaf (shortExact_eulerSC A m))
    (singlePlus (projSpace A m).sheaf (forms A m (p + 1)) 0)
    (scalarPairing (projSpace A m).sheaf (forms A m (p + 1))) (middlePairing A m p)
    (wedgePairing A m p) (compat_scalar_middle A m p) (compat_middle_wedge A m p)
    (cechComputesSheaf_forms A m (p + 1)) (cechComputesSheaf_wedge A m (p + 1))
    (cechComputesSheaf_forms A m p) (cechComputesSheaf_unit A m)
    (cechComputesSheaf_twistMinusOneSum A m) (cechComputesSheaf_differentials A m) (p : ℤ) 0 x
    (sectionClass (SheafOfModules.unit (ringSheaf (projSpace A m).sheaf))
      (1 : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj (op ⊤)))
  rw [boundary_euler_one] at key
  refine Eq.trans ?_ key
  exact (cup_scalarPairing_sectionClass_one (forms A m (p + 1))
    (cechComputesSheaf_forms A m (p + 1)) (cechComputesSheaf_unit A m) ((p : ℤ) + 1) _).symm

end Boundary

/-! ### The powers of the Hodge first Chern class of `𝒪(1)` -/

section Powers

/-- The unit section `1` of `Ω⁰_{ℙⁿ_A/A} = 𝒪`. -/
def unitForm : (forms A m 0).val.obj (op ⊤) :=
  (Scheme.Hom.relativeDifferentialFormsZeroIso (projToSpecCoeff A (m + 1))).inv.val.app (op ⊤)
    (1 : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj (op ⊤))

/-- **The powers `c₁^{Hodge}(𝒪(1))ᵖ ∈ Hᵖ(ℙⁿ_A, Ωᵖ)`**, in the cohomology of sheaves of modules:
`c⁰` is the class of the unit section `1` of `Ω⁰ = 𝒪`, and `c^{p+1} = cᵖ ∪ c₁^{Hodge}(𝒪(1))`, the
cup product of [Stacks, Section 01FP] for the wedge product `Ωᵖ × Ω ⟶ Ω^{p+1}`. Here
`c₁^{Hodge}(𝒪(1))` is `hodgeFirstChernClassModule`, the image of the Hodge first Chern class of
[Stacks, Tag 0FLE] in the cohomology of `Ω` as a sheaf of modules. -/
def chernPowR2 : (p : ℕ) → hypercohomology (projSpace A m).sheaf
    (singlePlus (projSpace A m).sheaf (forms A m p) 0) p
  | 0 => sectionClass (forms A m 0) (unitForm A m)
  | p + 1 => cup (projSpace A m).sheaf (cechComputesSheaf_forms A m p)
      (cechComputesSheaf_differentials A m) (wedgePairing A m p) p 1 ((p + 1 : ℕ) : ℤ)
      (by push_cast; ring) (chernPowR2 p) (hodgeFirstChernClassModule A m)

/-- The cohomology `Hᵠ(ℙⁿ_A, Ωᵖ)` computed by Mathlib's right derived functors is the
hypercohomology of `Ωᵖ` placed in degree zero, as `A`-modules. -/
def hodgeCohomologyIso (p q : ℕ) :
    hodgeCohomology A m p q ≅ (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
      (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m p) 0)
        q) :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).mapIso
    (rightDerivedIsoHypercohomology (projSpace A m) (forms A m p) q)

/-- **The powers `c₁^{Hodge}(𝒪(1))ᵖ ∈ Hᵖ(ℙⁿ_A, Ωᵖ)` of the Hodge first Chern class of `𝒪(1)`**:
`chernPowR2`, read in the cohomology computed by right derived functors. -/
def hodgeChernPow (p : ℕ) : ↥(hodgeCohomology A m p p) :=
  (hodgeCohomologyIso A m p p).inv (chernPowR2 A m p)

end Powers

/-! ### The middle terms are acyclic -/

/-- **The middle term of the filtration sequence is acyclic**: `⋀^{p+1}(𝒪(-1)^{⊕ (n+1)})` is a sum
    of
copies of `𝒪(-(p+1))`, which has no cohomology for `p + 1 ≤ n` ([Stacks, Tag 01XT]). -/
theorem isZero_hypercohomology_wedge {p : ℕ} (hp : p ≤ m) (q : ℕ) :
    IsZero (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf
      (Scheme.Modules.exteriorPower (X := projSpace A m) (twistMinusOneSum A (m + 1))
        ((p + 1 : ℕ) : ℤ)) 0) q) :=
  (isZero_cohomologySheaf_eulerWedge (A := A) (m := m) (Nat.succ_pos p) (by omega) q).of_iso
    ((rightDerivedIsoHypercohomology (projSpace A m) _ q).symm ≪≫
      ((globalSections A m).rightDerived q).mapIso (eulerWedgeMiddleIso A m (p + 1)))

/-- **The boundary map of the filtration sequence**, `Hᵖ(ℙⁿ_A, Ωᵖ) ≅ H^{p+1}(ℙⁿ_A, Ω^{p+1})` for
`p ≤ n - 1`, the middle term `⋀^{p+1}(𝒪(-1)^{⊕ (n+1)})` being acyclic in degrees `p` and
`p + 1`. -/
def boundaryEquiv {p : ℕ} (hp : p ≤ m) :
    (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
        (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m p) 0)
          p) ≃ₗ[A]
      (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
        (hypercohomology (projSpace A m).sheaf
          (singlePlus (projSpace A m).sheaf (forms A m (p + 1)) 0) ((p + 1 : ℕ) : ℤ)) :=
  LinearEquiv.ofBijective ((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).map
    (boundary (projSpace A m).sheaf (singlePlusSC (projSpace A m).sheaf (wedgeSC A m p))
      (shortExact_singlePlusSC (projSpace A m).sheaf (shortExact_wedgeSC A m p)) p (p + 1)
        rfl)).hom
    (bijective_boundary_of_isZero (projSpace A m).sheaf _ _ p
      (isZero_hypercohomology_wedge A m hp p) (isZero_hypercohomology_wedge A m hp (p + 1)))

/-- The boundary of the filtration sequence carries `cᵖ` to `(-1)^{p+1} c^{p+1}`. -/
theorem boundaryEquiv_chernPowR2 {p : ℕ} (hp : p ≤ m) :
    boundaryEquiv A m hp (chernPowR2 A m p) = wedgeSign p • chernPowR2 A m (p + 1) :=
  boundary_wedgeSC A m p (chernPowR2 A m p)

/-! ### Degree zero -/

section DegreeZero

/-- **A rank-one free module with a right-unital product linear in the second factor is
generated by the unit.** If `M ≃ A`, `μ(g, u) = g` for every `g` and `μ` is `A`-linear in its
second factor, then `u = a • g` with `g` a generator, and `g = μ(g, a • g) = a • μ(g, g)` forces
`a` to be a unit. -/
theorem exists_basis_of_rightUnit {M : Type*} [AddCommGroup M] [Module A M] (e : M ≃ₗ[A] A)
    (u : M) (μ : M → M → M) (hμ : ∀ g, μ g u = g) (hlin : ∀ g g' (a : A), μ g (a • g') = a • μ g g')
        :
    ∃ b : Module.Basis (Fin 1) A M, b 0 = u := by
  set g := e.symm 1 with hg
  have hrep : ∀ x : M, x = e x • g := fun x => by
    rw [hg, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hu := hrep u
  have hgg := hrep (μ g g)
  have h1 : g = (e u * e (μ g g)) • g := by
    conv_lhs => rw [← hμ g, hu, hlin, hgg, smul_smul]
  have hunit : e u * e (μ g g) = 1 := by
    have := congrArg e h1
    rw [map_smul, hg, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one] at this
    exact this.symm
  let a : Aˣ := ⟨e u, e (μ g g), hunit, by rw [mul_comm]; exact hunit⟩
  refine ⟨((Module.Basis.singleton (Fin 1) A).map e.symm).unitsSMul fun _ => a, ?_⟩
  rw [Module.Basis.unitsSMul_apply, Module.Basis.map_apply, Module.Basis.singleton_apply,
    Units.smul_def]
  exact hu.symm

/-- `H⁰(ℙⁿ_A, Ω⁰) ≅ A`, in the cohomology computed by hypercohomology. -/
def hypercohomologyFormsZeroEquiv :
    (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
        (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m 0) 0)
          ((0 : ℕ) : ℤ)) ≃ₗ[A] A :=
  ((hodgeCohomologyIso A m 0 0).symm ≪≫
    (nonempty_hodgeCohomology_diag_iso (A := A) (m := m) 0 (Nat.zero_le _)).some).toLinearEquiv

/-- `H⁰(ℙⁿ_A, 𝒪) ≅ H⁰(ℙⁿ_A, Ω⁰)`, induced by `𝒪 ≅ Ω⁰`. -/
def hypercohomologyUnitEquivForms :
    (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
        (hypercohomology (projSpace A m).sheaf
          (singlePlus (projSpace A m).sheaf
            (SheafOfModules.unit (ringSheaf (projSpace A m).sheaf)) 0) 0) ≃ₗ[A]
      (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
        (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m 0) 0)
          ((0 : ℕ) : ℤ)) :=
  ((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).mapIso
    (hypercohomologySingleIso (projSpace A m).sheaf
      (Scheme.Hom.relativeDifferentialFormsZeroIso (projToSpecCoeff A (m + 1))).symm
          0)).toLinearEquiv

/-- **`c⁰ = 1` is a basis of `H⁰(ℙⁿ_A, Ω⁰)`.** The class `1 ∈ H⁰(ℙⁿ_A, 𝒪)` is a right unit for the
cup product with the scalar action (`cup_scalarPairing_sectionClass_one`), which is linear in its
second factor, and `H⁰(ℙⁿ_A, 𝒪) ≅ A` by [Stacks, Tag 0FUK]; so `1` is a basis
(`exists_basis_of_rightUnit`), and `𝒪 ≅ Ω⁰` carries it to `c⁰`. -/
theorem exists_basis_chernPowR2_zero :
    ∃ b : Module.Basis (Fin 1) A ((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
      (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m 0) 0)
        ((0 : ℕ) : ℤ))), b 0 = chernPowR2 A m 0 := by
  obtain ⟨b, hb⟩ := exists_basis_of_rightUnit A
    ((hypercohomologyUnitEquivForms A m).trans (hypercohomologyFormsZeroEquiv A m))
    (sectionClass (unitSheaf (projSpace A m).sheaf) (oneSection (projSpace A m).sheaf))
    (fun g g' => cup (projSpace A m).sheaf (cechComputesSheaf_unit A m)
      (cechComputesSheaf_unit A m) (scalarPairing (projSpace A m).sheaf (unitSheaf _)) 0 0 0
      (add_zero 0) g g')
    (fun g => cup_scalarPairing_sectionClass_one _ (cechComputesSheaf_unit A m)
      (cechComputesSheaf_unit A m) 0 g)
    (fun g g' a => cup_smul_right (projSpace A m).sheaf _ _ _ 0 0 0 (add_zero 0) g g'
      (coeffScalar A (m + 1) a))
  refine ⟨b.map (hypercohomologyUnitEquivForms A m), ?_⟩
  rw [Module.Basis.map_apply, hb]
  exact hypercohomologyMap_sectionClass _ _

end DegreeZero

/-! ### [Stacks, Tag 0FMI] -/

section Basis

/-- The induction step: a basis of `Hᵖ(ℙⁿ_A, Ωᵖ)` with first vector `cᵖ` gives one of
`H^{p+1}(ℙⁿ_A, Ω^{p+1})` with first vector `c^{p+1}`, because the boundary of the filtration
sequence is an isomorphism carrying `cᵖ` to `±c^{p+1}`. -/
theorem exists_basis_chernPowR2_succ {p : ℕ} (hp : p ≤ m)
    (b : Module.Basis (Fin 1) A ((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
      (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m p) 0)
        p)))
    (hb : b 0 = chernPowR2 A m p) :
    ∃ b' : Module.Basis (Fin 1) A ((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
      (hypercohomology (projSpace A m).sheaf
        (singlePlus (projSpace A m).sheaf (forms A m (p + 1)) 0) ((p + 1 : ℕ) : ℤ))),
      b' 0 = chernPowR2 A m (p + 1) := by
  have hD := boundaryEquiv_chernPowR2 A m hp
  rcases Int.units_eq_one_or (((p : ℤ) + 1).negOnePow) with hε | hε
  · refine ⟨b.map (boundaryEquiv A m hp), ?_⟩
    rw [Module.Basis.map_apply, hb, hD, wedgeSign, hε, Units.val_one, one_smul]
  · refine ⟨b.map ((boundaryEquiv A m hp).trans (LinearEquiv.neg A)), ?_⟩
    rw [Module.Basis.map_apply]
    change -(boundaryEquiv A m hp (b 0)) = _
    rw [hb, hD, wedgeSign, hε, Units.val_neg, Units.val_one, neg_one_smul]
    exact neg_neg _

/-- `cᵖ` is a basis of `Hᵖ(ℙⁿ_A, Ωᵖ)` for `0 ≤ p ≤ n`, in the cohomology computed by
hypercohomology. -/
theorem exists_basis_chernPowR2 (p : ℕ) (hp : p ≤ m + 1) :
    ∃ b : Module.Basis (Fin 1) A ((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
      (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m p) 0)
        p)), b 0 = chernPowR2 A m p := by
  induction p with
  | zero => exact exists_basis_chernPowR2_zero A m
  | succ p ih =>
    obtain ⟨b, hb⟩ := ih (by omega)
    exact exists_basis_chernPowR2_succ A m (by omega) b hb

/-- **[Stacks, Tag 0FMI], the basis.** For `0 ≤ p ≤ n` the `A`-module `Hᵖ(ℙⁿ_A, Ωᵖ)` is free of
rank one with basis element `c₁^{Hodge}(𝒪(1))ᵖ`, the `p`-th cup power of the Hodge first Chern
class of `𝒪(1)` (`hodgeChernPow`).

The proof is the source's. In degree zero `H⁰(ℙⁿ_A, 𝒪) = A` carries the unit `1` as a basis. The
boundary of `1` along the Euler sequence `0 ⟶ Ω ⟶ 𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪 ⟶ 0` is
`c₁^{Hodge}(𝒪(1))`, computed on Čech cocycles: both are the class of `d log(T_{i₁}/T_{i₀})` on the
standard covering (`boundary_euler_one`). By [Stacks, Tag 07MC] applied to the filtration sequence
`0 ⟶ Ω^{p+1} ⟶ ⋀^{p+1}(𝒪(-1)^{⊕ (n+1)}) ⟶ Ωᵖ ⟶ 0` and the Euler sequence, the boundary of the
filtration sequence is, up to sign, the cup product with `c₁^{Hodge}(𝒪(1))`
(`boundary_wedgeSC`); since the middle term is acyclic it is an isomorphism
`Hᵖ(ℙⁿ_A, Ωᵖ) ≅ H^{p+1}(ℙⁿ_A, Ω^{p+1})` carrying `c₁^{Hodge}(𝒪(1))ᵖ` to
`±c₁^{Hodge}(𝒪(1))^{p+1}`. -/
@[stacks 0FMI "for 0 ≤ p ≤ n the A-module H^p(ℙⁿ_A, Ω^p) is free of rank one with basis element
c₁^{Hodge}(𝒪(1))^p, the p-th cup power of the Hodge first Chern class of 𝒪(1)"]
theorem exists_basis_chernPow (p : ℕ) (hp : p ≤ m + 1) :
    ∃ b : Module.Basis (Fin 1) A ↥(hodgeCohomology A m p p), b 0 = hodgeChernPow A m p := by
  obtain ⟨b, hb⟩ := exists_basis_chernPowR2 A m p hp
  refine ⟨b.map (hodgeCohomologyIso A m p p).toLinearEquiv.symm, ?_⟩
  rw [Module.Basis.map_apply, hb]
  rfl

end Basis

end Stacks.AlgebraicGeometry.ProjectiveSpaceHodge
