module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamCech
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeChernPowers
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechTransfer
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyGlobalScalars

/-!
# The graded pieces of the de Rham complex of projective space

Let `A` be a commutative ring, `n = m + 1` and `p : ℙⁿ_A ⟶ Spec A` the structure morphism. The
graded pieces `Ωᵏ[-k]` of the brutal filtration of the relative de Rham complex are sheaves of
`p⁻¹𝒪_{Spec A}`-modules; their hypercohomology is the Hodge cohomology `H^{*-k}(ℙⁿ_A, Ωᵏ)` of
[Stacks, Tag 0FMI], through the identification of Čech cocycles across restriction of scalars.
This file records that identification, its compatibility with the coefficients `A`, and the
resulting vanishing of the hypercohomology of the graded pieces off the diagonal.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.gradedEquiv`: the identification
  `H^{p+k}(ℙⁿ_A, Ωᵏ[-k]) ≅ H^p(ℙⁿ_A, Ωᵏ)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.gradedEquiv_smul`: it is compatible with the
  coefficients.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.isZero_hypercohomology_graded`: the graded
  pieces have no hypercohomology off the diagonal.

## References

* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cech.Hypercohomology
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)
open Stacks.Cohomology.InvertibleDerived (smulHom)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge
open Stacks.ProjectiveSpace.Cohomology (coeffScalar)

variable (A : Type u) [CommRing A] (m : ℕ)

/-- **Multiplication by a global function of the base ring sheaf, read over the base ring
sheaf**: restricting the scalars of multiplication by the image of `s ∈ Γ(p⁻¹𝒪_{Spec A})` in
`Γ(ℙⁿ_A, 𝒪)` gives multiplication by `s`. -/
theorem restrictScalars_map_smulHom (s : (baseRingSheaf A m).obj.obj (op ⊤))
    (F : (projSpace A m).Modules) :
    (_root_.SheafOfModules.restrictScalars (baseRingHom A m)).map
        (smulHom (X := (projSpace A m).toRingedSpace)
          (((baseRingHom A m).hom.app (op ⊤)).hom s) F) =
      smulHom (X := SheafOfModules.baseRingedSpace (X := (projSpace A m).toRingedSpace)
          (baseRingSheaf A m)) s
        ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj F) := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
  have h := ConcreteCategory.congr_hom
    ((baseRingHom A m).hom.naturality (homOfLE (le_top : V.unop ≤ ⊤)).op) s
  exact (congrArg (fun r : (ringSheaf (projSpace A m).sheaf).obj.obj V =>
    (r • (show F.val.obj V from y) : F.val.obj V)) h).symm

/-- Čech cohomology computes the cohomology of `Ωᵏ` read over `p⁻¹𝒪_{Spec A}` and placed in any
degree. -/
theorem cechComputes_forms_restrictScalars (k : ℕ) (a : ℤ) :
    CechComputes (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
      ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m k)) a) :=
  have := isQuasicoherent_forms A m k
  CechComputesSheaf.singlePlus (baseRingSheaf A m)
    (cechComputesSheaf_restrictScalars_of_isQuasicoherent (projSpace A m) (baseRingHom A m)
      (forms A m k)) a

/-- **The identification `H^{p+k}(ℙⁿ_A, Ωᵏ[-k]) ≅ H^p(ℙⁿ_A, Ωᵏ)`**, the left side computed for
`Ωᵏ` read over `p⁻¹𝒪_{Spec A}` and placed in degree `k`, the right side for `Ωᵏ` as an
`𝒪_{ℙⁿ_A}`-module: both are computed by the same Čech cocycles. -/
def gradedEquiv (k p : ℕ) :
    hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
        ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m k)) (k : ℤ))
        ((p : ℤ) + (k : ℤ)) ≃+
      hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m k) 0) p :=
  restrictScalarsCechEquiv (baseRingHom A m) (forms A m k) (k : ℤ)
    (cechComputes_forms_restrictScalars A m k k) (cechComputesSheaf_forms A m k) p

/-- **The identification of the graded pieces is semilinear** along the structure map
`Γ(p⁻¹𝒪_{Spec A}) ⟶ Γ(ℙⁿ_A, 𝒪)`. -/
theorem gradedEquiv_smul (k p : ℕ) (s : SectionRing (ringSheaf (baseRingSheaf A m)) ⊤)
    (x : hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
        ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m k)) (k : ℤ))
        ((p : ℤ) + (k : ℤ))) :
    gradedEquiv A m k p (s • x) =
      ((baseRingHom A m).hom.app (op ⊤)).hom s • gradedEquiv A m k p x := by
  have h1 := restrictScalarsCechEquiv_hypercohomologyMap (baseRingHom A m) (forms A m k) (k : ℤ)
    (smulHom (X := (projSpace A m).toRingedSpace) (((baseRingHom A m).hom.app (op ⊤)).hom s)
      (forms A m k))
    (cechComputes_forms_restrictScalars A m k k) (cechComputesSheaf_forms A m k)
    (cechComputes_forms_restrictScalars A m k k) (cechComputesSheaf_forms A m k) p x
  have h2 := hypercohomologyMap_smulHom
    (X := SheafOfModules.baseRingedSpace (X := (projSpace A m).toRingedSpace) (baseRingSheaf A m))
    s ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m k)) (k : ℤ)
    (cechComputes_forms_restrictScalars A m k k) _ x
  have h3 := hypercohomologyMap_smulHom (X := (projSpace A m).toRingedSpace)
    (((baseRingHom A m).hom.app (op ⊤)).hom s) (forms A m k) 0 (cechComputesSheaf_forms A m k) p
    (gradedEquiv A m k p x)
  rw [restrictScalars_map_smulHom] at h1
  exact (congrArg (gradedEquiv A m k p) h2.symm).trans (h1.trans h3)

/-- **The graded pieces of the de Rham complex of `ℙⁿ_A` have no hypercohomology off the
diagonal**: `H^n(ℙⁿ_A, Ωᵖ[-p]) = 0` unless `n = 2p`. In degrees `n = p + q` this is the vanishing
of `H^q(ℙⁿ_A, Ωᵖ)` for `q ≠ p` of [Stacks, Tag 0FMI]; below degree `p`, and for `p < 0` where the
term vanishes, there is nothing to compute. -/
theorem isZero_hypercohomology_graded (p n : ℤ) (h : n ≠ 2 * p) :
    IsZero (hypercohomology (baseRingSheaf A m)
      (singlePlus (baseRingSheaf A m) ((deRhamComplexIntCech A m).X p) p) n) := by
  by_cases hp : p < 0
  · refine isZero_hypercohomology_singlePlus_of_isZero (baseRingSheaf A m) ?_ p n
    exact (SheafOfModules.deRhamComplex _ _).isZero_extend_X embeddingUpNat p
      fun i hi => by
        have : ((i : ℕ) : ℤ) = p := hi
        omega
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hp)
  by_cases hn : n < (j : ℤ)
  · exact isZero_hypercohomology_singlePlus_of_lt (baseRingSheaf A m) _ hn
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, n = (q : ℤ) + (j : ℤ) := ⟨(n - j).toNat, by omega⟩
  have hqj : j ≠ q := fun hc => h (by rw [hc]; ring)
  have hz : Subsingleton (hypercohomology (projSpace A m).sheaf
      (singlePlus (projSpace A m).sheaf (forms A m j) 0) q) :=
    (hodgeCohomologyIso A m j q).symm.toLinearEquiv.toEquiv.subsingleton_congr.mpr
      (ModuleCat.subsingleton_of_isZero (isZero_hodgeCohomology_of_ne_or_gt j q (Or.inl hqj)))
  rw [deRhamComplexIntTerm A m j]
  have := (gradedEquiv A m j q).toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham
