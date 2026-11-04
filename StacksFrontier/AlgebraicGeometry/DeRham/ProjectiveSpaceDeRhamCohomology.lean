module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamGradedClasses

/-!
# The de Rham cohomology of projective space

Let `A` be a commutative ring and `n = m + 1 ≥ 1`. Write `ℙⁿ_A = Proj A[T₀, …, Tₙ]` with its
structure morphism `p : ℙⁿ_A ⟶ Spec A` and let `𝒪(1)` be the first Serre twist. Relative de Rham
cohomology `H^i_dR(ℙⁿ_A/A)` is the hypercohomology of the relative de Rham complex, read as an
`A`-module through the base.

This file proves [Stacks, Tag 0FMJ]: for `0 ≤ i ≤ n` the `A`-module `H^{2i}_dR(ℙⁿ_A/A)` is free
of rank one with basis element the `i`-th cup power `c₁^{dR}(𝒪(1))^i` of the de Rham first Chern
class of `𝒪(1)`, and in every other degree `H^i_dR(ℙⁿ_A/A)` vanishes.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.deRhamCohomology`: the `A`-module
  `H^i_dR(ℙⁿ_A/A)`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.deRhamFirstChernClassTwistingSheafOne`: the de
  Rham first Chern class `c₁^{dR}(𝒪(1))`, in the realization in which [Stacks, Tag 0FLE] forms it.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.chernPow`: its cup powers
  `c₁^{dR}(𝒪(1))^i ∈ H^{2i}_dR(ℙⁿ_A/A)`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.deRhamCohomologyEquiv`: the identification
  `H^{2i}_dR(ℙⁿ_A/A) ≅ Hⁱ(ℙⁿ_A, Ωⁱ)` given by the degeneration of the Hodge-to-de Rham spectral
  sequence.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.exists_basis_chernPow`: for `0 ≤ i ≤ n` the
  `A`-module `H^{2i}_dR(ℙⁿ_A/A)` is free of rank one with basis element `c₁^{dR}(𝒪(1))^i`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.isZero_deRhamCohomology`: in every degree not
  of the form `2i` with `0 ≤ i ≤ n` the de Rham cohomology of `ℙⁿ_A` over `A` vanishes.

## Implementation notes

The proof is the source's. By [Stacks, Tag 0FMI] the Hodge cohomology `H^q(ℙⁿ_A, Ωᵖ)` vanishes
unless `p = q ≤ n`, so the Hodge-to-de Rham spectral sequence of [Stacks, Section 0FM6]
degenerates; this is carried out without a spectral sequence, by induction along the brutal
filtration (`Stacks.Cech.Hypercohomology.collapseLinearEquiv`), and identifies `H^{2i}_dR` with
`H^{2i}(ℙⁿ_A, Ωⁱ[-i]) = Hⁱ(ℙⁿ_A, Ωⁱ)`. Under it `c₁^{dR}(𝒪(1))^i` goes to a unit multiple of
`c₁^{Hodge}(𝒪(1))^i` ([Stacks, Remark 0FME]), which is a basis by [Stacks, Tag 0FMI].

The de Rham first Chern class of `𝒪(1)` is the library's
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelianOf`, formed in the abelian-sheaf
realization of de Rham cohomology because `d log` is additive but not `𝒪`-linear; it is carried by
the comparison of [Stacks, Tag 01F1] to the realization over `p⁻¹𝒪_{Spec A}`, where the
`A`-module structure and the cup product of [Stacks, Section 0FM3] live
(`AlgebraicGeometry.Scheme.Hom.deRhamFirstChernClass`).

## References

* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Section 0FM6](https://stacks.math.columbia.edu/tag/0FM6)
* [Stacks Project, Remark 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Section 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Section 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cech.Hypercohomology
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge
open Stacks.ProjectiveSpace.Cohomology (coeffScalar)

/-! ### The setting -/

variable (A : Type u) [CommRing A] (m : ℕ)

/-- The three algebras of Stacks Section 17.21 on the sheaf of relative differentials of
`ℙⁿ_A ⟶ Spec A`, out of which the relative de Rham complex is formed. -/
abbrev deRhamAlgebras := Scheme.Hom.deRhamAlgebras (structureMorphism A m)

/-- The de Rham differential on the relative de Rham complex of `ℙⁿ_A ⟶ Spec A`. -/
abbrev deRhamDifferential :=
  AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras A m)

/-- **The `A`-module `H^i_dR(ℙⁿ_A/A)`** of relative de Rham cohomology of projective space: the
hypercohomology of the relative de Rham complex, a module over the global functions on `Spec A`
by [Stacks, Tag 0FL6], read over `A` along `A ≅ Γ(Spec A, 𝒪)`. -/
abbrev deRhamCohomology (i : ℤ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).obj
    (Scheme.Hom.deRhamCohomologyBaseModule (structureMorphism A m) i)

/-- **The de Rham first Chern class `c₁^{dR}(𝒪(1)) ∈ H²_dR(ℙⁿ_A/A)`** of the first Serre twist,
in the abelian-sheaf realization in which [Stacks, Tag 0FLE] constructs it. The twist is
invertible by `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isInvertible_twistingSheafOne`. -/
abbrev deRhamFirstChernClassTwistingSheafOne :
    ↥(AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian
      (deRhamAlgebras A m) (deRhamDifferential A m) 2) :=
  AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelianOf
    (deRhamAlgebras A m) (deRhamDifferential A m) _ (isInvertible_twistingSheafOne A m)

/-- **The powers `c₁^{dR}(𝒪(1))^i ∈ H^{2i}_dR(ℙⁿ_A/A)`** of the de Rham first Chern class of
`𝒪(1)`, for the cup product of [Stacks, Section 0FM3]: `c₁^{dR}(𝒪(1))⁰ = 1` and
`c₁^{dR}(𝒪(1))^{i+1} = c₁^{dR}(𝒪(1))^i ∪ c₁^{dR}(𝒪(1))` (`chernPow_zero`, `chernPow_succ`). -/
abbrev chernPow (i : ℕ) : ↥(deRhamCohomology A m (2 * (i : ℤ))) :=
  Scheme.Hom.deRhamChernPow (structureMorphism A m)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1)
    (isInvertible_twistingSheafOne A m) i

/-- The first Chern class entering `chernPow` is the de Rham first Chern class of `𝒪(1)`, carried
from the abelian-sheaf realization by the comparison of [Stacks, Tag 01F1]. -/
theorem deRhamFirstChernClass_eq :
    Scheme.Hom.deRhamFirstChernClass (structureMorphism A m)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1)
        (isInvertible_twistingSheafOne A m) =
      (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras A m)
        (deRhamDifferential A m) 2).hom
        ((SheafOfModules.deRhamCohomologyAbelianIso (deRhamAlgebras A m)
          (deRhamDifferential A m) 2).hom.hom (deRhamFirstChernClassTwistingSheafOne A m)) :=
  rfl

/-- The zeroth power is the unit `1 ∈ H⁰_dR(ℙⁿ_A/A)`. -/
theorem chernPow_zero : chernPow A m 0 = Scheme.Hom.deRhamUnit (structureMorphism A m) :=
  rfl

/-- **`c₁^{dR}(𝒪(1))^{i+1} = c₁^{dR}(𝒪(1))^i ∪ c₁^{dR}(𝒪(1))`.** -/
theorem chernPow_succ (i : ℕ) :
    chernPow A m (i + 1) =
      Scheme.Hom.deRhamCup (structureMorphism A m) (2 * (i : ℤ)) 2 (2 * ((i + 1 : ℕ) : ℤ))
        (by push_cast; ring) (chernPow A m i)
        (Scheme.Hom.deRhamFirstChernClass (structureMorphism A m)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1)
          (isInvertible_twistingSheafOne A m)) :=
  Scheme.Hom.deRhamChernPow_succ _ _ _ i

/-! ### The degeneration of the Hodge-to-de Rham spectral sequence -/

/-- The terms of the de Rham complex of `ℙⁿ_A` vanish above degree `n`. -/
theorem isZero_deRhamComplexPlus_X (q : ℤ) (hq : (m : ℤ) + 1 < q) :
    IsZero ((SheafOfModules.deRhamComplexPlus (deRhamAlgebras A m)
      (deRhamDifferential A m)).obj.X q) :=
  isZero_deRhamComplexInt_X_of_lt A m q hq

/-- **The identification `H^{2i}_dR(ℙⁿ_A/A) ≅ Hⁱ(ℙⁿ_A, Ωⁱ)`**, as additive groups: de Rham
cohomology is the hypercohomology of the de Rham complex; the Hodge-to-de Rham spectral sequence
degenerates, so the brutal filtration identifies `H^{2i}` with the hypercohomology
`H^{2i}(ℙⁿ_A, Ωⁱ[-i])` of the graded piece (`Stacks.Cech.Hypercohomology.collapseLinearEquiv`),
which is `Hⁱ(ℙⁿ_A, Ωⁱ)`. -/
def deRhamCohomologyAddEquiv (i : ℕ) :
    ↥(deRhamCohomology A m (2 * (i : ℤ))) ≃+
      hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m i) 0) i :=
  ((((SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras A m)
      (deRhamDifferential A m) (2 * (i : ℤ))).symm.toLinearEquiv.toAddEquiv.trans
    (collapseLinearEquiv (baseRingSheaf A m)
      (SheafOfModules.deRhamComplexPlus (deRhamAlgebras A m) (deRhamDifferential A m))
      (N := (m : ℤ) + 1) (isZero_deRhamComplexPlus_X A m)
      (isZero_hypercohomology_graded A m) (Int.natCast_nonneg i)).toAddEquiv).trans
    (hypercohomologyMapIso (baseRingSheaf A m)
      (eqToIso (congrArg (fun F => singlePlus (baseRingSheaf A m) F (i : ℤ))
        (deRhamComplexIntTerm A m i))) (2 * (i : ℤ))).toLinearEquiv.toAddEquiv).trans
    (eqToIso (congrArg (hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
      ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m i)) (i : ℤ)))
      (two_mul (i : ℤ)))).toLinearEquiv.toAddEquiv).trans
    (gradedEquiv A m i i)

/-- The identification of `H^{2i}_dR(ℙⁿ_A/A)` with `Hⁱ(ℙⁿ_A, Ωⁱ)` is compatible with the
coefficients `A`. -/
theorem deRhamCohomologyAddEquiv_smul (i : ℕ) (a : A) (x : ↥(deRhamCohomology A m (2 * (i : ℤ)))) :
    deRhamCohomologyAddEquiv A m i (a • x) =
      (show SectionRing (ringSheaf (projSpace A m).sheaf) ⊤ from coeffScalar A (m + 1) a) •
        deRhamCohomologyAddEquiv A m i x := by
  let L₁ := (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras A m)
    (deRhamDifferential A m) (2 * (i : ℤ))).symm.toLinearEquiv
  let L₂ := collapseLinearEquiv (baseRingSheaf A m)
    (SheafOfModules.deRhamComplexPlus (deRhamAlgebras A m) (deRhamDifferential A m))
    (N := (m : ℤ) + 1) (isZero_deRhamComplexPlus_X A m) (isZero_hypercohomology_graded A m)
    (Int.natCast_nonneg i)
  let L₃ := (hypercohomologyMapIso (baseRingSheaf A m)
    (eqToIso (congrArg (fun F => singlePlus (baseRingSheaf A m) F (i : ℤ))
      (deRhamComplexIntTerm A m i))) (2 * (i : ℤ))).toLinearEquiv
  let L₄ := (eqToIso (congrArg (hypercohomology (baseRingSheaf A m)
    (singlePlus (baseRingSheaf A m)
      ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m i)) (i : ℤ)))
    (two_mul (i : ℤ)))).toLinearEquiv
  let t := baseScalar A m a
  let x' : ↥(SheafOfModules.deRhamCohomology (deRhamAlgebras A m) (deRhamDifferential A m)
    (2 * (i : ℤ))) := x
  have h : L₄ (L₃ (L₂ (L₁ (t • x')))) = t • L₄ (L₃ (L₂ (L₁ x'))) := by
    rw [L₁.map_smul, L₂.map_smul]
    exact (congrArg L₄ (L₃.map_smul t _)).trans (L₄.map_smul t _)
  refine (congrArg (gradedEquiv A m i i) h).trans
    ((gradedEquiv_smul A m i i t _).trans ?_)
  rw [baseRingHom_app_top]
  rfl

/-- **The identification `H^{2i}_dR(ℙⁿ_A/A) ≅ Hⁱ(ℙⁿ_A, Ωⁱ)` of `A`-modules** given by the
degeneration of the Hodge-to-de Rham spectral sequence of [Stacks, Section 0FM6]. -/
def deRhamCohomologyEquiv (i : ℕ) :
    ↥(deRhamCohomology A m (2 * (i : ℤ))) ≃ₗ[A]
      ↥((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
        (hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m i) 0)
          i)) where
  __ := deRhamCohomologyAddEquiv A m i
  map_smul' := deRhamCohomologyAddEquiv_smul A m i

/-- **The identification carries `c₁^{dR}(𝒪(1))^i` to the image of `γ₁(𝒪(1))ⁱ` in the graded
piece** ([Stacks, Remark 0FME]). -/
theorem deRhamCohomologyAddEquiv_chernPow (i : ℕ) :
    deRhamCohomologyAddEquiv A m i (chernPow A m i) =
      gradedEquiv A m i i
        ((eqToHom (congrArg (hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
          ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m i)) (i : ℤ)))
          (two_mul (i : ℤ)))).hom (gradedChernPow A m i)) := by
  let C := collapseLinearEquiv (baseRingSheaf A m)
    (SheafOfModules.deRhamComplexPlus (deRhamAlgebras A m) (deRhamDifferential A m))
    (N := (m : ℤ) + 1) (isZero_deRhamComplexPlus_X A m) (isZero_hypercohomology_graded A m)
    (Int.natCast_nonneg i)
  let E := eqToIso (congrArg (fun F => singlePlus (baseRingSheaf A m) F (i : ℤ))
    (deRhamComplexIntTerm A m i))
  have h1 := Iso.hom_inv_id_apply (SheafOfModules.hypercohomologyIsoDeRhamCohomology
    (deRhamAlgebras A m) (deRhamDifferential A m) (2 * (i : ℤ)))
    (SheafOfModules.deRhamChernPowCech (deRhamAlgebras A m) (deRhamDifferential A m)
      (Scheme.Hom.cechComputesSheaf_deRhamComplexInt_X (structureMorphism A m))
      (twistingSheafOneClass A m) i)
  have h3 := collapseLinearEquiv_apply (baseRingSheaf A m)
    (SheafOfModules.deRhamComplexPlus (deRhamAlgebras A m) (deRhamDifferential A m))
    (N := (m : ℤ) + 1) (isZero_deRhamComplexPlus_X A m) (isZero_hypercohomology_graded A m)
    (Int.natCast_nonneg i)
    (SheafOfModules.filteredChernPow (deRhamAlgebras A m) (deRhamDifferential A m)
      (Scheme.Hom.cechComputesSheaf_deRhamComplexInt_X (structureMorphism A m))
      (twistingSheafOneClass A m) i)
  rw [SheafOfModules.hypercohomologyMap_ιTruncPlus_filteredChernPow] at h3
  have h4 := singlePlusMapAt_eqToHom (O := baseRingSheaf A m) (i : ℤ) (deRhamComplexIntTerm A m i)
  have h5 : hypercohomologyMap (baseRingSheaf A m) E.hom (2 * (i : ℤ))
      (C ((SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras A m)
        (deRhamDifferential A m) (2 * (i : ℤ))).inv (chernPow A m i))) =
      gradedChernPow A m i := by
    refine (congrArg (fun z => hypercohomologyMap (baseRingSheaf A m) E.hom (2 * (i : ℤ)) z)
      ((congrArg C h1).trans h3)).trans ?_
    rw [eqToIso.hom, ← h4]
    rfl
  exact congrArg (fun z => gradedEquiv A m i i ((eqToHom (congrArg (hypercohomology
    (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
      ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m i)) (i : ℤ)))
      (two_mul (i : ℤ)))).hom z)) h5

/-! ### [Stacks, Tag 0FMJ] -/

variable {A m}

/-- **[Stacks, Tag 0FMJ], the vanishing.** In every degree that is not `2i` for some
`0 ≤ i ≤ n` the de Rham cohomology `H^•_dR(ℙⁿ_A/A)` of projective space vanishes.

By [Stacks, Tag 0FMI] the Hodge cohomology `H^q(ℙⁿ_A, Ωᵖ)` vanishes unless `p = q ≤ n`, so the
hypercohomology `H^k(ℙⁿ_A, Ωᵖ[-p])` of the graded pieces of the brutal filtration vanishes unless
`k = 2p`, and the terms vanish above degree `n`; inductively along the brutal filtration the
de Rham cohomology vanishes outside the degrees `2i`, `0 ≤ i ≤ n`. -/
@[stacks 0FMJ "the vanishing in every degree other than 2i with 0 ≤ i ≤ n"]
theorem isZero_deRhamCohomology (i : ℤ) (hi : ∀ p : ℕ, p ≤ m + 1 → i ≠ 2 * p) :
    IsZero (deRhamCohomology A m i) := by
  have hz := isZero_hypercohomology_of_forall_ne (baseRingSheaf A m)
    (SheafOfModules.deRhamComplexPlus (deRhamAlgebras A m) (deRhamDifferential A m))
    (N := (m : ℤ) + 1) (isZero_deRhamComplexPlus_X A m) (isZero_hypercohomology_graded A m) i
    fun j hj0 hjN => by
      obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
      exact hi p (by omega)
  have : Subsingleton ↥(deRhamCohomology A m i) :=
    (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras A m)
      (deRhamDifferential A m) i).toLinearEquiv.toEquiv.subsingleton_congr.mp
        (ModuleCat.subsingleton_of_isZero hz)
  exact ModuleCat.isZero_of_subsingleton _

/-- **[Stacks, Tag 0FMJ], the computation in degree `2i`.** For `0 ≤ i ≤ n` the `A`-module
`H^{2i}_dR(ℙⁿ_A/A)` is free of rank one **with basis element `c₁^{dR}(𝒪(1))^i`**, the `i`-th cup
power of the de Rham first Chern class of `𝒪(1)`.

The Hodge-to-de Rham spectral sequence degenerates, which identifies `H^{2i}_dR(ℙⁿ_A/A)` with
`Hⁱ(ℙⁿ_A, Ωⁱ)` (`deRhamCohomologyEquiv`); under it `c₁^{dR}(𝒪(1))^i` goes to a unit multiple of
`c₁^{Hodge}(𝒪(1))^i` (`exists_gradedEquiv_gradedChernPow`), which is a basis by
[Stacks, Tag 0FMI]. -/
@[stacks 0FMJ "free of rank one with basis c₁^dR(𝒪(1))^i for 0 ≤ i ≤ n"]
theorem exists_basis_chernPow (i : ℕ) (hi : i ≤ m + 1) :
    ∃ b : Module.Basis (Fin 1) A ↥(deRhamCohomology A m (2 * (i : ℤ))), b 0 = chernPow A m i := by
  obtain ⟨ε, hε⟩ := exists_gradedEquiv_gradedChernPow A m i
  obtain ⟨b, hb⟩ := exists_basis_chernPowR2 A m i hi
  refine Module.Basis.exists_basis_of_linearEquiv_eq_unit_smul (deRhamCohomologyEquiv A m i) b
    (chernPow A m i) ε ?_
  rw [hb]
  exact (deRhamCohomologyAddEquiv_chernPow A m i).trans hε

end Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham
