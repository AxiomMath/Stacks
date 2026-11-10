module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceGradedForms
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquareRing
public import StacksFrontier.RingTheory.DeRham.WeightComparisonTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
import StacksCore.Tactic.StacksAttribute

/-!
# The graded forms of the total space of a line bundle over a chart

Over an affine open `U` of `X` on which the sections of the line bundle `L` are free of rank one
with basis `b`, the functions on the inverse image `π⁻¹U` in the total space are the polynomial
ring `Γ(X, U)[X]`. This file identifies the homogeneous functions of degree `k` there with the
images of the monomials `c Xᵏ`.

## Main results

* `Stacks.LineBundle.Situation.symSectionsRingEquiv_coe`: the symmetric powers of `Γ(L, U)` are
  carried to the homogeneous functions.
* `Stacks.LineBundle.Situation.exists_totalFunction_iff`: **over a trivializing affine open the
  homogeneous functions of degree `k` are the images of the monomials of degree `k`.**
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite Polynomial

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### Homogeneous functions over an affine open -/

/-- **Over an affine open the symmetric powers of the sections of `L` give the homogeneous
functions**: under the identification of the functions on `π⁻¹U` with `Sym(Γ(L, U))`, an element
of `Symᵏ(Γ(L, U))` is the homogeneous function of the corresponding section of `Symᵏ(L)`. -/
theorem Situation.symSectionsRingEquiv_coe (U : D.X.affineOpens) (k : ℕ)
    (y : SymPow.symmetricPower k Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.symSectionsRingEquiv U (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)) =
      D.totalFunction k U.1 (Stacks.SymAlgSections.pieceUnit D.L U.2 k y) := by
  have h1 : DirectSum.decomposeRingEquiv
      (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1))
      (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)) = DirectSum.of _ k y :=
    DirectSum.decompose_coe (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1)) y
  unfold Situation.totalFunction
  rw [D.universalAlgebraMap_app_eq_sectionsIso U]
  change (D.sectionsIso U).hom.hom (Stacks.RelativeSpec.ungradedSectionsRingEquiv D.X
    D.symmetricAlgebra D.symmetricAlgebra_mul_comm U.2
      (Stacks.SymAlgSections.symPowersRingEquiv D.L U.2 (DirectSum.decomposeRingEquiv
        (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1))
          (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1))))) = _
  rw [h1]
  exact congrArg (fun z => (D.sectionsIso U).hom.hom
    ((Stacks.RelativeSpec.ungradedCommUnit D.X D.symmetricAlgebra
      D.symmetricAlgebra_mul_comm U.1).hom z)) (Stacks.SymAlgSections.ofSymPowers_of D.L U.2 k y)

/-- The fibre coordinate of a basis of `Γ(L, U)` is the variable of the polynomial ring. -/
theorem Situation.polynomialAlgEquiv_ι (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.polynomialAlgEquiv U b (SymmetricAlgebra.ι Γ(D.X, U.1) Γ(D.L, U.1) (b PUnit.unit)) =
      Polynomial.X := by
  unfold Situation.polynomialAlgEquiv
  rw [AlgEquiv.trans_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  simp

/-- **The symmetric powers are the monomials of the polynomial model.** -/
theorem Situation.polynomialAlgEquiv_mem_range_monomial (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) (k : ℕ)
    {y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)}
    (hy : y ∈ SymPow.symmetricPower k Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.polynomialAlgEquiv U b y ∈ LinearMap.range (monomial k : Γ(D.X, U.1) →ₗ[Γ(D.X, U.1)] _) := by
  induction k generalizing y with
  | zero =>
      rw [SymPow.symmetricPower, pow_zero, Submodule.one_eq_range] at hy
      obtain ⟨c, rfl⟩ := hy
      exact ⟨c, by simp⟩
  | succ k ih =>
      rw [SymPow.symmetricPower, pow_succ] at hy
      refine Submodule.mul_induction_on hy (fun y₁ hy₁ y₂ hy₂ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
      · obtain ⟨c₁, hc₁⟩ := ih hy₁
        obtain ⟨m, rfl⟩ := hy₂
        have hspan : m ∈ Submodule.span Γ(D.X, U.1) {b PUnit.unit} := by
          simpa only [Set.range_unique] using b.mem_span m
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hspan
        refine ⟨c₁ * c, ?_⟩
        rw [map_mul (D.polynomialAlgEquiv U b), ← hc₁, map_smul, map_smul,
          D.polynomialAlgEquiv_ι, Polynomial.smul_eq_C_mul, ← Polynomial.monomial_zero_left,
          ← Polynomial.monomial_one_one_eq_X, monomial_mul_monomial, monomial_mul_monomial]
        simp
      · rw [map_add]
        exact Submodule.add_mem _ h₁ h₂

/-- **A monomial of the polynomial model comes from a symmetric power.** -/
theorem Situation.polynomialAlgEquiv_symm_monomial_mem (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) (k : ℕ) (c : Γ(D.X, U.1)) :
    (D.polynomialAlgEquiv U b).symm (monomial k c) ∈
      SymPow.symmetricPower k Γ(D.X, U.1) Γ(D.L, U.1) := by
  have h : (D.polynomialAlgEquiv U b).symm (monomial k c) =
      c • (SymmetricAlgebra.ι Γ(D.X, U.1) Γ(D.L, U.1) (b PUnit.unit)) ^ k := by
    rw [AlgEquiv.symm_apply_eq, map_smul, map_pow, D.polynomialAlgEquiv_ι,
      Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
  rw [h]
  exact Submodule.smul_mem _ c
    (Submodule.pow_mem_pow _ (LinearMap.mem_range_self _ (b PUnit.unit)) k)

/-- **Over a trivializing affine open the homogeneous functions of degree `k` are the images of
the monomials `c Xᵏ` of the polynomial model.** -/
theorem Situation.exists_totalFunction_iff (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) (k : ℕ)
    (a : Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U.1)) :
    (∃ x, D.totalFunction k U.1 x = a) ↔
      ∃ c : Γ(D.X, U.1), D.polynomialSectionsRingEquiv U b (monomial k c) = a := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Stacks.SymAlgSections.pieceUnit D.L U.2 k).surjective x
    obtain ⟨c, hc⟩ := D.polynomialAlgEquiv_mem_range_monomial U b k y.2
    refine ⟨c, ?_⟩
    rw [← D.symSectionsRingEquiv_coe]
    change D.symSectionsRingEquiv U ((D.polynomialAlgEquiv U b).symm (monomial k c)) = _
    rw [show (monomial k c : Γ(D.X, U.1)[X]) = D.polynomialAlgEquiv U b y from hc,
      AlgEquiv.symm_apply_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨Stacks.SymAlgSections.pieceUnit D.L U.2 k
      ⟨_, D.polynomialAlgEquiv_symm_monomial_mem U b k c⟩, ?_⟩
    rw [← D.symSectionsRingEquiv_coe]
    rfl

/-! ### The polynomial model of a chart -/

/-- **The polynomial model of the total space over a trivializing affine open**, as an
isomorphism of `Γ(X, U)`-algebras `Γ(X, U)[X] ≅ Γ(𝕃, π⁻¹U)` for the algebra structure given by
`π`. -/
def Situation.polynomialChartAlgEquiv {U : D.X.Opens} (hU : IsAffineOpen U)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U) Γ(D.L, U)) :
    letI : Algebra Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
      (D.totalSpaceToBase.app U).hom.toAlgebra
    Γ(D.X, U)[X] ≃ₐ[Γ(D.X, U)] Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
  letI : Algebra Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    (D.totalSpaceToBase.app U).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := D.polynomialSectionsRingEquiv ⟨U, hU⟩ b)
    fun r => D.polynomialSectionsRingEquiv_C ⟨U, hU⟩ b r

section Chart

variable {D} {U : D.X.Opens} {V : D.S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (e : U ≤ D.f ⁻¹ᵁ V) (b : Module.Basis PUnit.{u + 1} Γ(D.X, U) Γ(D.L, U))

include hU hV e b in
/-- **Over a chart the weight-`n` Kähler forms of the polynomial model are sections of
`Ω^p_{𝕃/S, n}`**: a generator `a₀ · (d a₁ ∧ ⋯ ∧ d aₚ)` with each `aᵢ` a monomial is a homogeneous
form. -/
theorem Situation.formsSectionsIso_inv_mem_gradedTotalForms (p n : ℕ) :
    letI : Algebra Γ(D.S, V) Γ(D.X, U) := (D.f.appLE V U e).hom.toAlgebra
    letI : Algebra Γ(D.S, V) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
      ((D.totalSpaceToBase ≫ D.f).appLE V _
        (Situation.preimage_le_preimage_comp e)).hom.toAlgebra
    letI : Algebra Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
      (D.totalSpaceToBase.app U).hom.toAlgebra
    haveI : IsScalarTower Γ(D.S, V) Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (ConcreteCategory.congr_hom (Situation.appLE_comp_app_totalSpaceToBase e) r).symm
    ∀ z ∈ KaehlerDifferential.gradedDifferentialFormComponent
        (PolynomialDeRham.polyGrading Γ(D.S, V) Γ(D.X, U) _
          (D.polynomialChartAlgEquiv hU b)) p n,
      D.ofForms p U ((Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso D.totalToBase
        (hU.preimage D.totalSpaceToBase) hV (Situation.preimage_le_preimage_comp e) p).inv z) ∈
        (D.gradedTotalForms p n).obj (op U) := by
  let : Algebra Γ(D.S, V) Γ(D.X, U) := (D.f.appLE V U e).hom.toAlgebra
  let : Algebra Γ(D.S, V) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    ((D.totalSpaceToBase ≫ D.f).appLE V _
      (Situation.preimage_le_preimage_comp e)).hom.toAlgebra
  let : Algebra Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    (D.totalSpaceToBase.app U).hom.toAlgebra
  have : IsScalarTower Γ(D.S, V) Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (ConcreteCategory.congr_hom (Situation.appLE_comp_app_totalSpaceToBase e) r).symm
  set φ := (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso D.totalToBase
    (hU.preimage D.totalSpaceToBase) hV (Situation.preimage_le_preimage_comp e) p).inv
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨deg, a, hn, rfl⟩ := hy
      have ha : ∀ i, ∃ x, D.totalFunction (deg i) U x = (a i).1 := fun i => by
        obtain ⟨_, ⟨c, rfl⟩, hc⟩ := (a i).2
        exact (D.exists_totalFunction_iff ⟨U, hU⟩ b (deg i) _).2 ⟨c, hc⟩
      have hω := D.mem_gradedTotalForms (W := U) ⟨deg, fun i => (a i).1, ha, hn, rfl⟩
      rw [Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_inv_smul_ιMulti_D
        D.totalToBase (hU.preimage D.totalSpaceToBase) hV
        (Situation.preimage_le_preimage_comp e) p (a 0).1 fun i => (a i.succ).1]
      exact hω
  | zero =>
      rw [show φ (0 : ⋀[Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U)]^p
        Ω[Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U)⁄Γ(D.S, V)]) = 0 from map_zero _, map_zero]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [show φ (y + z) = φ y + φ z from map_add _ y z, map_add]
      exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
      have h5 : φ (r • y) = (D.totalSpaceToBase.app U).hom (algebraMap Γ(D.S, V) Γ(D.X, U) r) •
          φ y := by
        have e1 : r • y = algebraMap Γ(D.S, V) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) r • y :=
          (algebraMap_smul Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) r y).symm
        rw [e1, IsScalarTower.algebraMap_apply Γ(D.S, V) Γ(D.X, U)
          Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U)]
        exact map_smul φ.hom
          (algebraMap Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U)
            (algebraMap Γ(D.S, V) Γ(D.X, U) r)) y
      rw [h5, D.ofForms_smul]
      exact Submodule.smul_mem _ _ hy

end Chart

end Stacks.LineBundle

end
