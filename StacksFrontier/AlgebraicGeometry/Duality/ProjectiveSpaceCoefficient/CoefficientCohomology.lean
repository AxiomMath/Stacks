module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.CoefficientTwist
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.DimensionShift
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CanonicalTwist
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoveringNumber.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence

/-!
# Cohomology of the twists of projective space with coefficients

Let `R` be a commutative ring, `n ≥ 0`, `p : ℙⁿ_R ⟶ Spec R`, and for an `R`-module `M` let
`T_d(M) = 𝒪(d) ⊗ p^*M~`, the geometric factor of the Eilenberg–Watts package of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/`. This file extends Serre's computation of
`Hᑫ(ℙⁿ_R, 𝒪(d))` ([Stacks, Tag 01XT]) to coefficients in `M`, in the two forms the twisted
inverse image of `p` needs:

* for `-n ≤ d ≤ -1` the module `T_d(M)` has no cohomology at all;
* the top-degree functor `M ↦ Hⁿ(ℙⁿ_R, T_{-n-1}(M))` is tensoring with `Hⁿ(ℙⁿ_R, 𝒪(-n-1)) ≅ R`
  (Eilenberg–Watts, using that quasi-coherent cohomology of `ℙⁿ_R` vanishes above `n`).

## Main results

* `Stacks.Duality.ProjCoeff.isZero_rightDerived_of_lt`: quasi-coherent cohomology of `ℙⁿ_R`
  vanishes above degree `n`.
* `Stacks.Duality.ProjCoeff.isZero_H_of_forall`: an exact, sum-preserving coefficient functor whose
  value at `R` is acyclic is acyclic at every module (dimension shifting).
* `Stacks.Duality.ProjCoeff.isZero_H_T_of_neg_le`: the twists `𝒪(-1), …, 𝒪(-n)` with
  coefficients are acyclic.
* `Stacks.Duality.ProjCoeff.topFunctorIso`, `Stacks.Duality.ProjCoeff.topFunctorObjIso`:
  `Hⁿ(ℙⁿ_R, 𝒪(-n-1) ⊗ p^*M~) ≅ M`, `R`-linearly.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.AffineBase

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

variable (R : Type u) [CommRing R] (n : ℕ)

/-- `ℙⁿ_R` as a scheme over `Spec R`. -/
abbrev W : Over (Spec (CommRingCat.of R)) := Over.mk (projToSpecCoeff R n)

/-- **The cohomology of a quasi-coherent module on `ℙⁿ_R` vanishes above degree `n`**, as a
module over the global sections. -/
theorem isZero_rightDerived_of_lt (F : (P R n).Modules) [F.IsQuasicoherent] (q : ℕ)
    (hq : n < q) : IsZero (((moduleGlobalSections (P R n)).rightDerived q).obj F) := by
  have h := Stacks.ProjectiveCohomology.isZero_Hgroup_proj_of_lt R n F q hq
  have e := (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
    (P R n).ringCatSheaf ⊤ q).app F
  have h' : IsZero ((forget₂ (ModuleCat.{u} Γ(P R n, ⊤)) AddCommGrpCat.{u}).obj
      (((moduleGlobalSections (P R n)).rightDerived q).obj F)) := e.isZero_iff.2 h
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero h')

/-- The same vanishing in the `ℤ`-indexed spelling consumed by the Eilenberg–Watts package. -/
theorem isZero_rightDerivedPlus_succ (F : (P R n).Modules) (hF : F.IsQuasicoherent) :
    IsZero (((moduleGlobalSections (P R n)).rightDerivedPlus ((n : ℤ) + 1)).obj F) := by
  have := hF
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (moduleGlobalSections (P R n))
    (n := n + 1) (by push_cast; rfl) F]
  exact isZero_rightDerived_of_lt R n F (n + 1) (by omega)

/-- `𝒪(d)` as a quasi-coherent module. -/
def Oqc (d : ℤ) : (SheafOfModules.isQuasicoherent (W R n).left.ringCatSheaf).FullSubcategory :=
  ⟨O R n d, Stacks.ProjectiveCohomology.isQuasicoherent_twistingSheaf R n d⟩

/-- The tensor factor of the Eilenberg–Watts geometric factor, `𝒪(d) ⊗ -`, is the right
tensor functor `- ⊗ 𝒪(d)` up to the braiding. -/
def tensorFactorIso (d : ℤ) :
    tensorFactor R (W R n) (O R n d) ≅
      Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules (P R n) (O R n d) :=
  (Stacks.SheafOfModules.Tensor.sheafTensorBraiding _).app (O R n d)

/-- The geometric factor `M ↦ 𝒪(d) ⊗ p^*M~`. -/
abbrev T (d : ℤ) : ModuleCat.{u} R ⥤ (P R n).Modules :=
  geometricFactorFormula R (W R n) (O R n d)

/-- The geometric factor `M ↦ 𝒪(d) ⊗ p^*M~` is left exact: `~` is, `p^*` is because `p` is flat,
and tensoring with the invertible module `𝒪(d)` is an equivalence. -/
instance (d : ℤ) : PreservesFiniteLimits (T R n d) := by
  have : (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules (P R n)
      (O R n d)).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule _ _
  have : (tensorFactor R (W R n) (O R n d)).IsEquivalence :=
    Functor.isEquivalence_of_iso (tensorFactorIso R n d).symm
  have h1 : PreservesFiniteLimits (tildeFactor R) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits (.of R)
  have h2 : PreservesFiniteLimits (pullbackFactor R (W R n)) :=
    AlgebraicGeometry.preservesFiniteLimits_pullback_of_flat (projToSpecCoeff R n)
  exact inferInstanceAs (PreservesFiniteLimits (tildeFactor R ⋙ pullbackFactor R (W R n) ⋙
    tensorFactor R (W R n) (O R n d)))

/-- `ℙⁿ_R` has compact space: `p : ℙⁿ_R ⟶ Spec R` is proper, hence quasi-compact. -/
instance : CompactSpace (P R n) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff R n
  exact (quasiCompact_iff_compactSpace (projToSpecCoeff R n)).1 inferInstance

/-- `ℙⁿ_R` has quasi-separated space: `p : ℙⁿ_R ⟶ Spec R` is proper, hence quasi-separated. -/
instance : QuasiSeparatedSpace (P R n) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff R n
  exact (quasiSeparated_iff_quasiSeparatedSpace (projToSpecCoeff R n)).1 inferInstance

/-- Cohomology of `𝒪_{ℙⁿ_R}`-modules, as modules over the global sections. -/
abbrev H (q : ℕ) : (P R n).Modules ⥤ ModuleCat.{u} Γ(P R n, ⊤) :=
  (moduleGlobalSections (P R n)).rightDerived q

/-- **Acyclicity with coefficients above a degree.** Let `Φ : ModuleCat R ⥤ 𝒪_{ℙⁿ_R}-modules`
be exact, commute with direct sums and take quasi-coherent values. If `Φ(R)` has no cohomology
in degrees `≥ q₀`, then neither has `Φ(M)` for any `R`-module `M`. -/
theorem isZero_H_of_forall_ge (Φ : ModuleCat.{u} R ⥤ (P R n).Modules) [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] (hsum : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) Φ)
    (hqc : ∀ L, (Φ.obj L).IsQuasicoherent) (q₀ : ℕ)
    (hq0 : ∀ q, q₀ ≤ q → IsZero ((H R n q).obj (Φ.obj (.of R R)))) :
    ∀ (q : ℕ), q₀ ≤ q → ∀ (L : ModuleCat.{u} R), IsZero ((H R n q).obj (Φ.obj L)) := by
  have hfree : ∀ (q : ℕ), q₀ ≤ q → ∀ (L : ModuleCat.{u} R),
      IsZero ((H R n q).obj (Φ.obj (freeCover L))) := by
    intro q hq L
    have hH := preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections (P R n) q L
    have hT := hsum L
    have : PreservesColimitsOfShape (Discrete L) (Φ ⋙ H R n q) :=
      comp_preservesColimitsOfShape _ _
    have hc := isColimitOfPreserves (Φ ⋙ H R n q)
      (Stacks.ModuleCat.isColimitFinsuppCofan (R := R) L)
    rw [IsZero.iff_id_eq_zero]
    exact hc.hom_ext fun j => (hq0 q hq).eq_of_src _ _
  have key : ∀ m q : ℕ, q₀ ≤ q → n + 1 ≤ q + m → ∀ L : ModuleCat.{u} R,
      IsZero ((H R n q).obj (Φ.obj L)) := by
    intro m
    induction m with
    | zero =>
      intro q _ hq L
      have := hqc L
      exact isZero_rightDerived_of_lt R n _ q (by omega)
    | succ m ih =>
      intro q hq₀ hq L
      by_cases hq' : n + 1 ≤ q + m
      · exact ih q hq₀ hq' L
      · exact isZero_of_isZero_free_of_isZero_succ
          (Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor (P R n)) Φ q
          (fun L' => hfree q hq₀ L') (fun L' => ih (q + 1) (by omega) (by omega) L') L
  intro q hq L
  exact key (n + 1) q hq (by omega) L

/-- **Acyclicity with coefficients, for a general exact coefficient functor.** Let
`Φ : ModuleCat R ⥤ 𝒪_{ℙⁿ_R}-modules` be exact, commute with direct sums and take quasi-coherent
values. If `Φ(R)` has no cohomology at all, then neither has `Φ(M)` for any `R`-module `M`:
`Φ` of a free module is a direct sum of copies of `Φ(R)`, and downward induction on the degree,
starting above `n`, shifts dimensions along a free presentation. -/
theorem isZero_H_of_forall (Φ : ModuleCat.{u} R ⥤ (P R n).Modules) [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] (hsum : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) Φ)
    (hqc : ∀ L, (Φ.obj L).IsQuasicoherent) (hq0 : ∀ q, IsZero ((H R n q).obj (Φ.obj (.of R R)))) :
    ∀ (q : ℕ) (L : ModuleCat.{u} R), IsZero ((H R n q).obj (Φ.obj L)) := fun q L =>
  isZero_H_of_forall_ge R n Φ hsum hqc 0 (fun q _ => hq0 q) q (Nat.zero_le q) L

/-- On a free module the coefficient twist is a direct sum of copies of `𝒪(d)`, so its
cohomology vanishes as soon as that of `𝒪(d)` does. -/
theorem isZero_H_T_freeCover (d : ℤ) (q : ℕ) (h : IsZero ((H R n q).obj (O R n d)))
    (L : ModuleCat.{u} R) : IsZero ((H R n q).obj ((T R n d).obj (freeCover L))) := by
  have hH := preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections (P R n) q L
  have hT : PreservesColimitsOfShape (Discrete L) (T R n d) :=
    (preservesColimitsOfSize_geometricFactorFormula R (W R n) (O R n d)).preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete L) (T R n d ⋙ H R n q) :=
    comp_preservesColimitsOfShape _ _
  have hc := isColimitOfPreserves (T R n d ⋙ H R n q)
    (Stacks.ModuleCat.isColimitFinsuppCofan (R := R) L)
  have h0 : IsZero ((T R n d ⋙ H R n q).obj (ModuleCat.of R R)) :=
    h.of_iso ((H R n q).mapIso (geometricFactorFormulaObjSelfIso R (W R n) (O R n d)))
  rw [IsZero.iff_id_eq_zero]
  exact hc.hom_ext fun j => h0.eq_of_src _ _

/-- The geometric factor `M ↦ 𝒪(d) ⊗ p^*M~` is right exact. -/
instance (d : ℤ) : PreservesFiniteColimits (T R n d) :=
  preservesFiniteColimits_geometricFactorFormula R (W R n) (O R n d)

/-- The geometric factor takes quasi-coherent values: `𝒪(d) ⊗ p^*M~` is quasi-coherent. -/
theorem isQuasicoherent_T (d : ℤ) (L : ModuleCat.{u} R) : ((T R n d).obj L).IsQuasicoherent :=
  isQuasicoherent_geometricFactorFormula R (W R n) (Oqc R n d) L

/-- The geometric factor commutes with direct sums of any size. -/
theorem preservesColimitsOfShape_T (d : ℤ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (T R n d) :=
  (preservesColimitsOfSize_geometricFactorFormula R (W R n) (O R n d)).preservesColimitsOfShape

/-- **Acyclic twists stay acyclic with coefficients.** If `𝒪(d)` has no cohomology in any
degree, then neither has `𝒪(d) ⊗ p^*M~`, for every `R`-module `M`. -/
theorem isZero_H_T_of_forall (d : ℤ) (hO : ∀ q, IsZero ((H R n q).obj (O R n d))) :
    ∀ (q : ℕ) (L : ModuleCat.{u} R), IsZero ((H R n q).obj ((T R n d).obj L)) :=
  isZero_H_of_forall R n (T R n d) (preservesColimitsOfShape_T R n d) (isQuasicoherent_T R n d)
    (fun q => (hO q).of_iso ((H R n q).mapIso
      (geometricFactorFormulaObjSelfIso R (W R n) (O R n d))))

section Scalars

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-- `p : ℙⁿ_R ⟶ Spec R` is quasi-compact, being proper. -/
instance : QuasiCompact (W R n).hom := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff R n
  exact inferInstanceAs (QuasiCompact (projToSpecCoeff R n))

/-- `p : ℙⁿ_R ⟶ Spec R` is quasi-separated, being proper. -/
instance : QuasiSeparated (W R n).hom := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff R n
  exact inferInstanceAs (QuasiSeparated (projToSpecCoeff R n))

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- `isZero_rightDerivedPlus_succ` for the standard derived category, the shape in which the
Eilenberg–Watts package consumes the vanishing above degree `n`. -/
theorem isZero_rightDerivedPlus_succ_std (F : (P R n).Modules) (hF : F.IsQuasicoherent) :
    IsZero (((moduleGlobalSections (P R n)).rightDerivedPlus ((n : ℤ) + 1)).obj F) := by
  have := hF
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (moduleGlobalSections (P R n))
    (n := n + 1) (by push_cast; rfl) F]
  exact isZero_rightDerived_of_lt R n F (n + 1) (by omega)

/-- **Eilenberg–Watts at the canonical twist**: the top-degree functor is tensoring with
`Hⁿ(ℙⁿ_R, 𝒪(-n-1))`. -/
def topFunctorIso :
    MonoidalCategory.tensorLeft (C := ModuleCat.{u} R)
      (Stacks.ProjectiveSpace.Cohomology.twistCohomology R n (-(n : ℤ) - 1) n) ≅
      affineTopDegreeFunctor R (W R n) n (geometricFactor R (W R n) (Oqc R n (-(n : ℤ) - 1))) :=
  affineTopDegreeTensorCohomologyIso R (W R n) n (Oqc R n (-(n : ℤ) - 1))
    (fun G hG => isZero_rightDerivedPlus_succ_std R n G hG)

end Standard

/-- The cohomology of `𝒪(d)`, read through `qcohCohomology`, is Serre's `twistCohomology`. -/
theorem restrictScalars_qcohCohomology_Oqc (d : ℤ) (q : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R Γ((W R n).left, ⊤))).obj
      ((qcohCohomology (W R n).left q).obj (Oqc R n d)) =
      Stacks.ProjectiveSpace.Cohomology.twistCohomology R n d q := rfl

/-- `𝒪(d)` is acyclic in degree `q` exactly when Serre's `twistCohomology` vanishes there. -/
theorem isZero_H_O_iff (d : ℤ) (q : ℕ) :
    IsZero ((H R n q).obj (O R n d)) ↔
      IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology R n d q) := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

/-- **The twists `𝒪(-1), …, 𝒪(-n)` with coefficients are acyclic.** -/
theorem isZero_H_T_of_neg_le (d : ℤ) (hd₁ : -(n : ℤ) ≤ d) (hd₂ : d < 0) (q : ℕ)
    (L : ModuleCat.{u} R) : IsZero ((H R n q).obj ((T R n d).obj L)) :=
  isZero_H_T_of_forall R n d (fun q => (isZero_H_O_iff R n d q).2
    (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_of_neg_le R n d hd₁ hd₂ q)) q L

/-- The top-degree functor `M ↦ Hⁿ(ℙⁿ_R, 𝒪(-n-1) ⊗ p^*M~)` of `R`-modules. -/
def topFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  affineTopDegreeFunctor R (W R n) n (geometricFactor R (W R n) (Oqc R n (-(n : ℤ) - 1)))

/-- **`Hⁿ(ℙⁿ_R, 𝒪(-n-1) ⊗ p^*M~) ≅ M`**, as `R`-modules. -/
def topFunctorObjIso (M : ModuleCat.{u} R) : (topFunctor R n).obj M ≅ M :=
  (topFunctorIso R n).symm.app M ≪≫
    MonoidalCategory.whiskerRightIso
      (Stacks.ProjectiveSpace.Cohomology.twistCohomologyCanonicalIsoCoeff R n) M ≪≫
    MonoidalCategory.leftUnitor M

end Scalars

end Stacks.Duality.ProjCoeff
