module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalTwistSections
import StacksCore.Tactic.StacksAttribute

/-!
# The degree of the first twist on the exceptional curve

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal and let
`E ⊆ X` be its exceptional divisor. This file proves clause (3) of [Stacks, Tag 0B63]:
`deg 𝒪_E(1) ≥ 1`, with equality only if `A` is a regular local ring.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_one`:
  **`deg 𝒪_E(1) = dim_κ(𝔪/𝔪²) − 1`**.
* `AlgebraicGeometry.BlowUpDualizing.one_le_invertibleCurveDegree_curveTwistSheaf_one` and
  `.isRegularLocalRing_of_invertibleCurveDegree_curveTwistSheaf_one_eq_one`: **clause (3) of
  [Stacks, Tag 0B63]**, the lower bound and its equality case.
* `AlgebraicGeometry.BlowUpDualizing.two_le_invertibleCurveDegree_curveTwistSheaf_one`:
  `deg 𝒪_E(1) ≥ 2` when `A` is not regular.

## The argument

The degree of an invertible module on a proper curve is the alternating sum of the dimensions of
its cohomology minus the same sum for the structure sheaf
(`AlgebraicGeometry.invertibleCurveDegree`). Both sums collapse to `h⁰ − h¹`, because `E` is
one-dimensional and so [Stacks, Tag 02UZ] kills everything above degree one
(`AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le`, which carries no
hypothesis beyond properness and the dimension bound); that collapse is
`AlgebraicGeometry.invertibleCurveDegree_eq_sub_of_isZero`. The four remaining dimensions are

* `h⁰(𝒪_E(1)) = dim_κ(𝔪/𝔪²)`, clause (5) of [Stacks, Tag 0B63] at `n = 1`, whose graded piece
  `𝔪/𝔪·𝔪` is `IsLocalRing.CotangentSpace`;
* `h¹(𝒪_E(1)) = 0`, clause (4) at `n = 1`;
* `h⁰(𝒪_E) = 1`, which is `H⁰(E, 𝒪_E) = κ`;
* `h¹(𝒪_E) = 0`, clause (4) at `n = 0` read through `𝒪_E(0) ≅ 𝒪_E`.

So `deg 𝒪_E(1) = dim_κ(𝔪/𝔪²) − 1`. Krull's height theorem gives `dim_κ(𝔪/𝔪²) ≥ dim(A) = 2`,
whence the bound; and equality means `dim_κ(𝔪/𝔪²) = dim(A)`, which is regularity by
`IsRegularLocalRing.iff_finrank_cotangentSpace`.

## Implementation notes

Clause (5) is an isomorphism of `A`-modules, while the degree is defined over the residue field
`κ`. Both sides are killed by `𝔪`, so the `A`-linear isomorphism becomes `κ`-linear once the two
`A`-actions are seen to factor through `κ`: on the cohomology side that is
`globalFunctionsCurve_eq_comp_residue`, which is
`AlgebraicGeometry.residue_comp_globalSections_exceptionalDivisorToCentre` read on global
sections, and `LinearEquiv.extendScalarsOfSurjective` performs the extension. The graded piece is
passed in as a parameter with an `A`-linear identification, because its `κ`-structure is not
canonical; at `n = 1` it is `IsLocalRing.CotangentSpace`, which carries one.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample Stacks.RelativeVeryAmple
open IsLocalRing (CotangentSpace ResidueField maximalIdeal residue)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (S : RationalSingularitySituation.{u})

/-! ### Degree-zero and degree-one cohomology over the residue field -/

/-- **`H¹(E, 𝒪_E(n)) = 0` in the `cohomologyOverField` reading**, which is clause (4) of
[Stacks, Tag 0B63] with the scalars restricted to the residue field. -/
theorem isZero_cohomologyOverField_curveTwistSheaf_one (n : ℕ) :
    IsZero (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (curveTwistSheaf S.A (n : ℤ)) 1) :=
  have : (restrictScalarsOverBase (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))).Additive :=
    ⟨by intros; rfl⟩
  Functor.map_isZero _ (isZero_firstCohomology_curveTwistSheaf S n)

/-- **`dim_κ H¹(E, 𝒪_E(n)) = 0`.** -/
theorem finrank_cohomologyOverField_curveTwistSheaf_one (n : ℕ) :
    Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (curveTwistSheaf S.A (n : ℤ)) 1) = 0 :=
  have := ModuleCat.subsingleton_of_isZero (isZero_cohomologyOverField_curveTwistSheaf_one S n)
  Module.finrank_zero_of_subsingleton

/-- **`appTop` of the exceptional curve over the residue field is `appLE ⊤ ⊤`.** -/
private theorem appTop_exceptionalDivisorToCentre_eq_appLE :
    (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appTop =
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appLE ⊤ ⊤ (by simp) := by
  simpa [Scheme.Hom.appTop] using
    (Scheme.Hom.app_eq_appLE
      (f := exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (U := (⊤ : (Spec (.of (ResidueField S.A))).Opens)))

/-- **The two scalar maps `A ⟶ Γ(E, 𝒪_E)` and `κ ⟶ Γ(E, 𝒪_E)` are compatible with the residue
map.** -/
theorem globalFunctionsCurve_eq_comp_residue :
    ((Scheme.ΓSpecIso (.of S.A)).inv ≫
        (exceptionalImmersion S.A ≫ blowUpToBase (centre S.A)).appTop).hom =
      (((Scheme.ΓSpecIso (.of (ResidueField S.A))).inv ≫
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appLE ⊤ ⊤
            (by simp)).hom).comp (residue S.A) := by
  have hsq : (Scheme.ΓSpecIso (.of S.A)).inv ≫
        (exceptionalImmersion S.A ≫ blowUpToBase (centre S.A)).appTop =
      CommRingCat.ofHom (residue S.A) ≫
        ((Scheme.ΓSpecIso (.of (ResidueField S.A))).inv ≫
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appTop) := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc,
      residue_comp_globalSections_exceptionalDivisorToCentre S]
  rw [← appTop_exceptionalDivisorToCentre_eq_appLE S]
  exact congrArg CommRingCat.Hom.hom hsq

/-- **`dim_κ H⁰(E, 𝒪_E(n)) = dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹`**, clause (5) of [Stacks, Tag 0B63] read as an
equality of dimensions over the residue field, for any `κ`-vector space `Q` with an `A`-linear
identification `eQ` with the graded piece `𝔪ⁿ/𝔪·𝔪ⁿ`. -/
theorem finrank_cohomologyOverField_curveTwistSheaf_zero (n : ℕ)
    (Q : Type u) [AddCommGroup Q] [Module S.A Q] [Module (ResidueField S.A) Q]
    [IsScalarTower S.A (ResidueField S.A) Q]
    (eQ : ((maximalIdeal S.A ^ n : Ideal S.A) ⧸
        (maximalIdeal S.A • ⊤ : Submodule S.A (maximalIdeal S.A ^ n : Ideal S.A))) ≃ₗ[S.A] Q) :
    Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (curveTwistSheaf S.A (n : ℤ)) 0) =
      Module.finrank (ResidueField S.A) Q := by
  let : Module S.A Γ(curveTwistSheaf S.A (n : ℤ), ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (.of S.A)).inv ≫
      (exceptionalImmersion S.A ≫ blowUpToBase (centre S.A)).appTop).hom
  let : Module (ResidueField S.A) Γ(curveTwistSheaf S.A (n : ℤ), ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (.of (ResidueField S.A))).inv ≫
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appLE ⊤ ⊤ (by simp)).hom
  let : IsScalarTower S.A (ResidueField S.A) Γ(curveTwistSheaf S.A (n : ℤ), ⊤) :=
    IsScalarTower.of_algebraMap_smul fun a x => by
      change ((Scheme.ΓSpecIso (.of (ResidueField S.A))).inv ≫
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appLE ⊤ ⊤
            (by simp)).hom (residue S.A a) • x =
        ((Scheme.ΓSpecIso (.of S.A)).inv ≫
          (exceptionalImmersion S.A ≫ blowUpToBase (centre S.A)).appTop).hom a • x
      exact congrArg (fun z => z • x)
        (DFunLike.congr_fun (globalFunctionsCurve_eq_comp_residue S) a).symm
  obtain ⟨eSec⟩ := nonempty_curveTwistSheafSections_iso_gradedPiece S n
  have eA : Γ(curveTwistSheaf S.A (n : ℤ), ⊤) ≃ₗ[S.A] Q := eSec.toLinearEquiv.trans eQ
  have hsurj : Function.Surjective (algebraMap S.A (ResidueField S.A)) :=
    IsLocalRing.residue_surjective
  exact ((cohomologyOverFieldZeroLinearIso (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (curveTwistSheaf S.A (n : ℤ))).toLinearEquiv.finrank_eq).trans
    (LinearEquiv.extendScalarsOfSurjective hsurj eA).finrank_eq

/-! ### A one-dimensional vector space -/

/-- **A bijective ring homomorphism `k ⟶ R` makes `R` a one-dimensional `k`-vector space**, the
scalars being restricted along it. -/
private theorem finrank_restrictScalars_eq_one {k R : Type u} [Field k] [CommRing R]
    (g : k →+* R) (hg : Function.Bijective g) :
    Module.finrank k ((ModuleCat.restrictScalars g).obj (ModuleCat.of R R)) = 1 := by
  let : Module k R := Module.compHom R g
  have e : k ≃ₗ[k] R :=
    LinearEquiv.ofBijective
      { toFun := fun c => g c
        map_add' := fun c c' => map_add g c c'
        map_smul' := fun c x => map_mul g c x } hg
  change Module.finrank k R = 1
  rw [← e.finrank_eq, Module.finrank_self]

/-! ### Instances for the exceptional curve over the residue field -/

/-- The exceptional curve is proper over the residue field, by clause (1) of
[Stacks, Tag 0B63]. -/
local instance isProper_exceptionalCurveToCentre (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint A)) :=
  isProper_exceptionalDivisorToCentre_residuePoint A

/-- `𝒪_E(n)` is invertible, in the spelling `AlgebraicGeometry.invertibleCurveDegree` takes:
the twisting sheaf of the blowup is invertible, and invertibility passes to tensor powers and to
inverse images. -/
local instance isInvertible_curveTwistSheaf (A : Type u) [CommRing A] [IsLocalRing A] (n : ℤ) :
    SheafOfModules.IsInvertible (exceptionalCurve A).presheaf
      (exceptionalCurve A).ringCatSheaf.2 (curveTwistSheaf A n) :=
  (inferInstance : IsInvertibleModule (exceptionalCurve A) (curveTwistSheaf A n))

/-! ### `H⁰(E, 𝒪_E) = κ` and `H¹(E, 𝒪_E) = 0` -/

/-- **`dim_κ H⁰(E, 𝒪_E) = 1`**, which is `H⁰(E, 𝒪_E) = κ`
(`AlgebraicGeometry.isIso_globalSections_exceptionalDivisorToCentre_residuePoint`): the global
sections are the base field, acting on itself. -/
theorem finrank_cohomologyOverField_unit_zero :
    Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (SheafOfModules.unit (exceptionalCurve S.A).ringCatSheaf) 0) = 1 := by
  have := isIso_globalSections_exceptionalDivisorToCentre_residuePoint S
  have hbij : Function.Bijective
      ((Scheme.ΓSpecIso (.of (ResidueField S.A))).inv ≫
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appLE ⊤ ⊤ (by simp)).hom := by
    rw [← appTop_exceptionalDivisorToCentre_eq_appLE S]
    exact ConcreteCategory.bijective_of_isIso _
  refine Eq.trans ((cohomologyOverFieldZeroLinearIso (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (SheafOfModules.unit (exceptionalCurve S.A).ringCatSheaf)).toLinearEquiv.finrank_eq) ?_
  exact finrank_restrictScalars_eq_one _ hbij

/-- **`dim_κ H¹(E, 𝒪_E) = 0`**, clause (4) of [Stacks, Tag 0B63] in degree zero read through
`𝒪_E(0) ≅ 𝒪_E`. -/
theorem finrank_cohomologyOverField_unit_one :
    Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (SheafOfModules.unit (exceptionalCurve S.A).ringCatSheaf) 1) = 0 := by
  rw [← finrank_cohomologyOverField_eq_of_iso (ResidueField S.A)
    (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
    (curveTwistSheafZeroIso S.A) 1]
  exact finrank_cohomologyOverField_curveTwistSheaf_one S 0

/-! ### The degree -/

/-- `𝔪¹/𝔪·𝔪¹` is the cotangent space of `A`. -/
def gradedPieceOneEquivCotangentSpace :
    ((maximalIdeal S.A ^ 1 : Ideal S.A) ⧸
        (maximalIdeal S.A • ⊤ :
          Submodule S.A (maximalIdeal S.A ^ 1 : Ideal S.A))) ≃ₗ[S.A] CotangentSpace S.A := by
  rw [pow_one]
  exact LinearEquiv.refl S.A (CotangentSpace S.A)

/-- **The degree of `𝒪_E(1)` is `dim_κ(𝔪/𝔪²) − 1`**:
`deg 𝒪_E(1) = χ(E, 𝒪_E(1)) − χ(E, 𝒪_E) = dim_κ(𝔪/𝔪²) − 1`. -/
theorem invertibleCurveDegree_curveTwistSheaf_one :
    invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A 1) =
      (Module.finrank (ResidueField S.A) (CotangentSpace S.A) : ℤ) - 1 := by
  have hvan : ∀ (F : (exceptionalCurve S.A).Modules) (m : ℕ), 2 ≤ m →
      IsZero (cohomologyOverField (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) F m) := fun F m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) F (d := 1)
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (by omega)
  rw [invertibleCurveDegree_eq_sub_of_isZero (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (curveTwistSheaf S.A 1) (fun m hm => hvan _ m hm) (fun m hm => hvan _ m hm),
    finrank_cohomologyOverField_unit_zero S, finrank_cohomologyOverField_unit_one S,
    show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl]
  rw [show Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (curveTwistSheaf S.A ((1 : ℕ) : ℤ)) 0) =
      Module.finrank (ResidueField S.A) (CotangentSpace S.A) from
    finrank_cohomologyOverField_curveTwistSheaf_zero S 1 (CotangentSpace S.A)
      (gradedPieceOneEquivCotangentSpace S),
    finrank_cohomologyOverField_curveTwistSheaf_one S 1]
  push_cast
  ring

/-! ### Clause (3) -/

/-- **`dim_κ(𝔪/𝔪²) ≥ 2`**, Krull's height theorem at the two-dimensional local ring `A`: the
embedding dimension is at least the Krull dimension. -/
theorem two_le_finrank_cotangentSpace :
    2 ≤ Module.finrank (ResidueField S.A) (CotangentSpace S.A) := by
  have hd := ringKrullDim_le_spanFinrank_maximalIdeal S.A
  rw [S.dimension_two, IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at hd
  exact_mod_cast hd

/-- **`A` is regular exactly when `dim_κ(𝔪/𝔪²) = 2`**, in Situation [Stacks, Tag 0B4W]: the
Krull dimension is two, and a Noetherian local ring is regular exactly when its embedding
dimension equals its Krull dimension. -/
theorem isRegularLocalRing_iff_finrank_cotangentSpace_eq_two :
    IsRegularLocalRing S.A ↔ Module.finrank (ResidueField S.A) (CotangentSpace S.A) = 2 := by
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace S.A, S.dimension_two]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    rw [h]
    rfl

/-- **`deg 𝒪_E(1) ≥ 1`**, the lower bound of clause (3) of [Stacks, Tag 0B63]. -/
theorem one_le_invertibleCurveDegree_curveTwistSheaf_one :
    1 ≤ invertibleCurveDegree (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (curveTwistSheaf S.A 1) := by
  rw [invertibleCurveDegree_curveTwistSheaf_one]
  have h := two_le_finrank_cotangentSpace S
  omega

/-- **`deg 𝒪_E(1) = 1` only if `A` is regular**, the equality case of clause (3) of
[Stacks, Tag 0B63]. -/
theorem isRegularLocalRing_of_invertibleCurveDegree_curveTwistSheaf_one_eq_one
    (h : invertibleCurveDegree (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (curveTwistSheaf S.A 1) = 1) : IsRegularLocalRing S.A := by
  rw [invertibleCurveDegree_curveTwistSheaf_one] at h
  exact (isRegularLocalRing_iff_finrank_cotangentSpace_eq_two S).2 (by omega)

/-- In Situation [Stacks, Tag 0B4W], with `E` the exceptional curve of the blowup of `Spec(A)` in
the maximal ideal and `𝒪_E(1)` the restriction of `𝒪_X(1)`, `deg 𝒪_E(1) ≥ 1`, and equality holds
only if `A` is a regular local ring. -/
@[stacks 0B63 "clause (3)"]
theorem one_le_invertibleCurveDegree_and_isRegularLocalRing_of_eq_one :
    1 ≤ invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A 1) ∧
      (invertibleCurveDegree (ResidueField S.A)
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
          (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
          (curveTwistSheaf S.A 1) = 1 → IsRegularLocalRing S.A) :=
  ⟨one_le_invertibleCurveDegree_curveTwistSheaf_one S,
    isRegularLocalRing_of_invertibleCurveDegree_curveTwistSheaf_one_eq_one S⟩

/-! ### The degree bound of [Stacks, Tag 0B5H] -/

/-- `𝒪_E(n)` is invertible, on the exceptional curve as it appears in Situation
[Stacks, Tag 0B5D] (`AlgebraicGeometry.cohenMacaulayCurveSituationExceptionalDivisor`). -/
instance isInvertible_curveTwistSheaf_situation (n : ℤ) :
    SheafOfModules.IsInvertible
      (cohenMacaulayCurveSituationExceptionalDivisor S).X.presheaf
      (cohenMacaulayCurveSituationExceptionalDivisor S).X.ringCatSheaf.2
      (curveTwistSheaf S.A n) :=
  (inferInstance : IsInvertibleModule (exceptionalCurve S.A) (curveTwistSheaf S.A n))

/-- **`deg 𝒪_E(1) ≥ 2` when `A` is not regular**, on the exceptional curve as it appears in
Situation [Stacks, Tag 0B5D]. -/
theorem two_le_invertibleCurveDegree_curveTwistSheaf_one
    (hreg : ¬ IsRegularLocalRing S.A) :
    2 ≤ invertibleCurveDegree (cohenMacaulayCurveSituationExceptionalDivisor S).k
      (cohenMacaulayCurveSituationExceptionalDivisor S).f
      (le_of_eq (cohenMacaulayCurveSituationExceptionalDivisor S).dimension_one)
      (curveTwistSheaf S.A 1) := by
  have heq : invertibleCurveDegree (cohenMacaulayCurveSituationExceptionalDivisor S).k
      (cohenMacaulayCurveSituationExceptionalDivisor S).f
      (le_of_eq (cohenMacaulayCurveSituationExceptionalDivisor S).dimension_one)
      (curveTwistSheaf S.A 1) =
      (Module.finrank (ResidueField S.A) (CotangentSpace S.A) : ℤ) - 1 :=
    invertibleCurveDegree_curveTwistSheaf_one S
  rw [heq]
  have h2 := two_le_finrank_cotangentSpace S
  have h3 : Module.finrank (ResidueField S.A) (CotangentSpace S.A) ≠ 2 := fun h =>
    hreg ((isRegularLocalRing_iff_finrank_cotangentSpace_eq_two S).2 h)
  omega

end AlgebraicGeometry.BlowUpDualizing

end
