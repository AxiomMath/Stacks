module

public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Algebraic.Integral
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Basic
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.CompleteLocalRing.FiniteEtaleResidueExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension

/-!
# The algebra of the induction on `[K : K₀]` for complete local domains

The source's proof of [Stacks, Tag 0BGN] chooses, by Cohen's structure theorem, a regular complete
local subring `A₀ ⊆ A` over which `A` is finite, and argues by induction on the degree `[K : K₀]`
of the fraction field extension. In the inductive step an intermediate field
`K₀ ⊊ L ⊊ K` is given, and the ring `B` is the integral closure of `A₀` in `L`; the induction
hypothesis is applied both to `A₀ → B` and, after a geometric construction, to rings finite over
completions of local rings of a resolution of `Spec B`. This file proves the purely algebraic
facts this needs.

## Main results

* `Stacks.ResolutionOfSurfaces.isNoetherianCompleteLocalRing_of_finite`: a domain finite over a
  Noetherian complete local ring is a Noetherian complete local ring.
* `Stacks.ResolutionOfSurfaces.intermediateSubalgebra`: for `R ⊆ A` finite and an intermediate
  field `M` of `Frac R ⊆ Frac A`, the subring `B = A ∩ M`.
* `Stacks.ResolutionOfSurfaces.isFractionRing_intermediateSubalgebra` and
  `Stacks.ResolutionOfSurfaces.isIntegrallyClosed_intermediateSubalgebra`: when `A` is integrally
  closed, `M` is the fraction field of `B` and `B` is integrally closed.
* `Stacks.ResolutionOfSurfaces.finrank_intermediateSubalgebra_lt` and
  `Stacks.ResolutionOfSurfaces.finrank_intermediateSubalgebra_top_lt`: when `M` is neither end of
  the extension, both `[B : R]` and `[A : B]` are smaller than `[A : R]`.

## Implementation notes

The degree is measured by `Module.finrank R A`, which for a finite torsion-free module over a
domain is the dimension of the generic fibre (`IsFractionRing.finrank_eq`); this keeps the
induction free of choices of fraction fields. `B` is realized as a subalgebra of `A`, so that the
inclusion `B → A` is available as an algebra map; `A ∩ M` is the integral closure of `R` in `M`
because `A` is integrally closed.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public noncomputable section

open IsLocalRing Module

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### Domains finite over a complete local ring -/

/-- **A domain finite over a Noetherian complete local ring is a Noetherian complete local
ring.** -/
theorem isNoetherianCompleteLocalRing_of_finite (R A : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsDomain A] [Algebra R A]
    [Module.Finite R A] : IsNoetherianCompleteLocalRing A := by
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete_maximalIdeal R
  have : IsLocalRing A :=
    Stacks.DiscreteValuationRing.Ramification.isLocalRing_of_finite_of_henselianLocalRing R A
  exact IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing (R := R)
    ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### The intermediate ring `A ∩ M` -/

section Intermediate

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [FaithfulSMul R A]

attribute [local instance] FractionRing.liftAlgebra

/-- For an intermediate field `M` of `Frac R ⊆ Frac A`, the subring of elements of `A` whose image
in `Frac A` lies in `M`. -/
def intermediateSubalgebra (M : IntermediateField (FractionRing R) (FractionRing A)) :
    Subalgebra R A :=
  (M.toSubalgebra.restrictScalars R).comap (IsScalarTower.toAlgHom R A (FractionRing A))

variable {R A}

/-- An element of `A` lies in `A ∩ M` exactly when its image in `Frac A` lies in `M`. -/
theorem mem_intermediateSubalgebra {M : IntermediateField (FractionRing R) (FractionRing A)}
    {a : A} : a ∈ intermediateSubalgebra R A M ↔ algebraMap A (FractionRing A) a ∈ M :=
  Iff.rfl

variable (M : IntermediateField (FractionRing R) (FractionRing A))

/-- The inclusion of `A ∩ M` into `M`. -/
def intermediateSubalgebraToField : intermediateSubalgebra R A M →+* M where
  toFun b := ⟨algebraMap A (FractionRing A) b, b.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The inclusion of `A ∩ M` into `M` is injective. -/
theorem intermediateSubalgebraToField_injective :
    Function.Injective (intermediateSubalgebraToField M) := fun _ _ h =>
  Subtype.ext (IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val h))

/-- `M` is an algebra over `A ∩ M` through the inclusion. -/
instance : Algebra (intermediateSubalgebra R A M) M :=
  (intermediateSubalgebraToField M).toAlgebra

/-- The image of `b ∈ A ∩ M` in `M`, viewed in `Frac A`, is the image of `b` under `A → Frac A`. -/
theorem algebraMap_intermediateSubalgebra_apply (b : intermediateSubalgebra R A M) :
    ((algebraMap (intermediateSubalgebra R A M) M b : M) : FractionRing A) =
      algebraMap A (FractionRing A) b :=
  rfl

/-- The maps `R → A ∩ M → M` compose to the algebra map `R → M`. -/
instance : IsScalarTower R (intermediateSubalgebra R A M) M :=
  .of_algebraMap_eq fun r => by
    ext
    change algebraMap R (FractionRing A) r = algebraMap A (FractionRing A) (algebraMap R A r)
    exact IsScalarTower.algebraMap_apply R A (FractionRing A) r

/-- The maps `R → Frac R → M` compose to the algebra map `R → M`. -/
instance : IsScalarTower R (FractionRing R) M :=
  .of_algebraMap_eq fun r => by
    ext
    change algebraMap R (FractionRing A) r =
      algebraMap (FractionRing R) (FractionRing A) (algebraMap R (FractionRing R) r)
    exact IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A) r

/-- The maps `A ∩ M → A → Frac A` compose to the algebra map `A ∩ M → Frac A`. -/
instance : IsScalarTower (intermediateSubalgebra R A M) A (FractionRing A) :=
  .of_algebraMap_eq fun _ => rfl

/-- The maps `A ∩ M → M → Frac A` compose to the algebra map `A ∩ M → Frac A`. -/
instance : IsScalarTower (intermediateSubalgebra R A M) M (FractionRing A) :=
  .of_algebraMap_eq fun _ => rfl

variable [IsIntegrallyClosed A] [Algebra.IsIntegral R A]

omit [IsDomain R] [FaithfulSMul R A] in
/-- Every element of `Frac A` becomes an element of `A` after multiplication by a nonzero element
of `R`. -/
theorem exists_ne_zero_algebraMap_mul_mem_range (x : FractionRing A) :
    ∃ r : R, r ≠ 0 ∧ ∃ a : A,
      algebraMap A (FractionRing A) a = algebraMap R (FractionRing A) r * x := by
  have : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  have : Algebra.IsAlgebraic R (FractionRing A) := Algebra.IsIntegral.trans_isAlgebraic R A _
  obtain ⟨r, hr, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) x).exists_integral_multiple
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hint.tower_top : IsIntegral A _)
  exact ⟨r, hr, a, by rw [ha, Algebra.smul_def]⟩

/-- **`M` is the fraction field of `A ∩ M`.** -/
theorem isFractionRing_intermediateSubalgebra :
    IsFractionRing (intermediateSubalgebra R A M) M where
  map_units y := by
    refine IsUnit.mk0 _ fun h => ?_
    exact nonZeroDivisors.coe_ne_zero y
      (intermediateSubalgebraToField_injective M (by rw [map_zero]; exact h))
  surj x := by
    obtain ⟨r, hr, a, ha⟩ := exists_ne_zero_algebraMap_mul_mem_range (R := R) (x : FractionRing A)
    have haM : a ∈ intermediateSubalgebra R A M := by
      rw [mem_intermediateSubalgebra, ha]
      refine M.mul_mem ?_ x.2
      rw [IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A)]
      exact M.algebraMap_mem _
    have hr' : algebraMap R (intermediateSubalgebra R A M) r ∈
        nonZeroDivisors (intermediateSubalgebra R A M) := by
      refine mem_nonZeroDivisors_of_ne_zero fun h => hr ?_
      exact FaithfulSMul.algebraMap_injective R A (by simpa using congrArg Subtype.val h)
    refine ⟨⟨⟨a, haM⟩, ⟨_, hr'⟩⟩, ?_⟩
    ext
    simp only [IntermediateField.coe_mul]
    rw [algebraMap_intermediateSubalgebra_apply, algebraMap_intermediateSubalgebra_apply, ha]
    simp [mul_comm, ← IsScalarTower.algebraMap_apply]
  exists_of_eq {x y} h := ⟨1, by simpa using intermediateSubalgebraToField_injective M h⟩

/-- **`A ∩ M` is integrally closed.** -/
theorem isIntegrallyClosed_intermediateSubalgebra :
    IsIntegrallyClosed (intermediateSubalgebra R A M) := by
  have := isFractionRing_intermediateSubalgebra M
  refine (isIntegrallyClosed_iff M).mpr fun {x} hx => ?_
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (show IsIntegral A (x : FractionRing A) from
      (hx.map (IsScalarTower.toAlgHom (intermediateSubalgebra R A M) M (FractionRing A))).tower_top)
  have haM : a ∈ intermediateSubalgebra R A M := by
    rw [mem_intermediateSubalgebra, ha]
    exact x.2
  exact ⟨⟨a, haM⟩, Subtype.ext ha⟩

variable (R A) in
/-- `Frac A` is finite-dimensional over `Frac R` when `A` is a finite `R`-module. -/
theorem finiteDimensional_fractionRing [Module.Finite R A] :
    FiniteDimensional (FractionRing R) (FractionRing A) := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := A)
  refine ⟨⟨t.image (algebraMap A (FractionRing A)), eq_top_iff.mpr fun x _ => ?_⟩⟩
  obtain ⟨r, hr, a, ha⟩ := exists_ne_zero_algebraMap_mul_mem_range (R := R) x
  have hra : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hr
  have hmem : algebraMap A (FractionRing A) a ∈
      Submodule.span (FractionRing R) (t.image (algebraMap A (FractionRing A)) : Set _) := by
    have hat : a ∈ Submodule.span R (t : Set A) := ht ▸ Submodule.mem_top
    have := Submodule.mem_map_of_mem
      (f := (IsScalarTower.toAlgHom R A (FractionRing A)).toLinearMap) hat
    rw [Submodule.map_span] at this
    refine Submodule.span_subset_span R (FractionRing R) _ ?_
    simpa using this
  have hx : x = (algebraMap R (FractionRing R) r)⁻¹ • algebraMap A (FractionRing A) a := by
    rw [ha, Algebra.smul_def, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A) r,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ hra, map_one, one_mul]
  rw [hx]
  exact Submodule.smul_mem _ _ hmem

/-- If `R` is Noetherian and `A` is a finite `R`-module, then `A ∩ M` is a finite `R`-module. -/
instance [IsNoetherianRing R] [Module.Finite R A] :
    Module.Finite R (intermediateSubalgebra R A M) :=
  Module.Finite.of_injective (IsScalarTower.toAlgHom R (intermediateSubalgebra R A M) A).toLinearMap
    Subtype.val_injective

/-- If `A` is a finite `R`-module, then `A` is a finite `A ∩ M`-module. -/
instance [Module.Finite R A] : Module.Finite (intermediateSubalgebra R A M) A :=
  Module.Finite.of_restrictScalars_finite R _ A

/-- The inclusion `A ∩ M → A` is injective. -/
instance : FaithfulSMul (intermediateSubalgebra R A M) A :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective

/-- The algebra map `R → A ∩ M` is injective. -/
instance : FaithfulSMul R (intermediateSubalgebra R A M) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr fun _ _ h =>
    FaithfulSMul.algebraMap_injective R A (congrArg Subtype.val h)

/-- **Both degrees drop.** If `M` is neither `Frac R` nor `Frac A`, then `[A ∩ M : R]` and
`[A : A ∩ M]` are both smaller than `[A : R]`. -/
theorem finrank_intermediateSubalgebra_lt [Module.Finite R A] (hbot : M ≠ ⊥) (htop : M ≠ ⊤) :
    Module.finrank R (intermediateSubalgebra R A M) < Module.finrank R A ∧
      Module.finrank (intermediateSubalgebra R A M) A < Module.finrank R A := by
  have := finiteDimensional_fractionRing R A
  have := isFractionRing_intermediateSubalgebra M
  have h1 : Module.finrank R (intermediateSubalgebra R A M) = Module.finrank (FractionRing R) M :=
    (IsFractionRing.finrank_eq R (FractionRing R) _ M).symm
  have h2 : Module.finrank (intermediateSubalgebra R A M) A = Module.finrank M (FractionRing A) :=
    (IsFractionRing.finrank_eq _ M A (FractionRing A)).symm
  have htower := Module.finrank_mul_finrank' (R := R) (S := intermediateSubalgebra R A M) A
  have hM1 : Module.finrank (FractionRing R) M ≠ 1 :=
    fun h => hbot (IntermediateField.finrank_eq_one_iff.mp h)
  have hM2 : Module.finrank M (FractionRing A) ≠ 1 :=
    fun h => htop (IntermediateField.finrank_eq_one_iff_eq_top.mp h)
  have : Module.IsTorsionFree (FractionRing R) M := DivisionSemiring.to_moduleIsTorsionFree
  have hM1' : 0 < Module.finrank (FractionRing R) M := Module.finrank_pos
  have hM2' : 0 < Module.finrank M (FractionRing A) := Module.finrank_pos
  rw [h1, h2] at htower ⊢
  rw [← htower]
  exact ⟨lt_mul_of_one_lt_right hM1' (by omega), lt_mul_of_one_lt_left hM2' (by omega)⟩

end Intermediate

/-! ### The induction -/

open AlgebraicGeometry

/-- **Resolution of complete local normal surfaces, from the two steps of the induction.**
Suppose that

* (`stepA`, the inductive step) whenever `B → A` is a finite injective map of Noetherian complete
  local normal domains with `A` of dimension two, `Spec B` has a resolution of singularities, and
  every complete local normal domain of dimension two which is finite over a regular complete
  local ring of dimension two of degree at most `[A : B]` has one, then `Spec A` has one; and
* (`stepB`, the base of the induction) whenever `A` is a Noetherian complete local normal domain
  finite over a regular complete local ring `R` of dimension two such that `Frac A / Frac R` has
  no intermediate field other than its two ends, `Spec A` has a resolution of singularities.

Then the spectrum of every Noetherian complete local normal domain of dimension two has a
resolution of singularities. -/
theorem exists_isResolution_of_steps
    (stepA : ∀ (B A : Type u) [CommRing B] [CommRing A] [IsNoetherianRing B] [IsLocalRing B]
      [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B] [IsNoetherianRing A] [IsLocalRing A]
      [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra B A] [Module.Finite B A]
      [FaithfulSMul B A], ringKrullDim A = 2 →
      (∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of B)), IsResolution g) →
      (∀ (R C : Type u) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
        [CommRing C] [IsNoetherianRing C] [IsLocalRing C] [IsNormalDomain C]
        [IsAdicComplete (maximalIdeal C) C] [Algebra R C] [Module.Finite R C] [FaithfulSMul R C],
        ringKrullDim R = 2 → Module.finrank R C ≤ Module.finrank B A →
        ∃ (Z : Scheme.{u}) (h : Z ⟶ Spec (.of C)), IsResolution h) →
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f)
    (stepB : ∀ (R A : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
      [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra R A] [Module.Finite R A]
      [FaithfulSMul R A], ringKrullDim R = 2 →
      (letI := FractionRing.liftAlgebra R (FractionRing A)
        ∀ M : IntermediateField (FractionRing R) (FractionRing A), M = ⊥ ∨ M = ⊤) →
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
  have key : ∀ n : ℕ, ∀ (R A : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra R A] [Module.Finite R A]
      [FaithfulSMul R A], ringKrullDim R = 2 → Module.finrank R A = n →
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro R A _ _ _ _ _ _ _ _ _ _ _ hR hn
    have : IsDomain R := IsRegularLocalRing.isDomain R
    let := FractionRing.liftAlgebra R (FractionRing A)
    by_cases hmin : ∀ M : IntermediateField (FractionRing R) (FractionRing A), M = ⊥ ∨ M = ⊤
    · exact stepB R A hR hmin
    push Not at hmin
    obtain ⟨M, hbot, htop⟩ := hmin
    let B := intermediateSubalgebra R A M
    obtain ⟨_, _, _⟩ := isNoetherianCompleteLocalRing_of_finite R B
    have : IsNormalDomain B := ⟨inferInstance, isIntegrallyClosed_intermediateSubalgebra M⟩
    obtain ⟨hltB, hltA⟩ := finrank_intermediateSubalgebra_lt M hbot htop
    rw [hn] at hltB hltA
    exact stepA B A ((Algebra.IsIntegral.ringKrullDim_eq R A).symm.trans hR)
      (ih _ hltB R B hR rfl) fun R' C _ _ _ _ _ _ _ _ _ _ _ hR' hle =>
        ih _ (hle.trans_lt hltA) R' C hR' rfl
  obtain ⟨d, Λ, _, _, -, hreg, hcomplete, φ, hinj, hfin, -⟩ :=
    IsLocalRing.exists_injective_finite_mvPowerSeries A
  let : Algebra (MvPowerSeries (Fin d) Λ) A := φ.toAlgebra
  have : Module.Finite (MvPowerSeries (Fin d) Λ) A := hfin
  have : FaithfulSMul (MvPowerSeries (Fin d) Λ) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact key _ (MvPowerSeries (Fin d) Λ) A
    ((Algebra.IsIntegral.ringKrullDim_eq (MvPowerSeries (Fin d) Λ) A).trans hdim) rfl

end Stacks.ResolutionOfSurfaces
