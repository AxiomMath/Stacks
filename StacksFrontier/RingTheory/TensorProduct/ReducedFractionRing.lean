module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The total ring of fractions of the reduction of a base change

Let `A` be a domain with fraction field `K`, let `B` be a finite flat `A`-algebra whose
localization at the nonzero elements of `A` is `L`, and let `O` be a domain containing `A`
with fraction field `F`. **The total ring of fractions of the reduction of `O ⊗[A] B` is the
reduction of `F ⊗[K] L`.**

The ring `O ⊗[A] B` is a finite flat `O`-algebra, so inverting the nonzero elements of `O`
turns it into the finite `F`-algebra `F ⊗[K] L`, which is Artinian; in an Artinian ring every
nonzerodivisor is a unit, so no further elements remain to be inverted once the reduction is
taken, and the reduction of `F ⊗[K] L` is already the total ring of fractions of the reduction
of `O ⊗[A] B`. Note that `F ⊗[K] L` itself need not be reduced, which is why the quotient by
the nilradical appears on both sides.

## Main definitions

* `nilradicalQuotientAlgebra`: the algebra structure induced on reductions by an algebra map.
* `tensorProductFractionRingAlgebra`: the algebra structure on `F ⊗[K] L` over `O ⊗[A] B`
  given by the two localization maps `O → F` and `B → L`.

## Main results

* `isFractionRing_nilradicalQuotient`: if `S` is a localization of `R` at a submonoid of
  nonzerodivisors and `S` is Artinian, then the reduction of `S` is the total ring of fractions
  of the reduction of `R`.
* `isLocalization_tensorProduct_fractionRing`: `F ⊗[K] L` is the localization of `O ⊗[A] B` at
  the nonzero elements of `O`.
* `isFractionRing_nilradicalQuotient_tensorProduct`: the reduction of `F ⊗[K] L` is the total
  ring of fractions of the reduction of `O ⊗[A] B`.
-/

@[expose] public section

open scoped nonZeroDivisors TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Reduction

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An algebra map carries nilpotents to nilpotents, hence induces an algebra structure on the
reductions. -/
@[instance_reducible]
noncomputable def nilradicalQuotientAlgebra (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Algebra (R ⧸ nilradical R) (S ⧸ nilradical S) :=
  Ideal.Quotient.algebraQuotientOfLEComap fun _ hx ↦
    Ideal.mem_comap.mpr (mem_nilradical.mpr ((mem_nilradical.mp hx).map (algebraMap R S)))

/-- The image of a nonzerodivisor in the reduction of a ring is a nonzerodivisor. -/
theorem mem_nonZeroDivisors_nilradicalQuotient {a : R} (ha : a ∈ nonZeroDivisors R) :
    Ideal.Quotient.mk (nilradical R) a ∈ nonZeroDivisors (R ⧸ nilradical R) := by
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
  obtain ⟨n, hn⟩ := hx
  rw [mul_pow] at hn
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨n, mem_nonZeroDivisors_iff_right.mp (pow_mem ha n) _ hn⟩

/-- The reduction of a localization of `R` at a submonoid `M` is the localization of the
reduction of `R` at the image of `M`. -/
theorem isLocalization_nilradicalQuotient (M : Submonoid R) [IsLocalization M S] :
    letI := nilradicalQuotientAlgebra R S
    IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ nilradical R) M) (S ⧸ nilradical S) :=
  let := nilradicalQuotientAlgebra R S
  IsLocalization.of_surjective M S (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl (by
      simp only [Ideal.mk_ker]
      simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
        (IsLocalization.map_radical M S (⊥ : Ideal R)).ge)

/-- If `S` is a localization of `R` at a submonoid consisting of nonzerodivisors and `S` is
Artinian, then the reduction of `S` is the total ring of fractions of the reduction of `R`. -/
theorem isFractionRing_nilradicalQuotient (M : Submonoid R) [IsLocalization M S]
    [IsArtinianRing S] (hM : M ≤ nonZeroDivisors R) :
    letI := nilradicalQuotientAlgebra R S
    IsFractionRing (R ⧸ nilradical R) (S ⧸ nilradical S) := by
  let _ := nilradicalQuotientAlgebra R S
  have _ := isLocalization_nilradicalQuotient (S := S) M
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid (R ⧸ nilradical R) M)
    (nonZeroDivisors (R ⧸ nilradical R)) ?_ fun r hr ↦ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact mem_nonZeroDivisors_nilradicalQuotient (hM hy)
  · exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors
      (IsLocalization.nonZeroDivisors_le_comap
        (Algebra.algebraMapSubmonoid (R ⧸ nilradical R) M) _ hr)

end Reduction

section BaseChange

variable (A O K F B L : Type*) [CommRing A] [CommRing O] [CommRing K] [CommRing F] [CommRing B]
  [CommRing L] [Algebra A O] [Algebra A K] [Algebra A F] [Algebra A B] [Algebra A L]
  [Algebra K F] [Algebra K L] [Algebra O F] [Algebra B L]
  [IsScalarTower A O F] [IsScalarTower A K F] [IsScalarTower A B L] [IsScalarTower A K L]

/-- The `O ⊗[A] B`-algebra structure on `F ⊗[K] L` determined by the two maps `O → F` and
`B → L`. -/
@[instance_reducible]
noncomputable def tensorProductFractionRingAlgebra : Algebra (O ⊗[A] B) (F ⊗[K] L) :=
  (Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] L).restrictScalars A).comp
      (IsScalarTower.toAlgHom A O F))
    (((Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L).restrictScalars A).comp
      (IsScalarTower.toAlgHom A B L))
    fun _ _ ↦ Commute.all _ _).toRingHom.toAlgebra

/-- Inverting the nonzero elements of `O` in `O ⊗[A] B` gives `F ⊗[K] L`, for `K` the fraction
field of `A`, `F` the fraction field of `O`, and `L` the localization of `B` at the nonzero
elements of `A`. -/
theorem isLocalization_tensorProduct_fractionRing [IsLocalization (nonZeroDivisors A) K]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    [IsLocalization (nonZeroDivisors O) F] :
    letI := tensorProductFractionRingAlgebra A O K F B L
    IsLocalization (Algebra.algebraMapSubmonoid (O ⊗[A] B) (nonZeroDivisors O)) (F ⊗[K] L) := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  let _ : Algebra B (F ⊗[K] L) := ((algebraMap L (F ⊗[K] L)).comp (algebraMap B L)).toAlgebra
  have _ : IsScalarTower B L (F ⊗[K] L) := IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsScalarTower A L (F ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L (F ⊗[K] L),
      ← IsScalarTower.algebraMap_apply A K (F ⊗[K] L)]
  have _ : IsScalarTower A B (F ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply B L (F ⊗[K] L), ← IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply A L (F ⊗[K] L)]
  have _ : IsScalarTower O (O ⊗[A] B) (F ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun o ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have _ : IsScalarTower B (O ⊗[A] B) (F ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun b ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have _ : IsScalarTower A (O ⊗[A] B) (F ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A O (O ⊗[A] B),
      ← IsScalarTower.algebraMap_apply O (O ⊗[A] B) (F ⊗[K] L),
      ← IsScalarTower.algebraMap_apply A O (F ⊗[K] L)]
  have _ : Algebra.IsPushout A K B L :=
    (Algebra.isPushout_of_isLocalization (nonZeroDivisors A) K B L).symm
  have h : Algebra.IsPushout A F B (F ⊗[K] L) :=
    (Algebra.IsPushout.comp_iff A K B L (T := F) (T' := F ⊗[K] L)).mpr inferInstance
  exact (Algebra.isLocalization_iff_isPushout (nonZeroDivisors O) F).mpr
    ((Algebra.IsPushout.comp_iff A O B (O ⊗[A] B) (T := F) (T' := F ⊗[K] L)).mp h).symm

/-- **The total ring of fractions of the reduction of a base change.** For `A` a domain with
fraction field `K`, `B` a finite flat `A`-algebra with `L` its localization at the nonzero
elements of `A`, and `O` a domain over `A` with fraction field `F`, the reduction of
`F ⊗[K] L` is the total ring of fractions of the reduction of `O ⊗[A] B`. -/
theorem isFractionRing_nilradicalQuotient_tensorProduct [IsArtinianRing F] [IsDomain O]
    [Module.Flat A B] [Module.Finite K L] [IsLocalization (nonZeroDivisors A) K]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    [IsLocalization (nonZeroDivisors O) F] :
    letI := tensorProductFractionRingAlgebra A O K F B L
    letI := nilradicalQuotientAlgebra (O ⊗[A] B) (F ⊗[K] L)
    IsFractionRing ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B))
      ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)) := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  have _ := isLocalization_tensorProduct_fractionRing A O K F B L
  have _ : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  have _ : IsArtinianRing (F ⊗[K] L) := isArtinian_of_tower F inferInstance
  refine isFractionRing_nilradicalQuotient
    (Algebra.algebraMapSubmonoid (O ⊗[A] B) (nonZeroDivisors O)) ?_
  rintro x ⟨o, ho, rfl⟩
  refine mem_nonZeroDivisors_iff_right.mpr fun y hy ↦ ?_
  have hreg : IsSMulRegular (O ⊗[A] B) (algebraMap O (O ⊗[A] B) o) :=
    IsSMulRegular.of_flat (IsRegular.of_ne_zero
      (mem_nonZeroDivisors_iff_ne_zero.mp ho)).left
  exact hreg (by simpa [Algebra.smul_def, mul_comm] using hy)

end BaseChange
