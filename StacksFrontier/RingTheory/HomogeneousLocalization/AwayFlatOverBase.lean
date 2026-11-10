module

public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayFlat
public import StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra

/-!
# Flatness of the degree-zero localization over a base ring that need not be the degree-zero part

Let `A` be a commutative ring graded by a `SetLike` family `𝒜 : ι → σ`, and let `R` be a base ring
mapping to `A` so that the image of `R` is homogeneous of degree zero. Every graded piece `𝒜 i` is
then an `R`-submodule of `A`, and `HomogeneousLocalization.Away 𝒜 a` is an `R`-algebra through
`R → 𝒜 0 → Away 𝒜 a`. The main result is that this `R`-algebra is flat as soon as the graded
pieces of degree a large multiple of `deg a` are flat `R`-modules.

## Main definitions

* `GradedRing.toSubmodules` promotes a `SetLike` grading to a grading by `R`-submodules.
* `GradedRing.toGradeZero` is the structure map of the base ring, read as a ring homomorphism to
  the degree-zero part.
* `GradedRing.toSubmodulesHom` and `GradedRing.ofSubmodulesHom` are the identity of `A`, read as
  graded ring homomorphisms between the two gradings.
* `HomogeneousLocalization.Away.toSubmodulesEquiv` identifies the degree-zero localizations taken
  with respect to the two gradings.

## Main results

* `HomogeneousLocalization.Away.flat_fromZeroRingHom_comp`: if `a ∈ 𝒜 d` and the `R`-submodule
  `𝒜 (n • d)` is flat for every `n ≥ N`, then the structure map `R → 𝒜 0 → Away 𝒜 a` is flat.

## References

* [Stacks Project, Tag 0D4C](https://stacks.math.columbia.edu/tag/0D4C)
* [Stacks Project, Tag 05UT](https://stacks.math.columbia.edu/tag/05UT)
-/

@[expose] public noncomputable section

universe u v w

namespace GradedRing

variable {ι : Type u} {R : Type v} {A : Type w} {σ : Type*} [CommRing R] [CommRing A]
  [Algebra R A] [SetLike σ A] [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
  (𝒜 : ι → σ) [GradedRing 𝒜] (h0 : ∀ r : R, algebraMap R A r ∈ 𝒜 0)

/-- **A `SetLike` grading whose degree-zero part contains the image of the base ring is a grading
by submodules over that base ring.** The `i`-th member is the `i`-th graded piece, with the same
underlying set. -/
public def toSubmodules (i : ι) : Submodule R A where
  carrier := 𝒜 i
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' r x hx := by
    rw [Algebra.smul_def]
    simpa using SetLike.mul_mem_graded (h0 r) hx

/-- The promoted grading has the same members as the original one. -/
@[simp]
public theorem mem_toSubmodules {i : ι} {x : A} : x ∈ toSubmodules 𝒜 h0 i ↔ x ∈ 𝒜 i := Iff.rfl

/-- The promoted grading is a grading, with the homogeneous decomposition of the original one. -/
public instance instGradedRingToSubmodules : GradedRing (toSubmodules 𝒜 h0) where
  one_mem := SetLike.one_mem_graded 𝒜
  mul_mem := fun _ _ _ _ hi hj => SetLike.mul_mem_graded (A := 𝒜) hi hj
  decompose' := DirectSum.decompose 𝒜
  left_inv := DirectSum.Decomposition.left_inv
  right_inv := DirectSum.Decomposition.right_inv

/-- **The structure map of the base ring, read as a map to the degree-zero part.** -/
public def toGradeZero : R →+* 𝒜 0 where
  toFun r := ⟨algebraMap R A r, h0 r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The degree-zero corestriction of the structure map is the structure map. -/
@[simp]
public theorem coe_toGradeZero_apply (r : R) :
    (toGradeZero 𝒜 h0 r : A) = algebraMap R A r := rfl

/-- The identity of `A`, read as a graded ring homomorphism from a `SetLike` grading to its
promotion to a grading by `R`-submodules. -/
public def toSubmodulesHom : 𝒜 →+*ᵍ toSubmodules 𝒜 h0 where
  __ := RingHom.id A
  map_mem := id

/-- The identity of `A`, read as a graded ring homomorphism from the promoted grading back to the
original one. -/
public def ofSubmodulesHom : toSubmodules 𝒜 h0 →+*ᵍ 𝒜 where
  __ := RingHom.id A
  map_mem := id

/-- The graded ring homomorphism into the promoted grading is the identity of `A`. -/
@[simp]
public theorem toSubmodulesHom_apply (x : A) : toSubmodulesHom 𝒜 h0 x = x := rfl

/-- The graded ring homomorphism out of the promoted grading is the identity of `A`. -/
@[simp]
public theorem ofSubmodulesHom_apply (x : A) : ofSubmodulesHom 𝒜 h0 x = x := rfl

end GradedRing

namespace HomogeneousLocalization.Away

open GradedRing

variable {ι : Type u} {R : Type v} {A : Type w} {σ : Type*} [CommRing R] [CommRing A]
  [Algebra R A] [SetLike σ A] [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
  (𝒜 : ι → σ) [GradedRing 𝒜] (h0 : ∀ r : R, algebraMap R A r ∈ 𝒜 0) (a : A)

/-- **The degree-zero localization does not see the promotion of the grading:** the identity of
`A` induces an isomorphism between the degree-zero localizations away from `a` with respect to the
two gradings. -/
public def toSubmodulesEquiv : Away 𝒜 a ≃+* Away (toSubmodules 𝒜 h0) a where
  __ := Away.map (toSubmodulesHom 𝒜 h0) a
  invFun := Away.map (ofSubmodulesHom 𝒜 h0) a
  left_inv := by rintro ⟨c⟩; rfl
  right_inv := by rintro ⟨c⟩; rfl

/-- The identification of the two degree-zero localizations does not change the underlying
fraction in the ordinary localization. -/
@[simp]
public theorem val_toSubmodulesEquiv (z : Away 𝒜 a) :
    (toSubmodulesEquiv 𝒜 h0 a z).val = z.val := by
  induction z using Quotient.ind
  rfl

/-- Under `HomogeneousLocalization.Away.toSubmodulesEquiv`, the composite `R → 𝒜 0 → Away 𝒜 a` is
the structure map of `Away (toSubmodules 𝒜 h0) a` as an `R`-algebra. -/
public theorem toSubmodulesEquiv_fromZeroRingHom_comp (r : R) :
    toSubmodulesEquiv 𝒜 h0 a
        ((fromZeroRingHom 𝒜 (Submonoid.powers a)) (toGradeZero 𝒜 h0 r)) =
      algebraMap R (Away (toSubmodules 𝒜 h0) a) r := by
  refine val_injective _ ?_
  rw [val_toSubmodulesEquiv, val_algebraMap]
  change Localization.mk (algebraMap R A r) 1 = _
  rw [Localization.mk_one_eq_algebraMap, ← IsScalarTower.algebraMap_apply R A _]

include h0 in
/-- **The degree-zero localization at a homogeneous element of degree `d` is flat over the base
ring as soon as the graded pieces of degree a large multiple of `d` are flat.** -/
public theorem flat_fromZeroRingHom_comp {d : ι} (ha : a ∈ 𝒜 d) (N : ℕ)
    (hflat : ∀ n : ℕ, N ≤ n → Module.Flat R (toSubmodules 𝒜 h0 (n • d))) :
    RingHom.Flat ((fromZeroRingHom 𝒜 (Submonoid.powers a)).comp (toGradeZero 𝒜 h0)) := by
  rw [← RingHom.Flat.comp_iff_of_bijective_left (g := (toSubmodulesEquiv 𝒜 h0 a).toRingHom)
    (toSubmodulesEquiv 𝒜 h0 a).bijective]
  have he : ((toSubmodulesEquiv 𝒜 h0 a).toRingHom.comp
      ((fromZeroRingHom 𝒜 (Submonoid.powers a)).comp (toGradeZero 𝒜 h0))) =
      algebraMap R (Away (toSubmodules 𝒜 h0) a) :=
    RingHom.ext fun r => toSubmodulesEquiv_fromZeroRingHom_comp 𝒜 h0 a r
  rw [he, RingHom.flat_algebraMap_iff]
  exact flat_of_eventually_flat (toSubmodules 𝒜 h0) ha N hflat

end HomogeneousLocalization.Away

end
