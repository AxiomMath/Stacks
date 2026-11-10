module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.RingTheory.Length.FlatLocalHom

/-!
# The delta invariant under extension of the ground field

A flat local homomorphism of local rings does not decrease the delta invariant, because the
base change of the quotient defining the invariant injects into the quotient defining the
invariant of the target. Applied to the stalks of a scheme over a field and of its base change
along a field extension, this says that the delta invariant of a locally algebraic scheme at a
point is at most its delta invariant at any point of the base change lying over it.

## Main results

* `AlgebraicGeometry.deltaInvariant_mul_length_quotient_le_of_flat_local_hom`: the inequality
  with the length of the closed fibre of the homomorphism as a factor on the smaller side.
* `AlgebraicGeometry.deltaInvariant_stalk_le_baseChange`: the delta invariant does not decrease
  under extension of the ground field.
* `AlgebraicGeometry.deltaInvariant_mul_length_specialFibre_stalk_le_baseChange`: the same
  inequality with the length of the special fibre of the map on local rings as a factor on the
  smaller side.

## Implementation notes

The base change is Mathlib's categorical pullback along `Spec K ⟶ Spec k`, and the delta
invariant of a scheme at a point is the ring-theoretic invariant of its stalk. The source states
the inequality for a point at which the scheme is geometrically reduced and where both stalks
have dimension one; neither hypothesis is used, so the statement here is the unconditional one
for a flat local base change of stalks.

## References

* [Stacks Project, Tag 0C3X](https://stacks.math.columbia.edu/tag/0C3X)
-/

@[expose] public section

open CategoryTheory Limits CommRingCat
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open scoped TensorProduct

/-- Along a flat algebra, the image of a non-zero-divisor is a non-zero-divisor. -/
private lemma algebraMapSubmonoid_nonZeroDivisors_le_of_flat
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
  rintro _ ⟨a, ha, rfl⟩
  refine mem_nonZeroDivisors_iff_right.mpr fun b hb => ?_
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) ha
  simp only [Algebra.smul_def, mul_zero]
  rwa [mul_comm]

/-- The map `B ⊗[A] Frac(A) → Frac(B)` of `B`-algebras along a flat algebra `A → B`. -/
private noncomputable def tensorFractionRingToFractionRing
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    B ⊗[A] FractionRing A →ₐ[B] FractionRing B :=
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (B ⊗[A] FractionRing A) := IsLocalization.tensor (FractionRing A) (nonZeroDivisors A)
  have hu (y : Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) :
      IsUnit (algebraMap B (FractionRing B) y) :=
    IsLocalization.map_units (FractionRing B)
      ⟨y.1, algebraMapSubmonoid_nonZeroDivisors_le_of_flat A B y.2⟩
  { IsLocalization.lift hu with commutes' := IsLocalization.lift_eq hu }

/-- The map `B ⊗[A] Frac(A) → Frac(B)` along a flat algebra is injective. -/
private lemma tensorFractionRingToFractionRing_injective
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    Function.Injective (tensorFractionRingToFractionRing A B) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (B ⊗[A] FractionRing A) := IsLocalization.tensor (FractionRing A) (nonZeroDivisors A)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, hs⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) z
  have ha : algebraMap B (FractionRing B) a = 0 := by
    rw [← (tensorFractionRingToFractionRing A B).commutes a, ← hs, map_mul, hz, zero_mul]
  obtain rfl : a = 0 := IsLocalization.injective (FractionRing B) le_rfl (by rw [ha, map_zero])
  exact (IsLocalization.map_units (B ⊗[A] FractionRing A) s).mul_left_eq_zero.mp
    (by rw [hs, map_zero])

/-- Along a flat algebra `A → B`, the base change of the integral closure of `A` in `Frac(A)`
lands in the integral closure of `B` in `Frac(B)`. -/
private lemma tensorFractionRingToFractionRing_baseChange_mem_integralClosure
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (z : B ⊗[A] integralClosure A (FractionRing A)) :
    (tensorFractionRingToFractionRing A B).toLinearMap.comp
        ((integralClosure A (FractionRing A)).val.toLinearMap.baseChange B) z ∈
      integralClosure B (FractionRing B) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    rw [map_add]
    exact add_mem hz hw
  | tmul b a =>
    let φ : FractionRing A →ₐ[A] FractionRing B :=
      ((tensorFractionRingToFractionRing A B).restrictScalars A).comp
        Algebra.TensorProduct.includeRight
    have hz : (b ⊗ₜ[A] a : B ⊗[A] integralClosure A (FractionRing A)) = b • (1 ⊗ₜ[A] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hgx : (tensorFractionRingToFractionRing A B).toLinearMap.comp
        ((integralClosure A (FractionRing A)).val.toLinearMap.baseChange B) (1 ⊗ₜ[A] a) =
          φ (a : FractionRing A) := by
      simp [φ]
    rw [hz, map_smul, hgx]
    simpa [Algebra.smul_def] using (integralClosure B (FractionRing B)).mul_mem
      (algebraMap B (integralClosure B (FractionRing B)) b).property
      ((a.property.map φ).tower_top (A := B))

/-- The `B`-linear map from the base change of the integral closure of `A` in `Frac(A)` to the
integral closure of `B` in `Frac(B)`, along a flat algebra `A → B`. -/
private noncomputable def baseChangeIntegralClosureMap
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    B ⊗[A] integralClosure A (FractionRing A) →ₗ[B] integralClosure B (FractionRing B) :=
  LinearMap.codRestrict (integralClosure B (FractionRing B)).toSubmodule _
    (tensorFractionRingToFractionRing_baseChange_mem_integralClosure A B)

/-- The map from the base change of the integral closure is injective. -/
private lemma baseChangeIntegralClosureMap_injective
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    Function.Injective (baseChangeIntegralClosureMap A B) := fun _ _ h =>
  ((tensorFractionRingToFractionRing_injective A B).comp
    (by
      rw [LinearMap.baseChange_eq_lTensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.coe_injective))
    (congrArg Subtype.val h)

/-- The map from the base change of the integral closure is compatible with the structure maps
of the two integral closures. -/
private lemma baseChangeIntegralClosureMap_comp_lTensor
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    (baseChangeIntegralClosureMap A B).comp
        (TensorProduct.AlgebraTensorModule.lTensor B B
          (Algebra.linearMap A (integralClosure A (FractionRing A)))) =
      (Algebra.linearMap B (integralClosure B (FractionRing B))).comp
        (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap := by
  set NA := integralClosure A (FractionRing A)
  set e := baseChangeIntegralClosureMap A B
  apply TensorProduct.AlgebraTensorModule.ext
  intro b a
  have hmul : TensorProduct.AlgebraTensorModule.lTensor B B (Algebra.linearMap A NA)
      (b ⊗ₜ[A] a) = Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := NA) b *
        Algebra.TensorProduct.includeRight (algebraMap A NA a) := by
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    simp
  have heright : e (Algebra.TensorProduct.includeRight (algebraMap A NA a)) =
      algebraMap B (integralClosure B (FractionRing B)) (algebraMap A B a) := by
    apply Subtype.ext
    have hsrc : (NA.val.toLinearMap.baseChange B)
        (Algebra.TensorProduct.includeRight (algebraMap A NA a)) =
          algebraMap B (B ⊗[A] FractionRing A) (algebraMap A B a) := by
      simp [LinearMap.baseChange_tmul]
    change tensorFractionRingToFractionRing A B (NA.val.toLinearMap.baseChange B _) = _
    rw [hsrc]
    exact (tensorFractionRingToFractionRing A B).commutes _
  have hsmul : Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := NA) b *
        Algebra.TensorProduct.includeRight (algebraMap A NA a) =
      b • Algebra.TensorProduct.includeRight (algebraMap A NA a) := by
    simp [Algebra.TensorProduct.includeLeft_apply, Algebra.smul_def]
  rw [LinearMap.comp_apply, hmul, hsmul, map_smul, heright]
  simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]

/-- If an injective `B`-linear map `e : B ⊗[A] M → N` carries the base change of `fA : A → M`
to `fB : B → N`, then the base change of `M / fA(A)` has length at most that of `N / fB(B)`. -/
private lemma length_baseChange_quotient_range_le_of_injective {A B M N : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (fA : A →ₗ[A] M) (fB : B →ₗ[B] N) (e : B ⊗[A] M →ₗ[B] N) (he : Function.Injective e)
    (hcomp : e.comp (TensorProduct.AlgebraTensorModule.lTensor B B fA) =
      fB.comp (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap) :
    Module.length B (B ⊗[A] (M ⧸ LinearMap.range fA)) ≤
      Module.length B (N ⧸ LinearMap.range fB) := by
  let lf := TensorProduct.AlgebraTensorModule.lTensor B B fA
  let rid := TensorProduct.AlgebraTensorModule.rid A B B
  let P : Submodule B (B ⊗[A] M) := LinearMap.range lf
  let qmk := (LinearMap.range fB).mkQ
  have hker : P ≤ LinearMap.ker (qmk.comp e) := by
    rw [LinearMap.range_le_ker_iff, LinearMap.comp_assoc, hcomp, ← LinearMap.comp_assoc]
    ext
    simp [qmk]
  let q : (B ⊗[A] M) ⧸ P →ₗ[B] N ⧸ LinearMap.range fB := P.liftQ (qmk.comp e) hker
  have hqinj : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P z
    obtain ⟨b, hb⟩ : e z ∈ LinearMap.range fB := by
      simpa [q, qmk, Submodule.liftQ_apply] using hz
    obtain ⟨t, ht⟩ := rid.surjective b
    have het : e (lf t) = e z := by
      have h₁ : e (lf t) = fB (rid t) := DFunLike.congr_fun hcomp t
      rw [h₁, ht, hb]
    obtain rfl := he het
    exact (Submodule.mem_bot B).2
      ((Submodule.Quotient.mk_eq_zero P).2 (LinearMap.mem_range_self lf t))
  let Pbase : Submodule B (B ⊗[A] M) :=
    LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor B B
      ((LinearMap.range fA).subtype.restrictScalars A))
  have hP : Pbase = P := by
    rw [← (Submodule.restrictScalars_injective A _ _).eq_iff]
    change LinearMap.range (LinearMap.lTensor B
      (Submodule.subtype (LinearMap.range fA))) = LinearMap.range (LinearMap.lTensor B fA)
    exact (LinearMap.lTensor_range (Q := B) (g := fA)).symm
  let et : B ⊗[A] (M ⧸ LinearMap.range fA) ≃ₗ[B] (B ⊗[A] M) ⧸ P :=
    (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv B A B (LinearMap.range fA)).trans
      (Pbase.quotEquivOfEq P hP)
  exact Module.length_le_of_injective (q.comp et.toLinearMap) (hqinj.comp et.injective)

/-- **The delta invariant under a flat local homomorphism, with the length of the closed fibre
as a factor.** For a flat local homomorphism `f : A → B` of local rings, the delta invariant of
`A` times the length of `B / 𝔪_A B` is at most the delta invariant of `B`.

The base change `B ⊗[A] (A'/A)` injects into `B'/B`, so its length bounds `δ(B)`; the length of
a base change along a flat local homomorphism is the length of the module times the length of
the closed fibre (`length_baseChange_eq_length_mul_length_quotient`, Tag 02M1), which is the
left-hand side.  Dropping the factor — it is at least one — gives Tag 0C3X itself,
`AlgebraicGeometry.deltaInvariant_le_of_flat_local_hom`. -/
@[stacks 0C3X "sharpened by the length of the closed fibre: the source states the inequality \
without that factor"]
public lemma deltaInvariant_mul_length_quotient_le_of_flat_local_hom
    (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hlocal : IsLocalHom f) (hflat : f.Flat) :
    Ring.deltaInvariant A *
        Module.length B (B ⧸ Ideal.map f (IsLocalRing.maximalIdeal A)) ≤
      Ring.deltaInvariant B := by
  let : Algebra A B := f.toAlgebra
  have : IsLocalHom (algebraMap A B) := hlocal
  have : Module.Flat A B := hflat
  have hlen := length_baseChange_quotient_range_le_of_injective _ _ _
    (baseChangeIntegralClosureMap_injective A B) (baseChangeIntegralClosureMap_comp_lTensor A B)
  simpa [Ring.deltaInvariant, extendedMaximalIdeal, RingHom.algebraMap_toAlgebra] using
    (length_baseChange_eq_length_mul_length_quotient A B
      (integralClosure A (FractionRing A) ⧸ LinearMap.range (Algebra.linearMap A _))).trans_le hlen

/-- **Stacks Tag 0C3X, in its ring-theoretic form.** A flat local homomorphism of local rings
does not decrease the delta invariant.  The length of the closed fibre is at least one, so this
is `AlgebraicGeometry.deltaInvariant_mul_length_quotient_le_of_flat_local_hom` with that factor
dropped. -/
private lemma deltaInvariant_le_of_flat_local_hom
    (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hlocal : IsLocalHom f) (hflat : f.Flat) :
    Ring.deltaInvariant A ≤ Ring.deltaInvariant B := by
  have hcne : Module.length B (B ⧸ Ideal.map f (IsLocalRing.maximalIdeal A)) ≠ 0 := by
    rw [ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial]
    exact Ideal.Quotient.nontrivial_iff.mpr
      (ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top f))
  have hc : 1 ≤ Module.length B (B ⧸ Ideal.map f (IsLocalRing.maximalIdeal A)) :=
    Order.one_le_iff_ne_zero.mpr hcne
  calc
    Ring.deltaInvariant A = Ring.deltaInvariant A * 1 := (mul_one _).symm
    _ ≤ Ring.deltaInvariant A *
        Module.length B (B ⧸ Ideal.map f (IsLocalRing.maximalIdeal A)) := by gcongr
    _ ≤ Ring.deltaInvariant B :=
      deltaInvariant_mul_length_quotient_le_of_flat_local_hom A B f hlocal hflat

/-- The map on stalks of the projection of the base change along a field extension is flat. -/
private lemma flat_stalkMap_fst_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom.Flat := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := (Flat.SpecMap_iff).2
    (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K))
  exact Flat.stalkMap _ y

/-- **Stacks Project, Tag 0C3X.** The delta invariant of a scheme locally of finite type over a
field at a point cannot decrease under an extension of the ground field. -/
@[stacks 0C3X]
public lemma deltaInvariant_stalk_le_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) y = x) :
    Ring.deltaInvariant (X.presheaf.stalk x) ≤
      Ring.deltaInvariant
        ((pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y) := by
  let e := eqToHom (congrArg X.presheaf.stalk hy.symm)
  exact deltaInvariant_le_of_flat_local_hom _ _ (e ≫ (pullback.fst f _).stalkMap y).hom
    inferInstance
    ((RingHom.Flat.of_bijective
      ((ConcreteCategory.isIso_iff_bijective _).mp (inferInstance : IsIso e))).comp
      (flat_stalkMap_fst_baseChange k K f y))

/-- **The delta invariant of a stalk under extension of the ground field, with the length of the
special fibre as a factor.** The delta invariant at `x` times the length of the quotient of the
local ring at a point `y` above `x` by the extension of the maximal ideal at `x` is at most the
delta invariant at `y`.

Dropping the factor — it is at least one — gives Stacks Tag 0C3X itself,
`AlgebraicGeometry.deltaInvariant_stalk_le_baseChange`.  Keeping it turns a delta invariant
that does not grow into a bound on the special fibre: when both delta invariants equal one the
quotient has length one, so the maximal ideal at `x` already generates the maximal ideal
at `y`. -/
@[stacks 0C3X "sharpened by the length of the special fibre of the map on local rings: the \
source states the inequality without that factor"]
public lemma deltaInvariant_mul_length_specialFibre_stalk_le_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    Ring.deltaInvariant
        (X.presheaf.stalk
          ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)) *
        Module.length
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
            Scheme.{u}).presheaf.stalk y)
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
              Scheme.{u}).presheaf.stalk y ⧸
            Ideal.map
              ((pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom
              (IsLocalRing.maximalIdeal
                (X.presheaf.stalk
                  ((pullback.fst f
                    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)))) ≤
      Ring.deltaInvariant
        ((pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y) := by
  exact deltaInvariant_mul_length_quotient_le_of_flat_local_hom _ _
    ((pullback.fst f _).stalkMap y).hom inferInstance (flat_stalkMap_fst_baseChange k K f y)

end AlgebraicGeometry

end
