module

public import Mathlib.FieldTheory.Galois.Infinite
public import StacksCore.FieldTheory.KrullTopology
public import StacksFrontier.RingTheory.Invariant.InertiaStrictHenselization

/-!
# The fixed field of an inertia group is the strictly henselized fraction field

Let `A` be a normal local domain with fraction field `K`, let `L / K` be a Galois extension with
`L` separably closed, let `B` be the integral closure of `A` in `L` and let `q` be a prime of `B`.
Write `I = q.inertia Gal(L/K)` for the inertia group at `q`. The ring `(B_q)^I` of
`IsIntegralClosure.inertiaInvariants` is a strict henselization of `A` when `q` lies over the
maximal ideal of `A` (Stacks 0BSW, the unnumbered step of its proof); this file identifies its
fraction field inside `L` as the fixed field `L^I`.

Two facts make the identification work. First, `I` is closed in the Krull topology: an element
outside `I` moves some `b ∈ B` out of `q`, and the set of automorphisms agreeing with it on `b`
is open by Stacks 0BMJ. So `L^I` has `I` as its fixing subgroup, by the Galois correspondence for
closed subgroups. Second, every `I`-invariant element of `L` is a ratio of two elements of
`(B_q)^I`: a nonzero multiple of it by an element of `A` lies in `B`, and that multiple is again
`I`-invariant, so numerator and denominator are both inertia invariants.

## Main results

* `IsIntegralClosure.isClosed_inertia` — the inertia group is closed in `Gal(L/K)`.
* `IsIntegralClosure.inertiaFixedField` — the fixed field `L^I`, as an intermediate field of
  `L / K`.
* `IsIntegralClosure.fixingSubgroup_inertiaFixedField` — the fixing subgroup of `L^I` is `I`.
* `IsIntegralClosure.isFractionRing_inertiaFixedField` — **`L^I` is a fraction field of
  `(B_q)^I`.**

## Implementation notes

The algebra structure of `(B_q)^I` on `L^I` is the restriction of the inclusion
`(B_q)^I ⊆ B_q ⊆ L`, written out as `IsIntegralClosure.toInertiaFixedField`; the algebra
structure of `A` on `L^I` is the one factoring through `K`, so that both
`IsScalarTower A K L^I` and `IsScalarTower A (B_q)^I L^I` hold. Those are the towers that the
local exact sequence of Stacks 0BSM asks for.

Closedness of the inertia group is stated for an arbitrary ideal `q`: neither primality nor the
lying-over condition is used.

## References

* [Stacks Project, Tag 0BSW](https://stacks.math.columbia.edu/tag/0BSW)
* [Stacks Project, Tag 0BMJ](https://stacks.math.columbia.edu/tag/0BMJ)

## Tags

inertia group, fixed field, strict henselization, Krull topology, fraction field
-/

@[expose] public noncomputable section

universe u

open IsLocalRing

namespace IsIntegralClosure

section Galois

open scoped Pointwise

variable (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsFractionRing A K] [IsGalois K L]

attribute [local instance] galAction galSMulCommClass

/-! ### The inertia group is closed -/

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- **The inertia group at a prime of `B` is closed in the Krull topology on `Gal(L/K)`.** An
automorphism outside the inertia group moves some `b ∈ B` out of `q`, and by Stacks 0BMJ the set
of automorphisms agreeing with it on `b` is an open neighbourhood disjoint from the inertia
group. -/
theorem isClosed_inertia (q : Ideal (integralClosure A L)) :
    IsClosed (q.inertia Gal(L/K) : Set Gal(L/K)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  have hσ' : σ ∉ q.inertia Gal(L/K) := hσ
  rw [Ideal.mem_inertia] at hσ'
  push Not at hσ'
  obtain ⟨b, hb⟩ := hσ'
  refine ⟨{τ : Gal(L/K) | τ (b : L) = σ (b : L)}, ?_, ?_, rfl⟩
  · intro τ hτ hτI
    have hsmul : τ • b = σ • b :=
      Subtype.ext ((coe_smul A K L τ b).trans (hτ.trans (coe_smul A K L σ b).symm))
    exact hb (by simpa only [hsmul] using (Ideal.mem_inertia.mp hτI) b)
  · exact isOpen_krullTopology_apply_eq' K (b : L) (σ (b : L))

/-! ### The fixed field of the inertia group -/

/-- **The fixed field `L^I` of the inertia group at `q`**, as an intermediate field of
`L / K`. -/
abbrev inertiaFixedField (q : Ideal (integralClosure A L)) : IntermediateField K L :=
  IntermediateField.fixedField (q.inertia Gal(L/K))

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- **The fixing subgroup of `L^I` is the inertia group itself**, the inertia group being closed:
this is the Galois correspondence for closed subgroups. -/
theorem fixingSubgroup_inertiaFixedField (q : Ideal (integralClosure A L)) :
    (inertiaFixedField A K L q).fixingSubgroup = q.inertia Gal(L/K) :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨q.inertia Gal(L/K), isClosed_inertia A K L q⟩

/-- An element of `(B_q)^I`, read inside `L`, is fixed by the inertia group. -/
theorem coe_mem_inertiaFixedField (q : Ideal (integralClosure A L)) [q.IsPrime]
    (x : inertiaInvariants A K L q) :
    ((x : localizedSubring q) : L) ∈ inertiaFixedField A K L q :=
  (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ =>
    (mem_inertiaInvariants_iff A K L q _).mp x.2 σ hσ

/-- **The inclusion of `(B_q)^I` into `L^I`**, the restriction of the inclusion
`(B_q)^I ⊆ B_q ⊆ L`. -/
def toInertiaFixedField (q : Ideal (integralClosure A L)) [q.IsPrime] :
    inertiaInvariants A K L q →+* inertiaFixedField A K L q where
  toFun x := ⟨((x : localizedSubring q) : L), coe_mem_inertiaFixedField A K L q x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion `(B_q)^I → L^I` is the inclusion, read inside `L`. -/
theorem coe_toInertiaFixedField (q : Ideal (integralClosure A L)) [q.IsPrime]
    (x : inertiaInvariants A K L q) :
    ((toInertiaFixedField A K L q x : inertiaFixedField A K L q) : L)
      = ((x : localizedSubring q) : L) := rfl

/-- The inclusion `(B_q)^I → L^I` is injective, both rings sitting inside `L`. -/
theorem toInertiaFixedField_injective (q : Ideal (integralClosure A L)) [q.IsPrime] :
    Function.Injective (toInertiaFixedField A K L q) := fun _ _ h =>
  Subtype.ext (Subtype.ext
    (congrArg (fun z : inertiaFixedField A K L q => (z : L)) h))

/-- The algebra structure of `(B_q)^I` on `L^I`, through
`IsIntegralClosure.toInertiaFixedField`. -/
instance algebraInertiaInvariantsFixedField (q : Ideal (integralClosure A L)) [q.IsPrime] :
    Algebra (inertiaInvariants A K L q) (inertiaFixedField A K L q) :=
  (toInertiaFixedField A K L q).toAlgebra

/-- The structure map `(B_q)^I → L^I` is the inclusion, read inside `L`. -/
theorem coe_algebraMap_inertiaFixedField (q : Ideal (integralClosure A L)) [q.IsPrime]
    (x : inertiaInvariants A K L q) :
    ((algebraMap (inertiaInvariants A K L q) (inertiaFixedField A K L q) x :
        inertiaFixedField A K L q) : L)
      = ((x : localizedSubring q) : L) := rfl

/-- The algebra structure of `A` on `L^I`, factoring through `K`. -/
instance algebraInertiaFixedField (q : Ideal (integralClosure A L)) :
    Algebra A (inertiaFixedField A K L q) :=
  ((algebraMap K (inertiaFixedField A K L q)).comp (algebraMap A K)).toAlgebra

/-- The structure map `A → L^I` factors through `K`. -/
instance isScalarTower_inertiaFixedField (q : Ideal (integralClosure A L)) :
    IsScalarTower A K (inertiaFixedField A K L q) :=
  .of_algebraMap_eq' rfl

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The structure map `A → L^I` is the structure map `A → L`, read inside `L`. -/
theorem coe_algebraMap_inertiaFixedField_base (q : Ideal (integralClosure A L)) (a : A) :
    ((algebraMap A (inertiaFixedField A K L q) a : inertiaFixedField A K L q) : L)
      = algebraMap A L a := by
  rw [IsScalarTower.algebraMap_apply A K (inertiaFixedField A K L q),
    IsScalarTower.algebraMap_apply A K L]
  rfl

/-- The structure map `A → L^I` factors through `(B_q)^I`, as one checks inside `L`. -/
instance isScalarTower_inertiaInvariants_inertiaFixedField
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    IsScalarTower A (inertiaInvariants A K L q) (inertiaFixedField A K L q) :=
  .of_algebraMap_eq fun a => Subtype.ext (by
    rw [coe_algebraMap_inertiaFixedField, coe_algebraMap_inertiaInvariants,
      coe_algebraMap_inertiaFixedField_base])

/-! ### `L^I` is a fraction field of `(B_q)^I` -/

include K in
/-- An `I`-invariant element of `L` has an `I`-invariant numerator and a denominator in `A`: a
nonzero `A`-multiple of it lies in `B`, and that multiple is again `I`-invariant. -/
theorem exists_mem_inertiaInvariants_smul_eq (q : Ideal (integralClosure A L)) [q.IsPrime]
    (z : inertiaFixedField A K L q) :
    ∃ (r : A) (b : inertiaInvariants A K L q), r ≠ 0 ∧
      algebraMap A L r * (z : L) = ((b : localizedSubring q) : L) := by
  have : Algebra.IsAlgebraic A L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K L)
  obtain ⟨r, s, hr, hs⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := A) (z : L)).exists_smul_eq (integralClosure A L)
  have hs' : algebraMap A L r * (z : L) = (s : L) := by
    simpa [Algebra.smul_def] using hs
  have hfix : ∀ σ ∈ q.inertia Gal(L/K),
      σ (algebraMap (integralClosure A L) (localizedSubring q) s : L) =
        (algebraMap (integralClosure A L) (localizedSubring q) s : L) := by
    intro σ hσ
    have hz : σ (z : L) = (z : L) :=
      (IntermediateField.mem_fixedField_iff _ _).1 z.2 σ hσ
    have hr' : σ (algebraMap A L r) = algebraMap A L r := by
      rw [IsScalarTower.algebraMap_apply A K L]
      exact σ.commutes _
    have : σ ((s : L)) = (s : L) := by rw [← hs', map_mul, hz, hr']
    simpa [coe_algebraMap_localizedSubring] using this
  refine ⟨r, ⟨algebraMap (integralClosure A L) (localizedSubring q) s,
    (mem_inertiaInvariants_iff A K L q _).mpr hfix⟩, hr, ?_⟩
  simpa [coe_algebraMap_localizedSubring] using hs'

include K in
/-- **`L^I` is a fraction field of `(B_q)^I`.** Every `I`-invariant element of `L` is a ratio of
two elements of `(B_q)^I` by
`IsIntegralClosure.exists_mem_inertiaInvariants_smul_eq`, and `(B_q)^I` injects into the field
`L^I`, so the nonzero divisors become units. -/
theorem isFractionRing_inertiaFixedField (q : Ideal (integralClosure A L)) [q.IsPrime] :
    IsFractionRing (inertiaInvariants A K L q) (inertiaFixedField A K L q) := by
  have hinj : Function.Injective
      (algebraMap (inertiaInvariants A K L q) (inertiaFixedField A K L q)) :=
    toInertiaFixedField_injective A K L q
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  · refine isUnit_iff_ne_zero.mpr fun hy => ?_
    exact nonZeroDivisors.coe_ne_zero y (hinj (hy.trans (map_zero _).symm))
  · obtain ⟨r, b, hr, hrz⟩ := exists_mem_inertiaInvariants_smul_eq A K L q z
    have hrne : algebraMap A (inertiaInvariants A K L q) r ≠ 0 := by
      intro h0
      have h1 : algebraMap A L r = 0 := by
        rw [← coe_algebraMap_inertiaInvariants A K L q r, h0]
        simp
      rw [IsScalarTower.algebraMap_apply A K L] at h1
      exact hr (IsFractionRing.to_map_eq_zero_iff.mp
        ((algebraMap K L).injective (h1.trans (map_zero (algebraMap K L)).symm)))
    refine ⟨(b, ⟨algebraMap A (inertiaInvariants A K L q) r,
      mem_nonZeroDivisors_of_ne_zero hrne⟩), Subtype.ext ?_⟩
    show (z : L) * ((algebraMap (inertiaInvariants A K L q) (inertiaFixedField A K L q)
        (algebraMap A (inertiaInvariants A K L q) r) : inertiaFixedField A K L q) : L)
      = ((algebraMap (inertiaInvariants A K L q) (inertiaFixedField A K L q) b :
        inertiaFixedField A K L q) : L)
    rw [coe_algebraMap_inertiaFixedField, coe_algebraMap_inertiaFixedField,
      coe_algebraMap_inertiaInvariants, mul_comm]
    exact hrz

end Galois

end IsIntegralClosure

end
