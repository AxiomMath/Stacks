module

public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Multiplication
public import Mathlib.Algebra.DirectSum.Ring

/-!
# The twisted global sections on Proj as a graded commutative ring

The pointwise product of twist sections built in
`StacksFrontier/AlgebraicGeometry/ProjTwistSectionRing/Multiplication.lean` makes the family
`n ↦ Γ(Proj(S), 𝒪(n))` of global-section groups into an additively graded commutative ring over
`ℕ`, so that the external direct sum `⨁ n, Γ(Proj(S), 𝒪(n))` is a commutative ring.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.gradedRing`: the graded commutative ring
  structure on `n ↦ Γ(Proj(S), 𝒪(n))`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_zero_right`,
  `zero_mul_left`, `mul_add_right`, `add_mul_left`: bilinearity of the product.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.cast_one_mul`,
  `cast_mul_one`, `cast_mul_assoc`, `cast_mul_comm`: the monoid laws, with the degrees
  transported by `cast` rather than by the heterogeneous equality of `GradedMonoid`.

## Implementation notes

**Every law is proved before the structure is assembled, and none of them mentions
`GradedMonoid`.** A graded monoid law such as associativity is an equation between dependent
pairs whose first components are equal only propositionally; `GradedMonoid` states it as such,
which means a proof written inside the structure instance has to open with `Sigma` plumbing and
then carry the whole pointwise computation while the partially-elaborated instance is in
scope. Writing the laws first, as equations between sections of a single twist with the degree
moved by `cast`, keeps each proof to a handful of pointwise rewrites, and reduces the instance
itself to a list of references: the plumbing appears once per law, applied to a finished
theorem. `cast_apply` is what makes that possible — it says the transport is invisible
pointwise — and it is proved by `cases` on the degree equality, which is the only place a
degree is ever eliminated.

The three `cast` laws are stated with the degrees in the order `GradedMonoid` produces them,
so that `heq_of_cast_eq` applied to `congrArg (twistGlobalSections 𝒮)` of the corresponding
`ℕ`-equation turns each one into the heterogeneous equality the field asks for with no further
transport.

The natural- and integer-number casts are the multiples of the unit section. Their three laws
are instances of the generic `AddCommGroup` facts `zero_nsmul`, `succ_nsmul`,
`natCast_zsmul` and `negSucc_zsmul`, so nothing about `Proj` enters there; the last of these
is exactly how Mathlib discharges the same field for the graded ring of additive
endomorphisms.

`gradedRing` is a `def` and not an `instance`. It is data that Tag 01MP asserts the existence
of, and the family it is a structure on is a plain `abbrev` for a sheaf-section group, so
registering it globally would put it in the way of instance search for every section group on
`Proj`.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.AlgebraicGeometry.ProjTwistSectionRing

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### Pointwise formulas for the additive structure and for the degree transport -/

/-- Sections of a twist are added pointwise. -/
@[simp] public theorem add_apply (n : ℕ) (s t : twistGlobalSections 𝒮 n)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) : (s + t).1 x = s.1 x + t.1 x := rfl

/-- The zero section of a twist vanishes at every point. -/
@[simp] public theorem zero_apply (n : ℕ)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (0 : twistGlobalSections 𝒮 n).1 x = 0 := rfl

/-- Transporting a section along an equality of degrees does not change its values. -/
@[simp] public theorem cast_apply {n m : ℕ} (h : n = m) (s : twistGlobalSections 𝒮 n)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (cast (congrArg (twistGlobalSections 𝒮) h) s).1 x = s.1 x := by
  cases h
  rfl

/-! ### Bilinearity of the product -/

/-- The product of twist sections vanishes when its right factor does. -/
public theorem mul_zero_right (n m : ℕ) (s : twistGlobalSections 𝒮 n) :
    mul 𝒮 n m s 0 = 0 := by
  refine section_ext 𝒮 fun x => ?_
  rw [mul_apply, zero_apply, zero_apply, mul_zero]

/-- The product of twist sections vanishes when its left factor does. -/
public theorem zero_mul_left (n m : ℕ) (t : twistGlobalSections 𝒮 m) :
    mul 𝒮 n m 0 t = 0 := by
  refine section_ext 𝒮 fun x => ?_
  rw [mul_apply, zero_apply, zero_apply, zero_mul]

/-- The product of twist sections is additive in its right factor. -/
public theorem mul_add_right (n m : ℕ) (s : twistGlobalSections 𝒮 n)
    (t₁ t₂ : twistGlobalSections 𝒮 m) :
    mul 𝒮 n m s (t₁ + t₂) = mul 𝒮 n m s t₁ + mul 𝒮 n m s t₂ := by
  refine section_ext 𝒮 fun x => ?_
  rw [mul_apply, add_apply, add_apply, mul_apply, mul_apply, mul_add]

/-- The product of twist sections is additive in its left factor. -/
public theorem add_mul_left (n m : ℕ) (s₁ s₂ : twistGlobalSections 𝒮 n)
    (t : twistGlobalSections 𝒮 m) :
    mul 𝒮 n m (s₁ + s₂) t = mul 𝒮 n m s₁ t + mul 𝒮 n m s₂ t := by
  refine section_ext 𝒮 fun x => ?_
  rw [mul_apply, add_apply, add_apply, mul_apply, mul_apply, add_mul]

/-! ### The monoid laws -/

/-- The unit section is a left identity, the degree `0 + j` being transported to `j`. -/
public theorem cast_one_mul (j : ℕ) (s : twistGlobalSections 𝒮 j) :
    cast (congrArg (twistGlobalSections 𝒮) (zero_add j)) (mul 𝒮 0 j (one 𝒮) s) = s := by
  refine section_ext 𝒮 fun x => ?_
  rw [cast_apply 𝒮 (zero_add j), mul_apply, one_apply, one_mul]

/-- The unit section is a right identity, the degree `j + 0` being transported to `j`. -/
public theorem cast_mul_one (j : ℕ) (s : twistGlobalSections 𝒮 j) :
    cast (congrArg (twistGlobalSections 𝒮) (add_zero j)) (mul 𝒮 j 0 s (one 𝒮)) = s := by
  refine section_ext 𝒮 fun x => ?_
  rw [cast_apply 𝒮 (add_zero j), mul_apply, one_apply, mul_one]

/-- The product of twist sections is associative, the degree `i + j + k` being transported to
`i + (j + k)`. -/
public theorem cast_mul_assoc (i j k : ℕ) (a : twistGlobalSections 𝒮 i)
    (b : twistGlobalSections 𝒮 j) (c : twistGlobalSections 𝒮 k) :
    cast (congrArg (twistGlobalSections 𝒮) (add_assoc i j k))
        (mul 𝒮 (i + j) k (mul 𝒮 i j a b) c) =
      mul 𝒮 i (j + k) a (mul 𝒮 j k b c) := by
  refine section_ext 𝒮 fun x => ?_
  rw [cast_apply 𝒮 (add_assoc i j k), mul_apply, mul_apply, mul_apply, mul_apply, mul_assoc]

/-- The product of twist sections is commutative, the degree `i + j` being transported to
`j + i`. -/
public theorem cast_mul_comm (i j : ℕ) (a : twistGlobalSections 𝒮 i)
    (b : twistGlobalSections 𝒮 j) :
    cast (congrArg (twistGlobalSections 𝒮) (add_comm i j)) (mul 𝒮 i j a b) =
      mul 𝒮 j i b a := by
  refine section_ext 𝒮 fun x => ?_
  rw [cast_apply 𝒮 (add_comm i j), mul_apply, mul_apply, mul_comm]

/-! ### The graded ring structure -/

/-- The graded commutative ring structure on the twisted global sections: the product is
pointwise multiplication of local fractions and the unit is the global section attached to the
homogeneous element `1`. -/
@[instance_reducible] public def gradedRing : DirectSum.GCommRing (twistGlobalSections 𝒮) := by
  letI : GradedMonoid.GMul (twistGlobalSections 𝒮) := ⟨fun {n m} => mul 𝒮 n m⟩
  letI : GradedMonoid.GOne (twistGlobalSections 𝒮) := ⟨one 𝒮⟩
  refine
    { mul := fun {n m} => mul 𝒮 n m
      one := one 𝒮
      mul_zero := fun {n m} s => mul_zero_right 𝒮 n m s
      zero_mul := fun {n m} t => zero_mul_left 𝒮 n m t
      mul_add := fun {n m} s t₁ t₂ => mul_add_right 𝒮 n m s t₁ t₂
      add_mul := fun {n m} s₁ s₂ t => add_mul_left 𝒮 n m s₁ s₂ t
      one_mul := ?_
      mul_one := ?_
      mul_assoc := ?_
      mul_comm := ?_
      natCast := fun k => k • one 𝒮
      natCast_zero := zero_nsmul (one 𝒮)
      natCast_succ := fun k => succ_nsmul (one 𝒮) k
      intCast := fun z => z • one 𝒮
      intCast_ofNat := fun k => natCast_zsmul (one 𝒮) k
      intCast_negSucc_ofNat := fun k => negSucc_zsmul (one 𝒮) k }
  · rintro ⟨j, s⟩
    exact Sigma.ext (zero_add j)
      (heq_of_cast_eq (congrArg (twistGlobalSections 𝒮) (zero_add j)) (cast_one_mul 𝒮 j s))
  · rintro ⟨j, s⟩
    exact Sigma.ext (add_zero j)
      (heq_of_cast_eq (congrArg (twistGlobalSections 𝒮) (add_zero j)) (cast_mul_one 𝒮 j s))
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    exact Sigma.ext (add_assoc i j k)
      (heq_of_cast_eq (congrArg (twistGlobalSections 𝒮) (add_assoc i j k))
        (cast_mul_assoc 𝒮 i j k a b c))
  · rintro ⟨i, a⟩ ⟨j, b⟩
    exact Sigma.ext (add_comm i j)
      (heq_of_cast_eq (congrArg (twistGlobalSections 𝒮) (add_comm i j))
        (cast_mul_comm 𝒮 i j a b))

end Stacks.AlgebraicGeometry.ProjTwistSectionRing

end
