module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The second continuous cohomology group of the units of a Galois extension

Let `Ω/K` be a Galois extension, possibly infinite. The continuous `2`-cochains of `Gal(Ω/K)`
with values in the discrete Galois module `Ωˣ` are the locally constant maps
`Gal(Ω/K) × Gal(Ω/K) → Ωˣ`; among them the `2`-cocycles form a subgroup, inside which the
coboundaries of locally constant `1`-cochains form a subgroup, and the quotient is the second
continuous cohomology group `H²(Gal(Ω/K), Ωˣ)`.

This is the group in which the classes of the two-cocycles attached to central simple algebras
live, so it is the target of the Brauer group map of
[Stacks, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7).

## Main definitions

* `Stacks.GaloisCohomology.twoCocycles`: the group of locally constant `2`-cocycles.
* `Stacks.GaloisCohomology.twoCoboundaries`: the subgroup of coboundaries of locally constant
  `1`-cochains.
* `Stacks.GaloisCohomology.TwoCohomology`: the quotient `H²(Gal(Ω/K), Ωˣ)`.
* `Stacks.GaloisCohomology.twoCohomologyClass`: the class of a locally constant `2`-cocycle.

## Main results

* `Stacks.GaloisCohomology.twoCohomologyClass_eq_one_iff`: a cocycle has trivial class exactly
  when it is the coboundary of a locally constant `1`-cochain.
* `Stacks.GaloisCohomology.twoCohomologyClass_surjective`: every cohomology class is the class
  of a cocycle.

## Implementation notes

The cocycle and coboundary conditions are Mathlib's `IsMulCocycle₂` and `IsMulCoboundary₂`, as
in `Hilbert90` and `TwoCocycleInflation`; continuity of a cochain is local constancy for the
Krull topology, the coefficients being discrete. Mathlib's comparison of `IsMulCocycle₂` with
`groupCohomology.cocycles₂` is stated only for a group and a module in `Type 0`, whereas
`Gal(Ω/K)` lives in the universe of `Ω`, so the quotient is formed here by hand rather than
imported.

The group is written multiplicatively, because its coefficients are: a class is an element of a
quotient of subgroups of `Gal(Ω/K) × Gal(Ω/K) → Ωˣ`. Composing with `Additive.ofMul` gives the
additive spelling customary for cohomology.

## References

* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7)
-/

@[expose] public section

open groupCohomology

namespace Stacks.GaloisCohomology

variable (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra K Ω]

/-- The locally constant multiplicative `2`-cocycles of `Gal(Ω/K)` with values in `Ωˣ`, a
subgroup of all maps `Gal(Ω/K) × Gal(Ω/K) → Ωˣ` under pointwise multiplication. -/
def twoCocycles : Subgroup (Gal(Ω/K) × Gal(Ω/K) → Ωˣ) where
  carrier := {c | IsLocallyConstant c ∧ IsMulCocycle₂ c}
  one_mem' := by
    refine ⟨IsLocallyConstant.const 1, ?_⟩
    intro σ τ υ
    simp
  mul_mem' := by
    rintro c e ⟨hclc, hc⟩ ⟨helc, he⟩
    refine ⟨hclc.comp₂ helc (· * ·), ?_⟩
    intro σ τ υ
    simp only [Pi.mul_apply, smul_mul']
    calc c (σ * τ, υ) * e (σ * τ, υ) * (c (σ, τ) * e (σ, τ))
        = c (σ * τ, υ) * c (σ, τ) * (e (σ * τ, υ) * e (σ, τ)) := by ac_rfl
      _ = σ • c (τ, υ) * c (σ, τ * υ) * (σ • e (τ, υ) * e (σ, τ * υ)) := by
          rw [hc σ τ υ, he σ τ υ]
      _ = _ := by ac_rfl
  inv_mem' := by
    rintro c ⟨hclc, hc⟩
    refine ⟨hclc.comp (Inv.inv : Ωˣ → Ωˣ), ?_⟩
    intro σ τ υ
    simpa only [Pi.inv_apply, smul_inv', mul_inv] using congrArg Inv.inv (hc σ τ υ)

variable {K Ω}

/-- A map `Gal(Ω/K) × Gal(Ω/K) → Ωˣ` lies in `twoCocycles K Ω` exactly when it is locally
constant and a multiplicative `2`-cocycle. -/
theorem mem_twoCocycles_iff (c : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) :
    c ∈ twoCocycles K Ω ↔ IsLocallyConstant c ∧ IsMulCocycle₂ c :=
  Iff.rfl

/-- A locally constant `2`-cocycle, as an element of the group of such. -/
def twoCocyclesMk (c : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) (hlc : IsLocallyConstant c)
    (hc : IsMulCocycle₂ c) : twoCocycles K Ω :=
  ⟨c, hlc, hc⟩

/-- The underlying map of `twoCocyclesMk c hlc hc` is `c`. -/
@[simp]
theorem coe_twoCocyclesMk (c : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) (hlc : IsLocallyConstant c)
    (hc : IsMulCocycle₂ c) :
    (twoCocyclesMk c hlc hc : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) = c :=
  rfl

/-- An element of `twoCocycles K Ω` is a locally constant map. -/
theorem isLocallyConstant_of_mem_twoCocycles (c : twoCocycles K Ω) :
    IsLocallyConstant (c : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) :=
  c.2.1

/-- An element of `twoCocycles K Ω` is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_of_mem_twoCocycles (c : twoCocycles K Ω) :
    IsMulCocycle₂ (c : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) :=
  c.2.2

variable (K Ω)

/-- The coboundaries of locally constant `1`-cochains, a subgroup of the locally constant
`2`-cocycles. -/
def twoCoboundaries : Subgroup (twoCocycles K Ω) where
  carrier := {c | ∃ b : Gal(Ω/K) → Ωˣ, IsLocallyConstant b ∧
    ∀ σ τ : Gal(Ω/K), σ • b τ / b (σ * τ) * b σ = (c : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) (σ, τ)}
  one_mem' := by
    refine ⟨1, IsLocallyConstant.const 1, ?_⟩
    intro σ τ
    simp
  mul_mem' := by
    rintro c e ⟨b, hblc, hb⟩ ⟨a, halc, ha⟩
    refine ⟨b * a, hblc.comp₂ halc (· * ·), fun σ τ => ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply]
    rw [← hb σ τ, ← ha σ τ]
    simp only [smul_mul', div_eq_mul_inv, mul_inv]
    ac_rfl
  inv_mem' := by
    rintro c ⟨b, hblc, hb⟩
    refine ⟨b⁻¹, hblc.comp (Inv.inv : Ωˣ → Ωˣ), fun σ τ => ?_⟩
    simp only [Subgroup.coe_inv, Pi.inv_apply]
    rw [← hb σ τ]
    simp only [smul_inv', div_eq_mul_inv, mul_inv]

variable {K Ω}

/-- A locally constant `2`-cocycle `c` lies in `twoCoboundaries K Ω` exactly when
`c (σ, τ) = σ • b τ / b (σ * τ) * b σ` for some locally constant `b : Gal(Ω/K) → Ωˣ`. -/
theorem mem_twoCoboundaries_iff (c : twoCocycles K Ω) :
    c ∈ twoCoboundaries K Ω ↔ ∃ b : Gal(Ω/K) → Ωˣ, IsLocallyConstant b ∧
      ∀ σ τ : Gal(Ω/K), σ • b τ / b (σ * τ) * b σ = (c : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) (σ, τ) :=
  Iff.rfl

/-- A coboundary of a locally constant `1`-cochain is in particular a coboundary in the sense of
`groupCohomology.IsMulCoboundary₂`. -/
theorem isMulCoboundary₂_of_mem_twoCoboundaries (c : twoCocycles K Ω)
    (hc : c ∈ twoCoboundaries K Ω) :
    IsMulCoboundary₂ (c : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) := by
  obtain ⟨b, -, hb⟩ := hc
  exact ⟨b, fun σ τ => hb σ τ⟩

variable (K Ω)

/-- The second continuous cohomology group `H²(Gal(Ω/K), Ωˣ)`, as locally constant `2`-cocycles
modulo coboundaries of locally constant `1`-cochains. -/
abbrev TwoCohomology := twoCocycles K Ω ⧸ twoCoboundaries K Ω

variable {K Ω}

/-- The class in `H²(Gal(Ω/K), Ωˣ)` of a locally constant `2`-cocycle. -/
def twoCohomologyClass : twoCocycles K Ω →* TwoCohomology K Ω :=
  QuotientGroup.mk' (twoCoboundaries K Ω)

/-- The class of a locally constant `2`-cocycle is its image in the quotient. -/
theorem twoCohomologyClass_apply (c : twoCocycles K Ω) :
    twoCohomologyClass c = QuotientGroup.mk c :=
  rfl

/-- The trivial `2`-cocycle has trivial class. -/
@[simp]
theorem twoCohomologyClass_one : twoCohomologyClass (1 : twoCocycles K Ω) = 1 :=
  map_one _

/-- The class of a product of locally constant `2`-cocycles is the product of their classes. -/
theorem twoCohomologyClass_mul (c e : twoCocycles K Ω) :
    twoCohomologyClass (c * e) = twoCohomologyClass c * twoCohomologyClass e :=
  map_mul _ _ _

/-- Two locally constant `2`-cocycles have the same class exactly when their ratio is the
coboundary of a locally constant `1`-cochain. -/
theorem twoCohomologyClass_eq_iff (c e : twoCocycles K Ω) :
    twoCohomologyClass c = twoCohomologyClass e ↔ c⁻¹ * e ∈ twoCoboundaries K Ω :=
  QuotientGroup.eq

/-- A locally constant `2`-cocycle has trivial class exactly when it is the coboundary of a
locally constant `1`-cochain. -/
theorem twoCohomologyClass_eq_one_iff (c : twoCocycles K Ω) :
    twoCohomologyClass c = 1 ↔ c ∈ twoCoboundaries K Ω :=
  QuotientGroup.eq_one_iff c

/-- Every element of `H²(Gal(Ω/K), Ωˣ)` is the class of a locally constant `2`-cocycle. -/
theorem twoCohomologyClass_surjective :
    Function.Surjective (twoCohomologyClass : twoCocycles K Ω → TwoCohomology K Ω) :=
  QuotientGroup.mk_surjective

end Stacks.GaloisCohomology
