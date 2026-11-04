module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.F6Rank201.WeilCohomologyBasePoint
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chow identity at the base point, and the cycle class of the point

Let `(S, δ)` be a base situation for Chow homology whose base has a single point and whose
dimension function vanishes — the case `S = Spec(k)`. Stacks 0AZ1 identifies `A_0(S)` with `ℤ`
(`Stacks.Chow.chowGroupBaseEquivInt`). This file proves that the identification carries the
fundamental class `[S]` to `1`, hence that `A_0(S)` is free of rank one on `[S]`, and pins down
the intersection product of `A_0(S)` from that: there is exactly one biadditive product on
`A_0(S)` for which `[S]` is a unit, and in it

  `[S] · [S] = [S]`.

That identity is the step of Stacks 0FHE which
`StacksFrontier.AlgebraicGeometry.F6Rank201.WeilCohomologyBasePoint` carries as the hypothesis
`cycleClass_fundamental_mul`, on the cohomology side and for an abstract cycle group. With it
proved, the last two clauses of Stacks 0FHE — that the cycle class of the point is the unit and
that the integral of the unit is `1` — follow from axiom `(C)(c)` alone, and that is how they are
stated here.

## Main results

* `Stacks.Chow.chowGroupBaseEquivInt_fundamentalChowClass` — the identification `A_0(S) = ℤ` of
  Stacks 0AZ1 sends `[S]` to `1`. Every docstring of that identification asserts this; this is
  the proof.
* `Stacks.Chow.eq_zsmul_fundamentalChowClass` — `A_0(S) = ℤ·[S]`: every class is the multiple of
  `[S]` by its degree.
* `Stacks.Chow.fundamentalChowClass_baseChowMul_self` — **the Chow identity**
  `[S] · [S] = [S]`, for the product `Stacks.Chow.baseChowMul`.
* `Stacks.Chow.eq_baseChowMul` — that product is the only biadditive one with `[S]` as a left
  unit, so the identity does not depend on the choice.
* `Stacks.Weil.cycleClass_fundamentalChowClass_eq_one` — the third clause of Stacks 0FHE with the
  Chow identity discharged: `γ([S]) = 1` from axiom `(C)(c)`.
* `Stacks.Weil.trace_one_fundamentalChowClass_eq_one` — the fourth clause, likewise.

## Implementation notes

### What the product is, and what is not proved about it

`Stacks.Chow.baseChowMul` is the product of `A_0(S)` read through Stacks 0AZ1: `α · β` is the
multiple of `[S]` by the product of the two degrees. It is not *assumed* to have `[S]` as a unit;
that is `Stacks.Chow.baseChowMul_fundamentalChowClass`, proved from
`Stacks.Chow.chowGroupBaseEquivInt_fundamentalChowClass`. And it is not an arbitrary choice among
products: by `Stacks.Chow.eq_baseChowMul` any biadditive product on `A_0(S)` having `[S]` as a
left unit is equal to it. So the identity `[S] · [S] = [S]` holds for whichever product a
consumer has.

What is **not** proved here is that `Stacks.Chow.intersectionProduct` — the product
`α · β = Δ^!(α × β)` of Stacks 0FC0, in
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct` — restricts to this one on the base.
Two lemmas are missing for that, and neither exists in this repository: that
`pullback.diagonal (𝟙 S)` is an isomorphism, and an evaluation of
`Stacks.Chow.intersectionProduct` in degree `d = 0` at the Gysin class of that diagonal (the
`Stacks.Chow.diagonalGysinProduct` of the definition has no lemmas at all). Until those exist a
consumer holding the Stacks 0FC0 product must go through
`Stacks.Chow.eq_baseChowMul`, supplying its unit law.

### Why the Chow part is in this file

`Stacks.Chow.baseChowMul` and the lemmas about it are stated in the `Stacks.Chow` namespace but
live here because Stacks 0FHE is their only consumer and the identity is tagged to it. A dedup
pass may move them next to `Stacks.Chow.chowGroupBaseEquivInt` in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree`.

## References

* [Stacks Project, Tag 0FHE](https://stacks.math.columbia.edu/tag/0FHE)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w t

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (hδ : ∀ s : C.S, C.dimensionFunction s = 0)
  [Subsingleton C.S] [IsIntegral C.S]

include hδ

/-- **The fundamental cycle of the base has coefficient one.** The base is integral, so it is its
own unique irreducible component and the multiplicity of that component is the length of the
residue field of the generic point over itself, which is one. -/
theorem fundamentalCycle_id_apply (s : C.S) : (fundamentalCycle C (𝟙 C.S) 0).1 s = 1 := by
  have hξ : genericPoint C.S ∈ genericPoints C.S := genericPoint_mem_genericPoints C.S
  have hs : s = genericPoint C.S := Subsingleton.elim _ _
  subst hs
  have hdim : relativeDimension C.dimensionFunction (𝟙 C.S)
      ((𝟙 C.S : C.S ⟶ C.S) (⟨genericPoint C.S, hξ⟩ : genericPoints C.S).1) = 0 := by
    rw [relativeDimension_id, hδ]
  have h := cycleAssociatedToClosedSubscheme_apply C (𝟙 C.S) (𝟙 C.S) (0 : ℤ)
    ⟨genericPoint C.S, hξ⟩ hdim
  rw [componentMultiplicity_eq_one (𝟙 C.S) hξ] at h
  exact h

/-- **The identification `A_0(S) = ℤ` of Stacks 0AZ1 sends `[S]` to `1`.** This is the
normalisation the degree homomorphism of Stacks 0AZ1 is defined by. -/
@[simp]
theorem chowGroupBaseEquivInt_fundamentalChowClass (s : C.S) :
    chowGroupBaseEquivInt C hδ s (fundamentalChowClass C (𝟙 C.S) 0) = 1 := by
  rw [fundamentalChowClass, chowGroupBaseEquivInt_mk]
  exact fundamentalCycle_id_apply C hδ s

/-- **`A_0(S) = ℤ·[S]`.** On a one-point base with vanishing dimension function the zeroth Chow
group is free of rank one on the fundamental class, and the coordinate of a class is its
degree. -/
theorem eq_zsmul_fundamentalChowClass (s : C.S) (α : chowGroup C (𝟙 C.S) 0) :
    α = chowGroupBaseEquivInt C hδ s α • fundamentalChowClass C (𝟙 C.S) 0 := by
  refine (chowGroupBaseEquivInt C hδ s).injective ?_
  rw [map_zsmul, chowGroupBaseEquivInt_fundamentalChowClass]
  simp

/-- The intersection product of `A_0(S)` for a one-point base with vanishing dimension function,
read through the identification `A_0(S) = ℤ` of Stacks 0AZ1: the product of two classes is the
multiple of the fundamental class by the product of their degrees.

`Stacks.Chow.eq_baseChowMul` shows this is the only biadditive product on `A_0(S)` having `[S]`
as a left unit. -/
def baseChowMul (s : C.S) (α β : chowGroup C (𝟙 C.S) 0) : chowGroup C (𝟙 C.S) 0 :=
  (chowGroupBaseEquivInt C hδ s α * chowGroupBaseEquivInt C hδ s β) •
    fundamentalChowClass C (𝟙 C.S) 0

/-- The fundamental class of the base is a left unit for the product of `A_0(S)`. -/
@[simp]
theorem baseChowMul_fundamentalChowClass (s : C.S) (β : chowGroup C (𝟙 C.S) 0) :
    baseChowMul C hδ s (fundamentalChowClass C (𝟙 C.S) 0) β = β := by
  rw [baseChowMul, chowGroupBaseEquivInt_fundamentalChowClass, one_mul]
  exact (eq_zsmul_fundamentalChowClass C hδ s β).symm

/-- The fundamental class of the base is a right unit for the product of `A_0(S)`. -/
@[simp]
theorem baseChowMul_fundamentalChowClass_right (s : C.S) (α : chowGroup C (𝟙 C.S) 0) :
    baseChowMul C hδ s α (fundamentalChowClass C (𝟙 C.S) 0) = α := by
  rw [baseChowMul, chowGroupBaseEquivInt_fundamentalChowClass, mul_one]
  exact (eq_zsmul_fundamentalChowClass C hδ s α).symm

/-- **The Chow identity `[S] · [S] = [S]`.** The self-intersection of the fundamental class of
the base is the fundamental class: it is the unit of the ring `A_0(S) = ℤ` of Stacks 0AZ1. This
is the step of Stacks 0FHE's proof that the cohomological statements of
`StacksFrontier.AlgebraicGeometry.F6Rank201.WeilCohomologyBasePoint` carry as a hypothesis. -/
@[stacks 0FHE "the Chow identity `[Spec(k)] · [Spec(k)] = [Spec(k)]`, proved from the \
identification `A_0(Spec(k)) = ℤ` of Stacks 0AZ1 and the normalisation `[Spec(k)] ↦ 1`"]
theorem fundamentalChowClass_baseChowMul_self (s : C.S) :
    baseChowMul C hδ s (fundamentalChowClass C (𝟙 C.S) 0)
        (fundamentalChowClass C (𝟙 C.S) 0) =
      fundamentalChowClass C (𝟙 C.S) 0 :=
  baseChowMul_fundamentalChowClass C hδ s _

omit [AlgebraicGeometry.IsIntegral C.S] in
/-- The product of `A_0(S)` is additive in its left argument. -/
theorem baseChowMul_add_left (s : C.S) (α α' β : chowGroup C (𝟙 C.S) 0) :
    baseChowMul C hδ s (α + α') β =
      baseChowMul C hδ s α β + baseChowMul C hδ s α' β := by
  rw [baseChowMul, baseChowMul, baseChowMul, map_add, add_mul, add_zsmul]

omit [AlgebraicGeometry.IsIntegral C.S] in
/-- The product of `A_0(S)` is additive in its right argument. -/
theorem baseChowMul_add_right (s : C.S) (α β β' : chowGroup C (𝟙 C.S) 0) :
    baseChowMul C hδ s α (β + β') =
      baseChowMul C hδ s α β + baseChowMul C hδ s α β' := by
  rw [baseChowMul, baseChowMul, baseChowMul, map_add, mul_add, add_zsmul]

/-- **The product of `A_0(S)` is unique.** Any biadditive product on the zeroth Chow group of a
one-point base having the fundamental class as a left unit is `Stacks.Chow.baseChowMul`: the
group is generated by `[S]`, so biadditivity determines the product from its value there. Hence
the Chow identity `Stacks.Chow.fundamentalChowClass_baseChowMul_self` holds for whichever
intersection product a consumer carries. -/
theorem eq_baseChowMul (s : C.S)
    (m : chowGroup C (𝟙 C.S) 0 →+ chowGroup C (𝟙 C.S) 0 →+ chowGroup C (𝟙 C.S) 0)
    (hm : ∀ β, m (fundamentalChowClass C (𝟙 C.S) 0) β = β)
    (α β : chowGroup C (𝟙 C.S) 0) :
    m α β = baseChowMul C hδ s α β := by
  have h : ∀ γ : chowGroup C (𝟙 C.S) 0, ∃ a : ℤ,
      γ = a • fundamentalChowClass C (𝟙 C.S) 0 ∧ chowGroupBaseEquivInt C hδ s γ = a :=
    fun γ ↦ ⟨_, eq_zsmul_fundamentalChowClass C hδ s γ, rfl⟩
  obtain ⟨a, ha, hdega⟩ := h α
  obtain ⟨b, hb, hdegb⟩ := h β
  rw [baseChowMul, hdega, hdegb, ha, hb]
  simp [map_zsmul, hm, smul_smul, mul_comm]

end Stacks.Chow

namespace Stacks.Weil

open Module Stacks.Chow

variable (F : Type v) [Field F]
  (H : ℤ → Type w)
  [∀ i : ℤ, AddCommGroup (H i)] [∀ i : ℤ, Module F (H i)]
  [∀ i : ℤ, FiniteDimensional F (H i)]
  (kunneth : ∀ n : ℤ,
    DirectSum ℤ (fun j : ℤ ↦ TensorProduct F (H j) (H (n - j))) ≃ₗ[F] H n)
  (Hpoint : Type t) [CommRing Hpoint] [Algebra F Hpoint]
  (degreeZero : H 0 ≃ₗ[F] Hpoint)
  (C : ChowSituation.{u}) (hδ : ∀ s : C.S, C.dimensionFunction s = 0)
  [Subsingleton C.S] [IsIntegral C.S] (s : C.S)
  (cycleClass : chowGroup C (𝟙 C.S) 0 →+ Hpoint)
  (trace : Hpoint →ₗ[F] F)
  (trace_fundamental :
    trace (cycleClass (fundamentalChowClass C (𝟙 C.S) 0)) = 1)
  (cycleClass_mul : ∀ α β : chowGroup C (𝟙 C.S) 0,
    cycleClass (baseChowMul C hδ s α β) = cycleClass α * cycleClass β)

include kunneth degreeZero trace_fundamental cycleClass_mul in
/-- **Stacks Project, Tag 0FHE**, third clause, with the Chow identity proved rather than
assumed. The cycle class of the fundamental class of the base point is the unit of
`H⁰(Spec(k))`.

The cycle group is the zeroth Chow group `A_0(Spec(k))` of chapter 42, which is where the cycle
class map `γ` of `(D2)` is defined, and the only hypothesis on `γ` beyond additivity is axiom
`(C)(c)`, that it is multiplicative for the intersection product. The idempotency of
`γ([Spec k])` — the hypothesis `cycleClass_fundamental_mul` of
`Stacks.Weil.cycleClass_fundamentalClass_eq_one` — is obtained here from
`Stacks.Chow.fundamentalChowClass_baseChowMul_self`, the Chow identity
`[Spec(k)] · [Spec(k)] = [Spec(k)]`. -/
@[stacks 0FHE "cycle class of the point"]
theorem cycleClass_fundamentalChowClass_eq_one :
    cycleClass (fundamentalChowClass C (𝟙 C.S) 0) = 1 :=
  cycleClass_fundamentalClass_eq_one F H kunneth Hpoint degreeZero
    (chowGroup C (𝟙 C.S) 0) (fundamentalChowClass C (𝟙 C.S) 0) cycleClass trace
    trace_fundamental
    (by rw [← cycleClass_mul, fundamentalChowClass_baseChowMul_self])

include kunneth degreeZero trace_fundamental cycleClass_mul in
/-- **Stacks Project, Tag 0FHE**, fourth clause, with the Chow identity proved rather than
assumed. Integration of the unit over the base point gives `1`.

Axiom `(C)(d)` normalises the integral at the cycle class of the fundamental class; this is the
same normalisation read at the unit, which the third clause licenses. -/
@[stacks 0FHE "trace of one"]
theorem trace_one_fundamentalChowClass_eq_one : trace 1 = 1 := by
  rw [← cycleClass_fundamentalChowClass_eq_one F H kunneth Hpoint degreeZero C hδ s cycleClass
    trace trace_fundamental cycleClass_mul]
  exact trace_fundamental

include kunneth degreeZero trace_fundamental hδ s in
/-- **Stacks Project, Tag 0FHE**, third clause, for a consumer carrying its own intersection
product on `A_0(Spec(k))`. Axiom `(C)(c)` is stated for that product, and the only property of it
required is that the fundamental class is a left unit, which is what pins it down to
`Stacks.Chow.baseChowMul` by `Stacks.Chow.eq_baseChowMul`. -/
theorem cycleClass_fundamentalChowClass_eq_one_of_mul
    (m : chowGroup C (𝟙 C.S) 0 →+ chowGroup C (𝟙 C.S) 0 →+ chowGroup C (𝟙 C.S) 0)
    (hm : ∀ β, m (fundamentalChowClass C (𝟙 C.S) 0) β = β)
    (cycleClass_m : ∀ α β, cycleClass (m α β) = cycleClass α * cycleClass β) :
    cycleClass (fundamentalChowClass C (𝟙 C.S) 0) = 1 :=
  cycleClass_fundamentalChowClass_eq_one F H kunneth Hpoint degreeZero C hδ s cycleClass trace
    trace_fundamental fun α β ↦ by rw [← eq_baseChowMul C hδ s m hm, cycleClass_m]

end Stacks.Weil

end
