module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionInput
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# The completion square of an extension of discrete valuation rings

The third step of the Stacks proof of Epp's theorem (Tag 09F9) runs over the square

```
  B  →  B^
  ↑      ↑
  A  →  A^
```

`EppCompletionInput` builds the left-hand column and everything about `A^`. This file builds the
**right-hand arrow**, `A^ → B^`, and with it the square.

## How the map is built, and why no comparison of topologies is needed

`A^` is the completion of `A` at `maximalIdeal A` and `B^` that of `B` at `maximalIdeal B` — each
at its *own* maximal ideal, which is the natural choice and the one Tag 0AP1 and Tag 09EJ are
stated for. One might look for an isomorphism
`AdicCompletion (maximalIdeal A) B ≅ AdicCompletion (maximalIdeal B) B`, on the grounds that
`maximalIdeal A · B` and `maximalIdeal B` induce the same topology on `B`; that comparison is true
but it is not needed, and Mathlib has neither it nor the ring-level functoriality of
`AdicCompletion` at a fixed ideal that would make it usable.

What is needed is only this. `A → B` is a **local** homomorphism, so `maximalIdeal A` maps into
`maximalIdeal B`, hence `(maximalIdeal A) ^ n` maps into `(maximalIdeal B) ^ n` for every `n`
(`map_maximalIdeal_pow_le`). That gives a map of truncations
`A ⧸ (maximalIdeal A) ^ n → B ⧸ (maximalIdeal B) ^ n` for each `n` (`truncationMap`), these are
compatible with the transition maps (`factorPow_comp_truncationMap`), and `A^` evaluates onto each
of its own truncations compatibly (`AdicCompletion.factorPow_evalₐ`). Composing and passing to
the limit through `AdicCompletion.liftRingHom` gives `A^ → B^` directly.

## Main results

* `IsDiscreteValuationRing.adicCompletionMap`: the ring map `A^ → B^`.
* `IsDiscreteValuationRing.adicCompletionMap_comp_algebraMap`: **the square commutes**, i.e.
  `A → A^ → B^` equals `A → B → B^`.
* `IsDiscreteValuationRing.isLocalHom_adicCompletionMap`: it is a local homomorphism.
* `IsDiscreteValuationRing.ramificationIdx_adicCompletionMap`: `e(B^/A^) = e(B/A)`.
* `IsDiscreteValuationRing.adicCompletionFractionFieldMap` and
  `algebraAdicCompletionFractionFieldMap`: the horizontal map `K^ → L^` of fraction fields, the one
  map of the square that is not definitional.
* `IsDiscreteValuationRing.isSeparableExtension_residueField_adicCompletionMap`: separability of
  the residue extension survives completion.
* `IsDiscreteValuationRing.charP_residueField_adicCompletion` and
  `perfectField_residueField_adicCompletion`: the residue characteristic and perfectness of the
  residue field survive completion. These are what let a theorem stated over a perfect residue
  field be applied to `A^`.
* `IsDiscreteValuationRing.tame_adicCompletionMap`: **the tame hypothesis survives completion** —
  the disjunction that `exists_finite_extension_isWeakSolution_of_tame_or_charZero` asks of
  `A → B` holds of `A^ → B^`. This is what lets the complete case be applied upstairs.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsLocalRing

section Truncations

variable (A : Type*) (B : Type*) [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- **A local homomorphism carries `m_A ^ n` into `m_B ^ n`.**

This is the only property of `A → B` the construction of `A^ → B^` uses. It is `Ideal.map_pow`
together with `maximalIdeal A ≤ comap (maximalIdeal B)`, which is what locality says. -/
theorem map_maximalIdeal_pow_le (n : ℕ) :
    ((maximalIdeal A) ^ n).map (algebraMap A B) ≤ (maximalIdeal B) ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr
    (le_of_eq (Ideal.LiesOver.over (p := maximalIdeal A) (P := maximalIdeal B)))) n

/-- The induced map on `n`-th truncations, `A ⧸ m_A ^ n → B ⧸ m_B ^ n`. -/
noncomputable def truncationMap (n : ℕ) :
    A ⧸ (maximalIdeal A) ^ n →+* B ⧸ (maximalIdeal B) ^ n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk ((maximalIdeal B) ^ n)).comp (algebraMap A B))
    fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact map_maximalIdeal_pow_le A B n (Ideal.mem_map_of_mem _ ha)

/-- `truncationMap` sends the class of `a` to the class of `algebraMap A B a`. -/
@[simp]
theorem truncationMap_mk (n : ℕ) (a : A) :
    truncationMap A B n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk ((maximalIdeal B) ^ n) (algebraMap A B a) := rfl

/-- The truncation maps commute with the transition maps of the two towers. -/
theorem factorPow_comp_truncationMap {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp (truncationMap A B n) =
      (truncationMap A B m).comp (Ideal.Quotient.factorPow (maximalIdeal A) hle) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply, truncationMap_mk, Ideal.Quotient.factor_mk]

end Truncations

section Square

variable (A : Type*) (B : Type*) [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- **The map `A^ → B^`.**

The compatible family `A^ → A ⧸ m_A ^ n → B ⧸ m_B ^ n`, passed to the limit. -/
noncomputable def adicCompletionMap :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  AdicCompletion.liftRingHom (maximalIdeal B)
    (fun n => (truncationMap A B n).comp
      ((AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom))
    fun {m n} hle => by
      rw [← RingHom.comp_assoc, factorPow_comp_truncationMap A B hle, RingHom.comp_assoc]
      refine congrArg _ ?_
      exact RingHom.ext fun x => AdicCompletion.factorPow_evalₐ (maximalIdeal A) hle x

/-- The `n`-th truncation of `adicCompletionMap A B x` is the image under `truncationMap` of the
`n`-th truncation of `x`. -/
@[simp]
theorem evalₐ_adicCompletionMap (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    AdicCompletion.evalₐ (maximalIdeal B) n (adicCompletionMap A B x) =
      truncationMap A B n (AdicCompletion.evalₐ (maximalIdeal A) n x) := by
  simp only [adicCompletionMap]
  apply AdicCompletion.evalₐ_liftRingHom

/-- **The completion square commutes**: `A → A^ → B^` equals `A → B → B^`. -/
@[simp]
theorem adicCompletionMap_of (a : A) :
    adicCompletionMap A B (AdicCompletion.of (maximalIdeal A) A a) =
      AdicCompletion.of (maximalIdeal B) B (algebraMap A B a) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  simp

/-- The commuting square, as an identity of ring maps. -/
theorem adicCompletionMap_comp_algebraMap :
    (adicCompletionMap A B).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp (algebraMap A B) :=
  RingHom.ext fun a => adicCompletionMap_of A B a

/-- **`A^ → B^` is a local homomorphism.**

The maximal ideal of `A^` is extended from `A`, so its image under `A^ → B^` is the image of
`maximalIdeal A` along `A → B → B^` by the commuting square, and that lands in `maximalIdeal B^`
because `A → B` is local and `maximalIdeal B^` is extended from `B`. -/
theorem isLocalHom_adicCompletionMap : IsLocalHom (adicCompletionMap A B) := by
  refine ((IsLocalRing.local_hom_TFAE (adicCompletionMap A B)).out 1 3 rfl rfl).mpr ?_
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, adicCompletionMap_comp_algebraMap,
    ← Ideal.map_map, AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le (algebraMap A B))

end Square

section Instances

variable (A : Type*) (B : Type*) [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
  [Algebra A B] [IsExtension A B]

/-- **`B^` as an `A^`-algebra**, along the map of completions.

Not an instance: it is the only sensible choice, but an `Algebra` instance whose two sides are both
`AdicCompletion`s of unrelated rings would be searched for far too often. A caller introduces it
with `letI`; every result below that needs it states it the same way. -/
@[instance_reducible]
noncomputable def algebraAdicCompletion :
    Algebra (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
  (adicCompletionMap A B).toAlgebra

/-- The tower `A → A^ → B^`, which is the commuting square read as a scalar tower. -/
theorem isScalarTower_adicCompletion :
    letI := algebraAdicCompletion A B
    IsScalarTower A (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) := by
  let _ := algebraAdicCompletion A B
  exact IsScalarTower.of_algebraMap_eq fun a => (adicCompletionMap_of A B a).symm

/-- A uniformizer of `A` has nonzero image in `B`. -/
private theorem algebraMap_ne_zero_of_irreducible {π : A} (hπ : Irreducible π) :
    algebraMap A B π ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr hπ.ne_zero

/-- **`A^ → B^` is injective.**

Every ideal of the discrete valuation ring `A^` is `⊥` or generated by a power of a uniformizer, so
it is enough that the kernel contains neither `1` nor a uniformizer. It contains no uniformizer
because `A → A^` carries one to one (`irreducible_algebraMap_adicCompletion`) while the square
sends that to `of (algebraMap A B π)`, which is nonzero since `A → B` and `B → B^` are both
injective. -/
theorem injective_adicCompletionMap : Function.Injective (adicCompletionMap A B) := by
  obtain ⟨π, hπprime⟩ := exists_prime A
  have hπ : Irreducible π := hπprime.irreducible
  have hπA : Irreducible (algebraMap A (AdicCompletion (maximalIdeal A) A) π) :=
    irreducible_algebraMap_adicCompletion A hπ
  -- the uniformizer of `A^` is not killed
  have hne : adicCompletionMap A B (algebraMap A (AdicCompletion (maximalIdeal A) A) π) ≠ 0 := by
    have heq : adicCompletionMap A B (algebraMap A (AdicCompletion (maximalIdeal A) A) π)
        = algebraMap B (AdicCompletion (maximalIdeal B) B) (algebraMap A B π) :=
      adicCompletionMap_of A B π
    rw [heq]
    intro h
    refine algebraMap_ne_zero_of_irreducible A B hπ
      (AdicCompletion.of_injective (maximalIdeal B) B ?_)
    rw [map_zero]
    exact h
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨n, hn⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hker hπA
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero, Ideal.span_singleton_one] at hn
    have hone : (1 : AdicCompletion (maximalIdeal A) A) ∈
        RingHom.ker (adicCompletionMap A B) := by
      rw [hn]; exact Submodule.mem_top
    have hz := RingHom.mem_ker.mp hone
    rw [map_one] at hz
    exact one_ne_zero hz
  · refine hne ?_
    have hmem : algebraMap A (AdicCompletion (maximalIdeal A) A) π ^ n ∈
        RingHom.ker (adicCompletionMap A B) := by
      rw [hn]; exact Ideal.mem_span_singleton_self _
    have := RingHom.mem_ker.mp hmem
    rw [map_pow] at this
    exact pow_eq_zero_iff hpos.ne' |>.mp this

/-- `A^ → B^` is faithful, being injective. -/
private theorem faithfulSMul_adicCompletionMap :
    letI := algebraAdicCompletion A B
    FaithfulSMul (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) := by
  let _ := algebraAdicCompletion A B
  exact (faithfulSMul_iff_algebraMap_injective _ _).mpr (injective_adicCompletionMap A B)

/-- `A^ → B^` is an extension of discrete valuation rings. -/
theorem isExtension_adicCompletionMap :
    letI := algebraAdicCompletion A B
    IsExtension (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) := by
  let _ := algebraAdicCompletion A B
  let _ := faithfulSMul_adicCompletionMap A B
  let _ : IsLocalHom
      (algebraMap (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B)) :=
    isLocalHom_adicCompletionMap A B
  exact ⟨⟩

/-- **Completion preserves the ramification index.**

A uniformizer `π` of `A` factors as `u * π_B ^ e` in `B` with `e = e(B/A)`, and `B → B^` carries
that to `of u * of π_B ^ e` with `of u` a unit and `of π_B` a uniformizer of `B^`. Since the square
sends the uniformizer `of π` of `A^` to exactly that element, its `B^`-valuation is `e`, and that
valuation *is* `e(B^/A^)`.

This is what moves a tameness hypothesis from `A → B` up to `A^ → B^`: the ramification index is
unchanged, and the residue fields are unchanged by
`surjective_algebraMap_residueField_adicCompletion`. -/
theorem ramificationIdx_adicCompletionMap :
    letI := algebraAdicCompletion A B
    letI : FaithfulSMul (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (injective_adicCompletionMap A B)
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B) =
          Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B := by
  let _ := algebraAdicCompletion A B
  let _ := faithfulSMul_adicCompletionMap A B
  obtain ⟨π, hπprime⟩ := exists_prime A
  have hπ : Irreducible π := hπprime.irreducible
  obtain ⟨πB, hπBprime⟩ := exists_prime B
  have hπB : Irreducible πB := hπBprime.irreducible
  -- factor the image of `π` in `B` as a unit times a power of `π_B`, the exponent being `e(B/A)`
  obtain ⟨k, u, hku⟩ :=
    eq_unit_mul_pow_irreducible (algebraMap_ne_zero_of_irreducible A B hπ) hπB
  have hk : k = Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B := by
    have h := Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx A B π
      hπ
    rw [hku, addVal_def' u hπB k] at h
    exact_mod_cast h
  -- transport the factorisation to `B^` and read off the valuation
  have hval := Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx
    (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B)
    (algebraMap A (AdicCompletion (maximalIdeal A) A) π)
    (irreducible_algebraMap_adicCompletion A hπ)
  have himg : (algebraMap (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B))
      (algebraMap A (AdicCompletion (maximalIdeal A) A) π)
      = algebraMap B (AdicCompletion (maximalIdeal B) B) (algebraMap A B π) :=
    adicCompletionMap_of A B π
  have hvalk : addVal (AdicCompletion (maximalIdeal B) B)
      (algebraMap B (AdicCompletion (maximalIdeal B) B) (algebraMap A B π)) = (k : ℕ∞) := by
    refine addVal_def _
      (Units.map (algebraMap B (AdicCompletion (maximalIdeal B) B)).toMonoidHom u)
      (irreducible_algebraMap_adicCompletion B hπB) k ?_
    rw [hku, map_mul, map_pow, Units.coe_map]
    rfl
  rw [← hk, ← Nat.cast_inj (R := ℕ∞), ← hval, himg, hvalk]

/-! ### The square of fraction fields

`EppCompletionInput` gives each completion a canonical fraction field and the map up from the
fraction field below it (`algebraAdicCompletionFractionField`). What is left is the **horizontal**
map `K^ → L^`, and it is the only one that is not definitional: Mathlib's `Localization` algebra
instances make `A^ → L^`, `B^ → L^` and `A → L^` composites *by definition*, but `K^ → L^` has to
be constructed, because `K^` is a localization of `A^` and the map has to be extended across it. -/

/-- **`A^ → L^` is injective**, being `A^ → B^` followed by `B^ → L^`.

This is what lets `K^ → L^` be built by extending across the localization `A^ → K^`. -/
theorem injective_algebraMap_adicCompletionFractionField_of_square :
    letI := algebraAdicCompletion A B
    Function.Injective (algebraMap (AdicCompletion (maximalIdeal A) A)
      (AdicCompletionFractionField B)) := by
  let := algebraAdicCompletion A B
  rw [IsScalarTower.algebraMap_eq (AdicCompletion (maximalIdeal A) A)
    (AdicCompletion (maximalIdeal B) B) (AdicCompletionFractionField B)]
  exact (IsFractionRing.injective (AdicCompletion (maximalIdeal B) B)
    (AdicCompletionFractionField B)).comp (injective_adicCompletionMap A B)

/-- **The map `K^ → L^`** of the fraction fields of the two completions: the unique extension of
`A^ → L^` across the localization `A^ → K^`.

Deliberately a bare ring map rather than an `Algebra` instance in the first instance, so that its
*type* mentions no instance of the square — a statement quantifying over the square can then name
it without a `letI` preamble for it. `algebraAdicCompletionFractionFieldMap` is the algebra form.
-/
noncomputable def adicCompletionFractionFieldMap :
    AdicCompletionFractionField A →+* AdicCompletionFractionField B :=
  letI := algebraAdicCompletion A B
  IsFractionRing.lift (A := AdicCompletion (maximalIdeal A) A)
    (K := AdicCompletionFractionField A) (L := AdicCompletionFractionField B)
    (injective_algebraMap_adicCompletionFractionField_of_square A B)

/-- **`L^` as a `K^`-algebra**, along `adicCompletionFractionFieldMap`.

Not an instance, for the same reason `algebraAdicCompletion` is not: a search for an `Algebra`
between the fraction fields of two unrelated completions would fire far too often. Its type needs
none of the square's instances, so a caller may name it in a statement. -/
@[instance_reducible]
noncomputable def algebraAdicCompletionFractionFieldMap :
    Algebra (AdicCompletionFractionField A) (AdicCompletionFractionField B) :=
  (adicCompletionFractionFieldMap A B).toAlgebra

/-- The tower `A^ → K^ → L^`: `K^ → L^` was built as the extension of `A^ → L^`, so this is
`IsFractionRing.lift_algebraMap`. -/
theorem isScalarTower_adicCompletionFractionFieldMap :
    letI := algebraAdicCompletion A B
    letI := algebraAdicCompletionFractionFieldMap A B
    IsScalarTower (AdicCompletion (maximalIdeal A) A) (AdicCompletionFractionField A)
      (AdicCompletionFractionField B) := by
  let := algebraAdicCompletion A B
  let := algebraAdicCompletionFractionFieldMap A B
  exact IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (A := AdicCompletion (maximalIdeal A) A)
      (K := AdicCompletionFractionField A)
      (injective_algebraMap_adicCompletionFractionField_of_square A B) a).symm

end Instances

section AdicCompletionTower

variable (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- **`A` acts on `B^` through `B`.**

Mathlib gives `B^` its `A`-algebra structure from `A → B` directly — `algebraMap A B^` is
`of ∘ algebraMap A B` by definition — so this tower holds by `rfl`. It is recorded because the
residue-field instances of the square are stated in terms of it. -/
theorem isScalarTower_algebraMap_adicCompletion :
    IsScalarTower A B (AdicCompletion (maximalIdeal B) B) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end AdicCompletionTower

section ResidueChar

variable (C : Type*) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]

/-- `κ_C → κ_{C^}` is bijective: injective as a map of fields, surjective by completion. -/
private theorem bijective_algebraMap_residueField_adicCompletion :
    Function.Bijective
      (algebraMap (ResidueField C) (ResidueField (AdicCompletion (maximalIdeal C) C))) :=
  ⟨(algebraMap (ResidueField C) (ResidueField (AdicCompletion (maximalIdeal C) C))).injective,
    surjective_algebraMap_residueField_adicCompletion C⟩

/-- **The residue characteristic is unchanged by completion.**

`κ_C → κ_{C^}` is a map of fields, hence injective, and a characteristic transfers along an
injective algebra map. -/
theorem ringChar_residueField_adicCompletion :
    ringChar (ResidueField (AdicCompletion (maximalIdeal C) C)) = ringChar (ResidueField C) := by
  let : CharP (ResidueField C) (ringChar (ResidueField C)) := ringChar.charP _
  exact CharP.eq _ (ringChar.charP _)
    (charP_of_injective_algebraMap
      (algebraMap (ResidueField C)
        (ResidueField (AdicCompletion (maximalIdeal C) C))).injective _)

/-- The residue characteristic is unchanged by completion, in `CharP` form.

`ringChar_residueField_adicCompletion` is the same fact as an equality of `ringChar`s; this is the
form a consumer that carries `[CharP (ResidueField A) p]` as an instance binder needs, which is how
`Stacks.EppTheorem.EppCondition` and Route P's condition (b) both take the residue characteristic.
-/
theorem charP_residueField_adicCompletion (p : ℕ) [CharP (ResidueField C) p] :
    CharP (ResidueField (AdicCompletion (maximalIdeal C) C)) p :=
  charP_of_injective_algebraMap
    (algebraMap (ResidueField C)
      (ResidueField (AdicCompletion (maximalIdeal C) C))).injective p

/-- **Perfectness of the residue field survives completion.**

`κ_C → κ_{C^}` is bijective — injective as a map of fields, surjective by
`surjective_algebraMap_residueField_adicCompletion` — so this is `PerfectField.of_ringEquiv`.

Needed because Route P's condition (b) and the complete perfect-residue case (obligation O1) both
ask for `PerfectField (ResidueField A)` of the ring they are applied to, and the completion descent
applies them to `A^`. -/
theorem perfectField_residueField_adicCompletion [PerfectField (ResidueField C)] :
    PerfectField (ResidueField (AdicCompletion (maximalIdeal C) C)) :=
  PerfectField.of_ringEquiv (RingEquiv.ofBijective _
    (bijective_algebraMap_residueField_adicCompletion C))

end ResidueChar

section ResidueSquare

variable (A : Type*) (B : Type*) [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
  [Algebra A B] [IsExtension A B]

/-- **`A → B^` is a local homomorphism**, being `A → B` followed by `B → B^`. -/
theorem isLocalHom_algebraMap_adicCompletion :
    IsLocalHom (algebraMap A (AdicCompletion (maximalIdeal B) B)) := by
  let := isScalarTower_algebraMap_adicCompletion A B
  rw [IsScalarTower.algebraMap_eq A B (AdicCompletion (maximalIdeal B) B)]
  infer_instance

/-- **`A → B^` is an extension of discrete valuation rings.** -/
theorem isExtension_algebraMap_adicCompletion :
    IsExtension A (AdicCompletion (maximalIdeal B) B) := by
  let := isScalarTower_algebraMap_adicCompletion A B
  let := isLocalHom_algebraMap_adicCompletion A B
  let : FaithfulSMul A (AdicCompletion (maximalIdeal B) B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [IsScalarTower.algebraMap_eq A B (AdicCompletion (maximalIdeal B) B)]
      exact (AdicCompletion.of_injective (maximalIdeal B) B).comp
        (FaithfulSMul.algebraMap_injective A B))
  exact ⟨⟩

/-- **Separability of the residue extension survives completion.**

The two vertical maps of residue fields are isomorphisms — `κ_A → κ_{A^}` and `κ_B → κ_{B^}` are
injective as maps of fields and surjective by `surjective_algebraMap_residueField_adicCompletion` —
and the residue square commutes, because the completion square does and `Ideal.Quotient` is
functorial in a local homomorphism (Mathlib supplies both towers `κ_A → κ_B → κ_{B^}` and
`κ_A → κ_{A^} → κ_{B^}` as instances).

The transport is through formal smoothness, which is where the two halves of the square get used
separately: `κ_B ≃ₐ[κ_A] κ_{B^}` moves formal smoothness *over `κ_A`* to the completed target, and
then `κ_A → κ_{A^}` being an isomorphism — hence formally unramified — lets
`Algebra.FormallySmooth.of_restrictScalars` move the base up as well. -/
theorem isSeparableExtension_residueField_adicCompletionMap
    (hsep : Algebra.IsSeparableExtension (ResidueField A) (ResidueField B)) :
    letI := algebraAdicCompletion A B
    letI : IsLocalHom (algebraMap (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B)) := isLocalHom_adicCompletionMap A B
    Algebra.IsSeparableExtension (ResidueField (AdicCompletion (maximalIdeal A) A))
      (ResidueField (AdicCompletion (maximalIdeal B) B)) := by
  let := algebraAdicCompletion A B
  let : IsLocalHom (algebraMap (AdicCompletion (maximalIdeal A) A)
    (AdicCompletion (maximalIdeal B) B)) := isLocalHom_adicCompletionMap A B
  let := isScalarTower_algebraMap_adicCompletion A B
  let := isLocalHom_algebraMap_adicCompletion A B
  let := isScalarTower_adicCompletion A B
  let : Algebra.FormallySmooth (ResidueField A) (ResidueField B) :=
    (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mpr hsep
  let : Algebra.FormallySmooth (ResidueField A)
      (ResidueField (AdicCompletion (maximalIdeal B) B)) :=
    Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom (ResidueField A) (ResidueField B)
        (ResidueField (AdicCompletion (maximalIdeal B) B)))
        (bijective_algebraMap_residueField_adicCompletion B))
  let : Algebra.FormallyUnramified (ResidueField A)
      (ResidueField (AdicCompletion (maximalIdeal A) A)) :=
    Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective
      (Algebra.ofId (ResidueField A)
        (ResidueField (AdicCompletion (maximalIdeal A) A)))
        (bijective_algebraMap_residueField_adicCompletion A))
  have hfs : Algebra.FormallySmooth (ResidueField (AdicCompletion (maximalIdeal A) A))
      (ResidueField (AdicCompletion (maximalIdeal B) B)) :=
    Algebra.FormallySmooth.of_restrictScalars (ResidueField A)
      (ResidueField (AdicCompletion (maximalIdeal A) A))
      (ResidueField (AdicCompletion (maximalIdeal B) B))
  exact (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mp hfs

/-- **The tame hypothesis survives completion.**

This is the disjunction that `exists_finite_extension_isWeakSolution_of_tame_or_charZero` asks of
`A → B`, transported to `A^ → B^`: the residue characteristic is unchanged
(`ringChar_residueField_adicCompletion`), the ramification index is unchanged
(`ramificationIdx_adicCompletionMap`), and the residue extension stays separable
(`isSeparableExtension_residueField_adicCompletionMap`). It is what lets the complete case of Epp's
theorem be applied to the completed square. -/
theorem tame_adicCompletionMap
    (htame : ringChar (ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (ResidueField A)) (ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (ResidueField A) (ResidueField B)) :
    letI := algebraAdicCompletion A B
    letI := isExtension_adicCompletionMap A B
    ringChar (ResidueField (AdicCompletion (maximalIdeal A) A)) = 0 ∨
      Nat.Coprime (ringChar (ResidueField (AdicCompletion (maximalIdeal A) A)))
          (ramificationIndex (AdicCompletion (maximalIdeal A) A)
            (AdicCompletion (maximalIdeal B) B)) ∧
        Algebra.IsSeparableExtension (ResidueField (AdicCompletion (maximalIdeal A) A))
          (ResidueField (AdicCompletion (maximalIdeal B) B)) := by
  let := algebraAdicCompletion A B
  let := isExtension_adicCompletionMap A B
  have he : ramificationIndex (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) = ramificationIndex A B :=
    ramificationIdx_adicCompletionMap A B
  rw [ringChar_residueField_adicCompletion A, he]
  rcases htame with h | ⟨hcop, hsep⟩
  · exact Or.inl h
  · exact Or.inr ⟨hcop, isSeparableExtension_residueField_adicCompletionMap A B hsep⟩

end ResidueSquare

end IsDiscreteValuationRing
