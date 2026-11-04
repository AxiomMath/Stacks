module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionDescent
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionSquare
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction

/-!
# Removing completeness from the tame case of Epp's theorem

`EppAlgClosedResidue.exists_finite_extension_isWeakSolution_of_tame_or_charZero` proves the
residue-characteristic-zero and tame cases of Epp's theorem (Tag 09F9) for *complete* discrete
valuation rings.  Its two `IsAdicComplete` hypotheses are not vestigial: they feed
`integralClosure_isCompleteDVR`, and for a non-complete discrete valuation ring the integral
closure in a finite extension of the fraction field need not even be local.  So they cannot be
dropped from that proof; they have to be paid for by the third step of the Stacks argument, the
descent along the completion square

```
  B  →  B^
  ↑      ↑
  A  →  A^
```

which is what this file carries out.  The pieces it uses are all in place:
`EppCompletionInput` builds the left-hand column and the fraction field `K^`,
`EppCompletionSquare` builds the arrow `A^ → B^` and transports the tame hypothesis across it,
`EppCompletionDescent` is the transport of a weak solution back down, and Tag 09EJ
(`exists_finite_separable_extension_tensorProduct_equiv_of_isDVR`) produces the finite extension
downstairs.  What is added here is the remaining input of the descent — that the finite extension
is a weak solution for `A → A^` — and the assembly.

## Main results

* `IsDiscreteValuationRing.isWeakSolution_canonicalBaseChange_adicCompletion`: **every** finite
  extension `K₁ / K` is a weak solution for `A → A^`.  This is the one hypothesis of
  `isWeakSolution_of_isWeakSolution_completion` into which all use of completeness is isolated.
  It is Tag 09EQ applied to `A → A^`, which is adically formally smooth by
  `formallySmoothNAdic_algebraMap_adicCompletion` (Tag 09E7), in the bundled form
  `IntegralClosureBaseChange.isWeakSolution_of_formallySmoothNAdic`.
* `IsDiscreteValuationRing.isWeakSolution_canonicalBaseChange_of_tensorProduct_algEquiv`: **the
  common core of step 3** — the completion square and the two Tag 09ES steps, taking the
  `K^ ⊗_K K₁ ≅ M` equivalence as an argument. Both routes into step 3 end at that equivalence and
  share everything after it; the separable route below is one of them, and the wild route through
  condition (b) is the other.
* `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion`:
  **step 3 itself** — a finite *separable* weak solution `M / K^` for `A^ → B^` descends to a
  finite separable weak solution `K₁ / K` for `A → B`. The hypothesis is written in the shape the
  complete case's conclusion has, so that any theorem proving the complete case can be applied to
  the square directly. Separability of `M / K^` is the whole of what restricts it, and it is Tag
  09EJ's hypothesis.
* `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_tame_or_charZero_of_isDVR`:
  **the tame and residue-characteristic-zero cases of Tag 09F9 with no completeness hypothesis** —
  the previous theorem fed by the complete tame case. Its statement is that of
  `exists_finite_extension_isWeakSolution_of_tame_or_charZero` with the two `IsAdicComplete`
  binders deleted and nothing else changed.

## Implementation notes

The descent is stated over an abstract square with ten carrier types and twelve presentation
universes, so instantiating it is mostly a matter of exhibiting the maps and the towers.  Most of
those come for free, and it is worth recording why: Mathlib gives `AdicCompletion I R` an
`S`-algebra structure for every `S` acting on `R`, with `algebraMap S (AdicCompletion I R)` equal
to `of ∘ algebraMap S R` *by definition*, and gives `Localization M` an `S`-algebra structure for
every `S` acting on the base in the same definitional way.  So all the vertical maps of the square
of fraction fields, and the towers along them, are definitional.

What is not definitional is anything crossing the square, and there are exactly three such things:
the tower `A → A^ → B^` (which is the square commuting, `isScalarTower_adicCompletion`), the
horizontal map `K^ → L^`, and the two towers `K → K^ → L^` and `K → L → L^`.  The horizontal map is
`IsFractionRing.lift` of `A^ → L^`, which is injective because `A^ → B^` is
(`injective_adicCompletionMap`); the two towers are equalities of ring maps out of `K`, and a ring
map out of a fraction field is determined by its restriction to the base, so both reduce to a
computation in `A` by `IsLocalization.ringHom_ext`.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09EJ](https://stacks.math.columbia.edu/tag/09EJ)
* [The Stacks Project, Tag 09EQ](https://stacks.math.columbia.edu/tag/09EQ)
* [The Stacks Project, Tag 09ES](https://stacks.math.columbia.edu/tag/09ES)
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsLocalRing

open scoped TensorProduct

universe uA uB uK uL z₁ z₂ z₃

section WeakSolutionAdicCompletion

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (K₁ : Type*) [Field K₁] [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
  [Module.Finite K K₁]

/-- **Every finite extension `K₁ / K` is a weak solution for `A → A^`.**

This is the single hypothesis of `isWeakSolution_of_isWeakSolution_completion` into which all use
of completeness is isolated, and the reason it holds for *every* `K₁` — not just for `K₁ = K`,
which is all that weak unramifiedness of `A → A^` gives directly — is Tag 09EQ: adic formal
smoothness of `A → A^` propagates to the localizations of the base-changed integral closures, and
there Tag 09E7 read backwards turns it into ramification index one. `A → A^` is adically formally
smooth by `formallySmoothNAdic_algebraMap_adicCompletion`, and the propagation is
`IntegralClosureBaseChange.isWeakSolution_of_formallySmoothNAdic`. -/
theorem isWeakSolution_canonicalBaseChange_adicCompletion :
    letI := algebraAdicCompletionFractionField A K
    letI := isScalarTower_adicCompletionFractionField A K
    (canonicalBaseChange A (AdicCompletion (IsLocalRing.maximalIdeal A) A) K
      (AdicCompletionFractionField A) K₁).IsWeakSolution := by
  let := algebraAdicCompletionFractionField A K
  let := isScalarTower_adicCompletionFractionField A K
  exact (canonicalBaseChange A (AdicCompletion (IsLocalRing.maximalIdeal A) A) K
    (AdicCompletionFractionField A) K₁).isWeakSolution_of_formallySmoothNAdic
    (formallySmoothNAdic_algebraMap_adicCompletion A)

end WeakSolutionAdicCompletion

/-- A tower `A → Y → X` with `K` the fraction field of `A` lifts to the tower `K → Y → X`. -/
private theorem isScalarTower_of_isFractionRing (A K Y X : Type*) [CommRing A] [IsDomain A]
    [Field K] [CommRing Y] [CommRing X] [Algebra A K] [IsFractionRing A K] [Algebra A Y]
    [Algebra A X] [Algebra K Y] [Algebra K X] [Algebra Y X] [IsScalarTower A K Y]
    [IsScalarTower A K X] [IsScalarTower A Y X] : IsScalarTower K Y X :=
  IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext (nonZeroDivisors A)
    (RingHom.ext fun a => by
      simp [← IsScalarTower.algebraMap_apply A K X, ← IsScalarTower.algebraMap_apply A K Y,
        IsScalarTower.algebraMap_apply A Y X]))

/-- **The core of step 3: descend along the completion square, given the base-change
equivalence.**

Both routes into step 3 of Tag 09F9 end at the same place — a finite `K₁ / K` together with a
`K^`-isomorphism `K^ ⊗_K K₁ ≅ M` and a weak solution for `A^ → B^` over `M` — and everything after
that point is common to them. This is that common part.

The routes differ only in how the equivalence is obtained. When `M / K^` is **separable** it is Tag
09EJ directly (`exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion` below). In
the wild case `M / K^` need not be separable and the equivalence comes from condition (b) of the
published proof, through Tag 09EJ over the base `A_n = integralClosure A K(π^{1/p^n})`; that route
is not yet built. Factoring the descent out here is what keeps it from being written twice.

What this theorem contains is the completion square and the two Tag 09ES steps: the square's maps
and towers (of which only `A → A^ → B^`, `K^ → L^`, `K → K^ → L^` and `K → L → L^` are not
definitional — see the module docstring), the weak solution for `A → A^` along `K₁`
(`isWeakSolution_canonicalBaseChange_adicCompletion`, which holds for *every* finite `K₁ / K` and
so needs nothing from the caller), and
`isWeakSolution_of_isWeakSolution_completion_of_tensorProduct_algEquiv`. -/
theorem isWeakSolution_canonicalBaseChange_of_tensorProduct_algEquiv
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK) (M : Type uA)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field M]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁] [Module.Finite K K₁]
    [Algebra (AdicCompletionFractionField A) M]
    [Algebra (AdicCompletion (IsLocalRing.maximalIdeal A) A) M]
    [IsScalarTower (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (AdicCompletionFractionField A) M]
    [Module.Finite (AdicCompletionFractionField A) M]
    (hup :
      letI := algebraAdicCompletion A B
      letI := isExtension_adicCompletionMap A B
      letI := algebraAdicCompletionFractionFieldMap A B
      letI := isScalarTower_adicCompletionFractionFieldMap A B
      ∃ D : IntegralClosureBaseChange.{uA, uB, uA, uB, uA, z₁, z₂, z₃}
        (AdicCompletion (IsLocalRing.maximalIdeal A) A)
        (AdicCompletion (IsLocalRing.maximalIdeal B) B)
        (AdicCompletionFractionField A) (AdicCompletionFractionField B) M,
        D.IsWeakSolution)
    (e :
      letI := algebraAdicCompletionFractionField A K
      (AdicCompletionFractionField A ⊗[K] K₁) ≃ₐ[AdicCompletionFractionField A] M) :
    (canonicalBaseChange A B K L K₁).IsWeakSolution := by
  -- The ring square `A → A^`, `B → B^`, `A^ → B^`.
  let := algebraAdicCompletion A B
  let := isExtension_adicCompletionMap A B
  let := isScalarTower_adicCompletion A B
  let := isScalarTower_algebraMap_adicCompletion A B
  let := isExtension_algebraMap_adicCompletion A B
  -- The two fraction fields of the completions, each receiving the fraction field below it.
  let := algebraAdicCompletionFractionField A K
  let := isScalarTower_adicCompletionFractionField A K
  let := algebraAdicCompletionFractionField B L
  let := isScalarTower_adicCompletionFractionField B L
  -- The tower `A → A^ → L^`, which is the only vertical tower the square does not make
  -- definitional: it says `A → B^` factors through `A^`, i.e. that the ring square commutes.
  let : IsScalarTower A (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (AdicCompletionFractionField B) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A (AdicCompletion (IsLocalRing.maximalIdeal B) B)
          (AdicCompletionFractionField B),
        IsScalarTower.algebraMap_apply A (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletion (IsLocalRing.maximalIdeal B) B),
        ← IsScalarTower.algebraMap_apply (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletion (IsLocalRing.maximalIdeal B) B) (AdicCompletionFractionField B)]
  -- The horizontal map `K^ → L^`: the unique extension of `A^ → L^` to the fraction field.
  have hinjAcLc : Function.Injective (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (AdicCompletionFractionField B)) :=
    injective_algebraMap_adicCompletionFractionField_of_square A B
  let := algebraAdicCompletionFractionFieldMap A B
  let := isScalarTower_adicCompletionFractionFieldMap A B
  -- `K → L^`, likewise the unique extension of `A → L^`.
  have hinjALc : Function.Injective (algebraMap A (AdicCompletionFractionField B)) := by
    rw [IsScalarTower.algebraMap_eq A (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (AdicCompletionFractionField B)]
    exact hinjAcLc.comp (AdicCompletion.of_injective (IsLocalRing.maximalIdeal A) A)
  let : Algebra K (AdicCompletionFractionField B) :=
    (IsFractionRing.lift (A := A) (K := K) (L := AdicCompletionFractionField B)
      hinjALc).toAlgebra
  let : IsScalarTower A K (AdicCompletionFractionField B) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (IsFractionRing.lift_algebraMap (A := A) (K := K) hinjALc a).symm
  -- `A → L → L^` is a tower, because `A → B → L` and `B → L → L^` are.
  let : IsScalarTower A L (AdicCompletionFractionField B) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A B L,
        ← IsScalarTower.algebraMap_apply B L (AdicCompletionFractionField B),
        ← IsScalarTower.algebraMap_apply A B (AdicCompletionFractionField B)]
  -- The two towers out of `K`.  A ring map out of a fraction field is determined by its
  -- restriction to the base, so each is a computation in `A`.
  let : IsScalarTower A (AdicCompletionFractionField A) (AdicCompletionFractionField B) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletionFractionField A),
        ← IsScalarTower.algebraMap_apply (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletionFractionField A) (AdicCompletionFractionField B),
        ← IsScalarTower.algebraMap_apply A (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletionFractionField B)]
  let : IsScalarTower K (AdicCompletionFractionField A) (AdicCompletionFractionField B) :=
    isScalarTower_of_isFractionRing A K _ _
  let : IsScalarTower K L (AdicCompletionFractionField B) :=
    isScalarTower_of_isFractionRing A K _ _
  -- The weak solution upstairs, from the hypothesis.
  obtain ⟨D_AcBc, hAcBc⟩ := hup
  -- Descend along the square.
  exact isWeakSolution_of_isWeakSolution_completion_of_tensorProduct_algEquiv
    A (AdicCompletion (IsLocalRing.maximalIdeal A) A) B
    (AdicCompletion (IsLocalRing.maximalIdeal B) B)
    K (AdicCompletionFractionField A) L (AdicCompletionFractionField B) K₁ M
    (canonicalBaseChange A B K L K₁)
    (canonicalBaseChange A (AdicCompletion (IsLocalRing.maximalIdeal A) A) K
      (AdicCompletionFractionField A) K₁)
    (canonicalBaseChange A (AdicCompletion (IsLocalRing.maximalIdeal B) B) K
      (AdicCompletionFractionField B) K₁)
    D_AcBc
    (isWeakSolution_canonicalBaseChange_adicCompletion A K K₁) hAcBc e

/-- **Step 3 of Tag 09F9: descending a separable weak solution from the completion.**

Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`, with no
completeness assumed. If there is a finite **separable** extension `M / K^` of the fraction field
of `A^` which is a weak solution for `A^ → B^`, then there is a finite separable `K₁ / K` which is
a weak solution for `A → B`.

This is the third paragraph of the published proof, and the hypothesis is written in the shape the
complete case's conclusion has — an existential over the field together with its algebra data and a
base-change package over it — so that a theorem proving the complete case can be applied to the
square directly. The four links are: Tag 09EJ to produce `K₁` with `K^ ⊗_K K₁ ≅ M`
(`exists_finite_separable_extension_tensorProduct_equiv_of_isDVR`), Tag 09E7 and Tag 09EQ to make
`K₁ / K` a weak solution for `A → A^` (`isWeakSolution_canonicalBaseChange_adicCompletion`, which
holds for every finite `K₁ / K`), and then Tag 09ES parts (2) and (1)
(`isWeakSolution_of_isWeakSolution_completion_of_tensorProduct_algEquiv`).

**Separability of `M / K^` is the whole of what restricts this statement**, and it is exactly Tag
09EJ's hypothesis. It is free when `A` has mixed characteristic, since then `K^` has characteristic
zero; in equal characteristic it is the content of condition (b) of the published proof — that `M`
is a compositum of a separable extension and one obtained by adjoining a `p`-power root of a
uniformizer — and the wild case has to supply it. -/
theorem exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (hup :
      letI := algebraAdicCompletion A B
      letI := isExtension_adicCompletionMap A B
      letI := algebraAdicCompletionFractionFieldMap A B
      letI := isScalarTower_adicCompletionFractionFieldMap A B
      ∃ (M : Type uA) (_ : Field M) (_ : Algebra (AdicCompletionFractionField A) M)
        (_ : Algebra (AdicCompletion (IsLocalRing.maximalIdeal A) A) M)
        (_ : IsScalarTower (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletionFractionField A) M)
        (_ : Module.Finite (AdicCompletionFractionField A) M)
        (_ : Algebra.IsSeparable (AdicCompletionFractionField A) M),
        ∃ D : IntegralClosureBaseChange.{uA, uB, uA, uB, uA, z₁, z₂, z₃}
          (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletion (IsLocalRing.maximalIdeal B) B)
          (AdicCompletionFractionField A) (AdicCompletionFractionField B) M,
          D.IsWeakSolution) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : Algebra.IsSeparable K K₁),
      ∃ D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK} A B K L K₁,
        D.IsWeakSolution := by
  let := algebraAdicCompletion A B
  let := isExtension_adicCompletionMap A B
  let := algebraAdicCompletionFractionFieldMap A B
  let := isScalarTower_adicCompletionFractionFieldMap A B
  let := algebraAdicCompletionFractionField A K
  let := isScalarTower_adicCompletionFractionField A K
  obtain ⟨M, hMfield, hMalgKc, hMalgAc, hMtower, hMfin, hMsep, D_AcBc, hAcBc⟩ := hup
  let := hMfield
  let := hMalgKc
  let := hMalgAc
  let := hMtower
  let := hMfin
  let := hMsep
  -- Tag 09EJ: `M / K^` comes from a finite separable extension `F / K` by base change.
  obtain ⟨F, hFfin, hFsep, ⟨e⟩⟩ :=
    exists_finite_separable_extension_tensorProduct_equiv_of_isDVR
      (A := A) (K := K) (Khat := AdicCompletionFractionField A) (M := M)
  let : Algebra A F := ((algebraMap K F).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K F := IsScalarTower.of_algebraMap_eq' rfl
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, hFfin, hFsep,
    canonicalBaseChange A B K L F,
    isWeakSolution_canonicalBaseChange_of_tensorProduct_algEquiv A B K L F M
      ⟨D_AcBc, hAcBc⟩ e⟩

/-- **Epp's theorem (Tag 09F9) in the residue-characteristic-zero and tame cases, for discrete
valuation rings that need not be complete.**

This is `exists_finite_extension_isWeakSolution_of_tame_or_charZero` with its two
`IsAdicComplete` binders deleted and nothing else changed — in particular the finite extension it
produces is still separable, which Tag 09EJ hands back for free.

The proof is `exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion` fed by the
complete case applied to the completion square: completeness is free there, since Mathlib makes
`AdicCompletion (IsLocalRing.maximalIdeal A) A` adically complete by instance, and the tame
hypothesis survives completion by `tame_adicCompletionMap`.

Not tagged `@[stacks 09F9]`, for the reason given at
`exists_finite_extension_isWeakSolution_of_tame_or_charZero`: the substance of 09F9 is the wild
case, and registering the tag on the tame half would misreport coverage. -/
theorem exists_finite_extension_isWeakSolution_of_tame_or_charZero_of_isDVR
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (htame : ringChar (ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (ResidueField A)) (ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (ResidueField A) (ResidueField B)) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : Algebra.IsSeparable K K₁),
      ∃ D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK} A B K L K₁,
        D.IsWeakSolution := by
  refine exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion A B K L ?_
  let := algebraAdicCompletion A B
  let := isExtension_adicCompletionMap A B
  let := algebraAdicCompletionFractionFieldMap A B
  let := isScalarTower_adicCompletionFractionFieldMap A B
  exact exists_finite_extension_isWeakSolution_of_tame_or_charZero
    (AdicCompletion (IsLocalRing.maximalIdeal A) A)
    (AdicCompletion (IsLocalRing.maximalIdeal B) B)
    (AdicCompletionFractionField A) (AdicCompletionFractionField B)
    (tame_adicCompletionMap A B htame)

end IsDiscreteValuationRing

end
