module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport

/-!
# The chart-wise class of a quadruple is a bijection, and its inverse

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `V` an open of
the base and `T` a test scheme given with a morphism `g_V : T ⟶ V`.
`...RelativeProjQcohSheaf.Fd.chartClass` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport` reads a strict
equivalence class of quadruples for `𝒜` over the composite `g_V ≫ V.ι : T ⟶ S` as a point of
`F_d(T)` for the restriction `𝒜|_V`, whose projective spectrum is the chart of `V`. This file
**inverts it**.

## Why the inverse is immediate, and what the blocked route was about

`Fd.chartClass` is the composite of two maps each of which is already a bijection in the tree:

* the base change of [Stacks, Tag 01NT] in the downward direction,
  `...RelativeProjQcohSheaf.Fd.baseChangeDownQ`, whose inverse is
  `...RelativeProjQcohSheaf.Fd.baseChangeUp` — the two round trips being
  `...Fd.baseChangeUp_baseChangeDownQ` and `...Fd.baseChangeDownQ_baseChangeUp`; and
* the comparison of the two spellings of the restriction,
  `...RelativeProjQcohSheaf.Fd.pullbackRestrictEquiv`, which is by construction an `Equiv` — the
  symm of `...Fd.restrictPullbackEquiv`.

So the inverse is the composite of the two inverses, and that is `Fd.chartClassInv` below.

This is *not* the construction that the implementation notes of
`...ChartClassifyingTransport` record as blocked. That one is different: a map from quadruples
for `𝒜|_U` to quadruples for `𝒜|_Z` for a nested pair `Z ≤ U` of opens, which would need
`(𝒜.restrict U.ι).restrict (S.homOfLE h) = 𝒜.restrict Z.ι` and therefore does not exist. Going
*back along one open* `V`, which is what inverting `Fd.chartClass` asks for, involves no iterated
restriction at all: the one restriction `𝒜|_V` is undone by the Tag 01NT bijection, landing on
`𝒜` on `S` itself. The two statements have been conflated; they are not the same.

## Main definitions

* `...RelativeProjQcohSheaf.Fd.chartClassEquiv`: **the bijection**, on classes over a fixed
  factorization — strict equivalence classes of quadruples for `𝒜` over `g_V ≫ V.ι` correspond
  to strict equivalence classes of quadruples for `𝒜|_V` over `g_V`.
* `...RelativeProjQcohSheaf.Fd.chartClassInv`: **the inverse of the chart-wise class**, as a map
  of the sets `F_d(T)`: a point of `F_d(T)` for `𝒜|_V` is a point of `F_d(T)` for `𝒜` over the
  composite of its morphism with `V.ι`.

## Main results

* `...RelativeProjQcohSheaf.Fd.chartClassInv_chartClass` and
  `...RelativeProjQcohSheaf.Fd.chartClass_chartClassInv`: **the two round trips**, so
  `Fd.chartClass A V gV` is a bijection onto the classes over `g_V`.
* `...RelativeProjQcohSheaf.Fd.chartClass_injective` and
  `...RelativeProjQcohSheaf.Fd.chartClass_surjective_of_fst`: the two halves separately, in the
  shape the descent consumes them.
* `...RelativeProjQcohSheaf.Fd.chartClassInv_pullback`: **the inverse is natural in the test
  scheme.**

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (V : S.Opens) {k : ℤ} {T : Scheme.{u}}

/-! ### The inverse of the chart-wise class -/

/-- **The inverse of `...RelativeProjQcohSheaf.Fd.chartClass`**, as a map of the sets `F_d(T)`: a
point of `F_d(T)` for the restriction `𝒜|_V` is a point of `F_d(T)` for `𝒜` itself, over the
composite of its own morphism `T ⟶ V` with the inclusion `V.ι : V ⟶ S`.

This is the comparison `...RelativeProjQcohSheaf.Fd.restrictPullbackEquiv` of the two spellings of
the restriction followed by the base change of [Stacks, Tag 01NT] in the *upward* direction,
`...RelativeProjQcohSheaf.Fd.baseChangeUp` — each the inverse of the corresponding half of
`Fd.chartClass`. -/
def Fd.chartClassInv (η : Fd (situationAlgebra (A.restrict V.ι)) k T) :
    Fd (situationAlgebra A) k T :=
  Fd.baseChangeUp V.ι (situationAlgebra A) k (Fd.restrictPullbackEquiv A V.ι k T η)

/-- The morphism to the base recorded by the inverse is the composite with the inclusion of
`V`. -/
@[simp] theorem Fd.chartClassInv_fst (η : Fd (situationAlgebra (A.restrict V.ι)) k T) :
    (Fd.chartClassInv A V η).1 = η.1 ≫ V.ι := rfl

/-! ### The two round trips -/

/-- Two equal points of `F_d(T)` have heterogeneously equal classes of quadruples. The classes
live over the recorded morphisms, so this is the only shape available; where the two morphisms are
*definitionally* equal, as they are below, `eq_of_heq` turns it into an equality. -/
theorem Fd.heq_snd
    {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    {T : Scheme.{u}} {ξ η : Fd B d T} (h : ξ = η) : HEq ξ.2 η.2 := by
  subst h; rfl

/-- **The chart-wise class followed by its inverse is the identity.** A class of quadruples for
`𝒜` over a chosen factorization `g_V ≫ V.ι` is recovered from its chart-wise class. -/
theorem Fd.chartClassInv_chartClass (gV : T ⟶ V.toScheme)
    (q : Quotient (Quadruple.setoid (gV ≫ V.ι) (situationAlgebra A) k)) :
    Fd.chartClassInv A V (Fd.chartClass A V gV q) = ⟨gV ≫ V.ι, q⟩ := by
  change Fd.baseChangeUp V.ι (situationAlgebra A) k
      (Fd.restrictPullbackEquiv A V.ι k T
        ((Fd.restrictPullbackEquiv A V.ι k T).symm
          (Fd.baseChangeDownQ V.ι (situationAlgebra A) k gV q))) = _
  rw [Equiv.apply_symm_apply]
  exact Fd.baseChangeUp_baseChangeDownQ V.ι (situationAlgebra A) k gV q

/-- **The inverse followed by the chart-wise class is the identity.** A point of `F_d(T)` for
`𝒜|_V` is recovered from the class of quadruples for `𝒜` it comes from, read over its own
morphism to `V`. -/
theorem Fd.chartClass_chartClassInv (η : Fd (situationAlgebra (A.restrict V.ι)) k T) :
    Fd.chartClass A V η.1 (Fd.chartClassInv A V η).2 = η := by
  have h : Fd.baseChangeDownQ V.ι (situationAlgebra A) k η.1
        (Fd.chartClassInv A V η).2
      = Fd.restrictPullbackEquiv A V.ι k T η :=
    Fd.baseChangeDownQ_baseChangeUp V.ι (situationAlgebra A) k
      (Fd.restrictPullbackEquiv A V.ι k T η)
  change (Fd.restrictPullbackEquiv A V.ι k T).symm
      (Fd.baseChangeDownQ V.ι (situationAlgebra A) k η.1 (Fd.chartClassInv A V η).2) = η
  rw [h]
  exact (Fd.restrictPullbackEquiv A V.ι k T).symm_apply_apply η

/-- **The chart-wise class is a bijection**, on classes over a fixed factorization: strict
equivalence classes of quadruples for `𝒜` over `g_V ≫ V.ι : T ⟶ S` correspond to strict
equivalence classes of quadruples for the restriction `𝒜|_V` over `g_V : T ⟶ V`.

The forward map is `Fd.chartClass` read on the second component, and the inverse is
`Fd.chartClassInv` read the same way. -/
def Fd.chartClassEquiv (gV : T ⟶ V.toScheme) :
    Quotient (Quadruple.setoid (gV ≫ V.ι) (situationAlgebra A) k)
      ≃ Quotient (Quadruple.setoid gV (situationAlgebra (A.restrict V.ι)) k) where
  toFun q := (Fd.chartClass A V gV q).2
  invFun r := (Fd.chartClassInv A V (⟨gV, r⟩ : Fd (situationAlgebra (A.restrict V.ι)) k T)).2
  left_inv q := eq_of_heq (Fd.heq_snd (Fd.chartClassInv_chartClass A V gV q))
  right_inv r := eq_of_heq (Fd.heq_snd (Fd.chartClass_chartClassInv A V
    (⟨gV, r⟩ : Fd (situationAlgebra (A.restrict V.ι)) k T)))

/-- The bijection is `Fd.chartClass` on the second component. -/
@[simp] theorem Fd.chartClassEquiv_apply (gV : T ⟶ V.toScheme)
    (q : Quotient (Quadruple.setoid (gV ≫ V.ι) (situationAlgebra A) k)) :
    Fd.chartClassEquiv A V gV q = (Fd.chartClass A V gV q).2 := rfl

/-- The chart-wise class is the bijection, read as an element of `F_d(T)`. -/
theorem Fd.chartClass_eq_mk (gV : T ⟶ V.toScheme)
    (q : Quotient (Quadruple.setoid (gV ≫ V.ι) (situationAlgebra A) k)) :
    Fd.chartClass A V gV q = ⟨gV, Fd.chartClassEquiv A V gV q⟩ := rfl

/-! ### The two halves separately -/

/-- **The chart-wise class is injective** on the classes over a fixed factorization. -/
theorem Fd.chartClass_injective (gV : T ⟶ V.toScheme) :
    Function.Injective (Fd.chartClass A V gV (k := k)) := by
  intro q q' h
  have h1 := Fd.chartClassInv_chartClass A V gV q
  have h2 := Fd.chartClassInv_chartClass A V gV q'
  rw [h] at h1
  exact eq_of_heq (Fd.heq_snd (h1.symm.trans h2))

/-- **The chart-wise class is surjective onto the classes over its factorization**: every point of
`F_d(T)` for `𝒜|_V` is the chart-wise class of a class of quadruples for `𝒜`, over the
factorization the point itself records. -/
theorem Fd.chartClass_surjective_of_fst (η : Fd (situationAlgebra (A.restrict V.ι)) k T)
    (gV : T ⟶ V.toScheme) (hgV : η.1 = gV) :
    ∃ q : Quotient (Quadruple.setoid (gV ≫ V.ι) (situationAlgebra A) k),
      Fd.chartClass A V gV q = η := by
  subst hgV
  exact ⟨(Fd.chartClassInv A V η).2, Fd.chartClass_chartClassInv A V η⟩

/-! ### Naturality in the test scheme -/

/-- **The inverse of the chart-wise class is natural in the test scheme.** Both halves are:
`...RelativeProjQcohSheaf.Fd.restrictPullbackEquiv_pullback` and
`...RelativeProjQcohSheaf.Fd.baseChangeUp_pullback`. -/
theorem Fd.chartClassInv_pullback {T' : Scheme.{u}} (g : T' ⟶ T)
    (η : Fd (situationAlgebra (A.restrict V.ι)) k T) :
    Fd.chartClassInv A V (Fd.pullback g η) = Fd.pullback g (Fd.chartClassInv A V η) := by
  rw [Fd.chartClassInv, Fd.chartClassInv, Fd.restrictPullbackEquiv_pullback]
  exact Fd.baseChangeUp_pullback V.ι (situationAlgebra A) k g _

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
