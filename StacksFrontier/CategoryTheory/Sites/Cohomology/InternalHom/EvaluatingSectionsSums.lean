module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSections

/-!
# Evaluating a finite sum of sections of an internal Hom complex

Let `(C, O)` be a ringed site and let `L` and `M` be complexes of `O`-modules. Evaluation of a
homogeneous local section of the internal Hom complex `SheafHom(L, M)` on a local section of `L`
is additive in each variable
(`AlgebraicGeometry.RingedSite.applyHomSectionOver_add_left` and `..._add_right`). This file
records the consequence for a finite sum in either variable, which is what a computation with a
section written in a finite basis uses.

## Main results

* `AlgebraicGeometry.RingedSite.applyHomSectionOver_zero_left`: evaluating the zero section
  gives zero.
* `AlgebraicGeometry.RingedSite.applyHomSectionOver_sum_left` and
  `AlgebraicGeometry.RingedSite.applyHomSectionOver_sum_right`: **evaluation distributes over a
  finite sum**, in the Hom section and in the source section respectively.

## Implementation notes

The two statements have different proofs. Evaluation on a *fixed* Hom section is the value of a
morphism of sheaves of modules on the slice site, so the sum in the source section is the
additivity of that morphism and nothing more. Evaluation at a *fixed* source section is not
packaged as such a morphism, because the source section lives over an object of the slice site
rather than over the base of the slice; the sum in the Hom section is therefore obtained by
induction on the index set from the binary additivity, with the zero case recorded separately.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  {L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (H : SheafHomComplex X L M)

/-- **Evaluating the zero section of the internal Hom complex gives zero.** -/
theorem applyHomSectionOver_zero_left (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (x : (L.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq 0 x = 0 :=
  congrArg (fun z : CochainComplex.HomComplex.Cochain _ _ n =>
    ((z.v p q hpq).val.app (op (Over.mk i))) x) (map_zero (H.sectionsEquiv U n))

/-- **Evaluation distributes over a finite sum of sections of the internal Hom complex.** -/
theorem applyHomSectionOver_sum_left {κ : Type*} (t : Finset κ) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q) (f : κ → (H.obj.X n).val.obj (op U))
    (x : (L.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq (∑ l ∈ t, f l) x =
      ∑ l ∈ t, applyHomSectionOver X H U V i n p q hpq (f l) x := by
  classical
  induction t using Finset.induction with
  | empty => exact applyHomSectionOver_zero_left X H U V i n p q hpq x
  | insert b u hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, applyHomSectionOver_add_left, ih]

/-- **Evaluation distributes over a finite sum of sections of the source complex.** -/
theorem applyHomSectionOver_sum_right {κ : Type*} (t : Finset κ) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q) (f : (H.obj.X n).val.obj (op U))
    (x : κ → (L.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f (∑ l ∈ t, x l) =
      ∑ l ∈ t, applyHomSectionOver X H U V i n p q hpq f (x l) :=
  map_sum _ _ _

end AlgebraicGeometry.RingedSite

end
