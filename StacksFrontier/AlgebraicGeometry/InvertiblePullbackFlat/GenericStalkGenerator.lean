module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicFromGenericStalk

/-!
# A generator of the generic stalk is a nonzerodivisor on it

The first paragraph of [Stacks, Tag 0BD7] produces an element `m` of the stalk of `ℒ` at the
generic point of `X` which *generates* that stalk, and then reads it as a **regular** meromorphic
section. `AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfGenericStalk` performs
that passage, but from a different input: it asks that `r ↦ r • m` be *injective*, and generation
alone does not give that — over `R = ℤ` and `M = ℤ/2` the element `1` generates while `r ↦ r • 1`
is not injective. This file supplies the missing step for an **invertible** `ℒ`, where it is true.

The argument is not the obvious one. One may be tempted to use that the local ring at the generic
point of an integral scheme is a field; this file does not, and needs no hypothesis on the ring at
all. An invertible module is trivialized near every point
(`Stacks.Divisors.isTrivializedNear_of_isInvertible`), so the stalk carries *some* element `t` with
`r ↦ r • t` bijective. A generator `m` is `a • t`, and `t` is `b • m` because `m` generates, so
`(b * a) • t = t` and `b * a = 1`. Multiplication by `m` is then multiplication by `a` followed by
multiplication by `t`, and `a` is a unit.

## Main results

* `Stacks.SheafOfModules.injective_smul_of_bijective_smul_of_span_eq_top`: the algebraic step — in
  any module carrying one element by which multiplication is bijective, multiplication by a
  generator is injective.
* `AlgebraicGeometry.injective_smul_genericPoint_of_span_eq_top`: multiplication by a generator of
  the stalk of an invertible module at the generic point is injective.
* `AlgebraicGeometry.isRegularMeromorphicSection_of_span_eq_top_genericPoint`: hence the
  meromorphic section the first paragraph of [Stacks, Tag 0BD7] builds from such a generator is
  regular — the first of the three conjuncts the family of that proof's penultimate paragraph is
  asked for.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.SheafOfModules

/-- **Multiplication by a generator is injective once multiplication by something is bijective.**
If `t` is an element of `M` with `r ↦ r • t` bijective and `t` is a multiple `b • m`, then
`m = a • t` gives `(b * a) • t = t`, so `b * a = 1`, `a` is a unit and `r ↦ r • m = (r * a) • t`
is injective. No hypothesis on the ring is used.

The hypothesis is `t = b • m` rather than `Submodule.span R {m} = ⊤` so that a consumer whose
generation statement is written for a *different* but pointwise-equal scalar action can supply
it: the membership is an equation between elements, which transports along an equality of
actions, while a `Submodule` does not, its very type depending on the `Module` instance. -/
theorem injective_smul_of_bijective_smul_of_smul_eq {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {t m : M}
    (ht : Function.Bijective fun r : R => r • t) {b : R} (hb : b • m = t) :
    Function.Injective fun r : R => r • m := by
  obtain ⟨a, ha⟩ := ht.2 m
  replace ha : a • t = m := ha
  have hba : b * a = 1 := by
    refine ht.1 ?_
    simp only [mul_smul, ha, hb, one_smul]
  intro r r' hrr'
  replace hrr' : r • m = r' • m := hrr'
  have h : (r * a) • t = (r' * a) • t := by
    rw [mul_smul, mul_smul, ha]
    exact hrr'
  have hra : r * a = r' * a := ht.1 h
  have hrab : r * (a * b) = r' * (a * b) := by rw [← mul_assoc, ← mul_assoc, hra]
  rwa [mul_comm a b, hba, mul_one, mul_one] at hrab

/-- The generation form of `Stacks.SheafOfModules.injective_smul_of_bijective_smul_of_smul_eq`:
a generator of a module carrying one element by which multiplication is bijective is itself such
an element. -/
theorem injective_smul_of_bijective_smul_of_span_eq_top {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {t m : M}
    (ht : Function.Bijective fun r : R => r • t)
    (hm : Submodule.span R {m} = ⊤) :
    Function.Injective fun r : R => r • m :=
  have htmem : t ∈ Submodule.span R {m} := by rw [hm]; exact Submodule.mem_top
  injective_smul_of_bijective_smul_of_smul_eq ht
    (Submodule.mem_span_singleton.1 htmem).choose_spec

end Stacks.SheafOfModules

namespace AlgebraicGeometry

/-- **Multiplication by a generator of the generic stalk of an invertible module is injective.**
An invertible module is trivialized near the generic point, which supplies the element by which
multiplication is bijective that
`Stacks.SheafOfModules.injective_smul_of_bijective_smul_of_span_eq_top` asks for. -/
theorem injective_smul_genericPoint_of_span_eq_top (X : Scheme.{u}) [IsIntegral X]
    (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F]
    {m : F.presheaf.stalk (genericPoint X)}
    (hm : Submodule.span (X.presheaf.stalk (genericPoint X)) {m} = ⊤) :
    Function.Injective fun r : X.presheaf.stalk (genericPoint X) => r • m := by
  obtain ⟨W, hηW, t, hb⟩ := Stacks.Divisors.isTrivializedNear_of_isInvertible F (genericPoint X)
  exact Stacks.SheafOfModules.injective_smul_of_bijective_smul_of_span_eq_top (hb _ hηW) hm

/-- **The meromorphic section of the first paragraph of [Stacks, Tag 0BD7] is regular**, from
generation of the generic stalk rather than from injectivity of multiplication. This is the
conjunct `IsRegularMeromorphicSection` of the family that proof's penultimate paragraph produces,
discharged for the named section `AlgebraicGeometry.meromorphicSectionOfGenericStalk X F m`. -/
theorem isRegularMeromorphicSection_of_span_eq_top_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F]
    {m : F.presheaf.stalk (genericPoint X)}
    (hm : Submodule.span (X.presheaf.stalk (genericPoint X)) {m} = ⊤) :
    IsRegularMeromorphicSection X.sheaf F (meromorphicSectionOfGenericStalk X F m) :=
  isRegularMeromorphicSection_meromorphicSectionOfGenericStalk X F
    (injective_smul_genericPoint_of_span_eq_top X F hm)

open Stacks.SheafOfModules.TensorStalkRingedSpace in
/-- **The same, with the generation hypothesis read at the `TensorStalkRingedSpace` spelling.**
The scalar action on `Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk` is Mathlib's on
`F.presheaf.stalk`, seated at that spelling by
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`. -/
theorem isRegularMeromorphicSection_of_span_eq_top_grpStalk (X : Scheme.{u}) [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F]
    (m : grpStalk X.toRingedSpace F.val (genericPoint X))
    (hm : letI := stalkModule X.toRingedSpace F.val (genericPoint X)
      Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} = ⊤) :
    IsRegularMeromorphicSection X.sheaf F (meromorphicSectionOfGenericStalk X F m) := by
  let := stalkModule X.toRingedSpace F.val (genericPoint X)
  obtain ⟨W, hηW, t, hbij⟩ :=
    Stacks.Divisors.isTrivializedNear_of_isInvertible F (genericPoint X)
  have htmem : (show grpStalk X.toRingedSpace F.val (genericPoint X) from
        F.presheaf.germ W (genericPoint X) hηW t) ∈
      Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} := by
    rw [hm]; exact Submodule.mem_top
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 htmem
  refine isRegularMeromorphicSection_meromorphicSectionOfGenericStalk X F
    (Stacks.SheafOfModules.injective_smul_of_bijective_smul_of_smul_eq (hbij _ hηW)
      (b := b) ?_)
  exact hb

end AlgebraicGeometry

end
