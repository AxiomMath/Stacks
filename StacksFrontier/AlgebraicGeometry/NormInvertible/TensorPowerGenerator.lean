module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorGenerator
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication

/-!
# Local generators of the tensor powers of an invertible module

Let `(X, 𝒪_X)` be a ringed space, let `L` be an invertible sheaf of `𝒪_X`-modules and let `U` be
an open of `X`. A section `s ∈ L(U)` *generates* `L` on `U` when multiplication by `s` is a
bijection `𝒪_X(V) → L(V)` for every `V ≤ U` (`Stacks.SheafOfModules.GeneratorSections`). This
file propagates such a section up the tower of tensor powers: it builds, for every `n : ℕ`, a
generator of `L^{⊗ n}` on `U` out of a generator of `L` on `U`, and computes the transition unit
of two of them to be the `n`-th power of the transition unit downstairs.

The second statement is what the degree formula `Norm_f(f^* 𝒩) ≅ 𝒩^{⊗ d}` of
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) needs: the norm of a transition
unit pulled back along a degree-`d` morphism is its `d`-th power, so the two sides of that
formula are compared by recognizing a `d`-th power of transition units as the transition units of
a `d`-th tensor power.

## Which tensor power

`Stacks.SheafOfModules.Invertible.tensorPowerModule' L (n : ℤ)`, the integer tensor power of Tag
01CU ascribed at `SheafOfModules (structureSheafRing X)`. The successor comparison
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso` is stated for
`TensorSheafification.tensorSheaf X.presheaf (structureSheafRing X).property`, while
`tmulGenerator` is stated for `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X`;
the two are **equal by `rfl`**, so the induction step below composes them with no bridging lemma,
exactly as `StacksFrontier.AlgebraicGeometry.NormInvertible.TensorAdditive` does.

## Main definitions

* `Stacks.SheafOfModules.tensorPowerZeroIso`: the zeroth tensor power is the structure sheaf,
  with the natural-number exponent `((0 : ℕ) : ℤ)`.
* `Stacks.SheafOfModules.tensorPowerSuccNatIso`: the successor comparison
  `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` at natural-number exponents.
* `Stacks.SheafOfModules.tensorPowerGenerator`: **a generator of `L` over `U` gives a generator
  of `L^{⊗ n}` over `U`.**

## Main results

* `Stacks.SheafOfModules.generatorOfIso_restrict`: the generator supplied by a trivialization
  commutes with restriction.
* `Stacks.SheafOfModules.tensorPowerGenerator_restrict`: the tensor-power generator commutes with
  restriction.
* `Stacks.SheafOfModules.generatorRatioUnit_tensorPowerGenerator`: **the transition unit of two
  tensor-power generators is the `n`-th power of the transition unit**, `[s^n : t^n] = [s : t]^n`.

## Implementation notes

The exponents are natural numbers cast into `ℤ`, not integers: the recursion is on `ℕ` with
`Stacks.SheafOfModules.Invertible.tensorPower_zero` as its base and
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso` as its step, which is the shape in which
`StacksFrontier.AlgebraicGeometry.NormAmple.TensorPower` already runs this induction.
Negative exponents are not needed and are not treated. The cast bookkeeping is done once, in
`tensorPowerZeroIso` and `tensorPowerSuccNatIso`, through
`Stacks.SheafOfModules.Invertible.tensorPowerReindex` and `eqToIso`, so that the three statements
below mention no reindexing at all.

At `n = 0` the generator is the image of the unit section under the trivialization and therefore
does **not** depend on the given generator `s`. Both tensor-power generators in the ratio law are
then literally the same term, which is why `Stacks.SheafOfModules.generatorRatioUnit_self`
closes the base case; the base case of the restriction law is the one new fact needed,
`generatorOfIso_restrict`, which is naturality of the trivialization together with
`map_one` on the structure sheaf.

Every step is term mode or `congrArg`/`congrArg₂` under the two generator constructors. `rw` is
avoided on the generator equalities: the recursion equations hold by `rfl` but their patterns
print identically to the goal, and the `congrArg` idiom of
`Stacks.Divisors.generatorRestrict_tensorNormGen` is what keeps the rewrites addressed to the
right subterm.

No `@[stacks]` attribute is placed: this is an ingredient of Tag 0BCY, not any clause of it.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}}

/-- The generator supplied by a trivialization commutes with restriction: it is the image of the
unit section, and the trivialization is natural. -/
theorem generatorOfIso_restrict (L : SheafOfModules.{u} (structureSheafRing X))
    (e : L ≅ _root_.SheafOfModules.unit (structureSheafRing X)) {U V : Opens X.carrier}
    (h : V ≤ U) :
    generatorRestrict L h (generatorOfIso L (U := U) e) = generatorOfIso L (U := V) e := by
  refine Subtype.ext ?_
  let oneU : (structureSheafRing X).obj.obj (op U) := 1
  let oneV : (structureSheafRing X).obj.obj (op V) := 1
  have hmap : (structureSheafRing X).obj.map (homOfLE h).op oneU = oneV :=
    ((structureSheafRing X).obj.map (homOfLE h).op).hom.map_one
  refine (PresheafOfModules.naturality_apply e.inv.val (homOfLE h).op oneU).symm.trans ?_
  change e.inv.val.app (op V) ((structureSheafRing X).obj.map (homOfLE h).op oneU) =
    e.inv.val.app (op V) oneV
  rw [hmap]

variable (L : SheafOfModules.{u} (structureSheafRing X))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X).property L]

/-- The zeroth tensor power of `L` is the structure sheaf, at the natural-number exponent
`((0 : ℕ) : ℤ)` in which the induction below runs. -/
noncomputable def tensorPowerZeroIso :
    Invertible.tensorPowerModule' L ((0 : ℕ) : ℤ) ≅
      _root_.SheafOfModules.unit (structureSheafRing X) :=
  Invertible.tensorPowerReindex X.presheaf (structureSheafRing X).property L Nat.cast_zero ≪≫
    eqToIso (Invertible.tensorPower_zero X.presheaf (structureSheafRing X).property L)

/-- The successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` at natural-number exponents. -/
noncomputable def tensorPowerSuccNatIso (n : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((Invertible.tensorPowerModule' L (n : ℤ)))).obj (L)) ≅
      Invertible.tensorPowerModule' L ((n + 1 : ℕ) : ℤ) := by
  have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := Nat.cast_succ n
  exact Invertible.tensorPowerSuccIso X.presheaf (structureSheafRing X).property L (n : ℤ) ≪≫
    eqToIso (congrArg (Invertible.tensorPower X.presheaf (structureSheafRing X).property L)
      hcast.symm)

/-- A generator of `L` over `U` gives a generator of `L^{⊗ n}` over `U`. -/
noncomputable def tensorPowerGenerator {U : Opens X.carrier} (s : GeneratorSections X L U)
    (n : ℕ) : GeneratorSections X (Invertible.tensorPowerModule' L (n : ℤ)) U :=
  Nat.rec (motive := fun k => GeneratorSections X (Invertible.tensorPowerModule' L (k : ℤ)) U)
    (generatorOfIso _ (tensorPowerZeroIso L))
    (fun k g => generatorMapIso (tensorPowerSuccNatIso L k) U (tmulGenerator g s)) n

/-- At `n = 0` the tensor-power generator is the image of the unit section under
`tensorPowerZeroIso`; in particular it does not depend on `s`. -/
theorem tensorPowerGenerator_zero {U : Opens X.carrier} (s : GeneratorSections X L U) :
    tensorPowerGenerator L s 0 =
      generatorOfIso (Invertible.tensorPowerModule' L ((0 : ℕ) : ℤ)) (tensorPowerZeroIso L) :=
  rfl

/-- The generator of `L^{⊗ (n + 1)}` is the tensor product of the generator of `L^{⊗ n}` with
`s`, transported along `tensorPowerSuccNatIso`. -/
theorem tensorPowerGenerator_succ {U : Opens X.carrier} (s : GeneratorSections X L U) (n : ℕ) :
    tensorPowerGenerator L s (n + 1) =
      generatorMapIso (tensorPowerSuccNatIso L n) U
        (tmulGenerator (tensorPowerGenerator L s n) s) :=
  rfl

/-- The tensor-power generator commutes with restriction. -/
theorem tensorPowerGenerator_restrict {U V : Opens X.carrier} (h : V ≤ U)
    (s : GeneratorSections X L U) (n : ℕ) :
    generatorRestrict (Invertible.tensorPowerModule' L (n : ℤ)) h
        (tensorPowerGenerator L s n) =
      tensorPowerGenerator L (generatorRestrict L h s) n := by
  induction n with
  | zero =>
      refine (congrArg
        (generatorRestrict (Invertible.tensorPowerModule' L ((0 : ℕ) : ℤ)) h)
        (tensorPowerGenerator_zero L s)).trans ?_
      refine Eq.trans ?_ (tensorPowerGenerator_zero L (generatorRestrict L h s)).symm
      exact generatorOfIso_restrict _ (tensorPowerZeroIso L) h
  | succ n ih =>
      refine (congrArg
        (generatorRestrict (Invertible.tensorPowerModule' L ((n + 1 : ℕ) : ℤ)) h)
        (tensorPowerGenerator_succ L s n)).trans ?_
      refine Eq.trans ?_ (tensorPowerGenerator_succ L (generatorRestrict L h s) n).symm
      refine (generatorMapIso_restrict (tensorPowerSuccNatIso L n) h
        (tmulGenerator (tensorPowerGenerator L s n) s)).symm.trans ?_
      refine congrArg (generatorMapIso (tensorPowerSuccNatIso L n) V) ?_
      refine (tmulGenerator_restrict (tensorPowerGenerator L s n) s h).trans ?_
      exact congrArg₂
        (fun (a : GeneratorSections X (Invertible.tensorPowerModule' L (n : ℤ)) V)
            (b : GeneratorSections X L V) => tmulGenerator a b) ih rfl

/-- **The transition unit of two tensor-power generators is the `n`-th power of the transition
unit.** -/
theorem generatorRatioUnit_tensorPowerGenerator (U : Opens X.carrier)
    (s t : GeneratorSections X L U) (n : ℕ) :
    generatorRatioUnit (Invertible.tensorPowerModule' L (n : ℤ)) U
        (tensorPowerGenerator L s n) (tensorPowerGenerator L t n) =
      (generatorRatioUnit L U s t) ^ n := by
  induction n with
  | zero =>
      refine (congrArg₂
        (generatorRatioUnit (Invertible.tensorPowerModule' L ((0 : ℕ) : ℤ)) U)
        (tensorPowerGenerator_zero L s) (tensorPowerGenerator_zero L t)).trans ?_
      exact (generatorRatioUnit_self _ U _).trans (pow_zero _).symm
  | succ n ih =>
      refine (congrArg₂
        (generatorRatioUnit (Invertible.tensorPowerModule' L ((n + 1 : ℕ) : ℤ)) U)
        (tensorPowerGenerator_succ L s n) (tensorPowerGenerator_succ L t n)).trans ?_
      refine (generatorRatioUnit_mapIso (tensorPowerSuccNatIso L n) U
        (tmulGenerator (tensorPowerGenerator L s n) s)
        (tmulGenerator (tensorPowerGenerator L t n) t)).trans ?_
      refine (generatorRatioUnit_tmulGenerator (tensorPowerGenerator L s n)
        (tensorPowerGenerator L t n) s t).trans ?_
      rw [ih, pow_succ]

end Stacks.SheafOfModules

end
