module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorRingedSpace
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionRestrict
public import StacksFrontier.AlgebraicGeometry.SchemeModulesSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSectionPower.Glue

/-!
# Reindexing: the right-bracketed tensor powers and the powers of [Stacks, Tag 01PW]

The surjectivity half of [Stacks, Tag 01PW],
`Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace`, is stated for
`Stacks.TensorSectionPower.powObj`, the **left-bracketed** tensor power indexed from the first
power: `powObj ℱ 0 = ℱ` and `powObj ℱ (k + 1) = powObj ℱ k ⊗ ℱ`.  The reflexive powers of
[Stacks, Tag 0EBN] and the ordinary powers
`Stacks.AlgebraicGeometry.ReflexivePowers.tensorPower` they restrict to on an open where `ℱ` is
invertible are **right-bracketed** and indexed from the zeroth power, which is the structure
sheaf: `tensorPower ℱ 1 = ℱ` and `tensorPower ℱ (n + 2) = ℱ ⊗ tensorPower ℱ (n + 1)`.

So the two families agree at `tensorPower ℱ 1 = ℱ = powObj ℱ 0` and shift by one from there on,
and this file builds the comparison

`ℱ^{⊗ (n + 1)} ≅ powObj ℱ n`.

The index `0` of `tensorPower` has no counterpart in `powObj` at all: `powObj` has no entry equal
to the structure sheaf, which is exactly why it is indexed from the first power (see its own
implementation notes).

## Main definitions

* `tensorPowerSuccRightIso`: `ℱ^{⊗ (n + 2)} ≅ ℱ^{⊗ (n + 1)} ⊗ ℱ`.  The right-bracketed power
  satisfies, up to isomorphism, the recursion that appends a factor on the *right*, which is the
  recursion `powObj` is built by.  Proved by induction from the associativity constraint
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafAssociator'` of the tensor product
  sheaf.
* `tensorPowerIsoPowObj`: **the reindexing comparison** `ℱ^{⊗ (n + 1)} ≅ powObj ℱ n`.
* `restrictReflexivePowerIsoPowObj`: the composite with the comparison of
  `StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionRestrict`, giving
  `ℱ^{[n + 1]}|_V ≅ powObj (ℱ|_V) n` for `ℱ` coherent on an integral locally Noetherian scheme
  and `V` a nonempty open on which `ℱ` is invertible.  This is the object-level identification a
  consumer of [Stacks, Tag 01PW] needs in order to speak about the reflexive powers.

## Implementation notes

**The two monoidal spellings.**  `powObj` is built from the monoidal product of
`Stacks.SheafInternalHom.schemeMonoidalCategory`, which is the localized structure: its tensor
product is only *isomorphic* to the tensor product sheaf of [Stacks, Tag 01CA], not equal to it.
`tensorPower` is built from `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` directly.
`Stacks.SchemeModulesSpelling.tensorSheafIsoMonoidal` is the identification of the two, and it is
the only place in the construction below where anything other than the associator is used.  No
monoidal-category instance has to be in scope to *state* either family, since both are plain
recursive `def`s.

**What this does not give.**  The conclusion of
`Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace` is not restated here for
`tensorPower`.  It asserts an equality of *sections* involving
`Stacks.SectionTensorFormula.tensorSection`, and transporting such an equality along an
isomorphism of the module arguments needs the naturality of `tensorSection` in those arguments —
a formula for `(ℱ ◁ φ).app U` on a product of local sections.  That formula is absent from both
trees; `StacksFrontier/AlgebraicGeometry/TensorSectionPower/Basic.lean` records the same gap as the
reason `powObj` is not identified with `Stacks.TensorPowers.natTensorPow` or with
`Stacks.Ample.tensorPowModule`.  What is built here is the object-level comparison, which is what
was missing for the statement of Tag 01PW to be *about* the reflexive powers at all.

**No `@[stacks]` attribute.**  A reindexing of iterated tensor products is not a clause of a tag.
Tag 01PW is registered where it is proved.  The colimit clause of [Stacks, Tag 0EBN] is proved in
`Divisors/Reflexive/SectionLocusColimitSections.lean`, by a route that reads the divisibility of
the transition maps off on sections rather than quoting Tag 01PW, and the two registrations of
[Stacks, Tag 0EBR], in `SectionLocusAffineTag.lean`, are unconditional.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace (tensorSheafAssociator')

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

variable {X : Scheme.{u}}

/-! ### Appending a factor on the right -/

/-- **The right-bracketed tensor power also satisfies the recursion that appends a factor on the
right**: `ℱ^{⊗ (n + 2)} ≅ ℱ^{⊗ (n + 1)} ⊗ ℱ`, by the associativity constraint of the tensor
product sheaf.  This is what lets the right-bracketed family be compared with the
left-bracketed `Stacks.TensorSectionPower.powObj`. -/
def tensorPowerSuccRightIso (L : X.Modules) : (n : ℕ) →
    (tensorPower L (n + 2) ≅
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((tensorPower L (n + 1)))).obj (L)) : X.Modules))
  | 0 => Iso.refl _
  | n + 1 =>
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf)).mapIso (X := (L, tensorPower L (n + 2)))
          (Y := (L, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf).obj (tensorPower L (n + 1))).obj L))
          (Iso.prod (Iso.refl L) (tensorPowerSuccRightIso L n)) ≪≫
        tensorSheafAssociator' X.toRingedSpace L (tensorPower L (n + 1)) L

/-- At `n = 0` the two bracketings of `ℱ^{⊗ 2}` are the same object. -/
theorem tensorPowerSuccRightIso_zero (L : X.Modules) :
    tensorPowerSuccRightIso L 0 = Iso.refl _ := rfl

/-- The recursion defining `tensorPowerSuccRightIso`. -/
theorem tensorPowerSuccRightIso_succ (L : X.Modules) (n : ℕ) :
    tensorPowerSuccRightIso L (n + 1) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf)).mapIso (X := (L, tensorPower L (n + 2)))
          (Y := (L, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf).obj (tensorPower L (n + 1))).obj L))
          (Iso.prod (Iso.refl L) (tensorPowerSuccRightIso L n)) ≪≫
        tensorSheafAssociator' X.toRingedSpace L (tensorPower L (n + 1)) L := rfl

/-! ### The reindexing comparison -/

/-- **The reindexing comparison.**  `ℱ^{⊗ (n + 1)}` in the right-bracketed indexing of
`Stacks.AlgebraicGeometry.ReflexivePowers.tensorPower` is the left-bracketed
`Stacks.TensorSectionPower.powObj ℱ n` of [Stacks, Tag 01PW].  The shift by one is forced: the
value of `tensorPower` at `0` is the structure sheaf and `powObj` has no such entry. -/
def tensorPowerIsoPowObj (L : X.Modules) : (n : ℕ) →
    (tensorPower L (n + 1) ≅ Stacks.TensorSectionPower.powObj L n)
  | 0 => Iso.refl _
  | n + 1 =>
      tensorPowerSuccRightIso L n ≪≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf)).mapIso (X := (tensorPower L (n + 1), L))
            (Y := (Stacks.TensorSectionPower.powObj L n, L))
            (Iso.prod (tensorPowerIsoPowObj L n) (Iso.refl L)) ≪≫
          (Stacks.SchemeModulesSpelling.tensorSheafIsoMonoidal X
            (Stacks.TensorSectionPower.powObj L n) L).symm

/-- The first ordinary tensor power and the zeroth power of [Stacks, Tag 01PW] are both `ℱ`. -/
theorem tensorPowerIsoPowObj_zero (L : X.Modules) :
    tensorPowerIsoPowObj L 0 = Iso.refl _ := rfl

/-- The recursion defining `tensorPowerIsoPowObj`: reassociate, compare at `n`, and cross the two
spellings of the tensor product. -/
theorem tensorPowerIsoPowObj_succ (L : X.Modules) (n : ℕ) :
    tensorPowerIsoPowObj L (n + 1) =
      tensorPowerSuccRightIso L n ≪≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf)).mapIso (X := (tensorPower L (n + 1), L))
            (Y := (Stacks.TensorSectionPower.powObj L n, L))
            (Iso.prod (tensorPowerIsoPowObj L n) (Iso.refl L)) ≪≫
          (Stacks.SchemeModulesSpelling.tensorSheafIsoMonoidal X
            (Stacks.TensorSectionPower.powObj L n) L).symm := rfl

/-! ### The reflexive powers on `V`, at the indexing of Tag 01PW -/

/-- **`ℱ^{[n + 1]}|_V ≅ powObj (ℱ|_V) n`.**  The comparison of
`StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionRestrict` followed by
the reindexing: on a nonempty open where the coherent module `ℱ` on an integral locally
Noetherian scheme is invertible, the reflexive powers of [Stacks, Tag 0EBN] are the powers
[Stacks, Tag 01PW] is stated for. -/
def restrictReflexivePowerIsoPowObj (F : X.Modules) (V : X.Opens) [IsIntegral X]
    [IsLocallyNoetherian X] (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F)) (n : ℕ) :
    (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1)) ≅
      Stacks.TensorSectionPower.powObj ((Scheme.Modules.restrictFunctor V.ι).obj F) n :=
  restrictPowerIso F V hF hV (n + 1) ≪≫
    tensorPowerIsoPowObj ((Scheme.Modules.restrictFunctor V.ι).obj F) n

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
