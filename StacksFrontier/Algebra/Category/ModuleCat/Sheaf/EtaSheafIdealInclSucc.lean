module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower

/-!
# The ideal-power inclusion is the degree-zero one after the successor comparison

`Stacks.IdealTorsion.Eta.idealPowerIncl`, of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf`, is the inclusion
`I^{⊗ (n + 1)} ⊗ M ⟶ I^{⊗ n} ⊗ M` of consecutive invertible ideal powers. By construction it is
the inverse of the successor comparison of the tensoring autoequivalence followed by the ideal
inclusion tensored into the `n`-th power, so in degree `0` it is the ideal inclusion alone — the
successor comparison in degree `0` being the identity.

This file proves that reading, namely

`idealPowerIncl X I ι n M = (powSuccIso e n M).inv ≫ idealPowerIncl X I ι 0 (I^{⊗ n} ⊗ M)`,

where `e` is the autoequivalence of tensoring on the right by `I`. It is what lets a statement
written in the spelling the abstract transport of
`StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc` produces — the successor comparison
followed by a component of a natural transformation to the identity — be rewritten in terms of
`idealPowerIncl` itself.

## Main definitions

* `Stacks.IdealTorsion.Eta.idealPowerInclCore`: the part of `idealPowerIncl` after the successor
  comparison, as a named morphism with an explicit type.

## Main results

* `Stacks.IdealTorsion.Eta.invertiblePowSuccIso_eq`: the two integer successor comparisons of an
  autoequivalence in this library — the one `idealPowerIncl` is built from and the one the
  transport is stated with — agree.
* `Stacks.IdealTorsion.Eta.idealPowerIncl_zero_eq_core`: in degree `0` the inclusion is the
  tensored ideal inclusion followed by the right unitor, with no successor comparison.
* `Stacks.IdealTorsion.Eta.idealPowerIncl_eq_powSuccIso_inv_comp`: **the inclusion in degree `n`
  is the inverse successor comparison followed by the degree-`0` inclusion at the `n`-th power.**

## Implementation notes

**Why the equality is not proved by `rfl`.** The two sides differ by the identity morphism that
the degree-`0` successor comparison contributes: `powSuccIso e 0 P` is `Iso.refl _`, so
`idealPowerIncl X I ι 0 P` unfolds to `𝟙 _ ≫ (ι ⊗ 1) ≫ (right unitor)` while
`idealPowerIncl X I ι n M` unfolds to `(powSuccIso e n M).inv ≫ (ι ⊗ 1) ≫ (right unitor)`.
Removing the `𝟙` is `Category.id_comp`, a *proof* in a general category rather than a reduction,
and asking for the whole equality definitionally makes the kernel unfold composition of
`SheafOfModules`, then of `PresheafOfModules`, down to `LinearMap.comp`, which exceeds the
heartbeat limit.

The remedy is to name the part after the successor comparison, as `idealPowerInclCore`, and to
split the equality into steps each of which is either a one-level unfolding of a definition at
syntactically identical arguments (`idealPowerIncl_eq_core`, `idealPowerInclCore_eq_zero`) or a
rewrite by `Category.id_comp` at the level of morphisms of sheaves, where nothing is unfolded at
all. No step compares composites of concrete linear maps.

**The two successor comparisons.** `idealPowerIncl` is built from
`Stacks.SheafOfModules.Invertible.powSuccIso` of
`StacksFrontier.AlgebraicGeometry.Divisors.TensorPower`, while the transport of
`StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc` is stated with
`Stacks.Equivalence.powSuccIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower`. These are two constants with the same
defining recursion in two namespaces; they agree, but not definitionally at a variable exponent,
since each is stuck on its own matcher. `invertiblePowSuccIso_eq` identifies them by that
recursion, the base cases `0` and `1` holding by `rfl` and the step reducing the exponent at a
shifted object exactly as the definitions do.

## References

* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

/- The same locally-unfoldable links as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullback`: without them instance search
does not see through the spelling `structureSheaf X.sheaf` of the structure sheaf of rings. -/
attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory

open Stacks.SheafOfModules.Invertible ( tensorRightFunctor_isEquivalence
  tensorPowerEquivalence   tensorProductRightUnitor)

universe v u

namespace Stacks.IdealTorsion.Eta

/-! ### The two successor comparisons agree -/

section Bridge

variable {A : Type u} [Category.{v} A]

/-- The two natural-number successor comparisons agree. Both recurse by reducing the exponent
`n + 2` to `n + 1` at the object `e M`, with `Iso.refl` at the exponents `0` and `1`. -/
theorem invertiblePowNatSuccIso_eq (e : A ≌ A) : ∀ (n : ℕ) (M : A),
    Stacks.SheafOfModules.Invertible.powNatSuccIso e n M =
      Stacks.Equivalence.powNatSuccIso e n M
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, M => invertiblePowNatSuccIso_eq e (n + 1) (e.functor.obj M)

/-- The two cancellation comparisons for inverse iterates agree. Both recurse by reducing the
exponent `n + 2` to `n + 1` at the object `e⁻¹ M`, with the counit at the exponents `0` and
`1`. -/
theorem invertiblePowNatInverseSuccIso_eq (e : A ≌ A) : ∀ (n : ℕ) (M : A),
    Stacks.SheafOfModules.Invertible.powNatInverseSuccIso e n M =
      Stacks.Equivalence.powNatInverseSuccIso e n M
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, M => invertiblePowNatInverseSuccIso_eq e (n + 1) (e.inverse.obj M)

/-- **The two integer successor comparisons agree.** `Stacks.IdealTorsion.Eta.idealPowerIncl` is
built from `Stacks.SheafOfModules.Invertible.powSuccIso`, while the transport of
`StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc` is stated with
`Stacks.Equivalence.powSuccIso`; the two are the same recursion in two namespaces, and so agree,
but not definitionally at a variable exponent, each being stuck on its own matcher. The three
branches are the three branches both definitions split into. -/
theorem invertiblePowSuccIso_eq (e : A ≌ A) (n : ℤ) (M : A) :
    Stacks.SheafOfModules.Invertible.powSuccIso e n M =
      Stacks.Equivalence.powSuccIso e n M := by
  match n with
  | Int.ofNat k => exact invertiblePowNatSuccIso_eq e k M
  | Int.negSucc 0 => rfl
  | Int.negSucc (k + 1) => exact invertiblePowNatInverseSuccIso_eq e (k + 1) M

end Bridge

/-! ### The inclusion in degree `n` through the inclusion in degree `0` -/

variable (X : RingedSpace.{u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- The part of `Stacks.IdealTorsion.Eta.idealPowerIncl` that follows the successor comparison:
the ideal inclusion tensored into the `n`-th ideal power, followed by the right unit constraint.
Naming it gives the two unfoldings of `idealPowerIncl` below a common, explicitly typed
subterm, which is what keeps them from unfolding further. -/
noncomputable def idealPowerInclCore
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj
        (idealPowerTerm X I n M)).obj I ⟶
      idealPowerTerm X I n M :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf))).map
      (X := (idealPowerTerm X I n M, I)) (Y := (idealPowerTerm X I n M, 𝒪)) (𝟙 _, ι) ≫
    (tensorProductRightUnitor X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property (idealPowerTerm X I n M)).hom

/-- The inclusion of consecutive ideal powers is the inverse successor comparison followed by
`idealPowerInclCore`. This is one level of unfolding of the definition, at syntactically the
arguments the definition itself writes. -/
theorem idealPowerIncl_eq_core (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    idealPowerIncl X I ι n M =
      (Stacks.SheafOfModules.Invertible.powSuccIso
        (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property I))
        n M).inv ≫ idealPowerInclCore X I ι n M := rfl

/-- `idealPowerInclCore` in degree `n` at `M` is the same morphism as in degree `0` at the
`n`-th ideal power of `M`: the zeroth power of the tensoring autoequivalence is the identity, so
the two are the same term. -/
theorem idealPowerInclCore_eq_zero (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    idealPowerInclCore X I ι n M = idealPowerInclCore X I ι 0 (idealPowerTerm X I n M) := rfl

/-- **In degree `0` the inclusion of consecutive ideal powers carries no successor comparison**:
it is the ideal inclusion tensored into the module, followed by the right unit constraint. The
degree-`0` successor comparison is `Iso.refl`, so the only difference from `idealPowerIncl_eq_core`
is an identity morphism in front, removed by `Category.id_comp`. -/
theorem idealPowerIncl_zero_eq_core (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (P : SheafOfModules.{u} Oₓ) :
    idealPowerIncl X I ι 0 P = idealPowerInclCore X I ι 0 P :=
  (idealPowerIncl_eq_core X I ι 0 P).trans (Category.id_comp _)

/-- **The inclusion of consecutive ideal powers in degree `n` is the inverse successor comparison
followed by the degree-`0` inclusion at the `n`-th ideal power.**

This is the form in which the abstract transport of
`StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc` produces the inclusion — the
successor comparison followed by a component of a natural transformation to the identity — so it
is what converts a statement in the transport's spelling into one about `idealPowerIncl`. -/
theorem idealPowerIncl_eq_powSuccIso_inv_comp (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    idealPowerIncl X I ι n M =
      (Stacks.Equivalence.powSuccIso
          (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property I))
          n M).inv ≫
        idealPowerIncl X I ι 0 (idealPowerTerm X I n M) :=
  (idealPowerIncl_eq_core X I ι n M).trans
    ((congrArg (fun k => Iso.inv k ≫ idealPowerInclCore X I ι n M)
        (invertiblePowSuccIso_eq
          (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property I))
          n M)).trans
      (congrArg (fun k => (Stacks.Equivalence.powSuccIso
            (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property I))
            n M).inv ≫ k)
        ((idealPowerInclCore_eq_zero X I ι n M).trans
          (idealPowerIncl_zero_eq_core X I ι (idealPowerTerm X I n M)).symm)))

end Stacks.IdealTorsion.Eta

end
