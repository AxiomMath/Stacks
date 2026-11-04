module

public import StacksFrontier.Deformation.SquareZero.ConormalCokernelBaseChange
public import StacksFrontier.Deformation.SquareZero.HenselizationNaiveCotangent

/-!
# The base-change comparison for the henselization of a pair

Let `k` be a field, let `B` be a finite type `k`-algebra, let `J ⊆ B` be an ideal and let
`(Bʰ, Jʰ)` be the henselization of the pair `(B, J)`.  For a `B`-module `N` and `Nʰ = Bʰ ⊗_B N`
there is a canonical identification

`Ext¹_{Bʰ}(NL_{Bʰ/k}, Nʰ) ≅ Ext¹_B(NL_{B/k}, N) ⊗_B Bʰ`.

It is the chain of three comparisons the proof of Stacks 0DZC runs through: Stacks 0D08 replaces
`NL_{Bʰ/k}` by `NL_{B/k} ⊗_B Bʰ`, Stacks 0GPY moves the base change from the complex to the
coefficients, and flat base change of `Ext` moves it out of the coefficients again, `Bʰ` being
flat over `B` because it is the henselization of a pair.

## Main results

* `Stacks.Deformation.extOneCokernelHenselizationBaseChangeEquiv`: **Stacks 0D08**, read on the
  `Ext` group — the first extension group of `NL_{Bʰ/k}` is the one taken out of
  `NL_{B/k} ⊗_B Bʰ`.
* `Stacks.Deformation.extOneCokernelHenselizationFlatBaseChangeEquiv`: the whole chain, which is
  the base-change input of Stacks 0DZC.

## Implementation notes

The three comparisons are stated against three different presentations of the same group and the
file's work is to make them composable.

Stacks 0D08 is used in the form `Stacks.Deformation.naiveCotangentExtOneHenselizationSourceEquiv`,
whose source complex is the cochain presentation of `NL_{B/k} ⊗_B Bʰ`; Stacks 0GPY is used in the
form `Stacks.Deformation.naiveCotangentExtOneBaseChangeEquiv`, whose source complex is the
termwise extension of scalars of the cochain presentation of `NL_{B/k}`.  The two complexes are
identified by `Stacks.Deformation.naiveCotangentBaseChangeExtendScalarsIso`.

The coefficient object of Stacks 0GPY's left-hand side is `Nʰ` restricted along `B → Bʰ`, while
`Stacks.Deformation.extCokernelIso` wants `Nʰ` as a `B`-module through the scalar tower; the two
`B`-actions agree, and `Stacks.Deformation.henselizationExtCoefficientRestrictIso` records that.

Flat base change in the coefficients is
`Deformation.Examples.extOneCokernelBaseChangeEquiv`, and the flatness it consumes is the first
half of `flat_henselization_and_bijective_quotientMap`.

## References

* [Stacks Project, Tag 0DZC](https://stacks.math.columbia.edu/tag/0DZC)
* [Stacks Project, Tag 0D08](https://stacks.math.columbia.edu/tag/0D08)
* [Stacks Project, Tag 0GPY](https://stacks.math.columbia.edu/tag/0GPY)
-/

@[expose] public section

open CategoryTheory Category Limits
open scoped TensorProduct

universe uk uB uN

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (B : Type uB) [CommRing B] (N : Type uN) [AddCommGroup N] [Module B N]
  (Bh : Type uB) [CommRing Bh] [Algebra B Bh]

/-- The coefficient object of the extension groups classifying square-zero extensions of `Bʰ` by
`Nʰ = Bʰ ⊗_B N`: the module `Nʰ` placed in cohomological degree `0`, universe-lifted exactly as
`Stacks.Deformation.extCokernelIso` places it. -/
public abbrev henselizationExtCoefficient : DerivedCategory (ModuleCat.{max uk uB uN} Bh) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max uk uB uN} Bh) 0).obj
    ((ModuleCat.uliftFunctor.{max uk uB} Bh).obj (ModuleCat.of Bh (Bh ⊗[B] N)))

/-- **The two `B`-actions on `Nʰ = Bʰ ⊗_B N` agree.**  The coefficient object of the extension
groups over `Bʰ`, restricted along `B → Bʰ`, is the coefficient object of the extension groups
over `B`: both are `Nʰ` with the action the scalar tower gives it. -/
public def henselizationExtCoefficientRestrictIso :
    (ModuleCat.restrictScalars (algebraMap B Bh)).obj
        ((ModuleCat.uliftFunctor.{max uk uB} Bh).obj (ModuleCat.of Bh (Bh ⊗[B] N))) ≅
      (ModuleCat.uliftFunctor.{max uk uB} B).obj (ModuleCat.of B (Bh ⊗[B] N)) :=
  LinearEquiv.toModuleIso <|
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (algebraMap B Bh)).obj
        ((ModuleCat.uliftFunctor.{max uk uB} Bh).obj
          (ModuleCat.of Bh (Bh ⊗[B] N)))).isModule) _
      (AddEquiv.refl (ULift.{max uk uB} (Bh ⊗[B] N)))
      (fun b x ↦ congrArg ULift.up (IsScalarTower.algebraMap_smul Bh b x.down))

end

noncomputable section

variable (k : Type uk) [CommRing k] (B : Type uB) [CommRing B] [Algebra k B]
  (N : Type uN) [AddCommGroup N] [Module B N]
  (Bh : Type uB) [CommRing Bh] [Algebra B Bh] [Algebra k Bh] [IsScalarTower k B Bh]
  (J : Ideal B)
  (hhens : HenselianPair Bh (J.map (algebraMap B Bh)))
  (huniv : ∀ (C : Type uB) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
    ∀ f : B →+* C, J ≤ JC.comap f →
      ∃! g : Bh →+* C, g.comp (algebraMap B Bh) = f ∧
        J.map (algebraMap B Bh) ≤ JC.comap g)

include J hhens huniv in
/-- **The conormal-functional model of `Ext¹_{Bʰ}(NL_{Bʰ/k}, Nʰ)` is the extension group taken
out of `NL_{B/k} ⊗_B Bʰ`.**  This is Stacks 0D08 for the henselization of a pair, read on the
`Ext` group the base-change comparison of Stacks 0DZC is about: the canonical comparison
`NL_{B/k} ⊗_B Bʰ ⟶ NL_{Bʰ/k}` is invertible in `D(Bʰ)`, so precomposition with it identifies the
two groups.

Marked `irreducible`: its body composes `Stacks.Deformation.extCokernelIso` with the
derived-category isomorphism of Stacks 0D08, whose inverse is extracted from an `IsIso`
instance, and unfolding that during a definitional-equality check exhausts the recursion
budget at every call site which specializes the coefficient module. Consumers use it as an
isomorphism, never as a formula. -/
@[irreducible] public def extOneCokernelHenselizationBaseChangeEquiv :
    extOneCokernel k Bh (Bh ⊗[B] N) ≃+
      DerivedCategory.Ext
        (DerivedCategory.Q.obj
          (naiveCotangentBaseChangeCochainComplex.{uk, uB, max uB uN} k B Bh))
        (henselizationExtCoefficient.{uk, uB, uN} B N Bh) 1 :=
  (extCokernelIso k Bh (Bh ⊗[B] N)).symm.trans
    (naiveCotangentExtOneHenselizationSourceEquiv.{uk, uB, max uB uN} k B Bh J hhens huniv
      (henselizationExtCoefficient.{uk, uB, uN} B N Bh)).symm

end

noncomputable section

variable (k : Type uk) [Field k] (B : Type uB) [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B]
  (N : Type uN) [AddCommGroup N] [Module B N]
  (Bh : Type uB) [CommRing Bh] [Algebra B Bh] [Algebra k Bh] [IsScalarTower k B Bh]
  (J : Ideal B)
  (hhens : HenselianPair Bh (J.map (algebraMap B Bh)))
  (huniv : ∀ (C : Type uB) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
    ∀ f : B →+* C, J ≤ JC.comap f →
      ∃! g : Bh →+* C, g.comp (algebraMap B Bh) = f ∧
        J.map (algebraMap B Bh) ≤ JC.comap g)

include hhens huniv in
/-- **The base-change comparison the proof of Stacks 0DZC runs on.**  For a field `k`, a finite
type `k`-algebra `B`, an ideal `J ⊆ B` and the henselization `(Bʰ, Jʰ)` of the pair `(B, J)`,

`Ext¹_{Bʰ}(NL_{Bʰ/k}, Bʰ ⊗_B N) ≅ Ext¹_B(NL_{B/k}, N) ⊗_B Bʰ`.

Stacks 0D08 replaces `NL_{Bʰ/k}` by `NL_{B/k} ⊗_B Bʰ`, Stacks 0GPY moves the base change onto the
coefficients, and flat base change of the conormal cokernel moves it back out; `Bʰ` is flat over
`B` because it is the henselization of a pair.

Marked `irreducible`, for the same reason
`Stacks.Deformation.extOneCokernelHenselizationBaseChangeEquiv` is: unfolding the composite
during a definitional-equality check exhausts the recursion budget at a call site which
specializes the coefficient module.  Consumers use it as an isomorphism, never as a formula. -/
@[irreducible] public def extOneCokernelHenselizationFlatBaseChangeEquiv :
    extOneCokernel k Bh (Bh ⊗[B] N) ≃+ (extOneCokernel k B N) ⊗[B] Bh :=
  haveI : Module.Flat B Bh :=
    (flat_henselization_and_bijective_quotientMap B J Bh hhens huniv).1
  (extOneCokernelHenselizationBaseChangeEquiv.{uk, uB, uN} k B N Bh J hhens huniv).trans
    ((extOneSourceIso (DerivedCategory.Q.mapIso
        (naiveCotangentBaseChangeExtendScalarsIso.{uk, uB, max uB uN} k B Bh))).trans
      ((naiveCotangentExtOneBaseChangeEquiv.{uk, uB, uB, uN} k B Bh
          ((ModuleCat.uliftFunctor.{max uk uB} Bh).obj
            (ModuleCat.of Bh (Bh ⊗[B] N)))).symm.trans
        ((extOneTargetIso ((DerivedCategory.singleFunctor (ModuleCat.{max uk uB uN} B) 0).mapIso
            (henselizationExtCoefficientRestrictIso.{uk, uB, uN} B N Bh))).trans
          ((extCokernelIso k B (Bh ⊗[B] N)).trans
            (Deformation.Examples.extOneCokernelBaseChangeEquiv k B N Bh)))))

end

end Stacks.Deformation

end
