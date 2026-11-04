module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafReductionDerivedIsoRegular
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafIdealWitness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatIdealTorsionFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealGeneratedByNonzerodivisor
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit

import StacksCore.Tactic.StacksAttribute

/-!
# What inhabits Tag 0GT9's binder list

Everything in `EtaSheaf*.lean` from Tag 0GT3 to Tag 0GT9 is stated for a ringed space `X`, an
invertible ideal subsheaf `ι : I ⟶ O_X`, and a cochain complex `F` of `I`-torsion-free
`O_X`-modules.  `EtaSheafIdealWitness.lean` assembles a non-degenerate `(X, I, ι)`: the ideal
sheaf of the zero divisor `D₀ ⊆ ℙ¹_S`, which is invertible for every `S` and is *not* the unit
ideal.  It records the remaining binder — a nonzero termwise `I`-torsion-free complex at that
instance — as unreached, the obstruction being that
`Stacks.IdealTorsion.isIdealTorsionFree_of_isFlat` and
`Stacks.IdealTorsion.isLocallyGeneratedByRegular_of_isInvertible` are stated over
`TensorStalkRingedSpace.structureSheafRing X` while the witness ideal lives over
`structureSheaf X.toRingedSpace.sheaf`.

**That obstruction does not exist.**  `TensorStalkRingedSpace.ringStalk X x` is by definition
`X.presheaf.stalk x`, so the local-ring hypothesis of Tag 0GT3 (2) ⟹ (1) is the one a scheme
already supplies by synthesis, and the two structure-sheaf spellings are interchangeable at
exactly this use site — `Stacks.IdealTorsion.exists_termwiseTorsionFree_quasiIso_of_isInvertible`
already mixes them.  So the last binder is three lines, and this file supplies it.

## Main results

* `isIdealTorsionFree_unit`: **the structure sheaf is `I`-torsion-free for an invertible ideal
  sheaf on a ringed space whose stalks are local rings.**  Flat modules are torsion-free
  (Tag 0GT5) and `O_X` is flat over itself.
* `structureSheafConstComplex` and `isIdealTorsionFree_structureSheafConstComplex`: the complex
  with every term `O_X` and zero differential, and its termwise torsion-freeness.  Its
  cohomology is `O_X` in every degree, so it is not a zero object and the instantiation is not
  degenerate.
* `Witness.isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex` and
  `Witness.zeroDivisorComparisonQ`: **Tag 0GT9's whole binder list, instantiated.**  The second
  is the canonical arrow of Tag 0GT9 in `D(O_X)` at `X = ℙ¹_S` with `I` the ideal sheaf of the
  zero divisor — built from declarations assuming only `S : Scheme`, with no ideal, no complex
  and no torsion-freeness hypothesis left open.

## Implementation notes

Nothing here carries `@[stacks 0GT9]`.  These are not clauses of the tag: they say that the
situation the tag is stated in is inhabited, which the tag does not assert.  They are the
machine-checked answer to "what inhabits this datum?", and they belong with the development
because a statement about an uninhabited situation is worth nothing however well it builds.

The constant complex is used rather than a single complex because its torsion-freeness is
uniform in the degree: `(F.X k)` is the same object for every `k`, so the `hF` binder is one
application of `isIdealTorsionFree_unit` and needs no case split on `k = 0`.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 0GT3](https://stacks.math.columbia.edu/tag/0GT3)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe u

namespace Stacks.IdealTorsion

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### The structure sheaf is torsion-free for an invertible ideal -/

/-- **The structure sheaf is `I`-torsion-free for an invertible ideal subsheaf**, on a ringed
space all of whose structure-sheaf stalks are local rings.  Invertibility gives local generation
by a nonzerodivisor there (Tag 0GT3, (2) ⟹ (1)), a flat module is `I`-torsion-free for such an
ideal (Tag 0GT5), and `O_X` is flat over itself. -/
public theorem isIdealTorsionFree_unit
    [∀ z : X.carrier, IsLocalRing (ringStalk X z)]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [monoIncl : Mono ι]
    (hI : Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property I) :
    IsIdealTorsionFree X ι 𝒪 :=
  @isIdealTorsionFree_of_isFlat X I ι monoIncl
    (@isLocallyGeneratedByRegular_of_isInvertible X _ I ι monoIncl hI) _
    (Stacks.RingedSpace.isFlat_unit_of_ringedSpace X)

/-! ### A non-degenerate termwise torsion-free complex -/

/-- The complex with every term the structure sheaf `O_X` and zero differential.  Its cohomology
is `O_X` in every degree, so it is not a zero object. -/
public noncomputable def structureSheafConstComplex :
    CochainComplex (SheafOfModules.{u} Oₓ) ℤ where
  X _ := 𝒪
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- Every term of `structureSheafConstComplex X` is the structure sheaf. -/
@[simp] public theorem structureSheafConstComplex_X (n : ℤ) :
    (structureSheafConstComplex X).X n = 𝒪 := rfl

/-- Every differential of `structureSheafConstComplex X` is zero. -/
@[simp] public theorem structureSheafConstComplex_d (m n : ℤ) :
    (structureSheafConstComplex X).d m n = 0 := rfl

/-- **The constant complex on the structure sheaf is termwise `I`-torsion-free** for an
invertible ideal subsheaf, on a ringed space whose structure-sheaf stalks are local rings. -/
public theorem isIdealTorsionFree_structureSheafConstComplex
    [∀ z : X.carrier, IsLocalRing (ringStalk X z)]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [monoIncl : Mono ι]
    (hI : Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property I)
    (k : ℤ) :
    IsIdealTorsionFree X ι ((structureSheafConstComplex X).X k) :=
  isIdealTorsionFree_unit X I ι hI

end Stacks.IdealTorsion

namespace Stacks.IdealTorsion.Witness

open Stacks.IdealTorsion Stacks.IdealTorsion.Reduction

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : Scheme.{u})

/-- **The last binder of Tag 0GT9's situation, at the non-degenerate witness.**  On `ℙ¹_S` the
ideal sheaf of the zero divisor `D₀` is invertible and not the unit ideal
(`isInvertible_zeroDivisorIdeal`), the structure-sheaf stalks are local rings (Mathlib's
instance `AlgebraicGeometry.LocallyRingedSpace.isLocalRing`), and so the constant complex on
`O_X` is termwise torsion-free for it.  Only `S : Scheme` is assumed. -/
public theorem isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex (k : ℤ) :
    IsIdealTorsionFree (line S).toRingedSpace (zeroDivisorIdealι S)
      ((structureSheafConstComplex (line S).toRingedSpace).X k) :=
  have := Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor S
  @isIdealTorsionFree_structureSheafConstComplex (line S).toRingedSpace _ _ _ (zeroDivisorIdeal S)
    (zeroDivisorIdealι S) (inferInstance : Mono (zeroDivisorIdealι S))
    (isInvertible_zeroDivisorIdeal S) k

/-- **Tag 0GT9's canonical arrow in `D(O_X)`, at the non-degenerate witness.**  Every binder of
`Reduction.reductionComparisonQ` is instantiated here from declarations assuming only
`S : Scheme`: the space is `ℙ¹_S`, the invertible ideal subsheaf is the ideal sheaf of the zero
divisor `D₀`, and the termwise `I`-torsion-free complex is the constant complex on `O_X`.

So Tag 0GT9's situation is inhabited, and inhabited by a datum for which `I` is a *proper*
ideal — not the unit ideal, modulo which `O_X/I` is zero and both sides of the tag vanish.  This
is the positive test for vacuity, machine-checked rather than argued. -/
public noncomputable def zeroDivisorComparisonQ :
    haveI := Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor S
    DerivedCategory.Q.obj
        (@etaModIdealComplex (line S).toRingedSpace (zeroDivisorIdeal S) (zeroDivisorIdealι S)
          (inferInstance : Mono (zeroDivisorIdealι S)) (isInvertible_zeroDivisorIdeal S)
          (structureSheafConstComplex (line S).toRingedSpace)
          (isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex S)) ⟶
      DerivedCategory.Q.obj
        (@bocksteinChainComplex (line S).toRingedSpace (zeroDivisorIdeal S)
          (zeroDivisorIdealι S) (inferInstance : Mono (zeroDivisorIdealι S))
          (isInvertible_zeroDivisorIdeal S)
          (structureSheafConstComplex (line S).toRingedSpace)
          (isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex S)) :=
  haveI := Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor S
  @reductionComparisonQ (line S).toRingedSpace (zeroDivisorIdeal S) (zeroDivisorIdealι S)
    (inferInstance : Mono (zeroDivisorIdealι S)) (isInvertible_zeroDivisorIdeal S)
    (structureSheafConstComplex (line S).toRingedSpace)
    (isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex S)

/-- **Situation 0GT4's own hypothesis at the non-degenerate witness**: on `ℙ¹_S` the ideal sheaf
of the zero divisor is locally generated by a nonzerodivisor.  Invertibility gives this on a
space whose structure-sheaf stalks are local rings (Tag 0GT3, (2) ⟹ (1)), and a scheme supplies
that by synthesis. -/
public theorem isLocallyGeneratedByRegular_zeroDivisorIdealι :
    IsLocallyGeneratedByRegular (line S).toRingedSpace (zeroDivisorIdealι S) :=
  have := Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor S
  have : Mono (zeroDivisorIdealι S) := inferInstance
  isLocallyGeneratedByRegular_of_isInvertible (line S).toRingedSpace (zeroDivisorIdealι S)
    (isInvertible_zeroDivisorIdeal S)

/-- **Tag 0GT9's canonical arrow is invertible at the non-degenerate witness.**  Every binder of
`Reduction.isIso_reductionComparisonQ_of_isLocallyGeneratedByRegular` — including Situation
0GT4's hypothesis that the ideal is locally generated by a nonzerodivisor — is instantiated here
from declarations assuming only `S : Scheme`.

This is the positive test for vacuity applied to the tag's *conclusion* rather than to its
situation: the isomorphism of Tag 0GT9 exists at a concrete instance in which `I` is a proper
ideal, so the conclusion is not reached because `O_X/I` is zero. -/
public theorem isIso_zeroDivisorComparisonQ : IsIso (zeroDivisorComparisonQ S) :=
  have := Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor S
  @isIso_reductionComparisonQ_of_isLocallyGeneratedByRegular (line S).toRingedSpace
    (zeroDivisorIdeal S) (zeroDivisorIdealι S) (inferInstance : Mono (zeroDivisorIdealι S))
    (isInvertible_zeroDivisorIdeal S)
    (isLocallyGeneratedByRegular_zeroDivisorIdealι S)
    (structureSheafConstComplex (line S).toRingedSpace)
    (isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex S)

/-- **Tag 0GT9's canonical isomorphism at the non-degenerate witness**, as data: the isomorphism

`η_I O_X^• ⊗ O_X/I ≅ H^•(O_X^•/I)` in `D(ℙ¹_S)`

for `I` the ideal sheaf of the zero divisor, assuming only `S : Scheme`. -/
public noncomputable def zeroDivisorComparisonQIso :
    haveI := Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor S
    DerivedCategory.Q.obj
        (@etaModIdealComplex (line S).toRingedSpace (zeroDivisorIdeal S) (zeroDivisorIdealι S)
          (inferInstance : Mono (zeroDivisorIdealι S)) (isInvertible_zeroDivisorIdeal S)
          (structureSheafConstComplex (line S).toRingedSpace)
          (isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex S)) ≅
      DerivedCategory.Q.obj
        (@bocksteinChainComplex (line S).toRingedSpace (zeroDivisorIdeal S)
          (zeroDivisorIdealι S) (inferInstance : Mono (zeroDivisorIdealι S))
          (isInvertible_zeroDivisorIdeal S)
          (structureSheafConstComplex (line S).toRingedSpace)
          (isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex S)) :=
  haveI := Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor S
  @reductionComparisonQIsoOfRegular (line S).toRingedSpace (zeroDivisorIdeal S)
    (zeroDivisorIdealι S) (inferInstance : Mono (zeroDivisorIdealι S))
    (isInvertible_zeroDivisorIdeal S)
    (isLocallyGeneratedByRegular_zeroDivisorIdealι S)
    (structureSheafConstComplex (line S).toRingedSpace)
    (isIdealTorsionFree_zeroDivisorIdeal_structureSheafConstComplex S)

/-- The witness isomorphism's forward map is the witness arrow, by `rfl`. -/
@[simp] public theorem zeroDivisorComparisonQIso_hom :
    (zeroDivisorComparisonQIso S).hom = zeroDivisorComparisonQ S := rfl

end Stacks.IdealTorsion.Witness

end
