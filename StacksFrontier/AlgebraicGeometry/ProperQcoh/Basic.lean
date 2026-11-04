module

public import StacksFrontier.AlgebraicGeometry.ProperHigherDirectImageQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.QcohInduction.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0EX4, the quasi-coherence assertion

[Stacks, Tag 0EX4] carries two assertions. The **quasi-coherence** one says that for a proper
morphism of schemes `f : X ⟶ Y` and a quasi-coherent `F : X.Modules`, the higher direct image
`R ⁱ f_* F` is quasi-coherent in every degree `i : ℕ`; the **finite type** one adds that when the
fibres of `f` have dimension at most `d` and `F` is of finite type, `R ᵈ f_* F` is of finite type.
This file proves the first, and says nothing about the second.

Both are stated at Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, while the
higher-direct-image theory used here is stated at the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus`.

## Main results

* `Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh.isQuasicoherent_rightDerived`: for a quasi-compact
  quasi-separated morphism and a quasi-coherent module, `R ⁱ f_* F` is quasi-coherent in every
  degree `i : ℕ`.
* `Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh.isQuasicoherent_rightDerived_of_isProper`:
  **[Stacks, Tag 0EX4], the `quasi-coherence` assertion**, in the hypotheses and the indexing the
  source states it in.

## Implementation notes

The whole content is in two results of the library, and the file is their composition:

* the `ℤ`-indexed quasi-coherence for a quasi-compact quasi-separated morphism, in every degree,
  is `Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent`
  ([Stacks, Tag 01XJ] part (1));
* the transfer between the two indexings is
  `Stacks.AlgebraicGeometry.Tag0EX4.isQuasicoherent_rightDerived_iff`, which runs on the natural
  isomorphism `Stacks.DerivedIndexing.rightDerivedIso` and has no hypothesis on `f` or on the
  degree.

A proper morphism is universally closed and separated, hence quasi-compact
(`AlgebraicGeometry.UniversallyClosed`) and quasi-separated (`AlgebraicGeometry.IsSeparated`), both
by instance; so no hypothesis of the source's statement is used beyond those two, and the
quasi-compact quasi-separated form is recorded as the general statement.

The `ℤ`-indexed `rightDerivedPlus` is taken with respect to the standard derived category, the
instance the existing theory is stated under. `Scheme.Modules` is a `def`, so
`HasDerivedCategory.standard` is not found by instance search and is installed locally, exactly as
in the two files above.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (i : ℕ)

/-- **Quasi-coherence of the `ℕ`-indexed higher direct images along a quasi-compact
quasi-separated morphism.** For `f : X ⟶ Y` quasi-compact and quasi-separated and `F`
quasi-coherent, `R ⁱ f_* F` is quasi-coherent for every `i : ℕ`.

This is [Stacks, Tag 01XJ] part (1) — proved `ℤ`-indexed as
`Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent` — carried across
the indexing by `Stacks.AlgebraicGeometry.Tag0EX4.isQuasicoherent_rightDerived_iff`. -/
instance isQuasicoherent_rightDerived [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent :=
  (Stacks.AlgebraicGeometry.ProperHigherDirectImageQcoh.isQuasicoherent_rightDerived_iff f F i).mpr
    (Tag01XJQcohInduction.higherDirectImage_isQuasicoherent f F (i : ℤ))

/-- **Stacks Project, Tag 0EX4 (quasi-coherence).** Let `f : X ⟶ Y` be a proper morphism of
schemes and let `F` be a quasi-coherent `𝒪_X`-module. Then the higher direct image `R ⁱ f_* F` is
a quasi-coherent `𝒪_Y`-module, in every degree `i : ℕ`.

A proper morphism is quasi-compact and quasi-separated, so this is `isQuasicoherent_rightDerived`;
properness is not otherwise used, and neither is any bound on the degree or on the dimension of
the fibres. -/
@[stacks 0EX4 "quasi-coherence"]
instance isQuasicoherent_rightDerived_of_isProper [IsProper f] [F.IsQuasicoherent] :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent :=
  isQuasicoherent_rightDerived f F i

/-! ### Faithfulness

The source's assertion, in the source's binder order, discharged by the tagged declaration and
nothing else. -/

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (F : X.Modules) [F.IsQuasicoherent]
    (i : ℕ) : (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent :=
  isQuasicoherent_rightDerived_of_isProper f F i

end Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh

end
