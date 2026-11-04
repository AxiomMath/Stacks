module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorNormalSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIdealSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic

/-!
# Stacks Tag 0C6K: the whole remark

[Stacks, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K) makes two statements.

1. For an invertible module `L` on a scheme `X` and a regular section `s` of `L`, the zero
   scheme `D = Z(s)` is an effective Cartier divisor, and the sequences
   `0 ⟶ 𝒪_X ⟶ L ⟶ i_*(L|_D) ⟶ 0` and `0 ⟶ L^{⊗ -1} ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` are short exact.
2. For an effective Cartier divisor `D ⊆ X`, the sequences
   `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩_{D/X} ⟶ 0` and `0 ⟶ 𝒪_X(-D) ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` are short
   exact.

This file states both on one theorem.

## Main results

* `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_and_shortExact_sequences`:
  **Tag 0C6K**, the whole remark.

## Implementation notes

Each of the four sequences is spelled exactly as the declaration proving it states it:
`AlgebraicGeometry.shortExact_zeroScheme_of_isRegularSection`,
`AlgebraicGeometry.shortExact_zeroScheme_ideal_of_isRegularSection`,
`Stacks.Divisors.shortExact_divisor_normal` and
`Stacks.IdealSheafSequence.divisorIdeal_shortExact`. The Cartier conclusion for `Z(s)` is the
backward direction of `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection`
([Stacks, Tag 02OR (4)]).

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal

namespace AlgebraicGeometry

/-- **Stacks Tag 0C6K.** Let `X` be a scheme.

1. For an invertible `𝒪_X`-module `L` and a regular section `s` of `L` ([Stacks, Tag 01WY]),
   with `i` the inclusion of the zero scheme `Z(s)`: `Z(s)` is an effective Cartier divisor on
   `X`, the sequence `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0` is short exact (first map multiplication by
   `s`, second the unit of `i^* ⊣ i_*`), and the sequence `0 ⟶ L^{⊗ -1} ⟶ 𝒪_X ⟶ i_* 𝒪_{Z(s)} ⟶ 0`
   is short exact (first map multiplication by `s` read through `L^{⊗ -1} ⊗ L ≅ 𝒪_X`, second
   restriction to the zero scheme).
2. For an effective Cartier divisor `D ⊆ X` with inclusion `i`: the normal sheaf `𝒩_{D/X}` is
   `i^* 𝒪_X(D)` and `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩_{D/X} ⟶ 0` is short exact (first map
   multiplication by the canonical section `1_D`), and `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` is short
   exact. -/
@[stacks 0C6K]
theorem isEffectiveCartierDivisor_zeroScheme_and_shortExact_sequences (X : Scheme.{u}) :
    (∀ (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
        (s : L.sections), IsRegularSection X.sheaf.obj X.ringCatSheaf.property s →
      Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X L (s.eval (op ⊤))) ∧
      (let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
        let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
        let f : O ⟶ L := L.unitHomEquiv.symm s
        let g : L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) :=
          (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
        ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact) ∧
      (let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
        let Linv : X.Modules := inverseTensorPower X L
        let u : Linv ⟶ SheafOfModules.unit X.ringCatSheaf :=
          ((ρ_ Linv).inv ≫ Linv ◁ L.unitHomEquiv.symm s) ≫ (inverseTensorPowerIsoUnit X L).hom
        let q : SheafOfModules.unit X.ringCatSheaf ⟶
            (Scheme.Modules.pushforward i).obj
              (SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf) :=
          SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
        ∃ h : u ≫ q = 0, (ShortComplex.mk u q h).ShortExact)) ∧
    (∀ (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D],
      (let i := D.subschemeι
        let L : X.Modules := Stacks.Divisors.invertibleSheaf D
        let N : D.subscheme.Modules := Stacks.Divisors.normalSheaf i
        ∃ e : (Scheme.Modules.pullback i).obj L ≅ N,
          let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
          let f : O ⟶ L := L.unitHomEquiv.symm (Stacks.Divisors.canonicalSections D)
          let g : L ⟶ (Scheme.Modules.pushforward i).obj N :=
            (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L ≫
              (Scheme.Modules.pushforward i).map e.hom
          ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact) ∧
      ∃ hz : Stacks.IdealSheafSequence.divisorIdealMap D ≫
          Stacks.IdealSheafSequence.divisorQuotientMap D = 0,
        (ShortComplex.mk (Stacks.IdealSheafSequence.divisorIdealMap D)
          (Stacks.IdealSheafSequence.divisorQuotientMap D) hz).ShortExact) :=
  ⟨fun L _ s hs =>
    ⟨(isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).mpr hs,
      shortExact_zeroScheme_of_isRegularSection X L s hs,
      shortExact_zeroScheme_ideal_of_isRegularSection X L s hs⟩,
    fun D _ => ⟨Stacks.Divisors.shortExact_divisor_normal D,
      Stacks.IdealSheafSequence.divisorIdeal_shortExact D⟩⟩

end AlgebraicGeometry

end
