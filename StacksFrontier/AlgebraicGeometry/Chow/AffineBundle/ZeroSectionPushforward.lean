module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceFiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic

/-!
# Proper pushforward along the zero section of a line bundle

Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of finite type over `S`, let
`ℒ` be an invertible `𝒪_X`-module and let

  `p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X`

be the associated line bundle, with zero section `o : X ⟶ L`. The zero section is a closed
immersion, hence proper, and is a morphism over `S`; this file constructs the proper pushforward

  `o_* : \CH_k(X) ⟶ \CH_k(L)`

of clause (2) of Stacks 0F96.

## Main results

* `Stacks.Chow.zeroSection_comp_totalSpaceToBase_comp`: the zero section is a morphism over the
  base scheme of chapter 42.
* `Stacks.Chow.zeroSectionChowPushforward`: the proper pushforward `o_* : \CH_k(X) ⟶ \CH_k(L)`
  along the zero section.
* `Stacks.Chow.zeroSectionChowPushforward_mk`: on the class of a cycle it is the class of the
  proper pushforward of that cycle.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

omit [LocallyOfFiniteType sX] in
/-- The zero section of a line bundle is a morphism over the base scheme of chapter 42: composing
it with the structure morphism of the total space over `S` returns the structure morphism of `X`
over `S`. -/
theorem zeroSection_comp_totalSpaceToBase_comp :
    D.zeroSection ≫ D.totalSpaceToBase ≫ sX = sX := by
  rw [← Category.assoc, D.zeroSection_comp_totalSpaceToBase, Category.id_comp]

/-- The proper pushforward on Chow groups along the zero section `o : X ⟶ L` of a line bundle,

  `o_* : \CH_k(X) ⟶ \CH_k(L)`. -/
@[stacks 0F96 "part (2)"]
def zeroSectionChowPushforward (k : ℤ) :
    chowGroup C sX k →+ chowGroup C (D.totalSpaceToBase ≫ sX) k :=
  properChowPushforward C sX (D.totalSpaceToBase ≫ sX) D.zeroSection
    (zeroSection_comp_totalSpaceToBase_comp C D sX) k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX
      (D.totalSpaceToBase ≫ sX) D.zeroSection (zeroSection_comp_totalSpaceToBase_comp C D sX) k)

/-- On the class of a cycle, pushforward along the zero section is the class of the proper
pushforward of that cycle. -/
theorem zeroSectionChowPushforward_mk (k : ℤ) (α : CycleGroup C sX k) :
    zeroSectionChowPushforward C D sX k
        (QuotientAddGroup.mk' (rationalEquivalences C sX k) α) =
      QuotientAddGroup.mk' (rationalEquivalences C (D.totalSpaceToBase ≫ sX) k)
        (properPushforward C sX (D.totalSpaceToBase ≫ sX) D.zeroSection
          (zeroSection_comp_totalSpaceToBase_comp C D sX) k α) :=
  rfl

end Stacks.Chow

end
