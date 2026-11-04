module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible

/-!
# The zero-scheme presentation of the divisor at infinity over a test scheme

Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre `W_∞` at infinity, and
let `t : T ⟶ X` be a test scheme. The Gysin recipe of Stacks 0F9J evaluates `i_∞^*β` for a cycle
`β` on the base change `W_T`, reading the result on `T ×_X W_∞`. This file records the part of the
geometry that recipe runs on: the base change `W_T`, an invertible module on it with a section
whose zero scheme is the divisor at infinity of `W_T`, and the identification of that zero scheme
with `T ×_X W_∞`.

## Main definitions

* `Stacks.Chow.InfinityDivisorZeroScheme` — that presentation.
* `Stacks.Chow.InfinityDivisorZeroScheme.gysinCap` — the class `i_∞^*β` read through it.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The zero-scheme presentation of the divisor at infinity over one test scheme `t : T ⟶ X`.

In the situation of Stacks 0F9J, `amb` is the base change `W_T` of the modified projective line.
The divisor at infinity of `W_T` is presented as the zero scheme of the section `divisorSection`
of the invertible module `line`, and `iso` identifies it with the base change `T ×_X W_∞` on
which the bivariant class `C` of Stacks 0F9J caps. -/
structure InfinityDivisorZeroScheme (C : ChowSituation.{u}) {X WInf T : Scheme.{u}}
    (sWInf : WInf ⟶ C.S) (pInf : WInf ⟶ X) (t : T ⟶ X) where
  /-- The base change `W_T` of the modified projective line. -/
  amb : Scheme.{u}
  /-- Its structure morphism over the base of the Chow situation. -/
  ambStructure : amb ⟶ C.S
  [finiteType_ambStructure : LocallyOfFiniteType ambStructure]
  /-- An invertible module on `W_T` cutting out the divisor at infinity. -/
  line : amb.Modules
  [invertible_line : AlgebraicGeometry.SheafOfModules.IsInvertible amb.sheaf.obj
    amb.ringCatSheaf.property line]
  /-- The section whose zero scheme is the divisor at infinity of `W_T`. -/
  divisorSection : Γ(line, ⊤)
  /-- The divisor at infinity of `W_T` is the base change of `W_∞`. -/
  iso : (Stacks.Divisors.zeroScheme amb line divisorSection).subscheme ≅ pullback pInf t
  /-- That identification lies over the base of the Chow situation. -/
  iso_comp : iso.hom ≫ (pullback.fst pInf t ≫ sWInf) =
    (Stacks.Divisors.zeroScheme amb line divisorSection).subschemeι ≫ ambStructure

namespace InfinityDivisorZeroScheme

variable {C : ChowSituation.{u}} {X WInf T : Scheme.{u}} {sWInf : WInf ⟶ C.S} {pInf : WInf ⟶ X}
  {t : T ⟶ X} (P : InfinityDivisorZeroScheme C sWInf pInf t)

attribute [instance] finiteType_ambStructure

/-- The module `P.line` on `W_T` is invertible. -/
instance isInvertible_line : AlgebraicGeometry.SheafOfModules.IsInvertible P.amb.sheaf.obj
    P.amb.ringCatSheaf.property P.line := P.invertible_line

variable [LocallyOfFiniteType sWInf] [LocallyOfFiniteType t]

/-- The class `i_∞^*β` of the Gysin recipe of Stacks 0F9J, transported along the identification
of the divisor at infinity of `W_T` with the base change of `W_∞`. -/
def gysinCap (hpp : ProperPushforwardDescends C) (k : ℤ)
    (β : CycleGroup C P.ambStructure (k + 1)) :
    chowGroup C (pullback.fst pInf t ≫ sWInf) k :=
  properChowPushforward C
    ((Stacks.Divisors.zeroScheme P.amb P.line P.divisorSection).subschemeι ≫ P.ambStructure)
    (pullback.fst pInf t ≫ sWInf) P.iso.hom P.iso_comp k (hpp _ _ _ _ _)
    (gysinHomomorphismOfInvertible C P.ambStructure k P.line P.divisorSection β)

end InfinityDivisorZeroScheme

end Stacks.Chow

end
