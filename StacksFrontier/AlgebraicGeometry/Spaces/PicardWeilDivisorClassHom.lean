module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassTensor

/-!
# Stacks 0EPW: the homomorphism `Pic(X) ⟶ Cl(X)`

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`.  This file
assembles the construction of Stacks 0EPW into the homomorphism of abelian groups

`Pic(X) ⟶ Cl(X)`

that assigns to an invertible `𝒪_X`-module its Weil divisor class, **on `X`'s own hypotheses
alone**.

The construction itself is
`AlgebraicGeometry.Space.PicardDivisorData.picardToWeilDivisorClassGroup`
(`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClass.lean`), which is carried by two
auxiliary objects that the source does not have: an
`AlgebraicGeometry.Space.GenericFractionEmbedding` and an
`AlgebraicGeometry.Space.PicardDivisorData`.  On such an `X` both are canonical: the embedding is
`AlgebraicGeometry.Space.genericFractionEmbedding` (Stacks 0ENK) and the data is
`AlgebraicGeometry.Space.canonicalPicardDivisorData`, whose two remaining fields are supplied as
follows:

* `AlgebraicGeometry.Space.canonicalRatioIsUnitOnGeneratingChart`
  (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorGenericStalkGeneratingChart.lean`) is
  the field `generating`, and
* `AlgebraicGeometry.Space.hasCanonicalTensorProductSection`
  (`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassTensor.lean`) feeds
  `AlgebraicGeometry.Space.canonicalTensorDivisorIdentity_of_exists_product`, which is the field
  `exists_ord_sub_eq_tensorModule`, Stacks 0EPV at the canonical choices.

So the two declarations below take only `X`'s hypotheses.

## Main definitions

* `AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom` is the homomorphism
  `Pic(X) ⟶ Cl(X)` of Stacks 0EPW.

## Main results

* `AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom_picardClass`: its value on the
  class of an invertible `𝒪_X`-module is that module's Weil divisor class, which characterizes
  it, every class in `Pic(X)` being the class of an invertible module.

## Implementation notes

The three instance hypotheses on the henselian local rings at the generic points of the prime
divisors — nontriviality, Noetherianness and Krull dimension at most one — are conclusions of
Stacks 0ENK on such an `X` and are discharged here by
`AlgebraicGeometry.Space.PrimeDivisor.nontrivial_genericHenselianLocalRing` and its two
companions, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassTensor.lean`.  They are `Prop`-valued
classes, hence definitionally unique, so the `haveI`-prefixed statement below needs no transport.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- The homomorphism of abelian groups

`Pic(X) ⟶ Cl(X)`

which assigns to an invertible `𝒪_X`-module its Weil divisor class, on a locally Noetherian
integral algebraic space `X` over a scheme `S`.

It is
`AlgebraicGeometry.Space.PicardDivisorData.picardToWeilDivisorClassGroup` at the canonical
choices: the embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK, the regular meromorphic sections
of Stacks 0EPQ and the ratio family of Stacks 0EPR.  Its value on the class of an invertible
module is that module's Weil divisor class
(`AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom_picardClass`), well defined on
isomorphism classes by Stacks 0EPT, and additivity is Stacks 0EPV, addition in `Pic(X)` being
tensor product. -/
@[stacks 0EPW "the homomorphism Pic(X) → Cl(X) assigning to an invertible module its Weil \
  divisor class, on a locally Noetherian integral algebraic space X over a scheme S — the \
  hypotheses of Lemma 72.7.5 and no others, decency coming from integrality by \
  `IsIntegralSpace.isDecentSpace`"]
def canonicalPicardToWeilDivisorClassHom :
    haveI hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
    picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩ →+
      (genericFractionEmbedding B S hS hX hdec hInt hN).weilDivisorClassGroup :=
  haveI hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
  haveI : ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  haveI : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  haveI : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  (canonicalPicardDivisorData B S hS hX hdec hInt hN
      (canonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
      (canonicalTensorDivisorIdentity_of_exists_product B S hS hX hdec hInt hN
        (hasCanonicalTensorProductSection B S hS hX hdec hInt hN))).picardToWeilDivisorClassGroup

include hInt hN in
/-- The homomorphism `Pic(X) ⟶ Cl(X)` sends the class of an invertible `𝒪_X`-module to its Weil
divisor class — the class of the Weil divisor of the regular meromorphic section of Stacks 0EPQ
read through the ratio family of Stacks 0EPR.  This characterizes the homomorphism, because every
class in `Pic(X)` is the class of an invertible module. -/
@[stacks 0EPW "the value of the homomorphism Pic(X) → Cl(X) on the class of an invertible \
  module, which characterizes it, on a locally Noetherian integral algebraic space X over a \
  scheme S — the hypotheses of Lemma 72.7.5 and no others, decency coming from integrality by \
  `IsIntegralSpace.isDecentSpace`"]
theorem canonicalPicardToWeilDivisorClassHom_picardClass (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    haveI hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
    canonicalPicardToWeilDivisorClassHom B S hS hX hInt hN
          (picardClass (B := B) ⟨X, hX⟩ L hL) =
        (canonicalPicardDivisorData B S hS hX hdec hInt hN
          (canonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
          (canonicalTensorDivisorIdentity_of_exists_product B S hS hX hdec hInt hN
            (hasCanonicalTensorProductSection B S hS hX hdec hInt hN))).divisorClass L hL := by
  have hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
  have := fun W : PrimeDivisor B S hS X =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  have := fun W : PrimeDivisor B S hS X =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  have := fun W : PrimeDivisor B S hS X =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  exact canonicalPicardToWeilDivisorClassGroup_picardClass B S hS hX hdec hInt hN
    (canonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
    (canonicalTensorDivisorIdentity_of_exists_product B S hS hX hdec hInt hN
      (hasCanonicalTensorProductSection B S hS hX hdec hInt hN)) L hL

end AlgebraicGeometry.Space

end
