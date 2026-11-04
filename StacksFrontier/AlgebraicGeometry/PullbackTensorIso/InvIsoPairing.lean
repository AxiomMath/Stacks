module

public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections

/-!
# The dualization isomorphisms, characterized by the duality pairings

`Stacks.TensorPowers.TensorInverse.invIso` identifies the inverse objects of two two-sided
tensor inverses of one object `L`. This file proves that it is compatible with the two
trivializations it is built from, and that this compatibility determines it. The same
characterization is stated for the two dualization isomorphisms built from it,

* `Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso`, `g^*(L^{⊗ -1}) ≅
  (g^*L)^{⊗ -1}`, and
* `Stacks.PullbackTensorIso.tensorPowerNegOneNegOneIso`, `L ≅ (L^{⊗ -1})^{⊗ -1}`.

## The pairing identity

For two two-sided tensor inverses `h`, `k` of `L`, the composite

`(h.inv ⊗ L) ⊗ k.inv --α--> h.inv ⊗ (L ⊗ k.inv) --h.inv ◁ k.mulIso--> h.inv ⊗ 𝟙 --ρ--> h.inv`

is an isomorphism, and `invIso h k` is the unique morphism `h.inv ⟶ k.inv` whose composition
with it is `h.mulIso' ▷ k.inv` followed by the left unitor. Read on local sections of a
trivializing open, with `t` a basis of `L`, `a` a section of `h.inv` and `r` the section of
`k.inv` dual to `t` for `k`, this says

`⟨t, r⟩_k • (invIso h k)(a) = ⟨a, t⟩_h • r`,

which determines the image of `a` from the two pairings alone — the computation of the
coordinate on a trivializing affine open.

The two pairings that enter are `h.mulIso'` and `k.mulIso`, i.e. the *right* trivialization of
the source's tensor inverse and the *left* trivialization of the target's. That asymmetry is not
cosmetic: `invIso` is built from exactly those two, and the identity obtained by pairing against
the other two is false in general — in modules over a ring, with `L`, `h.inv`, `k.inv` free of
rank one on `t`, `a`, `r` and `⟨a, t⟩_{h.mulIso'} = u`, `⟨t, r⟩_{k.mulIso} = v`,
`⟨r, t⟩_{k.mulIso'} = w`, one has `(invIso h k)(a) = u v^{-1} r`, so pairing the image against
`t` through `k.mulIso'` returns `u v^{-1} w`, which is `u` only when `k`'s two trivializations
agree under the symmetry. No braiding is available in the generality `invIso` is stated in, and
none is needed for the identity proved here.

## Main results

* `Stacks.TensorPowers.TensorInverse.invIso_pairing`: **`invIso h k` is compatible with the
  trivializations `h.mulIso'` and `k.mulIso`.**
* `Stacks.TensorPowers.TensorInverse.eq_invIso_of_pairing`: **and it is the only morphism that
  is** — the compatibility determines it.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso_pairing` and
  `Stacks.ProjBundleInverseBaseChange.eq_pullbackTensorPowerNegOneIso_of_pairing`: **the base
  change of the inverse, characterized by the pairings.** The pairing on the source is the
  pullback of the trivialization `L^{⊗ -1} ⊗ L ≅ 𝟙` along `g`, carried through [Stacks, Tag
  01CD]; the pairing on the target is the trivialization `g^*L ⊗ (g^*L)^{⊗ -1} ≅ 𝟙`.
* `Stacks.PullbackTensorIso.tensorPowerNegOneNegOneIso_pairing` and
  `Stacks.PullbackTensorIso.eq_tensorPowerNegOneNegOneIso_of_pairing`: **the involutivity of the
  inverse, characterized by the pairings.** Here both pairings are instances of
  `Stacks.ProjBundleInverseBaseChange.negOneMulIso'`, one for `L` and one for `L^{⊗ -1}`.

## Implementation notes

The prefix `(h.inv ⊗ L) ⊗ k.inv ⟶ h.inv` of the pairing identity is the isomorphism
`Stacks.TensorPowers.TensorInverse.pairingIso`, so that it is epic and uniqueness is
`CategoryTheory.cancel_epi`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

universe v u w

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)
open Stacks.SheafOfModules.TensorPower (tensorPower)
open Stacks.ProjBundleInverseBaseChange (negOneMulIso negOneMulIso' negOneTensorInverse
  pullbackFunctor pullbackTensorIso pullbackUnitMonoidalIso pullbackTensorInverse)

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {L : C}

namespace TensorInverse

/-- The isomorphism `(h.inv ⊗ L) ⊗ k.inv ≅ h.inv` obtained from the left trivialization of `k`:
reassociate, contract `L ⊗ k.inv` to the unit, and drop the unit. -/
def pairingIso (h k : TensorInverse L) : (h.inv ⊗ L) ⊗ k.inv ≅ h.inv :=
  α_ h.inv L k.inv ≪≫ whiskerLeftIso h.inv k.mulIso ≪≫ ρ_ h.inv

/-- **`Stacks.TensorPowers.TensorInverse.invIso` is compatible with the two trivializations it
is built from.** Pairing a section of `h.inv` against `L` through the right trivialization of
`h` and pairing its image under `invIso h k` against `L` through the left trivialization of `k`
give the same element of `k.inv`. -/
theorem invIso_pairing (h k : TensorInverse L) :
    (pairingIso h k).hom ≫ (invIso h k).hom =
      (h.mulIso'.hom ▷ k.inv) ≫ (λ_ k.inv).hom := by
  simp [pairingIso, invIso]

/-- **The compatibility of `invIso_pairing` determines `invIso`.** Every morphism
`φ : h.inv ⟶ k.inv` satisfying the pairing identity of `invIso_pairing` is `invIso h k`. -/
theorem eq_invIso_of_pairing (h k : TensorInverse L) (φ : h.inv ⟶ k.inv)
    (hφ : (pairingIso h k).hom ≫ φ = (h.mulIso'.hom ▷ k.inv) ≫ (λ_ k.inv).hom) :
    φ = (invIso h k).hom :=
  (cancel_epi (pairingIso h k).hom).mp (hφ.trans (invIso_pairing h k).symm)

end TensorInverse

end Stacks.TensorPowers

namespace Stacks.ProjBundleInverseBaseChange

open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.TensorPowers (TensorInverse)

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (L : Mods X)
  [Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) L]

/-- `Stacks.TensorPowers.TensorInverse.pairingIso` for the pullback along `g` of the tensor
inverse `L^{⊗ -1}` of `L` and the tensor inverse `(g^*L)^{⊗ -1}` of `g^*L`: the isomorphism
`(g^*(L^{⊗ -1}) ⊗ g^*L) ⊗ (g^*L)^{⊗ -1} ≅ g^*(L^{⊗ -1})` contracting `g^*L ⊗ (g^*L)^{⊗ -1}` by
its trivialization. -/
abbrev pullbackNegOnePairingIso :
    ((pullbackFunctor g).obj (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) ⊗
        (pullbackFunctor g).obj L) ⊗
      tensorPower X'.presheaf (isSheaf_structureRingPresheaf X')
        ((pullbackFunctor g).obj L) (-1) ≅
      (pullbackFunctor g).obj
        (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) :=
  TensorInverse.pairingIso
    (pullbackTensorInverse g L
      (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L))
    (negOneTensorInverse X'.presheaf (isSheaf_structureRingPresheaf X')
      ((pullbackFunctor g).obj L))

/-- **The base change of the inverse, characterized by the duality pairings**: the pullback of
the trivialization of `L` is the trivialization of `g^*L` read through
`pullbackTensorPowerNegOneIso`. -/
theorem pullbackTensorPowerNegOneIso_pairing :
    (pullbackNegOnePairingIso g L).hom ≫ (pullbackTensorPowerNegOneIso g L).hom =
      (((pullbackTensorIso g
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L).symm ≪≫
            (pullbackFunctor g).mapIso
              (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L) ≪≫
            pullbackUnitMonoidalIso g).hom ▷
          tensorPower X'.presheaf (isSheaf_structureRingPresheaf X')
            ((pullbackFunctor g).obj L) (-1)) ≫
        (λ_ (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X')
          ((pullbackFunctor g).obj L) (-1))).hom :=
  TensorInverse.invIso_pairing _ _

/-- **The pairing identity determines the base change of the inverse.** -/
theorem eq_pullbackTensorPowerNegOneIso_of_pairing
    (φ : (pullbackFunctor g).obj
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) ⟶
        tensorPower X'.presheaf (isSheaf_structureRingPresheaf X')
          ((pullbackFunctor g).obj L) (-1))
    (hφ : (pullbackNegOnePairingIso g L).hom ≫ φ =
      (((pullbackTensorIso g
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L).symm ≪≫
            (pullbackFunctor g).mapIso
              (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L) ≪≫
            pullbackUnitMonoidalIso g).hom ▷
          tensorPower X'.presheaf (isSheaf_structureRingPresheaf X')
            ((pullbackFunctor g).obj L) (-1)) ≫
        (λ_ (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X')
          ((pullbackFunctor g).obj L) (-1))).hom) :
    φ = (pullbackTensorPowerNegOneIso g L).hom :=
  TensorInverse.eq_invIso_of_pairing
    (pullbackTensorInverse g L
      (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L))
    (negOneTensorInverse X'.presheaf (isSheaf_structureRingPresheaf X')
      ((pullbackFunctor g).obj L)) φ hφ

end Stacks.ProjBundleInverseBaseChange

namespace Stacks.PullbackTensorIso

open Stacks.TensorPowers (TensorInverse)
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) [Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- `Stacks.TensorPowers.TensorInverse.pairingIso` over the object `L^{⊗ -1}`, for its tensor
inverses `L` and `(L^{⊗ -1})^{⊗ -1}`: the isomorphism
`(L ⊗ L^{⊗ -1}) ⊗ (L^{⊗ -1})^{⊗ -1} ≅ L` contracting `L^{⊗ -1} ⊗ (L^{⊗ -1})^{⊗ -1}` by its
trivialization. -/
abbrev negOneNegOnePairingIso :
    (L ⊗ tensorPower 𝒪 h𝒪 L (-1)) ⊗
        tensorPower 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) (-1) ≅ L :=
  haveI : Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower 𝒪 h𝒪 L (-1)
  TensorInverse.pairingIso (negOneTensorInverseSelf 𝒪 h𝒪 L)
    (negOneTensorInverse 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)))

/-- `L^{⊗ -1}` is invertible, so that it has its own tensor inverse. -/
private instance isInvertible_tensorPowerNegOne :
    Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) :=
  Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower 𝒪 h𝒪 L (-1)

/-- **The involutivity of the inverse, characterized by the duality pairings**: the
trivialization of `L` against `L^{⊗ -1}` is the trivialization of `L^{⊗ -1}` against its own
inverse, read through `tensorPowerNegOneNegOneIso`. -/
theorem tensorPowerNegOneNegOneIso_pairing :
    (negOneNegOnePairingIso 𝒪 h𝒪 L).hom ≫ (tensorPowerNegOneNegOneIso 𝒪 h𝒪 L).hom =
      ((negOneMulIso' 𝒪 h𝒪 L).hom ▷
          tensorPower 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) (-1)) ≫
        (λ_ (tensorPower 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) (-1))).hom :=
  TensorInverse.invIso_pairing _ _

/-- **The pairing identity determines the involutivity of the inverse.** -/
theorem eq_tensorPowerNegOneNegOneIso_of_pairing
    (φ : L ⟶ tensorPower 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) (-1))
    (hφ : (negOneNegOnePairingIso 𝒪 h𝒪 L).hom ≫ φ =
      ((negOneMulIso' 𝒪 h𝒪 L).hom ▷
          tensorPower 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) (-1)) ≫
        (λ_ (tensorPower 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) (-1))).hom) :
    φ = (tensorPowerNegOneNegOneIso 𝒪 h𝒪 L).hom :=
  TensorInverse.eq_invIso_of_pairing (negOneTensorInverseSelf 𝒪 h𝒪 L)
    (negOneTensorInverse 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1))) φ hφ

end Stacks.PullbackTensorIso

end
