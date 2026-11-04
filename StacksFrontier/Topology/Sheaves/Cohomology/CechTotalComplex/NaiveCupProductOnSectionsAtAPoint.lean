module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductOnSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CanonicalOnePointComparison

/-!
# The naive cup product at the coefficient point

Let `(S, 𝒪_S)` be a ringed space and let `π : S ⟶ ({*}, Γ(S, 𝒪_S))` be the morphism to the
coefficient point of Stacks 01BH, the one for which Cohomology, Section 0FKU reads the global cup
product as a relative cup product.  Taking `V = ⊤` in
`Stacks.RingedSpace.pushforwardTensorMap_eq_sheafTensorPairing` identifies, on global sections,
the degreewise naive cup product of `π` of Stacks Tag 0FP3 with the sheaf-tensor coefficient
pairing that the Čech cup product of Stacks Tag 0FKV consumes.

This is the instantiation the Γ-square of Tag 0FKV needs, and the point of isolating it is that
no bridge is required: `π⁻¹⊤ = ⊤` holds on the nose, so the general identification applies with
no transport, and the coefficient ring `Stacks.Cech.ModuleCupProduct.CoeffRing 𝒪_S ⊤` is
`Γ(S, 𝒪_S)` on the nose as well.

## Main results

* `Stacks.RingedSpace.pushforwardTensorMap_toCoeffPoint_top` — **the identification at the
  coefficient point.**

## Implementation notes

Nothing here is a clause of the statement of Tag 0FKV; it is a step of its proof — the
identification of the two cup products that the diagram of 0FKV compares — so it carries no
tag, as the sibling bridges of this directory also do not.

The one-point space enters only through `π`; in particular the non-definitional identification
`Γ({*}, 𝒪) = Γ(S, 𝒪_S)` of
`Stacks.Cohomology.DerivedGlobalCupProduct.baseRing_coeffPoint` is *not* used, and must not be:
the two pure tensors below are taken over the two different rings `Γ({*}, 𝒪_{\{*\}})` and
`Γ(S, 𝒪_S)`, and the statement is an equation between the two values at one pair of global
sections rather than between two maps out of one tensor product.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction _root_.Stacks.PresheafOfModules CategoryTheory.Sheaf
open Stacks.Cech.ModuleCupProduct Stacks.Cech.SheafTensorPairing
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsOnAPoint (onePointRingedSpace)
open Stacks.Cohomology.GlobalKunneth (baseRing)

-- The commutative ring structure on a ring of sections, at the `RingedSpace` spelling of the
-- space: instance search does not find `Stacks.Cech.ModuleCupProduct.sectionCommRing` there, as
-- the module docstring of
-- `StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductOnSections` records.
attribute [local instance] coeffCommRing

/-- **The degreewise naive cup product at the coefficient point is the Čech coefficient
pairing.**  For global sections `x` of `ℱ` and `y` of `𝒢`, the degreewise naive cup product of
`π : S ⟶ ({*}, Γ(S, 𝒪_S))` carries the sheafification-unit image of `x ⊗ y`, taken over
`Γ({*}, 𝒪_{\{*\}})`, to the value at `x ⊗ y`, taken over `Γ(S, 𝒪_S)`, of the sheaf-tensor
coefficient pairing of Tag 0FKV at the open `⊤` and the terminal object of the slice over it.

This is a step of the proof of Tag 0FKV and not a clause of its statement, so it carries no
tag. -/
theorem pushforwardTensorMap_toCoeffPoint_top (S : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureRingSheaf S))
    (x : ((pushforwardFunctor (toCoeffPoint S)).obj F).val.obj (op ⊤))
    (y : ((pushforwardFunctor (toCoeffPoint S)).obj G).val.obj (op ⊤)) :
    PresheafOfModules.Hom.app (pushforwardTensorMap (toCoeffPoint S) F G).val (op ⊤)
        (PresheafOfModules.Hom.app
          ((PresheafOfModules.sheafificationAdjunction
                (R := structureRingSheaf (onePointRingedSpace ↥(baseRing S)))
                (𝟙 (structureRingSheaf (onePointRingedSpace ↥(baseRing S))).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (onePointRingedSpace ↥(baseRing S)).presheaf)
              ((pushforwardFunctor (toCoeffPoint S)).obj F).val
              ((pushforwardFunctor (toCoeffPoint S)).obj G).val))
          (op ⊤) (x ⊗ₜ y)) =
      ((sheafTensorPairing S.sheaf ⊤ F G).app
        (op (Over.mk (𝟙 (⊤ : Opens S.carrier))))).hom (x ⊗ₜ y) :=
  pushforwardTensorMap_eq_sheafTensorPairing (toCoeffPoint S) F G (op ⊤) x y

end Stacks.RingedSpace

end
