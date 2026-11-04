module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderCategory
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# Quasi-coherence of an external tensor product

The external tensor product of two quasi-coherent modules on schemes over a common base is
quasi-coherent: each pullback is quasi-coherent, and a tensor product of quasi-coherent modules
on a ringed space is quasi-coherent. In particular the external tensor product of two
quasi-coherent modules is an object of the category of finite-order differential operators on the
fibre product over the base.

## Main results

* `AlgebraicGeometry.isQuasicoherent_externalTensorProduct`: the external tensor product of two
  quasi-coherent modules is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxProductObj` is the external
  tensor product, regarded as an object of the category of finite-order differential operators
  on the fibre product over the base.

## Implementation notes

The two inputs are Tag 01BG, `Stacks.Modules.isQuasicoherent_pullback`, and Tag 01CE,
`AlgebraicGeometry.tensorSheaf_isQuasicoherent`; the latter is applied with its hypotheses
supplied explicitly, since the quasi-coherence of a pullback is stated for the `X.Modules`
spelling of the module category and the tensor product for the underlying ringed space.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The external tensor product of two quasi-coherent modules is quasi-coherent.** -/
instance isQuasicoherent_externalTensorProduct {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (externalTensorProduct f g F G).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent (pullback f g).toRingedSpace _ _
    (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback (pullback.fst f g) F)
    (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback (pullback.snd f g) G)

namespace FiniteOrderDifferentialOperatorCategory

/-- The external tensor product `F ⊠ G = p^*F ⊗ q^*G` of two quasi-coherent modules, regarded as
an object of the category of finite-order differential operators on the fibre product over the
base. -/
noncomputable abbrev boxProductObj {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}
    (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a) :=
  { module := externalTensorProduct a b F.module G.module }

end FiniteOrderDifferentialOperatorCategory

end AlgebraicGeometry

end
