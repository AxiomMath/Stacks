module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# Pullback of an invertible sheaf with a trivialized power

Let `f : X ⟶ S` be a morphism of schemes and let `(ℒ, α)` be an invertible sheaf on `S` together
with a trivialization of its `n`th tensor power. Then `f^*ℒ` is invertible, and the comparison
`f^*(ℒ^{⊗n}) ≅ (f^*ℒ)^{⊗n}` of
`Stacks.TensorPowerPullback.pullbackIntPowIso` together with the comparison `f^*𝒪_S ≅ 𝒪_X` of
`Stacks.TensorPowerPullback.pullbackUnitSheafIso` carries `α` to a trivialization of
`(f^*ℒ)^{⊗n}`. This file records the resulting pair.

## Main definitions

* `AlgebraicGeometry.pullbackPair` is the pullback of such a pair along a morphism of schemes.

## Main results

* `AlgebraicGeometry.pullbackPair_sheaf` and `AlgebraicGeometry.pullbackPair_trivialization`
  compute its two components.

## Implementation notes

The comparisons are those of a morphism of ringed spaces, so `f` is used through
`f.toLRSHom.toShHom`; the sheaf condition `AlgebraicGeometry.ringSheafCond` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic` and
`Stacks.TensorPowerPullback.isSheafStructure` are two proofs of one proposition, so no transport
between the two spellings of the structure sheaf is needed. Invertibility of the pullback is
Tag 0B8L in the form `Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf`, whose
hypothesis and conclusion are in the `Stacks` spelling of Tag 01CS, hence the two conversions.

## References

* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

namespace AlgebraicGeometry

universe u

/-- The pullback of an invertible sheaf with a trivialized `n`th tensor power along a morphism of
schemes: the pullback of the sheaf, trivialized by the pullback of the trivialization read
through the comparisons of the tensor powers and of the structure sheaves. -/
public noncomputable def pullbackPair {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ}
    (P : TrivializedPower S n) : TrivializedPower X n where
  sheaf := (Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom).obj P.sheaf
  invertible := by
    let : Stacks.SheafOfModules.IsInvertible S.presheaf (ringSheafCond S) P.sheaf :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ P.invertible
    exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf f P.sheaf)
  trivialization :=
    let := P.invertible
    (Stacks.TensorPowerPullback.pullbackIntPowIso f.toLRSHom.toShHom P.sheaf (n : ℤ)).symm ≪≫
      (Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom).mapIso P.trivialization ≪≫
      Stacks.TensorPowerPullback.pullbackUnitSheafIso f.toLRSHom.toShHom

/-- The invertible sheaf of a pulled-back pair is the pullback of the invertible sheaf. -/
public theorem pullbackPair_sheaf {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ}
    (P : TrivializedPower S n) :
    (pullbackPair f P).sheaf =
      (Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom).obj P.sheaf :=
  rfl

/-- The trivialization of a pulled-back pair is the pullback of the trivialization, read through
the comparison of the tensor powers and the comparison of the structure sheaves. -/
public theorem pullbackPair_trivialization {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ}
    (P : TrivializedPower S n) :
    (pullbackPair f P).trivialization =
      letI := P.invertible
      (Stacks.TensorPowerPullback.pullbackIntPowIso f.toLRSHom.toShHom P.sheaf (n : ℤ)).symm ≪≫
        (Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom).mapIso P.trivialization ≪≫
        Stacks.TensorPowerPullback.pullbackUnitSheafIso f.toLRSHom.toShHom :=
  rfl

end AlgebraicGeometry

end
