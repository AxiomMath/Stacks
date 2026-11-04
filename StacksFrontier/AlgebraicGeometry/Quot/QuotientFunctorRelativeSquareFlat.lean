module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquare
public import StacksFrontier.Deformation.ToposThickening.RelativeBaseLeftFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverToposFlat

/-!
# Flatness over the test scheme, read through the relative square

In the relative square of `AlgebraicGeometry.Space.QuotientSituation.relativeSquare_comm`, the
morphism `X_T ⟶ T` is replaced by `f̃ : X_T ⟶ (X_{T'}, f'⁻¹t_*𝒪_T)`. This file shows that the two
readings of flatness over `T` agree: a quasi-coherent `𝒪_{X_T}`-module is flat over `T`
(Stacks 05VV) exactly when its direct image to `X_{T'}` is flat over the base along `f̃` in the
sense of `Deformation.ToposThickening.IsFlatOverBase`, the hypothesis Remark 0CZU puts on the
quotient `𝒬`.

The comparison `θ` of the relative square is the component at the structure sheaf of a natural
isomorphism `Θ : f'_* ∘ i_* ≅ t_* ∘ p_*`, built from the comparisons of Stacks 03G8, so
`Deformation.ToposThickening.isFlat_restrictScalars_relBaseLeft_iff` applies.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.isFlatOver_iff_isFlatOverBase_relativeSquareLeft`:
  flatness over `T` is flatness over the base of the relative square.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardCommRingCompIso
  pushforwardCommRingCompNatIso pushforwardCommRingCompNatIso_app pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace AlgebraicGeometry.Space

namespace QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotientSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

include hh in
/-- **Flatness over `T` is flatness over the base of the relative square.** A quasi-coherent
`𝒪_{X_T}`-module `𝒬` is flat over `T` (Stacks 05VV) exactly when its direct image `i_*𝒬` to
`X_{T'}` is flat over `f'⁻¹t_*𝒪_T` along `f̃`. -/
theorem isFlatOver_iff_isFlatOverBase_relativeSquareLeft
    (Q : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) [Q.IsQuasicoherentOnSite] :
    IsFlatOver B S hS (D.space T).2 (D.projection T).hom Q ↔
      IsFlatOverBase (smallEtaleRingedToposHom B S hS (D.relativeMap h)) (D.relativeSquareLeft h)
        ((pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS (D.relativeMap h)).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS (D.space T)).O)).obj Q) := by
  have := (D.relativeMapFirstOrderThickening h hh).equiv
  have h₁ := isFlatOver_iff_isFlat_restrictScalars B S hS (D.projection T) Q
  have h₂ := isFlat_restrictScalars_relBaseLeft_iff (θ := D.relativeSquareIso h)
    (squareRingNatIso B S hS (D.relativeMap h) (D.projection T') (D.projection T)
      ((schemeSpaceFunctor B S hS).map h.left) (D.relativeMap_comp_projection h))
    (D.testSchemeFirstOrderThickening h hh) rfl Q
  have h₃ := isFlatOverBase_pushforward_iff (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareLeft h) Q
  exact h₁.trans (h₂.symm.trans h₃.symm)

end QuotientSituation

end AlgebraicGeometry.Space

end
