module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushoutModules
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts

/-!
# Condition (RS*) for `Coh_{X/Y}`

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation (Situation 08KB).  By
Stacks 08LQ (`AlgebraicGeometry.Space.CoherentSituation.fiberSquareComparison_isEquivalence`), for
every pushout `Y'' = Y₀ ⨿_Z Z'` in the category of schemes over `S` along a thickening `Z ⟶ Z'` and
an affine morphism `Z ⟶ Y₀`, the functor on fibre categories
`Coh_{X/Y, Y''} ⟶ Coh_{X/Y, Y₀} ×_{Coh_{X/Y, Z}} Coh_{X/Y, Z'}` is an equivalence.  The pushouts
of condition (RS*) of Stacks 07Y8 are of this kind, so `Coh_{X/Y}` satisfies (RS*).  Condition
(RS) of Stacks 07WP is `AlgebraicGeometry.Space.CoherentSituation.satisfiesRS`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.satisfiesRSStar_coherentCFG`: condition (RS*) of
  Stacks 07Y8 for `Coh_{X/Y}`.

## References

* [Stacks Project, Tag 08LQ](https://stacks.math.columbia.edu/tag/08LQ)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-- **Condition (RS*) of Stacks 07Y8 for `Coh_{X/Y}`**, from Stacks 08LQ. -/
theorem satisfiesRSStar_coherentCFG :
    Deformation.Artin.SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2 :=
  Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence B S hS _ _
    fun i f a b _ hi hf hsq => by
      have := hf
      exact D.fiberSquareComparison_isEquivalence i f a b hi hsq

end AlgebraicGeometry.Space.CoherentSituation
