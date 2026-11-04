module

public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessingerEquivalenceOver
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
import all StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger

/-!
# Condition (RS*) transports along an equivalence over the site (towards Stacks 0D5A)

Condition (RS*) of Stacks 07Y8 asks that, at every fibre-product square of affine schemes of the
big fppf site with one leg a surjection with square-zero kernel on global sections, the canonical
functor from the fibre over the fourth corner to the 2-fibre product of the other three fibres
be an equivalence. This file shows that the condition transports along an equivalence over the
site, by the argument of `Deformation.Artin.satisfiesRS_of_equivalenceOver` for condition (RS):
the forward functor of the equivalence is an equivalence on every fibre, so the functor it induces
on the 2-fibre products of fibres is one (Stacks 02XB (3)), and it intertwines the two canonical
functors.

It is used to move condition (RS*) of the stack of curves to its hom-shrunk model
`AlgebraicGeometry.curvesSmall`, the model to which Artin's openness of versality criterion
(Stacks 0CXU) applies.

## Main results

* `AlgebraicGeometry.C1590Private.satisfiesRSStar_of_equivalenceOver`.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 02XB](https://stacks.math.columbia.edu/tag/02XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v₁ w₁ v₂ w₂

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (RS*) transports along an equivalence over the site.** If `P` and `Q` are fibred
in groupoids over the big fppf site of `S`, `P` satisfies (RS*) and `e` is an equivalence over the
site between `P` and `Q`, then `Q` satisfies (RS*). The categories may live in different
universes. -/
theorem satisfiesRSStar_of_equivalenceOver
    {X₁ : Type v₁} [Category.{w₁} X₁] {X₂ : Type v₂} [Category.{w₂} X₂]
    {P : X₁ ⥤ BigFppfOver B S hS} {Q : X₂ ⥤ BigFppfOver B S hS}
    (hP : P.IsFiberedInGroupoids) (hQ : Q.IsFiberedInGroupoids)
    (hRS : Deformation.Artin.SatisfiesRSStar B S hS P hP)
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS) P Q) :
    Deformation.Artin.SatisfiesRSStar B S hS Q hQ := by
  let : P.IsFibered := hP.isFibered
  let : Q.IsFibered := hQ.isFibered
  dsimp only [Deformation.Artin.SatisfiesRSStar]
  intro U V W Z f g i j h hpb hsurj hker
  have hx := hRS U V W Z f g i j h hpb hsurj hker
  have hF : Functor.IsFibredOneMorphism P Q e.hom.functor :=
    hQ.isFibredOneMorphism e.hom.w
  let ι := BigAffineFppf.inclusion B S hS
  have := Deformation.Artin.isEquivalence_fiberMap_of_equivalenceOver e
  have : (Deformation.Artin.fiberSquareTargetMap hF (ι.map f) (ι.map g)).IsEquivalence := by
    unfold Deformation.Artin.fiberSquareTargetMap
    exact CategoryTheory.induced_isEquivalence_of_isEquivalence _ _ _ _ _
  have hh : ι.map f ≫ ι.map i = ι.map g ≫ ι.map j := by
    simpa only [Functor.map_comp] using congrArg ι.map h
  have : (Functor.fiberMap P Q e.hom.functor hF.comp_eq (ι.obj Z) ⋙
      Deformation.Artin.fiberSquareComparison Q (Functor.chosenPullbacks Q)
        (ι.map f) (ι.map g) (ι.map i) (ι.map j) hh).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (Deformation.Artin.fiberSquareComparison_map hF (ι.map f) (ι.map g) (ι.map i) (ι.map j) hh)
  exact Functor.isEquivalence_of_comp_left
    (Functor.fiberMap P Q e.hom.functor hF.comp_eq (ι.obj Z)) _

end AlgebraicGeometry.C1590Private

end
