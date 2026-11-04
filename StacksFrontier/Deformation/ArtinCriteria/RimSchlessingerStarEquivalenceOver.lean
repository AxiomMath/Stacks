module

public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessingerEquivalenceOver
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
import all StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger

/-!
# Condition (RS*) transports along an equivalence over the site

Let `P` and `Q` be categories fibred in groupoids over the big fppf site of a scheme `S` and
`e : P ≃ Q` an equivalence over the site. If `P` satisfies condition (RS*) of Stacks 07Y8, so
does `Q`. The argument is the one for condition (RS),
`Deformation.Artin.satisfiesRS_of_equivalenceOver`: the forward functor of `e` restricts to an
equivalence on every fibre and intertwines the canonical functors from the fibre over the fourth
corner of a square to the 2-fibre product of the fibres over the other three, and the functor it
induces on those 2-fibre products is an equivalence by Stacks 02XB (3). Only the class of squares
differs.

## Main results

* `Deformation.Artin.satisfiesRSStar_of_equivalenceOver`.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 02XB](https://stacks.math.columbia.edu/tag/02XB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u v₁ w₁ v₂ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (RS*) transports along an equivalence over the site.** If `P` and `Q` are fibred
in groupoids over the big fppf site of `S`, `P` satisfies (RS*) (Stacks 07Y8) and `e` is an
equivalence over the site between `P` and `Q`, then `Q` satisfies (RS*). At each square of the
condition, the forward functor of `e` intertwines the two canonical functors to 2-fibre products
of fibres; it is an equivalence on each fibre
(`Deformation.Artin.isEquivalence_fiberMap_of_equivalenceOver`), so the functor it induces on the
2-fibre products of fibres is an equivalence (Stacks 02XB (3)), and the canonical functor of `Q` is
one because that of `P` is. -/
theorem satisfiesRSStar_of_equivalenceOver
    {X₁ : Type v₁} [Category.{w₁} X₁] {X₂ : Type v₂} [Category.{w₂} X₂]
    {P : X₁ ⥤ BigFppfOver B S hS} {Q : X₂ ⥤ BigFppfOver B S hS}
    (hP : P.IsFiberedInGroupoids) (hQ : Q.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS P hP)
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS) P Q) :
    SatisfiesRSStar B S hS Q hQ := by
  let : P.IsFibered := hP.isFibered
  let : Q.IsFibered := hQ.isFibered
  dsimp only [SatisfiesRSStar]
  intro U V W Z f g i j h hpb hsurj hsq
  have hx := hRS U V W Z f g i j h hpb hsurj hsq
  let ι := BigAffineFppf.inclusion B S hS
  have hw : ι.map f ≫ ι.map i = ι.map g ≫ ι.map j := by
    simpa only [Functor.map_comp] using congrArg ι.map h
  have hF : Functor.IsFibredOneMorphism P Q e.hom.functor :=
    hQ.isFibredOneMorphism e.hom.w
  have := isEquivalence_fiberMap_of_equivalenceOver e (ι.obj U)
  have := isEquivalence_fiberMap_of_equivalenceOver e (ι.obj V)
  have := isEquivalence_fiberMap_of_equivalenceOver e (ι.obj W)
  have := isEquivalence_fiberMap_of_equivalenceOver e (ι.obj Z)
  have : (fiberSquareTargetMap hF (ι.map f) (ι.map g)).IsEquivalence := by
    unfold fiberSquareTargetMap
    exact CategoryTheory.induced_isEquivalence_of_isEquivalence _ _ _ _ _
  have : (Functor.fiberMap P Q e.hom.functor hF.comp_eq (ι.obj Z) ⋙
      fiberSquareComparison Q (Functor.chosenPullbacks Q) (ι.map f) (ι.map g) (ι.map i)
        (ι.map j) hw).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (fiberSquareComparison_map hF (ι.map f) (ι.map g) (ι.map i) (ι.map j) hw)
  exact Functor.isEquivalence_of_comp_left
    (Functor.fiberMap P Q e.hom.functor hF.comp_eq (ι.obj Z)) _

end Deformation.Artin
