module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Transition
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules

/-!
# The structure map of a simplicial transition is the transition of Stacks 09WF

Let `S` be a simplicial-site situation (Stacks 09WE) and let `O` be a sheaf of commutative rings
on its total site. A simplex map `φ` induces a morphism of ringed topoi
`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom`, whose structure map is given
in inverse-image form by the structure-sheaf transition. This file reads both forms of that
structure map on underlying sheaves of sets, where they are the inverse-image and direct-image
transitions of Stacks 09WF.

Both statements hold in either case of the situation; nothing here distinguishes them.

## Main results

* `CategoryTheory.SimplicialSiteSituation.ringSheafMap_ringFsharpInverseImage_transition`: the
  inverse-image form of the structure map, on underlying sheaves of sets, is the inverse-image
  transition of Stacks 09WF.
* `CategoryTheory.SimplicialSiteSituation.ringSheafMap_ringFsharp_transition`: the direct-image
  form, on underlying sheaves of sets, is the direct-image transition of Stacks 09WF.

## Implementation notes

The two forms of the structure map of a morphism of ringed topoi are adjunct on underlying
sheaves of sets (`AlgebraicGeometry.RingedToposHom.ringSheafMap_ringFsharp`), and the mate of the
inverse-image transition is the direct-image transition
(`CategoryTheory.SimplicialSiteSituation.fiberTransition_adj`), so the second statement follows
from the first by transporting across the adjunction. Forgetting the ring operations through
`forget₂ CommRingCat RingCat` and then to sets is forgetting them to sets, which is what turns
`transitionRingedToposHom_fSharpInverseImage` and `fiberTransitionCommRing_forget` into the first.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (P : Sheaf S.totalTopology CommRingCat.{u})
  {m n : SimplexCategory}

/-- **The inverse-image form of the structure map of a simplicial transition is the
inverse-image transition of Stacks 09WF.** Forgetting the ring operations through
`forget₂ CommRingCat RingCat` and then to sets is forgetting them to sets, so this is
`transitionRingedToposHom_fSharpInverseImage` followed by `fiberTransitionCommRing_forget`. -/
theorem ringSheafMap_ringFsharpInverseImage_transition (φ : m ⟶ n) :
    (sheafCompose (S.componentTopology n) (forget RingCat.{u})).map
        (S.transitionRingedToposHom P φ).ringFsharpInverseImage =
      (S.fiberTransition φ).app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj P) :=
  (congrArg
      (fun g ↦ (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map g)
      (S.transitionRingedToposHom_fSharpInverseImage P φ)).trans
    (S.fiberTransitionCommRing_forget P φ)

/-- **The direct-image form of the structure map of a simplicial transition is the direct-image
transition of Stacks 09WF.** The two forms are adjunct, the inverse-image form is the
inverse-image transition, and the mate of the inverse-image transition is the direct-image
one. -/
theorem ringSheafMap_ringFsharp_transition (φ : m ⟶ n) :
    (sheafCompose (S.componentTopology m) (forget RingCat.{u})).map
        (S.transitionRingedToposHom P φ).ringFsharp =
      (S.restrictTransition φ).app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj P) :=
  (AlgebraicGeometry.RingedToposHom.ringSheafMap_ringFsharp
      (S.transitionRingedToposHom P φ)).trans
    ((congrArg
        (fun g ↦ (((S.transitionMorphism φ).adj.homEquiv _ _)) g)
        (S.ringSheafMap_ringFsharpInverseImage_transition P φ)).trans
      (S.fiberTransition_adj φ _))

end CategoryTheory.SimplicialSiteSituation

end
