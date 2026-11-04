module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable

/-!
# The two excision legs are representable and étale

Stacks 0BGY covers a presheaf `X` over an algebraic space `W` by two legs: the part of `X`
lying over the open complement `W⁰` of a closed subspace `T`, and the fibre product `X ×_W V`
along a separated étale `f : V ⟶ W`. That family is
`AlgebraicGeometry.Space.excisionBaseMap`, and
`AlgebraicGeometry.Space.familyImage_excisionBaseMap_sieveOfSection_mem` shows it covers.

This file proves the other hypothesis of the étale glueing criterion of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleCoverAlgebraic`: each leg is representable and étale
after every represented base change. Both are base changes of a morphism that is so.

## Main results

* `AlgebraicGeometry.Space.presheafEtale_preimage_openComplement_ι`: the `W⁰` leg. The
  inclusion of the open complement of a closed subspace is an open immersion, hence étale, and
  the leg is its base change along `g`.
* `AlgebraicGeometry.Space.presheafEtale_hom_of_isEtale_isSeparated`: a separated étale
  morphism of algebraic spaces is representable and étale after every represented base change.
  This is Stacks 0418 and Stacks 03XU for representability, and Stacks 03MJ to pass from the
  chart condition defining `AlgebraicGeometry.Space.IsEtale` to the relative property.
* `AlgebraicGeometry.Space.presheafEtale_excisionBaseMap`: both legs at once, indexed by
  `Bool` exactly as `AlgebraicGeometry.Space.excisionBaseMap` is.

## Implementation notes

`AlgebraicGeometry.Space.IsEtale` (Stacks 03FR) is *not* the relative morphism property: it is
the condition that composing with every étale chart of the source is étale, and it carries no
representability. The passage between the two is Stacks 03MJ, available here as
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative`, and it needs representability as
an input — which for a separated étale morphism is Stacks 0418 applied to Stacks 03XU.

## References

* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A separated étale morphism of algebraic spaces is representable and étale.**

Representability is Stacks 0418 applied to the local quasi-finiteness of an étale morphism,
Stacks 03XU; the passage from the chart condition defining `AlgebraicGeometry.Space.IsEtale` to
the relative morphism property is then Stacks 03MJ, étaleness of schemes being étale local on
source and target, stable under base change and local on the base for the fppf topology. -/
theorem presheafEtale_hom_of_isEtale_isSeparated
    {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W)
    (hf : IsEtale B S hS f) (hsep : IsSeparated B S hS f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
  (holdsOnEveryEtaleChart_iff_relative B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget hV hW f
      (relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f hV hW
        (isLocallyQuasiFinite_of_isEtale B S hS hW hf) hsep)).mp
    (holdsOnEveryEtaleChart_of_isEtale_hom B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (fun _ hg => hg) hW hf)

variable {V W : AlgebraicSpaces B S hS}

/-- **The `W⁰` leg of the excision covering is representable and étale.** The open complement
of a closed subspace of an algebraic space is an open subspace, so its inclusion is an open
immersion and in particular étale after every represented base change; and the leg is the base
change of that inclusion along `g`, the preimage of a subfunctor being a fibre product. -/
theorem presheafEtale_preimage_openComplement_ι (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ W.obj) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (((openComplement B S hS T).preimage g).ι) :=
  presheaf_of_isPullback B S hS
    (Subfunctor.isPullback_fromPreimage (openComplement B S hS T) g)
    (presheaf_etale_of_isOpenImmersion B S hS
      (isOpenSubspace_openComplement B S hS W.property T hT).2)

/-- **Both legs of the excision covering are representable and étale.** The family is
`AlgebraicGeometry.Space.excisionBaseMap`, indexed by `Bool`: the `W⁰` leg is the base change
of the inclusion of the open complement, and the `V` leg is the base change of `f`. -/
theorem presheafEtale_excisionBaseMap (f : V ⟶ W) (hf : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ W.obj) (b : Bool) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (excisionBaseMap B S hS f T g b) := by
  cases b with
  | false =>
    exact presheaf_of_isPullback B S hS (IsPullback.of_hasPullback g f.hom).flip
      (presheafEtale_hom_of_isEtale_isSeparated B S hS V.property W.property f.hom hf hsep)
  | true => exact presheafEtale_preimage_openComplement_ι B S hS T hT g

end AlgebraicGeometry.Space

end
