module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiPullbackSections

/-!
# Composing the big and small Zariski morphisms of topoi

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be composable morphisms of a big Zariski site. The geometric
morphism attached to `f ≫ g` is the composite of those attached to `f` and to `g`, both on the
big Zariski topoi and on the small ones:

`g_big ∘ f_big = (g ∘ f)_big` and `g_small ∘ f_small = (g ∘ f)_small`.

## Main definitions

* `AlgebraicGeometry.bigZariskiMorphism_comp_pushforwardIso` and
  `AlgebraicGeometry.bigZariskiMorphism_comp_inverseImageIso` — the comparison on the big
  Zariski topoi, on direct images and on inverse images.
* `AlgebraicGeometry.smallZariskiMorphism_comp_pushforwardIso` and
  `AlgebraicGeometry.smallZariskiMorphism_comp_inverseImageIso` — the same comparison on the
  small Zariski topoi.

## Implementation notes

The source states equalities of geometric morphisms. Neither of the two holds as an equality
here, and both are stated as canonical natural isomorphisms instead, following the convention
used throughout for equalities of morphisms of topoi: such an equality is expressed as a natural
isomorphism of the direct-image functors, together with its mate on the inverse images, since
functors obtained by composing adjunctions are not definitionally equal. The two isomorphisms
are two readings of one identification, each being determined by the other through the three
geometric adjunctions.

On the big sites the underlying site functors do compose on the nose, by
`CategoryTheory.Over.mapComp_eq`. That equality does not reach the topoi, however: the direct
image of `f_big` is the right Kan extension along `(Over.map f)ᵒᵖ`, which takes the
cocontinuity of `Over.map f` as an argument, so the equality of functors cannot be transported
into it, and a composite of right Kan extensions is in any case only canonically isomorphic to
the right Kan extension along the composite. The comparison is therefore assembled from the
base-change description of the direct image: along the adjunction `Over.map f ⊣ Over.pullback f`
the direct image becomes restriction along `Over.pullback f`, restrictions do compose on the
nose, and the two slice base-change functors are compared by `CategoryTheory.Over.pullbackComp`,
which is the canonical isomorphism `(U ×_Z Y) ×_Y X ≅ U ×_Z X` of iterated fibre products.

On the small sites even the underlying site functors compose only up to isomorphism: the
base-change functor is pinned down solely by the canonical isomorphism of its composite with
the inclusion into the slice of schemes with scheme-theoretic fibre product, so no equality
between successive base changes and base change along the composite is available. The
comparison of the site functors is `AlgebraicGeometry.smallZariskiBaseChange_compIso`, and the
direct-image comparison is the one it induces.

## References

* [Stacks Project, Tag 0212](https://stacks.math.columbia.edu/tag/0212)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (X Y Z : B.Schemes) (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks 0212.** The direct image of `g_big ∘ f_big` agrees naturally with that of
`(g ∘ f)_big`.

Both are read as restriction along slice base change, where the comparison is the canonical
isomorphism `(U ×_Z Y) ×_Y X ≅ U ×_Z X` of iterated fibre products. -/
@[stacks 0212 "the big sites, direct image"]
public noncomputable def bigZariskiMorphism_comp_pushforwardIso :
    ((bigZariskiMorphism B Y Z g).comp (bigZariskiMorphism B X Y f)).pushforward ≅
      (bigZariskiMorphism B X Z (f ≫ g)).pushforward :=
  Functor.isoWhiskerRight
      ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1)))
      (bigZariskiMorphism B Y Z g).pushforward ≪≫
    Functor.isoWhiskerLeft
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigZariskiOver.topology B Y.1 Y.property)
        (BigZariskiOver.topology B X.1 X.property))
      ((Over.mapPullbackAdj g).sheafPushforwardCocontinuousIso (Type (u + 1))) ≪≫
    Functor.sheafPushforwardContinuousComp'
      (Over.pullbackComp f g).symm (Type (u + 1))
      (BigZariskiOver.topology B Z.1 Z.property)
      (BigZariskiOver.topology B Y.1 Y.property)
      (BigZariskiOver.topology B X.1 X.property) ≪≫
    ((Over.mapPullbackAdj (f ≫ g)).sheafPushforwardCocontinuousIso (Type (u + 1))).symm

/-- **Stacks 0212.** The inverse image of `g_big ∘ f_big` agrees naturally with that of
`(g ∘ f)_big`; the isomorphism is the mate of the direct-image comparison under the three
geometric adjunctions. -/
@[stacks 0212 "the big sites, inverse image"]
public noncomputable def bigZariskiMorphism_comp_inverseImageIso :
    ((bigZariskiMorphism B Y Z g).comp (bigZariskiMorphism B X Y f)).inverseImage ≅
      (bigZariskiMorphism B X Z (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointCompIso
    (bigZariskiMorphism B Y Z g).adj
    (bigZariskiMorphism B X Y f).adj
    (bigZariskiMorphism B X Z (f ≫ g)).adj
    (bigZariskiMorphism_comp_pushforwardIso B X Y Z f g)

/-- **Stacks 0212.** The direct image of `g_small ∘ f_small` agrees naturally with that of
`(g ∘ f)_small`, by the composition comparison of the underlying small-site base-change
functors. -/
@[stacks 0212 "the small sites, direct image"]
public noncomputable def smallZariskiMorphism_comp_pushforwardIso :
    ((smallZariskiMorphism B Y Z g).comp (smallZariskiMorphism B X Y f)).pushforward ≅
      (smallZariskiMorphism B X Z (f ≫ g)).pushforward :=
  Functor.sheafPushforwardContinuousComp'
    (smallZariskiBaseChange_compIso B f g)
    (Type (u + 1)) (SmallZariski.topology B Z.1 Z.property)
    (SmallZariski.topology B Y.1 Y.property)
    (SmallZariski.topology B X.1 X.property)

/-- **Stacks 0212.** The inverse image of `g_small ∘ f_small` agrees naturally with that of
`(g ∘ f)_small`; the isomorphism is the mate of the direct-image comparison under the three
sheaf adjunctions. -/
@[stacks 0212 "the small sites, inverse image"]
public noncomputable def smallZariskiMorphism_comp_inverseImageIso :
    ((smallZariskiMorphism B Y Z g).comp (smallZariskiMorphism B X Y f)).inverseImage ≅
      (smallZariskiMorphism B X Z (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointCompIso
    (smallZariskiMorphism B Y Z g).adj
    (smallZariskiMorphism B X Y f).adj
    (smallZariskiMorphism B X Z (f ≫ g)).adj
    (smallZariskiMorphism_comp_pushforwardIso B X Y Z f g)

end AlgebraicGeometry
