module

public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import StacksCore.Tactic.StacksAttribute

/-!
# Presheaves of morphisms associated to a fibred category

For two objects over a site, their morphisms after pullback form a presheaf. Mathlib expresses
the construction for a pseudofunctor from the locally discrete bicategory on the opposite of the
base into `Cat`; its coherence is carried by `mapComp'`. The restriction maps, their identity and
composition laws, and the resulting presheaf are registered here.

## References

* [Stacks Project, Tag 02ZA](https://stacks.math.columbia.edu/tag/02ZA)
-/

@[expose] public section

add_to_stacks 02ZA "Remark 8.2.4 observes that a category fibred in groupoids is
  equivalent to the fibred category of a contravariant functor into groupoids, and that
  for the latter the restriction maps of the presheaf Mor(x, y) of Definition 8.2.2 need
  no coherence isomorphisms. Mathlib works in exactly that model: for a pseudofunctor
  from the locally discrete bicategory on the opposite of the base into Cat, this is the
  restriction map from a morphism of the fibre over Y to a morphism of the fibre over
  Y', with the coherence isomorphisms carried by mapComp'."
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
add_to_stacks 02ZA "Restriction along an identity is the identity, the first half of the
  functoriality that Remark 8.2.4 says is trivial in this model."
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id
add_to_stacks 02ZA "Restriction respects composition, the second half of that
  functoriality." CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom
add_to_stacks 02ZA "The presheaf Mor(x, y) itself: the presheaf on Over S whose sections
  over a morphism p : X ⟶ S are the morphisms from the pullback of M along p to the
  pullback of N along p. Assembling it is Lemma 8.2.1, which Remark 8.2.4 is a remark
  about; the further ingredient the remark cites, invariance of Mor(x, y) under an
  equivalence of fibred categories (Lemma 042V), is not covered here."
  CategoryTheory.Pseudofunctor.presheafHom
