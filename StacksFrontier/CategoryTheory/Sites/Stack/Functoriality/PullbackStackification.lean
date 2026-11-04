module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification.LocalizationMap
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification.Coverings
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification.LocalInjectivity
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification.LocalEssSurj

/-!
# The pullback of a stackification

Let `u : 𝒞 ⥤ 𝒟` be a continuous functor of sites preserving nonempty finite limits, and let
`G : 𝒮 ⥤ 𝒮'` be a 1-morphism of fibred categories over `𝒞`. The functor
`Φ : u_pp 𝒮 ⥤ u_pp 𝒮'`, `(V, x, φ) ↦ (V, G x, φ)`, induces `Ψ : u_p 𝒮 ⥤ u_p 𝒮'` on the
localizations, and `Ψ` is a 1-morphism of fibred categories over `𝒟`. If `G` exhibits `𝒮'` as
the stackification of `𝒮`, then `Ψ` is locally bijective on morphism presheaves and locally
essentially surjective, and the stackification of `u_p 𝒮'` is the stackification of `u_p 𝒮`.

The parts are:

* `PullbackStackification.LocalizationMap`: the functor `Ψ`, which is a 1-morphism of
  fibred categories, and the objects and isomorphisms of the fibres of `u_p 𝒮`;
* `PullbackStackification.Coverings`: covering sieves transferred along `u`, clauses (1)
  and (2) of Stacks 02ZN, and the morphisms of `u_pp 𝒮` written out;
* `PullbackStackification.LocalInjectivity`: the local content of Stacks 04WR, injectivity;
* `PullbackStackification.LocalEssSurj`: local bijectivity and local essential surjectivity
  of `Ψ`, and Stacks 04WR.

## References

* [Stacks Project, Tag 04WR](https://stacks.math.columbia.edu/tag/04WR)
-/
