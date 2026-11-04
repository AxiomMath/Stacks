module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleUniversallyInjectiveOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjectiveSchemeTests
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# An étale morphism with an invertible base change along a surjection

Let `g : G ⟶ A` be an étale morphism of algebraic spaces over a scheme `S` and let `p : A' ⟶ A`
be surjective. If the base change of `g` along `p` is an isomorphism, then `g` itself is an
isomorphism.

## References

* [Stacks Project, Tag 03MX](https://stacks.math.columbia.edu/tag/03MX)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A A' G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end AlgebraicGeometry.Space

end
