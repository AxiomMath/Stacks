module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkAbelian

/-!
# Vanishing of the higher sections with support on a direct image

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` and let `G` be an
injective abelian sheaf on the small étale site of `Z`. The higher sections with support in
`|Z|` of the direct image `i_*G` vanish: `H^p_Z(i_*G) = 0` for `p > 0`, where `H_Z` is the
functor of Stacks 0A4L and `H^p_Z` is its `p`-th right derived functor.

The two inputs are the source's. The direct image `i_*` carries injective abelian sheaves to
injective abelian sheaves, because it is right adjoint to the inverse image and the inverse
image of abelian sheaves is left exact; and the higher right derived functors of an additive
functor vanish on an injective object.

## Main results

* `AlgebraicGeometry.Space.preservesMonomorphisms_smallEtaleAbelianInverseImage`: the inverse
  image of abelian sheaves along a morphism of algebraic spaces with representable underlying
  morphism preserves monomorphisms.
* `AlgebraicGeometry.Space.preservesInjectiveObjects_smallEtaleAbelianPushforward` and
  `AlgebraicGeometry.Space.injective_smallEtaleAbelianPushforward_obj`: the direct image of
  abelian sheaves along such a morphism carries injective abelian sheaves to injective abelian
  sheaves. This is Stacks 015Z applied to the adjunction between the inverse image and the
  direct image.
* `AlgebraicGeometry.Space.isZero_rightDerivedPlus_sectionsWithSupportInClosedSubspace` is
  **Stacks 0A4N**.

## Implementation notes

Left exactness of the inverse image is quoted in the form the sheaf pullback of
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImage` needs it, namely
`AlgebraicGeometry.Space.preservesFiniteLimits_smallEtaleAbelianInverseImage`, which is part (1)
of Stacks 04K2. Only preservation of monomorphisms is extracted from it, since that is all
Stacks 015Z needs in order to turn the adjunction between the inverse image and the direct image
into preservation of injective objects.

Exactness of `i_*` along a closed immersion, which the source also quotes, is not used: it
enters the source's argument only through the preservation of injectives, and that is obtained
here from the adjunction with the inverse image instead. This matters, because the development
proves exactness of `i_*` only under a hypothesis owed to Étale Cohomology, whereas the
statement below is unconditional.

The derived category of the two sheaf categories is the standard one, supplied as a file-local
instance exactly as in `StacksFrontier/AlgebraicGeometry/Spaces/AbelianPushforwardExact.lean`; the
enough-injectives hypothesis of the vanishing is
`AlgebraicGeometry.Space.smallEtaleAbelianSheaf_enoughInjectives`.

## References

* [Stacks Project, Tag 015B](https://stacks.math.columbia.edu/tag/015B)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4N](https://stacks.math.columbia.edu/tag/0A4N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- The inverse image of abelian sheaves along a morphism of algebraic spaces with
representable underlying morphism preserves monomorphisms, being left exact. -/
theorem preservesMonomorphisms_smallEtaleAbelianInverseImage (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom) :
    (smallEtaleAbelianInverseImage B S hS i hr).PreservesMonomorphisms :=
  have := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hr
  inferInstance

/-- **Stacks 015Z for the small étale direct image.** The direct image of abelian sheaves along
a morphism of algebraic spaces with representable underlying morphism carries injective abelian
sheaves to injective abelian sheaves: it is right adjoint to the inverse image, and the inverse
image preserves monomorphisms. -/
theorem preservesInjectiveObjects_smallEtaleAbelianPushforward (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom) :
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hr).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_smallEtaleAbelianInverseImage B S hS i hr
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (smallEtaleAbelianInverseImageAdjunction B S hS i hr)

/-- The direct image `i_*G` of an injective abelian sheaf along a morphism of algebraic spaces
with representable underlying morphism is an injective abelian sheaf. -/
theorem injective_smallEtaleAbelianPushforward_obj (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1}) [Injective G] :
    Injective ((smallEtaleAbelianPushforward.{u + 1} B S hS i hr).obj G) :=
  have := preservesInjectiveObjects_smallEtaleAbelianPushforward B S hS i hr
  Functor.injective_obj_of_injective _ inferInstance

/-- **Stacks 0A4N.** Let `S` be a scheme, let `i : Z ⟶ X` be a closed immersion of algebraic
spaces over `S` and let `G` be an injective abelian sheaf on the small étale site of `Z`. Then
the higher sections with support in `|Z|` of the direct image `i_*G` vanish:
`H^p_Z(i_*G) = 0` for `p > 0`.

The direct image of an injective abelian sheaf is injective, and the higher right derived
functors of an additive functor vanish on an injective object. -/
@[stacks 0A4N]
theorem isZero_rightDerivedPlus_sectionsWithSupportInClosedSubspace (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1}) [Injective G]
    (p : ℤ) (hp : 0 < p) :
    IsZero (((sectionsWithSupportInClosedSubspace B S hS i hi).rightDerivedPlus p).obj
      ((smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G)) :=
  have := injective_smallEtaleAbelianPushforward_obj B S hS i hi.rep G
  Functor.isZero_rightDerivedPlus_obj_injective _ p hp.ne' _

end AlgebraicGeometry.Space

end
