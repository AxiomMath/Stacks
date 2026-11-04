module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionAlgebra
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedIsomCorepresentation
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedIsomRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria

/-!
# The diagonal of the stack of polarized schemes is representable (Stacks 0D42)

The diagonal `Δ : 𝒫olarized ⟶ 𝒫olarized × 𝒫olarized` of the stack of polarized proper flat
families of finite presentation is representable by algebraic spaces.

## Main results

* `AlgebraicGeometry.hasRepresentableDiagonal_polarizedStackUnconditional`: the diagonal of the
  stack of polarized schemes is representable by algebraic spaces.

## Implementation notes

The source deduces the lemma from Stacks 0D41 (the forgetful 1-morphism to
`Spaces'_{fp, flat, proper}` is algebraic) and Stacks 0D1F (that stack has representable diagonal)
by Stacks 0D3R. This file proves it directly, through condition (2) of Stacks 045G
(`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`): for two
objects `x`, `y` over a scheme `U` the presheaf `Isom(x, y)` is representable by an object of the
site, hence an algebraic space.

* `Isom(x, y)` is an fppf sheaf (`AlgebraicGeometry.isSheaf_polarizedIsomPresheaf`: descent of
  morphisms of schemes and of quasi-coherent modules along fpqc coverings).
* Over an affine open `V` of `U`, with `d₀` a uniform degree bound of [Stacks, Tag 0D4F] for the
  two families over `V`, an isomorphism of polarized families over an affine `T ⟶ V` is the same
  thing as an isomorphism of the graded algebras of global sections of the truncated section
  algebras `𝒪_T ⊕ ⨁_{d ≥ d₀} f_* ℒ^{⊗ d}`
  (`Stacks.AlgebraicGeometry.ProjectiveDeformation.polarizedIsoSectionBijection`, by relative
  `Proj` and the degree-one determination of twists); these algebras are base changes of those
  over `V`, with finite projective pieces, and the functor of graded isomorphisms of base changes
  of such algebras is corepresented by a ring `H` over `Γ(V, 𝒪_V)`
  (`Stacks.GradedIsomScheme.exists_corepresenting`): `Isom` over `V` is `Spec H`
  (`AlgebraicGeometry.PolarizedFamily.exists_corepresentation_isoOverBase_of_sectionBijection`).
* These local representing objects glue by Stacks 01JJ over the affine opens of `U`
  (`AlgebraicGeometry.isRepresentable_isomPresheaf_of_corepresented`).

## References

* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- The diagonal `𝒫olarized ⟶ 𝒫olarized × 𝒫olarized` of the stack of polarized proper flat
families of finite presentation, over the big fppf site of a terminal base scheme, is representable
by algebraic spaces. -/
@[stacks 0D42]
theorem hasRepresentableDiagonal_polarizedStackUnconditional :
    Stack.HasRepresentableDiagonal B S hS (polarizedStackUnconditional B hS hT) := by
  refine (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS _).2
    fun U x y => ?_
  have hrep := isRepresentable_isomPresheaf_of_corepresented B hS hT U x y
    (isSheaf_polarizedIsomPresheaf B hS hT U x y) fun a b hab _ =>
      PolarizedFamily.exists_corepresentation_isoOverBase_of_sectionBijection
        Stacks.AlgebraicGeometry.ProjectiveDeformation.polarizedIsoSectionBijection a b hab
  exact ⟨yoneda.obj _, isAlgebraicSpace_yoneda B _ _ _,
    ⟨Functor.isoWhiskerRight (Functor.reprW _) uliftFunctor⟩⟩

end AlgebraicGeometry

end
