module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata

/-!
# The integral closed subspaces of a space and of its top subfunctor

The multiplicity `m_{W, Y}` of Stacks 0EE9 is defined for an integral closed subspace `W` of a
*closed subspace* `Y ⊆ X`, as `AlgebraicGeometry.Space.closedSubspaceMultiplicity`. The
multiplicity `m_{X', X}` of an irreducible component `X'` *in `X` itself* — the coefficient of
the right-hand side of Stacks 0EQA — is the case `Y = ⊤`. But `(⊤ : Subfunctor X).toFunctor` is
only *isomorphic* to `X`, not equal to it, so `m_{X', X}` is indexed by the integral closed
subspaces of `(⊤ : Subfunctor X).toFunctor` while a consumer's components are integral closed
subspaces of `X`. This file transports between the two.

The transport is `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward` along the inclusion
`(⊤ : Subfunctor X).ι`, which is an isomorphism and so in particular a closed immersion
(`AlgebraicGeometry.Space.isClosedSubspace_top_subfunctor`). It is injective for any closed
immersion, and here it is also surjective, because every integral closed subspace of `X` has its
point set inside the range of a surjection. The δ-dimension is unchanged, by
`AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_pushforward`, so the index set of
the cycle `[X]_k` is transported along with the subspaces.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.ofTopSubfunctor`: an integral closed subspace of
  `(⊤ : Subfunctor X).toFunctor` as one of `X`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.topSubfunctorEquiv`: the resulting bijection.
* `AlgebraicGeometry.Space.multiplicityInAmbient`: the multiplicity `m_{X', X}` of an integral
  closed subspace of `X` in `X` itself, that is `m_{W, ⊤}` for the `W` corresponding to `X'`.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.bijective_ofTopSubfunctor`: the transport is a
  bijection.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_ofTopSubfunctor`: it preserves
  the δ-dimension.
* `AlgebraicGeometry.Space.closedSubspaceMultiplicity_top_eq_multiplicityInAmbient`: the
  multiplicity of `W` in `⊤` is the multiplicity in `X` of the integral closed subspace of `X`
  that `W` transports to.

## References

* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The transport of integral closed subspaces -/

section Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)

/-- **An integral closed subspace of the top subfunctor, as one of the space itself.** The
inclusion `(⊤ : Subfunctor X).ι` is an isomorphism, hence a closed immersion, so an integral
closed subspace of `(⊤ : Subfunctor X).toFunctor` has an image which is an integral closed
subspace of `X`. -/
def IntegralClosedSubspace.ofTopSubfunctor
    (W : IntegralClosedSubspace B S hS (⊤ : Subfunctor X).toFunctor) :
    IntegralClosedSubspace B S hS X :=
  IntegralClosedSubspace.pushforward B S hS hX
    (isClosedSubspace_top_subfunctor B S hS hX).1 hXdec
    (isClosedSubspace_top_subfunctor B S hS hX).2 W

/-- **The integral closed subspaces of a space and of its top subfunctor correspond.** Taking the
image along the inclusion `(⊤ : Subfunctor X).ι` is a bijection from the integral closed
subspaces of `(⊤ : Subfunctor X).toFunctor` onto those of `X`. -/
theorem IntegralClosedSubspace.bijective_ofTopSubfunctor :
    Function.Bijective (IntegralClosedSubspace.ofTopSubfunctor B S hS hX hXdec) :=
  ⟨IntegralClosedSubspace.injective_pushforward B S hS hX _ hXdec _, fun W =>
    IntegralClosedSubspace.exists_pushforward_eq B S hS hX
      (isClosedSubspace_top_subfunctor B S hS hX).1 hXdec
      (isDecentSpace_of_iso B S hS (asIso (⊤ : Subfunctor X).ι).symm hXdec)
      (isClosedSubspace_top_subfunctor B S hS hX).2 W fun x _ =>
        pointsMap_surjective_of_isIso B S hS _ x⟩

/-- The bijection between the integral closed subspaces of `(⊤ : Subfunctor X).toFunctor` and
those of `X`. -/
def IntegralClosedSubspace.topSubfunctorEquiv :
    IntegralClosedSubspace B S hS (⊤ : Subfunctor X).toFunctor ≃
      IntegralClosedSubspace B S hS X :=
  Equiv.ofBijective _ (IntegralClosedSubspace.bijective_ofTopSubfunctor B S hS hX hXdec)

@[simp]
theorem IntegralClosedSubspace.topSubfunctorEquiv_apply
    (W : IntegralClosedSubspace B S hS (⊤ : Subfunctor X).toFunctor) :
    IntegralClosedSubspace.topSubfunctorEquiv B S hS hX hXdec W =
      IntegralClosedSubspace.ofTopSubfunctor B S hS hX hXdec W :=
  rfl

end Transport

/-! ### The δ-dimension and the multiplicity through the transport -/

section Multiplicity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)

/-- **The transport preserves the δ-dimension**, the structure morphism of
`(⊤ : Subfunctor X).toFunctor` being the inclusion `(⊤ : Subfunctor X).ι` followed by `sX`. -/
theorem IntegralClosedSubspace.deltaDimension_ofTopSubfunctor
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem (⊤ : Subfunctor X).toFunctor) :
    deltaDimension D sX
        (IntegralClosedSubspace.ofTopSubfunctor D.site D.base D.base_mem hX hXdec W) =
      deltaDimension D ((⊤ : Subfunctor X).ι ≫ sX) W :=
  IntegralClosedSubspace.deltaDimension_pushforward D sX hsX hX _ hXdec _ W

/-- **The multiplicity `m_{X', X}` of an integral closed subspace of `X` in `X` itself**: the
multiplicity of Stacks 0EE9 of the closed subspace `⊤ ⊆ X`, read at the integral closed subspace
of `(⊤ : Subfunctor X).toFunctor` corresponding to `X'`.

This is the coefficient of the right-hand side of Stacks 0EQA, which is indexed by the
irreducible components of `X` and not by integral closed subspaces of a subfunctor. -/
def multiplicityInAmbient (X' : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  closedSubspaceMultiplicity D (⊤ : Subfunctor X)
    (isClosedSubspace_top_subfunctor D.site D.base D.base_mem hX)
    ((IntegralClosedSubspace.topSubfunctorEquiv D.site D.base D.base_mem hX hXdec).symm X')

/-- **The multiplicity of `W` in `⊤` is the multiplicity in `X` of the integral closed subspace
of `X` it transports to.** -/
theorem closedSubspaceMultiplicity_top_eq_multiplicityInAmbient
    (W : IntegralClosedSubspace D.site D.base D.base_mem (⊤ : Subfunctor X).toFunctor) :
    closedSubspaceMultiplicity D (⊤ : Subfunctor X)
        (isClosedSubspace_top_subfunctor D.site D.base D.base_mem hX) W =
      multiplicityInAmbient D hX hXdec
        (IntegralClosedSubspace.ofTopSubfunctor D.site D.base D.base_mem hX hXdec W) := by
  simp [multiplicityInAmbient, IntegralClosedSubspace.topSubfunctorEquiv]

end Multiplicity

end AlgebraicGeometry.Space

end
