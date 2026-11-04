module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints

/-!
# Separatedness of an affine elementary étale neighborhood

An elementary étale neighborhood `(U, u) ⟶ (X, x)` of a point of an algebraic space whose
scheme `U` is affine is a separated morphism of algebraic spaces. The relative diagonal of
`U ⟶ X` is a base change of the diagonal of `U` over the base, and the latter is a closed
immersion because an affine scheme is separated; neither the étaleness of `U ⟶ X` nor any
property of `X` beyond being a presheaf enters.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.isSeparated_toSpace`: an elementary
  étale neighborhood with affine scheme is a separated morphism of algebraic spaces.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isSeparated_toSpaceHom`: each of the
  chosen neighborhoods `Uᵢ ⟶ X` of a family of closed points is separated.

## Implementation notes

This is the separatedness hypothesis of Stacks 0BGY for the neighborhoods chosen in the
strategy of Stacks 0BH9. The strategy lists affineness of `Uᵢ`, étaleness of `Uᵢ ⟶ X`,
uniqueness of `uᵢ` above `xᵢ` and monicity of `Spec κ(uᵢ) ⟶ X` but not separatedness, which
is derived here from affineness alone.

The derivation is `AlgebraicGeometry.Space.isSeparated_of_isEtale_of_scheme_isSeparated`, the
first assertion of Stacks 03FZ, applied to the affine scheme of the neighborhood: an affine
scheme is a separated scheme, so the presheaf it represents is separated over the base and
every morphism out of that presheaf is separated. Decency of the target space is therefore
not used, and neither is the uniqueness of the point above `x` nor the monomorphism
representing it.

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An elementary étale neighborhood with affine scheme is a separated morphism.** An affine
scheme is separated over the base, so the presheaf it represents is separated over the base and
every morphism out of that presheaf has a closed immersion for its relative diagonal. -/
theorem ElementaryEtaleNeighborhood.isSeparated_toSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    {x : points B S hS X} (E : ElementaryEtaleNeighborhood B S hS X hX x)
    (hAff : IsAffine E.scheme.left.1) :
    IsSeparated B S hS E.toSpace :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj E.scheme) := hAff
  isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX E.scheme inferInstance
    E.toSpace E.etale_toSpace

namespace ClosedPointNeighborhoods

variable {B S hS} {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **Each chosen neighborhood of a family of closed points is separated over the space.** The
neighborhoods chosen in the strategy of Stacks 0BH9 have affine schemes, which is what makes
`Uᵢ ⟶ X` separated and so lets Stacks 0BGY be applied to it. -/
theorem isSeparated_toSpaceHom (i : Fin n) : IsSeparated B S hS (D.toSpaceHom i).hom :=
  (D.neighborhood i).isSeparated_toSpace B S hS (D.isAffine_neighborhood i)

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
