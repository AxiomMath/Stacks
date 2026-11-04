module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties

/-!
# Flattening a morphism of finite type by a blowup: the conclusion

Let `f : X ⟶ A` be a morphism of algebraic spaces over `S` and `U ⊆ A` an open subspace.  We
say that `f` *is flattened over `U` by a blowup* when there are a closed subspace `Z ⊆ A` of
finite presentation whose points avoid those of `U` and a blowup `b : A' ⟶ A` of `A` in `Z`
such that the strict transform of `X` with respect to `b` is flat and locally of finite
presentation over `A'`.  This is the conclusion of Stacks 087E, up to quasi-compactness and
quasi-separatedness of the strict transform, which come for free when `f` is of finite type
and quasi-separated.

## Main definitions

* `AlgebraicGeometry.Space.FlattensByBlowup`: the property above.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `f : X ⟶ A` is flattened over the open subspace `U ⊆ A` by a `U`-admissible blowup: there
are a finitely presented closed subspace `Z ⊆ A` disjoint from `U` and a blowup `b : A' ⟶ A` in
`Z` along which the strict transform of `X` is flat and locally of finite presentation over
`A'`. -/
abbrev FlattensByBlowup {A X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1) : Prop :=
  ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
    IsFinitePresentation B S hS Z.1.ι ∧
      Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
        IsBlowupAlong B S hS Z b ∧
          IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom ∧
            IsLocallyOfFinitePresentation B S hS
              (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom

end AlgebraicGeometry.Space

end
