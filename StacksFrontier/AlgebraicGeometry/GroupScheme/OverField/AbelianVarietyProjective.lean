module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveOverAmpleBase
public import StacksCore.Tactic.StacksAttribute

/-!
# Abelian varieties are projective

Let `k` be a field. An abelian variety over `k` is projective over `k`, in the sense of the first
condition of Tag 01W8: it is a closed subscheme of the projective bundle of a quasi-coherent
`𝒪_{Spec k}`-module of finite type.

## Main results

* `AlgebraicGeometry.isProjective_of_isQuasiProjective_of_isProper_over_field`: a proper,
  quasi-projective morphism to the spectrum of a field is projective.
* `AlgebraicGeometry.isProjective_of_isAbelianVariety`: an abelian variety over a field is
  projective.  This is also part (1) of Tag 03RP.

## Implementation notes

The source's proof cites two results. Tag 0BF7 makes the abelian variety, an algebraic group
scheme, quasi-projective over `k`; it is
`AlgebraicGeometry.isQuasiProjective_of_groupScheme_over_field`, applied to the group object
`CategoryTheory.Grp.mk A`, whose underlying object is `A` itself. Tag 0B45, conditions
(3) ⟹ (1), turns a quasi-projective proper morphism into a projective one over a base carrying an
ample invertible sheaf; it is `AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple`, and
the base `Spec k` is affine, so its structure sheaf is ample (Tag 01QE), which is
`Stacks.HProjective.exists_isAmple_of_isAffine`.

## References

* [Stacks Project, Tag 0BFA](https://stacks.math.columbia.edu/tag/0BFA)
* [Stacks Project, Proposition 39.9.11 (Tag 03RP)](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BF7](https://stacks.math.columbia.edu/tag/0BF7)
* [Stacks Project, Tag 0B45](https://stacks.math.columbia.edu/tag/0B45)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A proper, quasi-projective morphism to the spectrum of a field is projective.

This is conditions (3) ⟹ (1) of Tag 0B45 over the affine base `Spec k`, whose structure sheaf is
ample by Tag 01QE. -/
theorem isProjective_of_isQuasiProjective_of_isProper_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hq : IsQuasiProjective f) [IsProper f] :
    IsProjective f := by
  have h := (isProjective_tfae_seven_of_exists_isAmple f
    (Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k)))).out 1 3
  exact h.mpr ⟨hq, inferInstance⟩

/-- **Stacks Project, Tag 0BFA.** Let `k` be a field and let `A` be an abelian variety over `k`.
Then `A` is projective over `k`.

An abelian variety is an algebraic group scheme over `k`, hence quasi-projective over `k` by
Tag 0BF7, and it is proper over `k`, so Tag 0B45 makes it projective over the affine base
`Spec k`. -/
@[stacks 0BFA]
theorem isProjective_of_isAbelianVariety (k : Type u) [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsAbelianVariety k A] : IsProjective A.hom := by
  have : LocallyOfFiniteType (Grp.mk A).X.hom := inferInstanceAs (LocallyOfFiniteType A.hom)
  have : QuasiCompact (Grp.mk A).X.hom := inferInstanceAs (QuasiCompact A.hom)
  exact isProjective_of_isQuasiProjective_of_isProper_over_field k A.hom
    (isQuasiProjective_of_groupScheme_over_field (Grp.mk A))

end AlgebraicGeometry

add_to_stacks 03RP "projective" AlgebraicGeometry.isProjective_of_isAbelianVariety

end
