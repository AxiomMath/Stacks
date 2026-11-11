module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableFromDiagonal

/-!
# The final bootstrap: a flat chart and a representable diagonal

[Stacks, Tag 04S6] lists six conditions on a functor `F` on the big fppf site of a scheme `S`,
each of which implies that `F` is an algebraic space.  Conditions (5) and (6) are the two that
assume something about the diagonal of `F`:

* (5) `F` is a sheaf, `Δ_F` is representable by algebraic spaces, and there is an algebraic
  space `X` over `S` and a morphism `X ⟶ F` which is surjective, flat and locally of finite
  presentation;
* (6) `F` is a sheaf, `Δ_F` is representable, and there is a scheme `U` over `S` and a
  morphism `h_U ⟶ F` which is surjective, flat and locally of finite presentation.

Neither condition assumes the chart to be representable by algebraic spaces — that is what
distinguishes them from conditions (3) and (4), and the assumption on the diagonal is what
replaces it.  This module proves that the replacement works: a representable diagonal makes
*every* morphism to `F` from an algebraic space representable by algebraic spaces, by the two
halves of [Stacks, Tag 03Y2], so conditions (5) and (6) carry the data that condition (3)
consumes.

The unconditional step -- if `Δ_F` is representable by algebraic spaces then every morphism to
`F` from an algebraic space over `S` is representable by algebraic spaces -- is
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_diagonal`, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentableFromDiagonal.lean`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_diag_of_flat_chart` is [Stacks, Tag 04S6]
  condition (5).
* `AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_diag_of_flat_scheme_chart`
  is [Stacks, Tag 04S6] condition (6).
* `Space.isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective_unconditional`
  is [Stacks, Tag 0AMP], with nothing carried.

## Implementation notes

Condition (3) of the source is
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`, derived from condition
(1), `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/Unconditional.lean`.  Conditions
(5) and (6) are reduced to it here, as in the source: a representable diagonal supplies the
representability of the chart that condition (3) needs, by Stacks 03Y2.

The two theorems below take the diagonal as a hypothesis rather than deriving it from Stacks
046K, because that is what conditions (5) and (6) of the source assume.

The properties of the chart are read through `AlgebraicGeometry.Space.HasProperty`, which takes
a witness of representability by algebraic spaces as an argument.  Conditions (5) and (6) do
not assume one, so the witness used is the one produced by
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_diagonal` from the hypothesis on the
diagonal.  Since `IsAlgebraicSpace` is a `Prop`, the choice of witness does not affect the
statement.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0AMP](https://stacks.math.columbia.edu/tag/0AMP)
* [Stacks Project, Tag 03Y2](https://stacks.math.columbia.edu/tag/03Y2)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04S6, condition (5).** Let `F` be a sheaf on the big fppf site of a scheme `S`
whose absolute diagonal is representable by algebraic spaces, and suppose there is an algebraic
space `X` over `S` and a morphism `f : X ⟶ F` which is surjective, flat and locally of finite
presentation.  Then `F` is an algebraic space over `S`.

The chart `f` is not assumed to be representable by algebraic spaces; it is so automatically, by
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_diagonal`, which is what turns the
data of condition (5) into the data of condition (3). -/
@[stacks 04S6 "condition (5)"]
theorem isAlgebraicSpace_of_diag_of_flat_chart
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ F)
    (hSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag hX f))
    (hFlat : HasProperty B S hS (flatProperty B S hS) f
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag hX f))
    (hLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag hX f)) :
    IsAlgebraicSpace B S hS F :=
  isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS f hF hX
    (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag hX f) hSurj hFlat hLfp

/-- **Stacks 04S6, condition (6).** Let `F` be a sheaf on the big fppf site of a scheme `S`
whose absolute diagonal is representable, and suppose there is a scheme `U` over `S` and a
morphism `f : h_U ⟶ F` which is surjective, flat and locally of finite presentation.  Then `F`
is an algebraic space over `S`.

This is condition (5) for the algebraic space `h_U`: a representable diagonal is representable
by algebraic spaces by
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable`, and a
representable presheaf is an algebraic space by **Stacks 025Z**. -/
@[stacks 04S6 "condition (6)"]
theorem isAlgebraicSpace_of_relativelyRepresentable_diag_of_flat_scheme_chart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hdiag : yoneda.relativelyRepresentable (diag F))
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS
        (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hdiag)
        (isAlgebraicSpace_yoneda B S hS U) f))
    (hFlat : HasProperty B S hS (flatProperty B S hS) f
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS
        (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hdiag)
        (isAlgebraicSpace_yoneda B S hS U) f))
    (hLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS
        (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hdiag)
        (isAlgebraicSpace_yoneda B S hS U) f)) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_diag_of_flat_chart B S hS hF
    (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hdiag)
    (isAlgebraicSpace_yoneda B S hS U) f hSurj hFlat hLfp

/-- **Stacks 0AMP.** Let `a : F ⟶ G` and `b : G ⟶ H` be morphisms of presheaves on the big fppf
site of `S`, with `G` and `H` sheaves.  If `a` is representable by algebraic spaces, surjective,
flat and locally of finite presentation and the composite `a ≫ b` is representable by algebraic
spaces, then `b` is representable by algebraic spaces.

At a scheme-valued point `ξ` of `H` the fibre product `U ×_H F` is an algebraic space, being a
base change of `a ≫ b`, and `U ×_H G` is a sheaf.  The morphism `U ×_H F ⟶ U ×_H G` is the base
change of `a` along `U ×_H G ⟶ G`, so Stacks 046F gives it the three properties of `a`, and
Stacks 04S6 condition (3) makes `U ×_H G` an algebraic space; that deduction is
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective`, whose
bootstrap input is discharged here by
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.

Sheafness of `F` is assumed in the source and is not needed here: representability of `a ≫ b`
already makes the base changes of `F` that the argument uses algebraic spaces.

This is the complete statement of Stacks 0AMP and its only registration; nothing is assumed. -/
@[stacks 0AMP]
theorem isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective_unconditional
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (haRep : IsRepresentableByAlgebraicSpaces B S hS a)
    (haSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a haRep)
    (haFlat : HasProperty B S hS (flatProperty B S hS) a haRep)
    (haLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) a haRep)
    (hcomp : IsRepresentableByAlgebraicSpaces B S hS (a ≫ b)) :
    IsRepresentableByAlgebraicSpaces B S hS b :=
  isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective B S hS
    (isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS) a b hG hH haRep haSurj haFlat haLfp
    hcomp

end AlgebraicGeometry.Space

end
