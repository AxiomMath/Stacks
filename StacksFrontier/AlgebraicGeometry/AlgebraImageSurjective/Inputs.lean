module

public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Algebra
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.Directedness

/-!
# Input 2 of [Stacks, Tag 05JT] is discharged

`StacksFrontier/AlgebraicGeometry/FiniteTypeSubalgebraJoin/Directedness.lean` reduces both
assertions of [Stacks, Tag 05JT] to three named inputs.  This file discharges the second of
them, `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.ImageIsLocallySurjective`, from
`Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_algebraSheaf`, and records
what that alone buys: **nonemptiness of the finite type quasi-coherent subalgebras of a
quasi-coherent algebra sheaf now needs only Input 1.**

Nonemptiness is the one consumer of the three that does not touch the coproduct.  Its witness is
the image of the initial algebra sheaf `𝒪_X`, whose structure morphism is an identity, so there
is no tensor product to identify and Input 3 does not
appear.  The two directedness and colimit consumers still carry Input 1 and Input 3.

## Main results

* `Stacks.AlgebraImageSurjective.imageIsLocallySurjective`: **Input 2, discharged**, with no
  hypothesis on `X` whatsoever.
* `Stacks.AlgebraImageSurjective.nonempty_finiteTypeSubalgebra_of_imageIsQuasicoherent`:
  nonemptiness of `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.FiniteTypeSubalgebra A` from
  Input 1 alone.
* `Stacks.AlgebraImageSurjective.isFiltered_of_imageIsQuasicoherent_of_dominating` and
  `Stacks.AlgebraImageSurjective.nonempty_isColimit_of_imageIsQuasicoherent`: the two assertions
  of the tag with the Input 2 slot filled, so that what remains outstanding is visible in the
  statement.

## Implementation notes

The three inputs are `Prop`-valued definitions universally quantified over the morphism, so each
discharge is a `fun` abstraction over the quantifiers followed by the corresponding theorem.
`ImageIsLocallySurjective` quantifies over the two algebra sheaves *explicitly* while
`isLocallySurjective_factorThruImage_algebraSheaf` takes them implicitly, which is why the
discharge is written with two `_` binders rather than as a bare name.

**No stacks attribute is attached.**  No assertion of [Stacks, Tag 05JT] is proved
unconditionally here: Input 1 remains a hypothesis of every statement below except the discharge
of Input 2 itself, and Input 3 remains a hypothesis of the directedness and colimit statements.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec
open Stacks.AlgebraicGeometry.FiniteTypeSubalgebras

universe u

namespace Stacks.AlgebraImageSurjective

/-- **Input 2 of [Stacks, Tag 05JT], discharged.**  The corestriction of a morphism of algebra
sheaves to its image is locally surjective, with no hypothesis on the scheme and none on the
algebra sheaves. -/
theorem imageIsLocallySurjective (X : Scheme.{u}) : ImageIsLocallySurjective X :=
  fun _ _ φ => isLocallySurjective_factorThruImage_algebraSheaf φ

/-- **The finite type quasi-coherent subalgebras of a quasi-coherent algebra sheaf are nonempty,
granted Input 1 alone.**  Input 2 is supplied by `imageIsLocallySurjective` and Input 3 is not
needed: the witness is the image of the initial algebra sheaf, so no coproduct occurs. -/
theorem nonempty_finiteTypeSubalgebra_of_imageIsQuasicoherent {X : Scheme.{u}}
    (h₁ : ImageIsQuasicoherent X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : Nonempty (FiniteTypeSubalgebra A) :=
  nonempty_finiteTypeSubalgebra h₁ (imageIsLocallySurjective X) A hA

/-- **The directedness assertion of [Stacks, Tag 05JT] with the Input 2 slot filled.**  What
remains are Input 1 and the dominating form of Input 3. -/
theorem isFiltered_of_imageIsQuasicoherent_of_dominating {X : Scheme.{u}}
    (h₁ : ImageIsQuasicoherent X) (h₃ : ExistsFiniteTypeDominating X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : IsFiltered (FiniteTypeSubalgebra A) :=
  isFiltered_of_dominating h₁ (imageIsLocallySurjective X) h₃ A hA

/-- **The colimit assertion of [Stacks, Tag 05JT] with the Input 2 slot filled.**  What remains
are Input 1, Input 3 in its coproduct form, and the affine sections statement. -/
theorem nonempty_isColimit_of_imageIsQuasicoherent {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (h₁ : ImageIsQuasicoherent X)
    (h₃ : CoprodIsQuasicoherentFiniteType X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A)
    (hsec : ∀ U : X.Opens, IsAffineOpen U → ∀ x : A.right.obj.obj (op U),
      ∃ (B : FiniteTypeSubalgebra A) (y : (B.obj : AlgebraSheaf X).right.obj.obj (op U)),
        (B.obj.arrow.right.hom.app (op U)) y = x) :
    Nonempty (IsColimit (finiteTypeSubalgebraCocone A)) :=
  nonempty_isColimit_of_imageData h₁ (imageIsLocallySurjective X) h₃ A hA hsec

end Stacks.AlgebraImageSurjective
