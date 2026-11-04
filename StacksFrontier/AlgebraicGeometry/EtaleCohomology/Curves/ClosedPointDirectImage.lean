module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage

/-!
# The direct image at a point, and the skyscraper sheaf `ℤ` it carries

The divisor sequence of Stacks 03RM on a curve `X`,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0`,
has one summand of its third term for each closed point `x` of `X`, namely the direct image
along `i_x : Spec κ(x) ⟶ X` of the constant sheaf `ℤ` on the small étale site of the residue
field. This file constructs that summand, and records the exactness properties of the direct
image that the sequence needs.

Nothing here is special to a closed immersion. The direct image
`Stacks.EtaleCohomology.etaleAbelianDirectImage` is defined for an arbitrary morphism of schemes,
so `i_{x,*}` is an instance of it, as is `j_*` at the generic point; the only thing a closed
immersion would buy is exactness of `i^{-1}`, which is not used to state the sequence.

## Main definitions

* `Stacks.EtaleCohomology.residueFieldDirectImage`: `i_{x,*}` along `Spec κ(x) ⟶ X`.
* `Stacks.EtaleCohomology.integerSkyscraper`: the sheaf `i_{x,*} ℤ`, a summand of the third term
  of the divisor sequence.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDirectImage_preservesLimits` and
  `Stacks.EtaleCohomology.etaleAbelianDirectImage_additive`: the direct image preserves limits
  and is additive, being a right adjoint between abelian categories. Left exactness of `i_*` is
  what makes the divisor sequence exact on the left once its first map is a monomorphism.
* `Stacks.EtaleCohomology.integerSkyscraper_obj_obj`: the sections of `i_{x,*} ℤ` over an étale
  `X`-scheme `U` are the sections of the constant sheaf `ℤ` over the fibre `U ×_X Spec κ(x)`.

## Implementation notes

The coefficient `ℤ` is `AddCommGrpCat.of (ULift ℤ)` raised to the universe
`max (u + 1) v` in which this library computes étale cohomology; this is the same group that
`CategoryTheory.Sheaf.H` takes its `Ext` from, so the skyscraper here is the one whose cohomology
the dévissage of 03RM compares against.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section Exactness

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- **The direct image on abelian sheaves of small étale sites preserves limits**, being a right
adjoint. In particular it is left exact, which is what makes the left end of the divisor sequence
of Stacks 03RM exact. -/
instance etaleAbelianDirectImage_preservesLimits :
    PreservesLimitsOfSize.{max (u + 1) v, max (u + 1) v}
      (etaleAbelianDirectImage.{u, v} i) :=
  (etaleAbelianInverseImageDirectImageAdj.{u, v} i).rightAdjoint_preservesLimits

/-- The direct image on abelian sheaves of small étale sites is additive, since it preserves
binary products. -/
instance etaleAbelianDirectImage_additive :
    (etaleAbelianDirectImage.{u, v} i).Additive :=
  Functor.additive_of_preserves_binary_products _

end Exactness

section Skyscraper

variable (X : Scheme.{u}) (x : X)

/-- **The direct image `i_{x,*}` along the inclusion of a point** `i_x : Spec κ(x) ⟶ X` of a
scheme, on abelian sheaves of the small étale sites. Its sections over an étale `X`-scheme `U`
are the sections over the fibre `U ×_X Spec κ(x)`. -/
abbrev residueFieldDirectImage :
    Sheaf (Spec (X.residueField x)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  etaleAbelianDirectImage.{u, v} (X.fromSpecResidueField x)

/-- **The skyscraper sheaf `i_{x,*} ℤ` at a point** of a scheme: the direct image along
`Spec κ(x) ⟶ X` of the constant sheaf `ℤ` on the small étale site of the residue field. For `x`
a closed point of a curve this is one summand of the third term of the divisor sequence of
Stacks 03RM. -/
abbrev integerSkyscraper : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (residueFieldDirectImage.{u, v} X x).obj
    ((constantSheaf (Spec (X.residueField x)).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift ℤ)))

/-- The sections of the skyscraper sheaf `i_{x,*} ℤ` over an étale `X`-scheme `U` are the
sections of the constant sheaf `ℤ` over the fibre `U ×_X Spec κ(x)`. -/
theorem integerSkyscraper_obj_obj (U : X.Etale) :
    (integerSkyscraper.{u, v} X x).obj.obj (op U) =
      ((constantSheaf (Spec (X.residueField x)).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift ℤ))).obj.obj
          (op ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U)) :=
  rfl

end Skyscraper

end Stacks.EtaleCohomology

end
