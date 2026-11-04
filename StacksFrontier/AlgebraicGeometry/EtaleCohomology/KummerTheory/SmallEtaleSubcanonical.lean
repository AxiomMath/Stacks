module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleGlobalFunctions
import StacksFrontier.AlgebraicGeometry.Topologies.Etale.RepresentableSheaves
import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageRepresentable

/-!
# Representable presheaves on the small étale site

A Grothendieck topology is subcanonical when every representable presheaf is a sheaf.  For the
étale topology on schemes and for the small étale site of a scheme this is
`AlgebraicGeometry.Scheme.etaleTopology_subcanonical` and
`AlgebraicGeometry.Scheme.subcanonical_smallEtaleTopology`, imported here.  This file supplies
the consequence that is actually used: a presheaf on the small étale site of `X` obtained by
restricting a representable presheaf on `Over X` is a sheaf.

That consequence is what makes group schemes over `X` into sheaves on the small étale site of
`X`.  The functor of points of an `X`-scheme `T` is a representable presheaf on `Over X`; the
small étale site is not an over-category, so subcanonicity of the small étale site alone would
only give the sheaf condition for the `T` that happen to be étale over `X`, which excludes
`𝐆_m` and `μ_n`.

## Main results

* `AlgebraicGeometry.Scheme.locallyCoverDense_etaleForget`: the forgetful functor from the
  small étale site of `X` to `Over X` is locally cover dense for the étale topology localized
  at `X`.
* `AlgebraicGeometry.Scheme.isSheaf_smallEtale_comp_of_isRepresentable`: the restriction to the
  small étale site of a representable presheaf on `Over X` is a sheaf.

## Implementation notes

Subcanonicity of the small étale site alone would only give the sheaf condition for those `T`
that happen to be étale over `X`, which excludes `𝐆_m` and `μ_n`; restricting a representable
presheaf on `Over X` along the forgetful functor is what covers them, and that needs the functor
to be continuous as well as the étale topology localized at `X` to be subcanonical.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T): descent of morphisms
  of schemes, of which subcanonicity of a topology of schemes is the sheaf-theoretic reading.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor from the small étale site of `X` to `X`-schemes is locally cover
dense for the étale topology localized at `X`: an étale covering of an étale `X`-scheme can be
refined by one whose members are again étale over `X`. -/
instance locallyCoverDense_etaleForget (X : Scheme.{u}) :
    (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.{u}.over X) :=
  Scheme.locallyCoverDense_of_le X le_rfl

/-- **A representable presheaf on `X`-schemes restricts to a sheaf on the small étale site of
`X`.**  Together with a representation of a group-valued functor this is what exhibits a group
scheme over `X` as a sheaf of groups on the small étale site, for group schemes that are not
themselves étale over `X`. -/
theorem isSheaf_smallEtale_comp_of_isRepresentable (X : Scheme.{u}) (P : (Over X)ᵒᵖ ⥤ Type w)
    [P.IsRepresentable] :
    Presieve.IsSheaf X.smallEtaleTopology ((Scheme.Etale.forget X).op ⋙ P) :=
  (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf_type _
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.etaleTopology.{u}.over X) P)

end AlgebraicGeometry.Scheme

end
