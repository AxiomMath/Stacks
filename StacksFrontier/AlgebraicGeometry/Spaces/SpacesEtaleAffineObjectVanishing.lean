module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSpacesEtaleGlobalVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite

/-!
# Serre vanishing at an affine object of the spaces-étale site of an algebraic space

Let `X` be an algebraic space over a scheme `S`, let `U` be an object of the spaces-étale site
`X_{spaces,étale}` of [Stacks, Tag 03G0] whose underlying algebraic space is **affine**, and let
`F` be a quasi-coherent module on `U`.  Then

  `H^q(U, F) = 0` for every `q > 0`.

This is the positive-degree clause of Descent, Proposition 03DW on the spaces-étale site — the
cohomological input that the proof of [Stacks, Tag 072C] takes from [Stacks, Tag 01XB] through
the discussion of [Stacks, Tag 071Y], and the one condition (3) of [Stacks, Tag 0DC4] asks of the
family of quasi-coherent modules on the slices of the spaces-étale site.

## What the statement is

*The cohomology.*  `H^q(U, F)` is the global cohomology `CategoryTheory.Sheaf.H` of the
localization `(X_{spaces,étale})/U` of the spaces-étale site at `U`, which is cohomology over `U`
in the sense of `Stacks.Cohomology.OverObjectCohomology.h'IsoHOver`.  It is *not* written as
`CategoryTheory.Sheaf.H'` over the object `U`, and that is forced rather than chosen: `Sheaf.H'`
pins its coefficients to the morphism universe of the site, which for the spaces-étale site is
`u + 1`, whereas the sections of a quasi-coherent module live in the universe `u` of the
structure rings, and `Ext` admits no comparison between abelian sheaves at those two coefficient
universes.  `Sheaf.H` is free in its coefficient universe, so it is the shape in which the two
sites can be compared at all.

*The coefficients.*  A quasi-coherent module on `U` is a quasi-coherent `𝒪_U`-module in the sense
of [Stacks, Tag 03G9], that is, an object of
`AlgebraicGeometry.Space.QuasicoherentSheaves` for the algebraic space underlying `U`: a sheaf of
modules on the small étale ringed site of that space which is quasi-coherent,
`SheafOfModules.IsQuasicoherentOnSite`, which is clause (6) of [Stacks, Tag 03DL].  It is read on
the slice of the spaces-étale site at `U` by
`AlgebraicGeometry.Space.spacesEtaleSliceSheaf`, the composite of the comparison of
[Stacks, Tag 03G1] with the identification of [Stacks, Tag 04LY] of the slice at `U` with the
spaces-étale site of `U`; both are equivalences of topoi, so this is a reading and not a
restriction of generality.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleSliceSheaf`: the abelian sheaf on the slice of the
  spaces-étale site of `X` at `U` determined by an abelian sheaf on the small étale site of the
  algebraic space underlying `U`.

## Main results

* `AlgebraicGeometry.Space.subsingleton_sheafH_slice_of_isQuasicoherentOnSite`: **the vanishing,
  for every `q > 0`, at every affine object of the spaces-étale site, of the cohomology of every
  quasi-coherent module.**
* `AlgebraicGeometry.Space.subsingleton_sheafH_slice_of_isQuasicoherentOnSite_of_isAffineScheme`:
  the same, with affineness of the object stated as
  `AlgebraicGeometry.Space.SpacesEtale.IsAffineScheme`, the predicate the cover-density of the
  affine objects is proved for.
* `AlgebraicGeometry.Space.subsingleton_sheafH_slice_of_iso_of_isQuasicoherentOnSite`: the same
  for any abelian sheaf on the slice isomorphic to that reading.
* `AlgebraicGeometry.Space.isAffineSpace_of_isAffineScheme`: the two readings of affineness of an
  object of the spaces-étale site agree.

## Implementation notes

The two transports are
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_functor`, along the comparison of
[Stacks, Tag 03G1], carried out in
`StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSpacesEtaleGlobalVanishing`, and
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_sheafCongr_inverse`, along the
identification of [Stacks, Tag 04LY] of `Over U` with the spaces-étale site of `U`, carried out
here.  The second is the equivalence-of-sites form, not the dense-subsite form: `Over U` and the
spaces-étale site of `U` both have their morphisms in `Type (u + 1)` while the coefficients are
`AddCommGrpCat.{u}`, so the right Kan extension that
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` is built from is unavailable, whereas
`CategoryTheory.Equivalence.sheafCongr` needs nothing.

The dense-subsite property of the *inverse* of that identification, which
`CategoryTheory.Equivalence.sheafCongr` asks for, is obtained from
`CategoryTheory.Equivalence.isDenseSubsite_inverse_of_isCocontinuous`, whose two cocontinuity
hypotheses are the one a dense subsite inclusion already has and, for the inverse, cover
preservation of the functor read through the adjunction
`CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving`.  That is the route
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent` takes for [Stacks, Tag
04M0].

Sheafification of `AddCommGrpCat.{u}`-valued presheaves on the slice is transported along that
same identification by `CategoryTheory.Equivalence.hasSheafify`; the `Ext`-groups are the
standard ones, both sheaf categories being `Type (u + 1)`-sized with `Type (u + 1)` morphisms.

The terminal objects the transport needs are `CategoryTheory.Over.mkIdTerminal` on the slice and
its image, terminal because the identification is an equivalence of categories.

No `@[stacks]` attribute is claimed.  [Stacks, Tag 03DW] is a statement about schemes in the five
topologies and is already registered elsewhere in this tree; what is here is the positive-degree
vanishing on the spaces-étale site of an algebraic space, which is the role that proposition plays
in the proofs of [Stacks, Tag 072B] and [Stacks, Tag 072C].

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 071Y](https://stacks.math.columbia.edu/tag/071Y)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 04LY](https://stacks.math.columbia.edu/tag/04LY)
* [Stacks Project, Tag 0DC4](https://stacks.math.columbia.edu/tag/0DC4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X)

attribute [local instance] enoughInjectives_sheaf_smallEtale
  hasExt_sheaf_smallEtale

/-- The identification of [Stacks, Tag 04LY] of the slice of the spaces-étale site of `X` at `U`
with the spaces-étale site of the algebraic space underlying `U` is cocontinuous: a dense
subsite inclusion is. -/
instance isCocontinuous_sliceEquivSmall_functor :
    (SpacesEtale.sliceEquivSmall B S hS U).functor.IsCocontinuous
      ((SpacesEtale.topology B S hS X).over U)
      (SpacesEtale.topology B S hS U.obj.left) :=
  inferInstanceAs ((SpacesEtale.sliceToSmall B S hS U).IsCocontinuous _ _)

/-- The inverse of the identification of [Stacks, Tag 04LY] is cocontinuous: through the
adjunction it provides, this is cover preservation of the identification itself. -/
instance isCocontinuous_sliceEquivSmall_inverse :
    (SpacesEtale.sliceEquivSmall B S hS U).inverse.IsCocontinuous
      (SpacesEtale.topology B S hS U.obj.left)
      ((SpacesEtale.topology B S hS X).over U) :=
  (Adjunction.isCocontinuous_iff_coverPreserving
      (SpacesEtale.topology B S hS U.obj.left)
      ((SpacesEtale.topology B S hS X).over U)
      (SpacesEtale.sliceEquivSmall B S hS U).symm.toAdjunction).2
    (Functor.IsDenseSubsite.coverPreserving
      ((SpacesEtale.topology B S hS X).over U)
      (SpacesEtale.topology B S hS U.obj.left)
      (SpacesEtale.sliceToSmall B S hS U))

/-- The inverse of the identification of [Stacks, Tag 04LY] is a dense subsite inclusion of the
spaces-étale site of the algebraic space underlying `U` into the slice at `U`. -/
instance isDenseSubsite_smallToSlice :
    (SpacesEtale.sliceEquivSmall B S hS U).inverse.IsDenseSubsite
      (SpacesEtale.topology B S hS U.obj.left)
      ((SpacesEtale.topology B S hS X).over U) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous
    ((SpacesEtale.topology B S hS X).over U)
    (SpacesEtale.topology B S hS U.obj.left)
    (SpacesEtale.sliceEquivSmall B S hS U)

/-- Sheafification of `AddCommGrpCat.{u}`-valued presheaves on the slice of the spaces-étale site
at `U`, transported along the identification of [Stacks, Tag 04LY] from the spaces-étale site of
the algebraic space underlying `U`. -/
instance hasSheafify_spacesEtaleOver_addCommGrp :
    HasSheafify ((SpacesEtale.topology B S hS X).over U) AddCommGrpCat.{u} :=
  Equivalence.hasSheafify ((SpacesEtale.topology B S hS X).over U)
    (SpacesEtale.topology B S hS U.obj.left) (SpacesEtale.sliceEquivSmall B S hS U)
    AddCommGrpCat.{u}

/-- `Ext`-groups of the abelian sheaves on the slice of the spaces-étale site at `U` at the
universe of the structure rings, in the universe `u + 1`. -/
instance hasExt_abelianSheaf_spacesEtaleOver :
    HasExt.{u + 1} (Sheaf ((SpacesEtale.topology B S hS X).over U) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- The identification of [Stacks, Tag 04LY] on abelian sheaves at the universe of the structure
rings: an abelian sheaf on the slice of the spaces-étale site of `X` at `U` is the same thing as
an abelian sheaf on the spaces-étale site of the algebraic space underlying `U`. -/
abbrev sliceSheafCongr :
    Sheaf ((SpacesEtale.topology B S hS X).over U) AddCommGrpCat.{u} ≌
      Sheaf (SpacesEtale.topology B S hS U.obj.left) AddCommGrpCat.{u} :=
  (SpacesEtale.sliceEquivSmall B S hS U).sheafCongr
    ((SpacesEtale.topology B S hS X).over U)
    (SpacesEtale.topology B S hS U.obj.left) AddCommGrpCat.{u}

/-- **The reading, on the slice of the spaces-étale site of `X` at `U`, of an abelian sheaf on
the small étale site of the algebraic space underlying `U`.**

This is the comparison of [Stacks, Tag 03G1] for that algebraic space followed by the
identification of [Stacks, Tag 04LY] of its spaces-étale site with the slice at `U`.  Both are
equivalences of topoi. -/
abbrev spacesEtaleSliceSheaf :
    Sheaf (SmallEtale.topology B S hS U.obj.left.1) AddCommGrpCat.{u} ⥤
      Sheaf ((SpacesEtale.topology B S hS X).over U) AddCommGrpCat.{u} :=
  (spacesEtaleSheafEquiv B S hS U.obj.left).functor ⋙ (sliceSheafCongr B S hS X U).inverse

/-- The image under the identification of [Stacks, Tag 04LY] of the terminal object of the slice
at `U` is a terminal object of the spaces-étale site of the algebraic space underlying `U`: the
identification is an equivalence of categories. -/
def isTerminal_sliceToSmall_mkId :
    IsTerminal ((SpacesEtale.sliceEquivSmall B S hS U).functor.obj (Over.mk (𝟙 U))) :=
  IsTerminal.isTerminalObj (SpacesEtale.sliceEquivSmall B S hS U).functor _ Over.mkIdTerminal

/-- **An object of the spaces-étale site representable by an affine scheme has affine underlying
algebraic space.**  `AlgebraicGeometry.Space.SpacesEtale.IsAffineScheme` records the representing
isomorphism in the category of algebraic spaces and
`AlgebraicGeometry.Space.IsAffineSpace` records it on the underlying presheaves; the inclusion of
the algebraic spaces into the presheaves carries one to the other. -/
theorem isAffineSpace_of_isAffineScheme (hU : SpacesEtale.IsAffineScheme B S hS X U) :
    IsAffineSpace B S hS U.obj.left.1 := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hU
  exact ⟨W, hW, ⟨((ObjectProperty.ι (IsAlgebraicSpace B S hS)).mapIso e).symm⟩⟩

variable {B S hS X U}

/-- **Serre vanishing at an affine object of the spaces-étale site of an algebraic space.**

Let `X` be an algebraic space over a scheme `S`, let `U` be an object of the spaces-étale site of
`X` — an algebraic space étale over `X` — whose underlying algebraic space is affine, and let `K`
be a quasi-coherent `𝒪_U`-module, that is, a quasi-coherent sheaf on `U` in the sense of
[Stacks, Tag 03G9].  Then the cohomology of `K` over `U`, computed on the spaces-étale site of
`X`, vanishes in every positive degree:

  `H^q(U, K) = 0` for all `q > 0`.

Cohomology over `U` is the global cohomology `CategoryTheory.Sheaf.H` of the localization of the
spaces-étale site at `U`, and `K` is read there by
`AlgebraicGeometry.Space.spacesEtaleSliceSheaf`; the module documentation explains both choices.

This is the positive-degree clause of Descent, Proposition 03DW on the spaces-étale site, the
input that [Stacks, Tag 072C] takes from [Stacks, Tag 01XB] through [Stacks, Tag 071Y]. -/
theorem subsingleton_sheafH_slice_of_isQuasicoherentOnSite
    (hU : IsAffineSpace B S hS U.obj.left.1)
    (K : Modules.{u, u} B S hS U.obj.left.1 U.obj.left.2)
    (hK : K.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((spacesEtaleSliceSheaf B S hS X U).obj
        (smallEtaleAbelianSheaf B S hS U.obj.left K)) q) :=
  Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_sheafCongr_inverse
    ((SpacesEtale.topology B S hS X).over U)
    (SpacesEtale.topology B S hS U.obj.left)
    (SpacesEtale.sliceEquivSmall B S hS U)
    Over.mkIdTerminal (isTerminal_sliceToSmall_mkId B S hS X U)
    ((spacesEtaleSheafEquiv B S hS U.obj.left).functor.obj
      (smallEtaleAbelianSheaf B S hS U.obj.left K)) q
    (subsingleton_sheafH_spacesEtale_of_isQuasicoherentOnSite hU K hK q hq)

/-- **Serre vanishing at an affine object of the spaces-étale site**, with affineness of the
object stated as `AlgebraicGeometry.Space.SpacesEtale.IsAffineScheme`, the predicate under which
the affine objects of the spaces-étale site are shown to be cover-dense in
`AlgebraicGeometry.Space.SpacesEtale.generate_affineSchemePresieve_mem`. -/
theorem subsingleton_sheafH_slice_of_isQuasicoherentOnSite_of_isAffineScheme
    (hU : SpacesEtale.IsAffineScheme B S hS X U)
    (K : Modules.{u, u} B S hS U.obj.left.1 U.obj.left.2)
    (hK : K.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((spacesEtaleSliceSheaf B S hS X U).obj
        (smallEtaleAbelianSheaf B S hS U.obj.left K)) q) :=
  subsingleton_sheafH_slice_of_isQuasicoherentOnSite
    (isAffineSpace_of_isAffineScheme B S hS X U hU) K hK q hq

/-- **Serre vanishing at an affine object of the spaces-étale site**, for any abelian sheaf on the
slice isomorphic to the reading of a quasi-coherent module: nothing in the conclusion depends on
how that reading is spelled. -/
theorem subsingleton_sheafH_slice_of_iso_of_isQuasicoherentOnSite
    (hU : IsAffineSpace B S hS U.obj.left.1)
    (K : Modules.{u, u} B S hS U.obj.left.1 U.obj.left.2)
    (hK : K.IsQuasicoherentOnSite)
    (F : Sheaf ((SpacesEtale.topology B S hS X).over U) AddCommGrpCat.{u})
    (e : F ≅ (spacesEtaleSliceSheaf B S hS X U).obj
      (smallEtaleAbelianSheaf B S hS U.obj.left K))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} F q) :=
  Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target e.symm q
    (subsingleton_sheafH_slice_of_isQuasicoherentOnSite hU K hK q hq)

end AlgebraicGeometry.Space

end
