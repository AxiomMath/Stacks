module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSmallEtaleGlobalVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DenseSubsiteGlobalVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre vanishing on an affine algebraic space, globally on its spaces-étale site

Let `X` be an *affine* algebraic space over a scheme `S` and let `K` be a quasi-coherent
`𝒪_X`-module.  This file carries the vanishing of the positive-degree global cohomology of the
abelian sheaf underlying `K` from the **small** étale site of `X`, where it is
`AlgebraicGeometry.Space.subsingleton_sheafH_of_isQuasicoherentOnSite`, to the **spaces-étale**
site of `X`, across the comparison of [Stacks, Tag 03G1].

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleSheafEquiv`: the equivalence of [Stacks, Tag 03G1] on
  abelian sheaves at the universe of the structure rings, from the small étale site of `X` to its
  spaces-étale site.
* `AlgebraicGeometry.Space.smallEtaleAbelianSheaf`: the abelian sheaf on the small étale site
  underlying an `𝒪_X`-module, typed at `AlgebraicGeometry.Space.SmallEtale.topology` rather than
  at the projection of the ringed site.

## Main results

* `AlgebraicGeometry.Space.isTerminal_comparisonFunctor_representingChart`: the comparison
  functor of [Stacks, Tag 03G1] carries the terminal object of the small étale site of an affine
  algebraic space to a terminal object of its spaces-étale site.
* `AlgebraicGeometry.Space.subsingleton_sheafH_spacesEtale_of_isQuasicoherentOnSite`: **the
  global cohomology of a quasi-coherent module on an affine algebraic space, read on the
  spaces-étale site, vanishes in positive degrees.**

## Implementation notes

The transport is
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_functor`, whose universes are free;
the one-pair-of-universes form
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` does not apply here,
the small étale site having its morphisms in `Type u` and the spaces-étale site in
`Type (u + 1)`.  Its terminal-object hypothesis is discharged by
`AlgebraicGeometry.Space.isTerminal_representingChart` on the small side and by
`AlgebraicGeometry.Space.isTerminal_comparisonFunctor_representingChart` on the spaces side: the
image of the representing chart is an object of the slice `Over X` whose structure morphism is
the inverse of the representing isomorphism, hence an isomorphism, hence terminal.

*The coefficient universe is `u`*, the universe of the structure rings, and not the morphism
universe `u + 1` of the spaces-étale site.  That is what makes the transport possible: a
quasi-coherent `𝒪_X`-module has its sections in `Type u`, and `CategoryTheory.Sheaf.H'` over an
object of the spaces-étale site would demand coefficients in `AddCommGrpCat.{u + 1}`, where the
small étale statement is not available — `Ext` has no comparison between those two coefficient
categories.  `CategoryTheory.Sheaf.H`, global cohomology, is free in its coefficient universe,
which is why it is the shape used.  The sheafification of `AddCommGrpCat.{u}`-valued presheaves
on the spaces-étale site is itself transported from the small étale site along the same
comparison, exactly as `AlgebraicGeometry.Space.hasSheafify_spacesEtale` does at `Type u`, and
the `Ext`-groups are the standard ones, the sheaf category being `Type (u + 1)`-sized with
`Type (u + 1)` morphisms.

No `@[stacks]` attribute is claimed: [Stacks, Tag 03G1] is registered on
`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence` and what is here is one consequence
of it.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Sheafification of `AddCommGrpCat.{u}`-valued presheaves on the spaces-étale site, transported
along the comparison of [Stacks, Tag 03G1] from the small étale site.  This is
`AlgebraicGeometry.Space.hasSheafify_spacesEtale` at abelian coefficients instead of sets. -/
instance hasSheafify_spacesEtale_addCommGrp :
    HasSheafify (SpacesEtale.topology B S hS X) AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
    (comparisonFunctor B S hS X)

/-- `Ext`-groups of the abelian sheaves on the spaces-étale site at the universe of the structure
rings, in the universe `u + 1`: the sheaf category has its objects and its morphisms there, so
these are the standard `Ext`-groups. -/
instance hasExt_abelianSheaf_spacesEtale :
    HasExt.{u + 1} (Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-! The `Ext`-groups and the injectives of the abelian sheaves on the small étale site are
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtale` and
`AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale`, deliberately not instances
where they are declared; they are activated here. -/

attribute [local instance] enoughInjectives_sheaf_smallEtale
  hasExt_sheaf_smallEtale

variable (T : BigFppfOver B S hS)

/-- **The comparison functor of [Stacks, Tag 03G1] carries the chart presented by a representing
isomorphism to a terminal object of the spaces-étale site.**  The image of that chart is the
object of `Over X` whose structure morphism is the inverse of the representing isomorphism; an
object of a slice whose structure morphism is an isomorphism is terminal, and the spaces-étale
site is a full subcategory of the slice. -/
def isTerminal_comparisonFunctor_representingChart (i : X.1 ≅ yoneda.obj T) :
    IsTerminal ((comparisonFunctor B S hS X).obj (representingChart B S hS X T i)) := by
  refine ObjectProperty.isTerminal_of_isTerminal_obj _ ?_
  refine IsTerminal.ofIso Over.mkIdTerminal (Over.isoMk (ObjectProperty.isoMk
    (P := IsAlgebraicSpace B S hS) (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (Y := X) i.symm) ?_).symm
  exact Category.comp_id _

/-- The abelian sheaf on the small étale site of `X` underlying an `𝒪_X`-module, typed at
`AlgebraicGeometry.Space.SmallEtale.topology` and not at the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite …).J`, to which it is definitionally equal; the
two readings carry different instance terms and instance search does not unfold the
projection. -/
abbrev smallEtaleAbelianSheaf (K : Modules.{u, u} B S hS X.1 X.2) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf
    (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj K

/-- **The equivalence of [Stacks, Tag 03G1] on abelian sheaves at the universe of the structure
rings**: an abelian sheaf on the small étale site of `X` is the same thing as an abelian sheaf on
its spaces-étale site.  This is the equivalence of
`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`, packaged as
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`. -/
abbrev spacesEtaleSheafEquiv :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} ≌
      Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.sheafEquiv (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X) AddCommGrpCat.{u}

variable {B S hS X}

/-- **The global cohomology of a quasi-coherent module on an affine algebraic space, read on the
spaces-étale site, vanishes in positive degrees.**

Let `X` be an algebraic space over `S` which is representable by an affine scheme of the ambient
big fppf site, and let `K` be an `𝒪_X`-module which is quasi-coherent on the small étale site of
`X`, that is, a quasi-coherent sheaf on `X` in the sense of [Stacks, Tag 03G9].  Read on the
spaces-étale site of `X` through the equivalence of [Stacks, Tag 03G1], the abelian sheaf
underlying `K` has vanishing global cohomology in every positive degree.

This is `AlgebraicGeometry.Space.subsingleton_sheafH_of_isQuasicoherentOnSite` transported by
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_functor`. -/
@[sga "4 VII 4.4"]
theorem subsingleton_sheafH_spacesEtale_of_isQuasicoherentOnSite
    (hX : IsAffineSpace B S hS X.1) (K : Modules.{u, u} B S hS X.1 X.2)
    (hK : K.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((spacesEtaleSheafEquiv B S hS X).functor.obj (smallEtaleAbelianSheaf B S hS X K)) q) := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hX
  exact Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_functor
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
    (comparisonFunctor B S hS X)
    (isTerminal_representingChart B S hS X T i)
    (isTerminal_comparisonFunctor_representingChart B S hS X T i)
    (smallEtaleAbelianSheaf B S hS X K) q
    (subsingleton_sheafH_of_isQuasicoherentOnSite ⟨T, hT, ⟨i⟩⟩ K hK q hq)

end AlgebraicGeometry.Space

end
