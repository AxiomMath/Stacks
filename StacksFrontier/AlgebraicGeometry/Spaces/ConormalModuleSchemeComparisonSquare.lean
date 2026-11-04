module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleSchemeComparison

/-!
# Naturality of a comparison of conormal modules in squares of closed subspaces

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square in which `Z` is a closed subspace of an algebraic space `X` and `Z'` a
closed subspace of `X'`, and let a square of closed immersions of ringed spaces be given
alongside it, together with a comparison of the four categories of modules at the four corners
which is compatible with inverse image.  This file says that such a comparison carries
`AlgebraicGeometry.Space.conormalMap` (Stacks 04CP) to
`Stacks.ClosedImmersion.conormalSheafMap` (Stacks 01R4) as soon as it carries the map of
defining ideal sheaves to the map of ideal sheaves.

This is item 3 of the carry note of the file `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/ConormalShortExact.lean` under
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/` —
"naturality of that identification in squares of closed subspaces, which is what makes the two
conormal *maps* of Stacks 04CP correspond" — reduced to item 2, the identification of the
objects, read at the level of the **ideal sheaves** rather than of the conormal modules.  Both
`hmid` and `hmono` of Stacks 06CC need it, and so does the transfer of the scheme-level
middle exactness `@[stacks 06AE "part (2): exactness at the middle term"]` of
`StacksFrontier/AlgebraicGeometry/Thickenings/TransitivityConormal.lean`.

## Main results

* `AlgebraicGeometry.Space.conormalPullbackComparison_comparison_square`: the naturality square,
  with each conormal map written out as its defining composite.
* `AlgebraicGeometry.Space.conormalMap_comparison_square`: the same square with the two maps in
  their folded spellings, `AlgebraicGeometry.Space.conormalMap` and
  `Stacks.ClosedImmersion.conormalSheafMap`.  Composed with
  `Stacks.Thickenings.universalConormalSheafMap_eq` it is the statement at a morphism of
  universal first-order thickenings, which is the form a chart bridge for Stacks 06CC consumes.
* `AlgebraicGeometry.Space.conormalMap_comp_pullback_definingIdealSheaf_ι`: the space-level
  counterpart of `Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι` — the map of conormal
  modules read inside the inverse image of the structure sheaf.  It is the shape in which the
  two maps are compared sectionwise.

## What the comparison is, and what is left to supply

The comparison is not constructed here: the four functors `EX, EX', EZ, EZ'`, the four edge
comparisons `pI, pI', pG, pF`, the two identifications `eX, eX'` of the defining ideal sheaves
with the ideal sheaves of the closed immersions, and the three compatibilities `hpullback`,
`hideal`, `hpaste` are hypotheses.  Supplying them for a representable algebraic space is
exactly item 2 of that carry note.

**The identification of the *objects* is not a blocker.**  The square it rests on — that the
transport of the structure projection of the representing closed immersion of schemes is
`AlgebraicGeometry.Space.structureProjection` — is proved at the module level, as
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedStructureProjectionSquare.lean`, and not only as
its ring-level shadow
`AlgebraicGeometry.Space.representedStructureMapRing_square`.  The object
identification it feeds is `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedDefiningIdealSheafObject.lean`, which assumes
nothing; the note of `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/Conormal.lean` beside `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/ConormalShortExact.lean` cites it as available.

**Which of the three compatibilities is available.**  Read with the comparison of module
categories taken from the scheme to the space — the comparison functor being the associated
module followed by `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, so that the
conclusion carries `Stacks.ClosedImmersion.conormalSheafMap` to
`AlgebraicGeometry.Space.conormalMap` rather than the other way round — the edge comparison `pI`
is the inverse of `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, and
`hpullback` is then
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_inv_naturality` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackNaturality.lean`, which holds at
an arbitrary morphism of Zariski modules.  Of the other two:

* `hideal` is the compatibility of `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented`
  with the two maps of ideal sheaves.  Each map is characterised by its composite with the
  inclusion into the structure sheaf —
  `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` and
  `Stacks.ClosedImmersion.idealSheafMap_comp_ι` — and the inclusion of a defining ideal sheaf is
  a monomorphism, so the compatibility reduces to the compatibility of that identification with
  the two inclusions.  That reduction is
  `AlgebraicGeometry.Space.idealComparison_of_inclusions` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedIdealSheafInclusion.lean`; what each of its
  six hypotheses is, and which are proved, is the *What `hideal` and `hpaste` still owe* section
  of that file, which is the current record.
* `hpaste` is the compatibility of the edge comparisons with composition, transported along
  `hsq`.  Its scheme-side half is proved, as
  `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp`, and so is the transport
  of the comparison along an equality of two morphisms of the site,
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_congr`; the remaining
  space-side half — a composition law for
  `AlgebraicGeometry.Space.representedModulePullbackIso`, matching
  `AlgebraicGeometry.Space.modulePullbackCompIso` of the represented morphisms with
  `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` of the underlying morphisms of
  schemes — does not exist, but it is not owed as a statement about inverse images.
  `AlgebraicGeometry.Space.conjugateIsoEquiv_representedModulePullbackIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackConjugate.lean` computes the
  **mate** of the edge comparison: it is
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, the comparison of the two
  direct images, on the nose.  Conjugation being a bijection onto the morphisms of right
  adjoints, the composition law holds exactly when the corresponding law holds for that
  direct-image comparison — a statement with no
  `AlgebraicGeometry.Space.modulePullback`, hence no sheafification, in it.  What that leaves is
  one piece of space-side geometry: a pseudofunctoriality for
  `AlgebraicGeometry.Space.smallBaseChange`, identifying base change of étale scheme charts
  along a composite of two morphisms of algebraic spaces with the two successive base changes,
  compatibly with `AlgebraicGeometry.Space.smallBaseChangeSharp`.  That is the space-side
  counterpart of the scheme-side `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`
  and of `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRingHom_app_comp`, and it is the
  one thing `hpaste` is blocked on.

**Which square those hypotheses belong to.**  They are read above as hypotheses of
`AlgebraicGeometry.Space.conormalMap_comparison_square` of this file, and for that statement they
cannot be supplied at all: its comparison `EZ` goes from the modules of an algebraic space to the
modules of a ringed space, whereas the comparison a representable algebraic space furnishes runs
from the scheme to the space, and it cannot be inverted —
`AlgebraicGeometry.SmallEtale.associatedModule` is not an equivalence, and
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, which is one, is an
equivalence of the *quasi-coherent* modules only.  The statement whose hypotheses the above
paragraph is about is therefore `Stacks.ConormalComparison.comparison_square` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeComparison.lean`, whose `hpullback`
slot `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_inv_naturality` matches
exactly, and whose hypotheses of the names `hideal` and `hpaste` are the two above.

**The scheme-side spelling is not a second obstruction.**  The scheme-side category below is
`SheafOfModules (structureSheafRing _)` on the Zariski site of a ringed space, because that is
where `Stacks.ClosedImmersion.conormalSheafMap` and `Stacks.Thickenings.universalConormalSheaf`
live, whereas the comparison of module categories
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` has
`AlgebraicGeometry.Scheme.Modules` on its scheme side, which is `SheafOfModules` over the ring
sheaf read as a `TopCat.Sheaf`.  Those two are the **same type**:
`Stacks.RingedSpaceModules.schemeModules_eq` of
`StacksFrontier/AlgebraicGeometry/RingedSpaceModuleSpellings.lean` is `rfl`, as is
`Stacks.RingedSpaceModules.schemeRingCatSheaf_eq_ringSheaf` on the two sheaves of rings, and
`Stacks.RingedSpaceModules.schemeModulesEquivalence` packages the identity as an equivalence.
So nothing mathematical is owed there; the implementation notes of that file record only that
typeclass synthesis and `rw` do not cross the equality, because `TopCat.Sheaf` stays folded at
the transparency they run at, so a consumer instantiating the hypotheses below must cross it in
term mode.  Item 2 is therefore the single thing owed.

## Implementation notes

**Why each statement appears twice.**  `AlgebraicGeometry.Space.conormalMap` and
`Stacks.ClosedImmersion.conormalSheafMap` are definitions whose bodies are the composites the
transfer `Stacks.ConormalComparison.comparison_square` speaks about, but a goal in which the
folded and the written-out spellings meet is not type-correct at `implicit` transparency, and
unifying them directly exhausts the heartbeat budget at `whnf`.  Each result is therefore proved
first in the written-out spelling — where the transfer applies with no unification to do — and
then transported to the folded one by rewriting with the defining equations
`AlgebraicGeometry.Space.conormalMap_eq` and
`Stacks.ClosedImmersion.conormalSheafMap_eq_of_comm`, which
carry the type ascriptions that make the rewrite well-typed.

**Why the proofs of the two `..._ι` results are in term mode.**  The step
`F.map a ≫ F.map b = F.map (a ≫ b)` is not reachable by `rw` here: the source of the inverse
image is `AlgebraicGeometry.Space.Modules` while the defining ideal sheaf is typed as a
`SheafOfModules` over `AlgebraicGeometry.Space.structureRingSheaf`, and `rw` does not see
through that.  `CategoryTheory.Functor.map_comp` applied as a term, with its functor and both
morphisms given explicitly, does.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-- **A comparison of module categories compatible with inverse image carries the map of
conormal modules of a square of closed subspaces to the map of conormal sheaves of a square of
closed immersions of ringed spaces**, provided it carries the map of defining ideal sheaves of
the one square to the map of ideal sheaves of the other.  This is the written-out form; the
folded form is `AlgebraicGeometry.Space.conormalMap_comparison_square`.

The comparison is the data `EX, EX', EZ, EZ'` at the four corners, the edge comparisons
`pI, pI', pG, pF` of `E` with inverse image, and the identifications `eX, eX'` of the two
defining ideal sheaves with the two ideal sheaves; `hpullback`, `hideal` and `hpaste` are its
three compatibilities.  See the module documentation for what supplying them would take and why
it is not available in this development. -/
theorem conormalPullbackComparison_comparison_square
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    {Zs Xs Zs' Xs' : RingedSpace.{u, u}} {is : Zs ⟶ Xs} {is' : Zs' ⟶ Xs'}
    {fs : Zs ⟶ Zs'} {gs : Xs ⟶ Xs'} (comm : is ≫ gs = fs ≫ is')
    (EX : Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (structureSheafRing Xs))
    (EX' : Modules.{u, u} B S hS X'.1 X'.2 ⥤
      SheafOfModules.{u} (structureSheafRing Xs'))
    (EZ : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1 ⥤
      SheafOfModules.{u} (structureSheafRing Zs))
    (EZ' : Modules.{u, u} B S hS Z'.1.toFunctor Z'.2.1 ⥤
      SheafOfModules.{u} (structureSheafRing Zs'))
    (pI : ∀ M : Modules.{u, u} B S hS X.1 X.2,
      EZ.obj ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj M) ⟶
        (RingedSpaceModuleAdjunction.modulePullback is).obj (EX.obj M))
    (pI' : ∀ M : Modules.{u, u} B S hS X'.1 X'.2,
      EZ'.obj ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).obj M) ⟶
        (RingedSpaceModuleAdjunction.modulePullback is').obj (EX'.obj M))
    (pG : ∀ M : Modules.{u, u} B S hS X'.1 X'.2,
      EX.obj ((modulePullback B S hS g).obj M) ⟶
        (RingedSpaceModuleAdjunction.modulePullback gs).obj (EX'.obj M))
    (pF : ∀ M : Modules.{u, u} B S hS Z'.1.toFunctor Z'.2.1,
      EZ.obj ((modulePullback B S hS f).obj M) ⟶
        (RingedSpaceModuleAdjunction.modulePullback fs).obj (EZ'.obj M))
    (eX : EX.obj (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      Stacks.ClosedImmersion.idealSheaf is)
    (eX' : EX'.obj (definingIdealSheaf B S hS X' Z').toSheafOfModules ⟶
      Stacks.ClosedImmersion.idealSheaf is')
    (hpullback : EZ.map ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z Z' g f hsq)) ≫
        pI (definingIdealSheaf B S hS X Z).toSheafOfModules =
      pI ((modulePullback B S hS g).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
        (RingedSpaceModuleAdjunction.modulePullback is).map
          (EX.map (idealSheafMap B S hS Z Z' g f hsq)))
    (hideal : EX.map (idealSheafMap B S hS Z Z' g f hsq) ≫ eX =
      pG (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫
        (RingedSpaceModuleAdjunction.modulePullback gs).map eX' ≫
          Stacks.ClosedImmersion.idealSheafMap comm)
    (hpaste : EZ.map (conormalPullbackComparison B S hS Z Z' g f hsq) ≫
        pI ((modulePullback B S hS g).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
          (RingedSpaceModuleAdjunction.modulePullback is).map
            (pG (definingIdealSheaf B S hS X' Z').toSheafOfModules) =
      pF ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
        (RingedSpaceModuleAdjunction.modulePullback fs).map
            (pI' (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
          (Stacks.ClosedImmersion.pullbackCompIso comm
            (EX'.obj (definingIdealSheaf B S hS X' Z').toSheafOfModules)).hom) :
    EZ.map (conormalPullbackComparison B S hS Z Z' g f hsq ≫
          (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
            (idealSheafMap B S hS Z Z' g f hsq)) ≫
        pI (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
          (RingedSpaceModuleAdjunction.modulePullback is).map eX =
      (pF ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).obj
            (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
          (RingedSpaceModuleAdjunction.modulePullback fs).map
              (pI' (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
            (RingedSpaceModuleAdjunction.modulePullback fs).map
              ((RingedSpaceModuleAdjunction.modulePullback is').map eX')) ≫
        ((Stacks.ClosedImmersion.pullbackCompIso comm
            (Stacks.ClosedImmersion.idealSheaf is')).hom ≫
          (RingedSpaceModuleAdjunction.modulePullback is).map
            (Stacks.ClosedImmersion.idealSheafMap comm)) :=
  Stacks.ConormalComparison.comparison_square
    (ai := modulePullback B S hS (subspaceInclusion B S hS X Z))
    (ai' := modulePullback B S hS (subspaceInclusion B S hS X' Z'))
    (ag := modulePullback B S hS g) (af := modulePullback B S hS f)
    (bi := RingedSpaceModuleAdjunction.modulePullback is)
    (bi' := RingedSpaceModuleAdjunction.modulePullback is')
    (bg := RingedSpaceModuleAdjunction.modulePullback gs)
    (bf := RingedSpaceModuleAdjunction.modulePullback fs)
    (EX := EX) (EX' := EX') (EZ := EZ) (EZ' := EZ')
    (fun M => (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app M)
    (fun N => (Stacks.ClosedImmersion.pullbackCompIso comm N).hom) pI pI' pG pF
    (idealSheafMap B S hS Z Z' g f hsq) (Stacks.ClosedImmersion.idealSheafMap comm) eX eX'
    hpullback hideal hpaste
    (Stacks.ClosedImmersion.pullbackCompIso_naturality comm eX').symm

/-- **The naturality square in the folded spelling of the two conormal maps**: the comparison
carries `AlgebraicGeometry.Space.conormalMap` of the square of closed subspaces to
`Stacks.ClosedImmersion.conormalSheafMap` of the square of closed immersions.

This is `AlgebraicGeometry.Space.conormalPullbackComparison_comparison_square` rewritten through
the defining equations `AlgebraicGeometry.Space.conormalMap_eq` and
`Stacks.ClosedImmersion.conormalSheafMap_eq_of_comm`.  Rewriting further with
`Stacks.Thickenings.universalConormalSheafMap_eq` puts the right-hand side at a morphism of
universal first-order thickenings, where the scheme-level conormal sheaf is
`Stacks.Thickenings.universalConormalSheaf`. -/
theorem conormalMap_comparison_square
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    {Zs Xs Zs' Xs' : RingedSpace.{u, u}} {is : Zs ⟶ Xs} {is' : Zs' ⟶ Xs'}
    {fs : Zs ⟶ Zs'} {gs : Xs ⟶ Xs'} (comm : is ≫ gs = fs ≫ is')
    (EX : Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (structureSheafRing Xs))
    (EX' : Modules.{u, u} B S hS X'.1 X'.2 ⥤
      SheafOfModules.{u} (structureSheafRing Xs'))
    (EZ : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1 ⥤
      SheafOfModules.{u} (structureSheafRing Zs))
    (EZ' : Modules.{u, u} B S hS Z'.1.toFunctor Z'.2.1 ⥤
      SheafOfModules.{u} (structureSheafRing Zs'))
    (pI : ∀ M : Modules.{u, u} B S hS X.1 X.2,
      EZ.obj ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj M) ⟶
        (RingedSpaceModuleAdjunction.modulePullback is).obj (EX.obj M))
    (pI' : ∀ M : Modules.{u, u} B S hS X'.1 X'.2,
      EZ'.obj ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).obj M) ⟶
        (RingedSpaceModuleAdjunction.modulePullback is').obj (EX'.obj M))
    (pG : ∀ M : Modules.{u, u} B S hS X'.1 X'.2,
      EX.obj ((modulePullback B S hS g).obj M) ⟶
        (RingedSpaceModuleAdjunction.modulePullback gs).obj (EX'.obj M))
    (pF : ∀ M : Modules.{u, u} B S hS Z'.1.toFunctor Z'.2.1,
      EZ.obj ((modulePullback B S hS f).obj M) ⟶
        (RingedSpaceModuleAdjunction.modulePullback fs).obj (EZ'.obj M))
    (eX : EX.obj (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      Stacks.ClosedImmersion.idealSheaf is)
    (eX' : EX'.obj (definingIdealSheaf B S hS X' Z').toSheafOfModules ⟶
      Stacks.ClosedImmersion.idealSheaf is')
    (hpullback : EZ.map ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z Z' g f hsq)) ≫
        pI (definingIdealSheaf B S hS X Z).toSheafOfModules =
      pI ((modulePullback B S hS g).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
        (RingedSpaceModuleAdjunction.modulePullback is).map
          (EX.map (idealSheafMap B S hS Z Z' g f hsq)))
    (hideal : EX.map (idealSheafMap B S hS Z Z' g f hsq) ≫ eX =
      pG (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫
        (RingedSpaceModuleAdjunction.modulePullback gs).map eX' ≫
          Stacks.ClosedImmersion.idealSheafMap comm)
    (hpaste : EZ.map (conormalPullbackComparison B S hS Z Z' g f hsq) ≫
        pI ((modulePullback B S hS g).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
          (RingedSpaceModuleAdjunction.modulePullback is).map
            (pG (definingIdealSheaf B S hS X' Z').toSheafOfModules) =
      pF ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
        (RingedSpaceModuleAdjunction.modulePullback fs).map
            (pI' (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
          (Stacks.ClosedImmersion.pullbackCompIso comm
            (EX'.obj (definingIdealSheaf B S hS X' Z').toSheafOfModules)).hom) :
    EZ.map (conormalMap B S hS Z Z' g f hsq) ≫
        pI (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
          (RingedSpaceModuleAdjunction.modulePullback is).map eX =
      (pF ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).obj
            (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
          (RingedSpaceModuleAdjunction.modulePullback fs).map
              (pI' (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
            (RingedSpaceModuleAdjunction.modulePullback fs).map
              ((RingedSpaceModuleAdjunction.modulePullback is').map eX')) ≫
        Stacks.ClosedImmersion.conormalSheafMap comm := by
  rw [conormalMap_eq, Stacks.ClosedImmersion.conormalSheafMap_eq_of_comm]
  exact conormalPullbackComparison_comparison_square B S hS Z Z' g f hsq comm EX EX' EZ EZ'
    pI pI' pG pF eX eX' hpullback hideal hpaste

/-- **The map of conormal modules of a square, read inside the inverse image of the structure
sheaf**, in the written-out spelling.  Followed by the inverse image along the inclusion of `Z`
of the inclusion `𝓘 ⊆ 𝒪_X`, the map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` becomes the comparison
`AlgebraicGeometry.Space.conormalPullbackComparison` followed by the inverse image along that
inclusion of the composite which
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` characterises. -/
theorem conormalPullbackComparison_comp_pullback_definingIdealSheaf_ι
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    (conormalPullbackComparison B S hS Z Z' g f hsq ≫
          (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
            (idealSheafMap B S hS Z Z' g f hsq)) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (definingIdealSheaf B S hS X Z).ι =
      conormalPullbackComparison B S hS Z Z' g f hsq ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
            structureModulePullbackMap B S hS g) := by
  refine Eq.trans (Category.assoc _ _ _) (whisker_eq _ ?_)
  exact Eq.trans
    (Functor.map_comp (modulePullback B S hS (subspaceInclusion B S hS X Z))
      (idealSheafMap B S hS Z Z' g f hsq) (definingIdealSheaf B S hS X Z).ι).symm
    (congrArg (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
      (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq))

/-- **The map of conormal modules of a square, read inside the inverse image of the structure
sheaf.**  This is the space-level counterpart of
`Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι`, and it says that
`AlgebraicGeometry.Space.conormalMap` is the map induced by `g^♯`: past the comparison
isomorphism, the whole of its content is the inverse image of the inclusion `𝓘' ⊆ 𝒪_{X'}` read
in `𝒪_X` through `AlgebraicGeometry.Space.structureModulePullbackMap`.

Since the inclusion of an ideal sheaf is a monomorphism but its inverse image need not be, this
does not determine `conormalMap`; it is the shape in which the map is compared with another
construction of it, and the shape in which the chartwise description of Stacks 04CP is read. -/
theorem conormalMap_comp_pullback_definingIdealSheaf_ι
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    conormalMap B S hS Z Z' g f hsq ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (definingIdealSheaf B S hS X Z).ι =
      conormalPullbackComparison B S hS Z Z' g f hsq ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
            structureModulePullbackMap B S hS g) := by
  rw [conormalMap_eq]
  exact conormalPullbackComparison_comp_pullback_definingIdealSheaf_ι B S hS Z Z' g f hsq

end AlgebraicGeometry.Space

end
