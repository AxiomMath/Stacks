module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Conormal.SelfIsoComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleSchemeAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceImmersionFirstMap
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedImmersionCoborderLift

/-!
# **Stacks 04G2, part (1)**, at immersion generality

Let `j : R ⟶ V` be a morphism of the big fppf category over a scheme `S` whose underlying
morphism of schemes is an **immersion**.  Part (1) of [Stacks Project, Tag 04G2] asserts that the
conormal sheaf of [Stacks Project, Tag 04CN] of the morphism of algebraic spaces it represents
agrees with the conormal sheaf of Morphisms, Definition [Stacks Project, Tag 01R2] of the
underlying morphism of schemes.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean` proves this for a
**closed** immersion.  This file removes that hypothesis, which is the generality the source
states the clause at.

## Main results

* `AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`: **part (1) of [Stacks
  Project, Tag 04G2]**.  For an arbitrary immersion, the conormal module
  `AlgebraicGeometry.Space.immersionConormalModule` of the represented morphism of algebraic
  spaces is the module which `Stacks.Conormal.conormalSheaf` of the underlying morphism of
  schemes becomes on the small étale site of `yoneda.obj R`.
* `Stacks.Conormal.conormalSheafLiftCoborderIso_eq`: the schemes-side link of that chain is the
  inverse of `Stacks.Immersion.conormalSheafSelfIso`, the isomorphism by which the canonical map
  of [Stacks Project, Tag 01R4] is conjugated throughout the conormal files. This is the bridge
  between the two vocabularies, and it is `Stacks.Immersion`'s own
  `conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf` read at
  `AlgebraicGeometry.Scheme.Hom.liftCoborder`.

## Route

Both sides of the comparison are *defined* through the ambient open of the immersion — the space
side by [Stacks Project, Tag 04CE] and the scheme side by Morphisms, Definition 01R2 — and the
closed case is applied on that ambient.
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedImmersionCoborderLift.lean` supplies the ambient
as an object `U` of the site together with the factorisation
`k := AlgebraicGeometry.Space.immersionCoborderLift` of `j` through it, whose morphism of schemes
is `AlgebraicGeometry.Scheme.Hom.liftCoborder` on the nose and hence a closed immersion.  The
chain has five links.

* The square with `𝟙` along the top, `k` down the left, `j` down the right and the ambient
  inclusion along the bottom is cartesian
  (`AlgebraicGeometry.Space.isPullback_representedSpaceMap_immersionCoborderLift`) and its bottom
  edge is étale, so [Stacks Project, Tag 04CO] —
  `AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso` — identifies the
  conormal module of `j` with that of `k`, the inverse image along the identity being stripped by
  the unit law of [Stacks Project, Tag 03LU].
* `AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso` presents the conormal
  module of `k` as the inverse image along `k` of `AlgebraicGeometry.Space.kernelIdealSheaf` of
  `k`.
* `AlgebraicGeometry.Space.modulePullbackKernelIdealSheafDefiningIdealSheafIso`, which is
  `AlgebraicGeometry.Space.kernelIdealSheaf_representedSpaceMap`, replaces that kernel by the
  defining ideal sheaf of [Stacks Project, Tag 03MB] of the closed subspace which `k` cuts out of
  `yoneda.obj U`.  This is the step that needs `k` to be a **closed** immersion, and it is where
  the ambient earns its place: the kernel ideal sheaf of a general immersion is the ideal of its
  scheme-theoretic image, whose quasi-coherence Morphisms, Lemma [Stacks Project, Tag 01R8]
  derives from quasi-compactness, so the comparison cannot be made at `j` itself.
* `AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso` at `k` is the closed
  case, and lands on the associated module of `Stacks.Conormal.conormalSheaf` of the morphism of
  schemes underlying `k`, which **is** `AlgebraicGeometry.Scheme.Hom.liftCoborder` of the one
  underlying `j` by `AlgebraicGeometry.Space.toScheme_map_immersionCoborderLift`.
* `Stacks.Conormal.conormalSheafLiftCoborderIso` closes the gap on the schemes side: the conormal
  sheaf of `f.liftCoborder` is the conormal sheaf of `f`, both being the pullback of one ideal
  sheaf along one morphism.

## Implementation notes

`AlgebraicGeometry.Space.modulePullback` is made locally irreducible, as it is in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean`: unfolding the inverse
image to its construction by sheafification does not terminate, and nothing below needs it.

`Stacks.Conormal.conormalSheafLiftCoborderIso` is stated for a bare morphism of schemes rather
than inline at `(BigFppfOver.toScheme B S hS).map j`, because instance search reaches Mathlib's
`AlgebraicGeometry.IsClosedImmersion` instance for
`AlgebraicGeometry.Scheme.Hom.liftCoborder` only at the bare spelling; this is the same reason
`AlgebraicGeometry.Space.isClosedImmersion_liftCoborder` exists.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.Conormal

/-- **The conormal sheaf of the closed factorisation of an immersion is the conormal sheaf of the
immersion.**  For an immersion of schemes `f : X ⟶ Y`, the conormal sheaf of Morphisms,
Definition [Stacks Project, Tag 01R2] of the closed immersion
`AlgebraicGeometry.Scheme.Hom.liftCoborder` into the coborder of `f` is the conormal sheaf of `f`
itself.

Both are the module pullback of one ideal sheaf along one morphism: `Stacks.Conormal.conormalSheaf`
of `f` is *by definition* the pullback along `f.liftCoborder` of the ideal sheaf of
`f.liftCoborder`, and `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` presents the conormal
sheaf of any immersion — here `f.liftCoborder` — as the pullback along that immersion of its own
ideal sheaf. -/
def conormalSheafLiftCoborderIso {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion f] :
    Stacks.Conormal.conormalSheaf f.liftCoborder ≅ Stacks.Conormal.conormalSheaf f :=
  Stacks.CartierConormal.conormalSheafIsoPullbackSelf f.liftCoborder

/-- **The schemes-side link of part (1) is the inverse of
`Stacks.Immersion.conormalSheafSelfIso` at `AlgebraicGeometry.Scheme.Hom.liftCoborder`.**  The
canonical map of [Stacks Project, Tag 01R4] is conjugated by
`Stacks.Immersion.conormalSheafSelfIso`, so this is what lets a statement about that map be read
through the comparison chain of part (1) above.

It is `Stacks.Immersion.conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf` at
`f.liftCoborder`, which is the identification of the two routes to this one bridge — through
`Stacks.Immersion.conormalSheafFactorIso` and through
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq`. -/
theorem conormalSheafLiftCoborderIso_eq {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion f] :
    conormalSheafLiftCoborderIso f =
      (Stacks.Immersion.conormalSheafSelfIso f.liftCoborder).symm :=
  (congrArg Iso.symm (Stacks.Immersion.conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf
    f.liftCoborder)).symm

end Stacks.Conormal

namespace AlgebraicGeometry.Space

-- See the implementation notes: this keeps the elaborator from unfolding the inverse image to
-- its construction, which does not terminate.
attribute [local irreducible] modulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inclusion of an open of the site, read as a morphism of algebraic spaces, is étale.**
Its morphism of schemes is the inclusion of a Zariski open by
`AlgebraicGeometry.Space.etale_toScheme_map_openSubHom`, and for a represented morphism that is
étaleness after every representable base change. -/
theorem isEtale_representedSpaceMap_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    IsEtale B S hS (representedSpaceMap B S hS (openSubHom A O)).hom :=
  isEtale_of_presheaf_etale B S hS
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (openSubHom A O)).2
      (etale_toScheme_map_openSubHom B S hS A O))

variable {R V : BigFppfOver B S hS}

/-- **A represented immersion of schemes is an immersion of algebraic spaces.**  Immersions of
schemes are stable under base change, so for a represented morphism the definition of Stacks
02YU (5) is exactly immersion of the underlying morphism of schemes. -/
theorem isImmersion_representedSpaceMap (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    IsImmersion B S hS (representedSpaceMap B S hS j).hom :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) j).2 hj

/-- **For a represented closed immersion, the inverse image of the kernel ideal sheaf is the
inverse image of the defining ideal sheaf of its range.**  This is
`AlgebraicGeometry.Space.kernelIdealSheaf_representedSpaceMap` read inside the inverse image. -/
def modulePullbackKernelIdealSheafDefiningIdealSheafIso (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    (modulePullback B S hS (representedSpaceMap B S hS j)).obj
        (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)).toSheafOfModules ≅
      (modulePullback B S hS (representedSpaceMap B S hS j)).obj
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).toSheafOfModules :=
  eqToIso (by rw [kernelIdealSheaf_representedSpaceMap B S hS j hj])

/-- **Stacks 04G2, part (1).**  For a morphism `j : R ⟶ V` of the big fppf category over `S`
whose underlying morphism of schemes is an **immersion**, the conormal module of [Stacks Project,
Tag 04CN] of the morphism of algebraic spaces `yoneda.obj R ⟶ yoneda.obj V` which `j` represents
is the module which the conormal sheaf of Morphisms, Definition [Stacks Project, Tag 01R2] of the
underlying morphism of schemes becomes on the small étale site of `yoneda.obj R`.

No hypothesis beyond the immersion of the source is carried: the closed case is
`AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso`, and this is that comparison
applied over the ambient open of [Stacks Project, Tag 04CE], transported back to `j` by
[Stacks Project, Tag 04CO]. -/
@[stacks 04G2 "part (1): for an immersion of schemes of the site, the conormal sheaf of 04CN of \
the represented morphism is the associated module of the conormal sheaf of Morphisms, Definition \
01R2"]
def conormalModuleOfImmersionRepresentedIso (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    immersionConormalModule B S hS (representedSpaceMap B S hS j)
        (isImmersion_representedSpaceMap B S hS j) ≅
      (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          (Stacks.Conormal.conormalSheaf ((BigFppfOver.toScheme B S hS).map j))) :=
  ((modulePullbackIdIso B S hS ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩).app
        (immersionConormalModule B S hS (representedSpaceMap B S hS j)
          (isImmersion_representedSpaceMap B S hS j))).symm ≪≫
    conormalModuleOfImmersionEtaleRestrictionIso B S hS
        (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
        (representedSpaceMap B S hS j)
        (representedSpaceMap B S hS
          (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
        (isPullback_representedSpaceMap_immersionCoborderLift B S hS j)
        (isImmersion_representedSpaceMap B S hS j)
        (isEtale_representedSpaceMap_openSubHom B S hS V
          ((BigFppfOver.toScheme B S hS).map j).coborderRange) ≪≫
      conormalModuleOfImmersionKernelPullbackIso B S hS
          (representedSpaceMap B S hS (immersionCoborderLift B S hS j)) _ ≪≫
        modulePullbackKernelIdealSheafDefiningIdealSheafIso B S hS
            (immersionCoborderLift B S hS j)
            (isClosedImmersion_toScheme_map_immersionCoborderLift B S hS j) ≪≫
          representedDefiningIdealPullbackConormalSheafIso B S hS
              (immersionCoborderLift B S hS j) ≪≫
            (representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
                (Stacks.Conormal.conormalSheafLiftCoborderIso
                  ((BigFppfOver.toScheme B S hS).map j)))

end AlgebraicGeometry.Space

end
