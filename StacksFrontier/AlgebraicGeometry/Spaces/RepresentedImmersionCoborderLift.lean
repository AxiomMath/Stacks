module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DenseOpenAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspacePushforwardCech
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedImmersionAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange

/-!
# The ambient open of a represented immersion, as an object of the site

Let `B` be a big fppf site containing a scheme `S` and let `j : R ⟶ V` be a morphism of the big
fppf category over `S` whose underlying morphism of schemes is an **immersion**.  Morphisms,
Definition 01R2 reads the conormal sheaf of such a morphism of schemes off the closed immersion
`AlgebraicGeometry.Scheme.Hom.liftCoborder` into the open subscheme
`AlgebraicGeometry.Scheme.Hom.coborderRange`, and [Stacks Project, Tag 04CE] does the same on the
space side with the open subspace `AlgebraicGeometry.Space.immersionAmbient`.

`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedImmersionAmbient.lean` matches the two ambients
**as sets of points**.  A set of points is not something the conormal comparison can be applied
over: for that the ambient has to be an *object of the site*, with `j` factoring through it by a
closed immersion, so that the closed-immersion statements of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedChartZariskiIdeal.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean` apply with the ambient
in place of `V`.  This file supplies that; the comparison assembled over it is
`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreementImmersion.lean`, part (1) of
[Stacks Project, Tag 04G2] at the immersion generality the source states it at.

A Zariski open of the scheme underlying an object of the site is itself an object of the site,
`AlgebraicGeometry.Space.openSub`; the ambient is that object at
`AlgebraicGeometry.Scheme.Hom.coborderRange`, and the factorisation of `j` through it is Mathlib's
`AlgebraicGeometry.IsOpenImmersion.lift`, read in the site.  Everything is pinned on the nose:
the underlying morphism of schemes of the factorisation **is**
`AlgebraicGeometry.Scheme.Hom.liftCoborder`, not merely isomorphic to it, so Mathlib's instance
makes it a closed immersion and no transport is needed anywhere.

## Main definitions

* `AlgebraicGeometry.Space.openLiftScheme`: the morphism of schemes underlying the base's
  `AlgebraicGeometry.Space.openSubLift` (of
  `StacksFrontier/AlgebraicGeometry/Spaces/OpenSubspacePushforwardCech.lean`), by which a morphism
  of the site whose points land in a Zariski open of its target factors through
  `AlgebraicGeometry.Space.openSub` at that open.
* `AlgebraicGeometry.Space.immersionCoborderObj`: the ambient open of a represented immersion as
  an object of the site, and `AlgebraicGeometry.Space.immersionCoborderLift` the factorisation of
  `j` through it.

## Main results

* `AlgebraicGeometry.Space.toScheme_map_openSubLift`: the underlying morphism of schemes of the
  base's factorisation `AlgebraicGeometry.Space.openSubLift` is
  `AlgebraicGeometry.Space.openLiftScheme`.  This is the characterising statement: the base's
  triangle `AlgebraicGeometry.Space.openSubLift_comp_openSubHom` alone does not pin the
  factorisation down without knowing that the inclusion of the open is a monomorphism, and every
  consumer below computes with the scheme morphism rather than with the triangle.
* `AlgebraicGeometry.Space.toScheme_map_immersionCoborderLift`: **the underlying morphism of
  schemes of the factorisation is `AlgebraicGeometry.Scheme.Hom.liftCoborder`**, by `rfl`.
* `AlgebraicGeometry.Space.isClosedImmersion_toScheme_map_immersionCoborderLift`: consequently
  `j` factors through its ambient by a **closed** immersion of schemes, which is the hypothesis
  the conormal comparison of the closed case carries.
* `AlgebraicGeometry.Space.isOpenImmersion_toScheme_map_openSubHom_immersionCoborder`: the
  ambient sits in `V` by an open immersion, hence étale by
  `AlgebraicGeometry.Space.etale_toScheme_map_openSubHom`, which is what Stacks 04CO asks of
  it.
* `AlgebraicGeometry.Space.mono_representedSpaceMap`, with the base's
  `AlgebraicGeometry.Space.mono_openSubHom_of_opens`,
  and `AlgebraicGeometry.Space.isPullback_representedSpaceMap_immersionCoborderLift`: **the
  factorisation square is cartesian**, with the identity along the top — which is the square
  Stacks 04CO consumes, exhibiting `R` as `U ×_V R`.
* `AlgebraicGeometry.Space.range_pointsMap_ι_immersionAmbient_eq_openSubHom_coborder`: **the
  ambient match, carried onto the object built here.**  The open subspace
  `AlgebraicGeometry.Space.immersionAmbient` of [Stacks Project, Tag 04CE] and the open subspace
  which `AlgebraicGeometry.Space.immersionCoborderObj` cuts out of `yoneda.obj V` have the same
  set of points.  The two are therefore the same open subspace, `AlgebraicGeometry.Space
  .openSubspacesOrderIso` being an order isomorphism; that last step is *not* taken here,
  because nothing below needs it — the comparison is applied over the object, not over the
  subspace.

## Implementation notes

The factorisation through a general open is the base's `AlgebraicGeometry.Space.openSubLift`,
whose underlying morphism of the size-bounded category is
`AlgebraicGeometry.Space.openSubLiftLeft`, the preimage along `B.inclusion` of
`AlgebraicGeometry.IsOpenImmersion.lift`; its hypothesis is pointwise membership in the open.

`AlgebraicGeometry.Space.toScheme_map_immersionCoborderLift` holds by `rfl`, which is why
`AlgebraicGeometry.Space.immersionCoborderLift` is built from `ObjectProperty.homMk` rather than
from the base's `AlgebraicGeometry.Space.openSubLift`, whose `B.inclusion.preimage` does not
unfold: `AlgebraicGeometry.Scheme.Hom.liftCoborder` *is* `AlgebraicGeometry.IsOpenImmersion.lift`
at the coborder, and the two differ only in the proof of the range inclusion, which is
irrelevant.  This is what keeps the closed immersion instance free of any transport.

`AlgebraicGeometry.BigFppfOver.openSubObj` of
`StacksFrontier/AlgebraicGeometry/Descent/SectionsPullbackComparison/Comparison.lean` is a second
spelling of the same object, with `AlgebraicGeometry.Space.openSubObjLift` already lifting into
it.  That spelling is **not** definitionally equal to `AlgebraicGeometry.Space.openSub` — the two
structure morphisms are `ObjectProperty.homMk (O.ι ≫ A.hom.hom)` and
`B.inclusion.preimage O.ι ≫ A.hom`, which agree only through
`ObjectProperty.FullSubcategory.comp_hom` — and it is `AlgebraicGeometry.Space.openSub` that
`AlgebraicGeometry.Space.openChart` is built from, so the lift is rebuilt here for that one rather
than transported.  For the same reason the monomorphism statement used below is the base's
`AlgebraicGeometry.Space.mono_openSubHom_of_opens` and not
`AlgebraicGeometry.Space.mono_openSubHom`, which is the one for the other spelling.  Collapsing
the two spellings is a dedup worth doing and is not done here.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 06EC](https://stacks.math.columbia.edu/tag/06EC)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factoring a morphism of the site through an open of its target -/

variable {B S hS} in
/-- **The factorisation of a morphism of schemes through an open containing its range**, as a
morphism of schemes and with no algebraic spaces in the statement: Mathlib's
`AlgebraicGeometry.IsOpenImmersion.lift` at the inclusion of the open.

It is given a name of its own, rather than written inline in the statement of
`AlgebraicGeometry.Space.toScheme_map_openSubLift`, because in a position whose expected type
mentions `AlgebraicGeometry.Space.openSub` the elaborator replaces `↑O` by
`(openSub A O).left.obj` and `O.ι` then no longer typechecks. -/
noncomputable def openLiftScheme {A A' : BigFppfOver B S hS} (a : A' ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens)
    (ha : Set.range ⇑((BigFppfOver.toScheme B S hS).map a) ⊆ (O : Set _)) :
    (BigFppfOver.toScheme B S hS).obj A' ⟶ (O : Scheme) :=
  IsOpenImmersion.lift O.ι ((BigFppfOver.toScheme B S hS).map a) (by rwa [O.range_ι])

variable {B S hS} in
/-- `AlgebraicGeometry.Space.openLiftScheme` followed by the inclusion of the open is the
original morphism of schemes. -/
theorem openLiftScheme_comp_ι {A A' : BigFppfOver B S hS} (a : A' ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens)
    (ha : Set.range ⇑((BigFppfOver.toScheme B S hS).map a) ⊆ (O : Set _)) :
    openLiftScheme a O ha ≫ O.ι = (BigFppfOver.toScheme B S hS).map a :=
  IsOpenImmersion.lift_fac _ _ _

variable {B S hS} in
/-- The underlying morphism of schemes of the base's `AlgebraicGeometry.Space.openSubLift` is
`AlgebraicGeometry.IsOpenImmersion.lift`, in the spelling `AlgebraicGeometry.Space.openLiftScheme`.

This is the characterising statement, and the one every consumer uses: the triangle
`AlgebraicGeometry.Space.openSubLift_comp_openSubHom` determines the factorisation only through
the monomorphism `AlgebraicGeometry.Space.openSubHom`, whereas this identifies the morphism of
schemes outright. -/
theorem toScheme_map_openSubLift (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) {A' : BigFppfOver B S hS} (a : A' ⟶ A)
    (ha : ∀ y, (BigFppfOver.toScheme B S hS).map a y ∈ O) :
    (BigFppfOver.toScheme B S hS).map (openSubLift A O a ha) =
      openLiftScheme a O (by rintro _ ⟨y, rfl⟩; exact ha y) :=
  B.inclusion.map_preimage _

/-! ### The ambient open of a represented immersion -/

/-- **An immersion of schemes is a closed immersion into its coborder.**  Mathlib's instance,
given a name: instance search does not reach it at the spellings below, where the morphism is
`(BigFppfOver.toScheme B S hS).map j` rather than a bare morphism of schemes. -/
theorem isClosedImmersion_liftCoborder {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion f] :
    AlgebraicGeometry.IsClosedImmersion f.liftCoborder :=
  inferInstance

variable {R V : BigFppfOver B S hS}

/-- **The ambient open of a represented immersion, as an object of the site.**  For `j : R ⟶ V`
with underlying morphism of schemes an immersion, this is the Zariski open
`AlgebraicGeometry.Scheme.Hom.coborderRange` of the scheme underlying `V`, read as an object of
the big fppf category over `S` by `AlgebraicGeometry.Space.openSub`. -/
noncomputable abbrev immersionCoborderObj (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    BigFppfOver B S hS :=
  openSub V ((BigFppfOver.toScheme B S hS).map j).coborderRange

/-- The morphism of the size-bounded category underlying
`AlgebraicGeometry.Space.immersionCoborderLift`: `AlgebraicGeometry.Space.openLiftScheme` at the
coborder, which is `AlgebraicGeometry.Scheme.Hom.liftCoborder` up to the proof of the range
inclusion.

The base's `AlgebraicGeometry.Space.openSubLift` produces the same morphism, but through
`B.inclusion.preimage`, which does not unfold; the consumers of this factorisation read its
morphism of schemes as `AlgebraicGeometry.Scheme.Hom.liftCoborder` *definitionally* (the conormal
sheaf of the one is the conormal sheaf of the other on the nose), so it is built here from
`ObjectProperty.homMk` instead. -/
noncomputable def immersionCoborderLiftLeft (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    R.left ⟶ (immersionCoborderObj B S hS j).left :=
  ObjectProperty.homMk (openLiftScheme j ((BigFppfOver.toScheme B S hS).map j).coborderRange
    (by rw [Scheme.Hom.coborderRange]; exact subset_coborder))

/-- `AlgebraicGeometry.Space.immersionCoborderLiftLeft` followed by the inclusion of the ambient
open is `j`. -/
theorem immersionCoborderLiftLeft_comp_left (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    immersionCoborderLiftLeft B S hS j ≫
        (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange).left = j.left := by
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp]
  show _ ≫ (BigFppfOver.toScheme B S hS).map
      (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) =
    (BigFppfOver.toScheme B S hS).map j
  rw [toScheme_map_openSubHom]
  exact Scheme.Hom.liftCoborder_ι _

/-- **A represented immersion factors through its ambient open, in the site.** -/
noncomputable def immersionCoborderLift (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    R ⟶ immersionCoborderObj B S hS j :=
  Over.homMk (immersionCoborderLiftLeft B S hS j) (by
    change immersionCoborderLiftLeft B S hS j ≫
        (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange).left ≫ V.hom = R.hom
    rw [← Category.assoc, immersionCoborderLiftLeft_comp_left, Over.w j])

/-- **The underlying morphism of schemes of the factorisation is
`AlgebraicGeometry.Scheme.Hom.liftCoborder`.**

It holds by `rfl`: `AlgebraicGeometry.Scheme.Hom.liftCoborder` is *defined* as
`AlgebraicGeometry.IsOpenImmersion.lift` at the coborder, and it and
`AlgebraicGeometry.Space.openLiftScheme` differ only in the proof of the range inclusion. -/
theorem toScheme_map_immersionCoborderLift (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    (BigFppfOver.toScheme B S hS).map (immersionCoborderLift B S hS j) =
      ((BigFppfOver.toScheme B S hS).map j).liftCoborder :=
  rfl

/-- The factorisation composed with the inclusion of the ambient open is `j`. -/
theorem immersionCoborderLift_comp_openSubHom (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    immersionCoborderLift B S hS j ≫
        openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange = j :=
  Over.OverMorphism.ext (immersionCoborderLiftLeft_comp_left B S hS j)

/-- **A represented immersion factors through its ambient open by a closed immersion of
schemes.**  This is the hypothesis that the conormal comparison of the closed case carries, and
it is obtained with no transport: the morphism of schemes underlying the factorisation is
`AlgebraicGeometry.Scheme.Hom.liftCoborder` on the nose. -/
instance isClosedImmersion_toScheme_map_immersionCoborderLift (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (immersionCoborderLift B S hS j)) :=
  (toScheme_map_immersionCoborderLift B S hS j) ▸
    isClosedImmersion_liftCoborder ((BigFppfOver.toScheme B S hS).map j)

/-- The ambient open sits in `V` by an open immersion of schemes. -/
instance isOpenImmersion_toScheme_map_openSubHom_immersionCoborder (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) := by
  rw [toScheme_map_openSubHom]
  exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B S hS).map j).coborderRange.ι)

/-! ### The ambient inclusion is a monomorphism, and the factorisation square is cartesian -/

/-- A monomorphism of the big fppf category over `S` represents a monomorphism of algebraic
spaces: `yoneda` is fully faithful and so is the inclusion of the algebraic spaces. -/
theorem mono_representedSpaceMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T) (hg : Mono g) :
    Mono (representedSpaceMap B S hS g) :=
  (ObjectProperty.ι
    (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).mono_of_mono_map
      (f := representedSpaceMap B S hS g) (inferInstanceAs (Mono (yoneda.map g)))

/-- **The factorisation square of a represented immersion through its ambient open is
cartesian**, with the identity along the top: `R = R ×_V U`.

This is the square that Stacks 04CO consumes — `φ = ` the ambient inclusion is étale, and the
fibre product `Z_U = U ×_X Z` is `R` itself — and it is cartesian for the reason the closed
factorisation of Stacks 04CE is: a square with an invertible top edge and a monomorphism along
the bottom is cartesian. -/
theorem isPullback_representedSpaceMap_immersionCoborderLift (j : R ⟶ V)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    IsPullback (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
      (schemeSpaceMap (immersionCoborderLift B S hS j))
      (schemeSpaceMap j)
      (schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) :=
  have hmono : Mono (schemeSpaceMap
      (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) :=
    mono_representedSpaceMap B S hS _ (mono_openSubHom_of_opens V _)
  have hfac : schemeSpaceMap (immersionCoborderLift B S hS j) ≫
      schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) =
      schemeSpaceMap j := by
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom]
    exact (yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (immersionCoborderLift_comp_openSubHom B S hS j))
  hfac ▸ isPullback_id_comp_of_mono _ _

/-! ### The ambient match, lifted off the point sets -/

/-- The range of points of the inclusion of `AlgebraicGeometry.Space.openSub` is the open. -/
theorem range_toScheme_map_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    Set.range ⇑((BigFppfOver.toScheme B S hS).map (openSubHom A O)) = (O : Set _) := by
  rw [toScheme_map_openSubHom]
  exact O.range_ι

attribute [local instance] pointTopology

/-- **The ambient match.**  The open subspace `AlgebraicGeometry.Space.immersionAmbient` of
[Stacks Project, Tag 04CE] attached to a represented immersion and the open subspace which
`AlgebraicGeometry.Space.immersionCoborderObj` cuts out of `yoneda.obj V` have the same set of
points.

Both are read off `AlgebraicGeometry.Scheme.Hom.coborderRange` through the Stacks 03BX
homeomorphism: the left side by
`AlgebraicGeometry.Space.range_pointsMap_ι_immersionAmbient_yoneda_map` and the right side by
`AlgebraicGeometry.Space.range_pointsMap_yoneda_map_eq_schemePointsHomeomorph_preimage` at
`AlgebraicGeometry.Space.openSubHom`, whose morphism of schemes is the inclusion of that open and
so has it as its range. -/
theorem range_pointsMap_ι_immersionAmbient_eq_openSubHom_coborder (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    Set.range (pointsMap B S hS
        (immersionAmbient B S hS (isAlgebraicSpace_yoneda B S hS V)
            (isAlgebraicSpace_yoneda B S hS R) (yoneda.map j)
            ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
              (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) j).2 hj)).1
        (boundaryComplement B S hS (yoneda.obj V)
          (Set.range (pointsMap B S hS (yoneda.obj R) (yoneda.map j)))).ι) =
      Set.range (pointsMap B S hS (yoneda.obj (immersionCoborderObj B S hS j))
        (yoneda.map (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))) :=
  (range_pointsMap_ι_immersionAmbient_yoneda_map B S hS j).trans
    ((congrArg (fun s => schemePointsHomeomorph B S hS V ⁻¹' s)
        (range_toScheme_map_openSubHom B S hS V
          ((BigFppfOver.toScheme B S hS).map j).coborderRange).symm).trans
      (range_pointsMap_yoneda_map_eq_schemePointsHomeomorph_preimage B S hS
        (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)).symm)

end AlgebraicGeometry.Space

end
