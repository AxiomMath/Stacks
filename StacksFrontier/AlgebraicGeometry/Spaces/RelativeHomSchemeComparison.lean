module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.AffineRepresentability
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeMorphismFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The two relative morphism functors agree at representable data (Stacks 0BL2 and Stacks 05Y2)

The library carries two relative morphism functors, and they are **not** two spellings of one
notion:

* `AlgebraicGeometry.relativeHom` of **Stacks 0BL2** is a presheaf on the category of schemes
  over a scheme `S`, sending an `S`-scheme `T` to the `S`-morphisms `T ×_S Z ⟶ X`;
* `AlgebraicGeometry.Space.relativeHom` of **Stacks 05Y2** is a presheaf on the big fppf site
  of `S`, sending an object `T` of the site to the pairs `(a, b)` of Stacks 05Y1 for two
  morphisms `z : Z ⟶ Q` and `x : X ⟶ Q` of *presheaves* on that site, the base `Q` being
  arbitrary.

There was no bridge between them. This file builds the
bridge, in the one situation in which the two functors can be compared: the base `Q` and the two
sources `Z` and `X` are representable by objects `V`, `Z` and `X` of the site. The comparison is

```text
Mor_{V}(Z, X)(T)  ≃  Σ (a : T ⟶ V), Mor_{V}(Z, X)(T, a),
```

the left side being the pairs of Stacks 05Y1 at `yoneda.obj T` and the right side the sections
of the functor of Stacks 0BL2 over the scheme underlying `V`, summed over the morphisms
`a : T ⟶ V` of the site. The sum is there because the base of Stacks 0BL2 is the base of the
slice the functor lives on, whereas the base of Stacks 05Y2 is an object of the *site* over `S`
and a test object carries no morphism to it; a pair `(a, b)` of Stacks 05Y1 is exactly a choice
of `a` together with a section of the Stacks 0BL2 functor at `a`.

Once the comparison is available, Stacks 05Y6 for algebraic spaces follows: the library proves
representability of the functor of Stacks 0BL2 on the scheme side, for a finite locally free `z`
and an affine `x` over an arbitrary base, as Stacks 0BL3
(`Stacks.Morphisms.relativeHom_representableBy_affineHom`), where the gluing of Stacks 02WR over
an affine chart of the base is already carried out. Transporting the representing object into the
site makes the functor of Stacks 05Y2 representable, hence an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.prodLeftIso`: the identification of the fibre product `T ×_V Z`
  taken in the big fppf site of `S` with the product of `Z` and `T` in the category of schemes
  over the scheme underlying `V`, which is the geometric content of the comparison.
* `AlgebraicGeometry.Space.relativeMorphismFibreEquiv`: the comparison at a fixed
  `a : T ⟶ V` — the second components `b` of the pairs of Stacks 05Y1 over `a` are the sections
  of the functor of Stacks 0BL2 at `a`.
* `AlgebraicGeometry.Space.relativeMorphismEquivSigma`: the pairs of Stacks 05Y1 at
  `yoneda.obj T` are the dependent pairs `(a, b)`.
* `AlgebraicGeometry.Space.siteObjOfOver` and `AlgebraicGeometry.Space.siteHomOfOver`: a
  representing object of the functor of Stacks 0BL2, read as an object of the site over `V`.
* `AlgebraicGeometry.Space.universalRelativeMorphism`: the pair of Stacks 05Y1 over the
  representing object which corresponds to its identity.

## Main results

* `AlgebraicGeometry.Space.relativeMorphismEquivRelativeHom`: **the comparison of Stacks 0BL2
  with Stacks 05Y2**, obtained by composing the two previous equivalences.
* `AlgebraicGeometry.Space.restrict_relativeMorphismOfSigma` and
  `AlgebraicGeometry.Space.fibreSectionOfHom_mapFst`: the comparison is compatible with
  restriction, respectively with base change of the morphism `b`; these are what make the
  comparison come from a single morphism of presheaves.
* `AlgebraicGeometry.Space.siteHomEquivSigma` and
  `AlgebraicGeometry.Space.restrictUniversalEquiv`: the morphisms of the site into a
  representing object are the pairs of Stacks 05Y1, and the identification is restriction of the
  universal pair.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_representableBy` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_isAffineHom`:
  **Stacks 05Y6 for algebraic spaces**, from a representing object of the functor of
  Stacks 0BL2 and from Stacks 0BL3 respectively.

## What is still owed

The statement proved here is Stacks 05Y6 for algebraic spaces at *representable* data: the base
`V` and the two sources `Z` and `X` are objects of the site. Two things separate it from the
hypothesis `hrepresentable` of the library's Stacks 05Y7
(`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree`), which asks for
an arbitrary algebraic space base `Q`:

* the reduction of the base to an object of the site, which is
  `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_atlas` in
  `StacksFrontier.AlgebraicGeometry.Stacks.RelativeHomBaseReduction`, and
* the representability of a finite locally free algebraic space over an object of the site,
  which is Stacks 03ZU and is not in the library; see the "What Stacks 03ZU still owes" note of
  `StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentable`.

The size condition — that the representing object produced on the scheme side satisfies the
cutoff of the big fppf site — is carried as a hypothesis and is not proved here.

## Implementation notes

Both fibre products are reached through `CategoryTheory.IsPullback` rather than through the
canonical `CategoryTheory.Limits.pullback`: the fibre product in the site has underlying scheme
a fibre product of the underlying scheme morphisms because
`AlgebraicGeometry.BigFppfOver.toScheme` preserves fibre products
(`AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme`), and the product in a slice
category is a fibre product in the ambient one by
`CategoryTheory.Over.isPullback_of_binaryFan_isLimit`; the two are then compared by
`CategoryTheory.IsPullback.isoIsPullback`, which avoids transporting along an equality of
objects.

The second component `b` of a pair of Stacks 05Y1 is a morphism of presheaves on the site out of
a fibre product of representables, and the fibre product of representables is representable
because the Yoneda embedding preserves fibre products
(`CategoryTheory.Limits.PreservesPullback.iso`). A morphism of the site between two objects is
determined by, and recovered from, the underlying morphism of schemes over `S`
(`AlgebraicGeometry.BigFppfOver.homOfCompEq`), and the condition that `b` lie over `V` already
forces the underlying morphism of schemes to lie over `S`; that is why no size or containment
hypothesis enters the comparison itself. Containment enters only when the representing object
produced on the scheme side is read back into the site.

That the identification of
`AlgebraicGeometry.Space.restrictUniversalEquiv` comes from a morphism of presheaves is not
proved by exhibiting a natural transformation and checking its naturality: the morphism is
produced from the universal pair by part (2) of Stacks 05Y3
(`AlgebraicGeometry.Space.homOfRelativeMorphism`), whose naturality is already proved, and only
the bijectivity of its components is checked here. That is what
`AlgebraicGeometry.Space.restrictUniversalEquiv_apply` supplies.

## References

* [Stacks Project, Tag 0BL2](https://stacks.math.columbia.edu/tag/0BL2)
* [Stacks Project, Tag 0BL3](https://stacks.math.columbia.edu/tag/0BL3)
* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {V Zs Xs : BigFppfOver B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_RelativeHomSchemeComparison :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RelativeHomSchemeComparison
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The fibre product in the site and the product in the slice over the base scheme -/

/-- The fibre product `T ×_V Z` taken in the big fppf site of `S` has underlying scheme a fibre
product of the underlying scheme morphisms, `AlgebraicGeometry.BigFppfOver.toScheme` preserving
fibre products. The square is written with the projection to `Z` first, which is the order in
which the product in the slice over the base scheme presents it. -/
theorem isPullback_toScheme_pullback (z : Zs ⟶ V) {T : BigFppfOver B S hS} (a : T ⟶ V) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.snd a z))
      ((BigFppfOver.toScheme B S hS).map (pullback.fst a z))
      ((BigFppfOver.toScheme B S hS).map z) ((BigFppfOver.toScheme B S hS).map a) :=
  ((BigFppfOver.toScheme B S hS).map_isPullback (IsPullback.of_hasPullback a z)).flip

/-- The product of `Z` and `T` in the category of schemes over the scheme underlying `V` is a
fibre product of their structure morphisms. -/
theorem isPullback_prodLeft (z : Zs ⟶ V) {T : BigFppfOver B S hS} (a : T ⟶ V) :
    IsPullback
      (prod.fst (X := Over.mk ((BigFppfOver.toScheme B S hS).map z))
        (Y := Over.mk ((BigFppfOver.toScheme B S hS).map a))).left
      (prod.snd (X := Over.mk ((BigFppfOver.toScheme B S hS).map z))
        (Y := Over.mk ((BigFppfOver.toScheme B S hS).map a))).left
      ((BigFppfOver.toScheme B S hS).map z) ((BigFppfOver.toScheme B S hS).map a) :=
  Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd) (prodIsProd _ _)

/-- **The geometric content of the comparison.** The fibre product `T ×_V Z` taken in the big
fppf site of `S` has underlying scheme the product of `Z` and `T` in the category of schemes
over the scheme underlying `V`: both are fibre products of the same pair of scheme
morphisms. -/
noncomputable def prodLeftIso (z : Zs ⟶ V) {T : BigFppfOver B S hS} (a : T ⟶ V) :
    (BigFppfOver.toScheme B S hS).obj (pullback a z) ≅
      (Over.mk ((BigFppfOver.toScheme B S hS).map z) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map a)).left :=
  (isPullback_toScheme_pullback z a).isoIsPullback _ _ (isPullback_prodLeft z a)

/-- The isomorphism `AlgebraicGeometry.Space.prodLeftIso` followed by the projection to `Z` is the
image of the second projection `T ×_V Z ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem prodLeftIso_hom_fst (z : Zs ⟶ V) {T : BigFppfOver B S hS} (a : T ⟶ V) :
    (prodLeftIso z a).hom ≫
        (prod.fst (X := Over.mk ((BigFppfOver.toScheme B S hS).map z))
          (Y := Over.mk ((BigFppfOver.toScheme B S hS).map a))).left =
      (BigFppfOver.toScheme B S hS).map (pullback.snd a z) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The isomorphism `AlgebraicGeometry.Space.prodLeftIso` followed by the projection to `T` is the
image of the first projection `T ×_V Z ⟶ T`. -/
@[reassoc (attr := simp)]
theorem prodLeftIso_hom_snd (z : Zs ⟶ V) {T : BigFppfOver B S hS} (a : T ⟶ V) :
    (prodLeftIso z a).hom ≫
        (prod.snd (X := Over.mk ((BigFppfOver.toScheme B S hS).map z))
          (Y := Over.mk ((BigFppfOver.toScheme B S hS).map a))).left =
      (BigFppfOver.toScheme B S hS).map (pullback.fst a z) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The structure morphism to the base scheme of the product of `Z` and `T` in the slice, read
through `AlgebraicGeometry.Space.prodLeftIso`, is the projection to `Z` followed by the
structure morphism of `Z`. -/
@[reassoc (attr := simp)]
theorem prodLeftIso_hom_comp_hom (z : Zs ⟶ V) {T : BigFppfOver B S hS} (a : T ⟶ V) :
    (prodLeftIso z a).hom ≫
        (Over.mk ((BigFppfOver.toScheme B S hS).map z) ⨯
          Over.mk ((BigFppfOver.toScheme B S hS).map a)).hom =
      (BigFppfOver.toScheme B S hS).map (pullback.snd a z ≫ z) := by
  rw [← Over.w (prod.fst (X := Over.mk ((BigFppfOver.toScheme B S hS).map z))
    (Y := Over.mk ((BigFppfOver.toScheme B S hS).map a))), ← Category.assoc,
    prodLeftIso_hom_fst, Functor.map_comp]
  rfl

/-! ### The comparison at a fixed first component -/

/-- The section of the relative morphism functor of Stacks 0BL2 at `a` attached to a morphism
`b : T ×_{a, V} Z ⟶ X` of the site lying over `V`: the underlying morphism of schemes, read
through `AlgebraicGeometry.Space.prodLeftIso`. -/
noncomputable def fibreSectionOfHom (z : Zs ⟶ V) (x : Xs ⟶ V) {T : BigFppfOver B S hS}
    (a : T ⟶ V) (b : pullback a z ⟶ Xs) (hb : b ≫ x = pullback.snd a z ≫ z) :
    Over.mk ((BigFppfOver.toScheme B S hS).map z) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶
      Over.mk ((BigFppfOver.toScheme B S hS).map x) :=
  Over.homMk ((prodLeftIso z a).inv ≫ (BigFppfOver.toScheme B S hS).map b)
    ((Category.assoc _ _ _).trans
      (((congrArg (fun k => (prodLeftIso z a).inv ≫ k)
          (((BigFppfOver.toScheme B S hS).map_comp b x).symm.trans
            (congrArg (BigFppfOver.toScheme B S hS).map hb))).trans
        (congrArg (fun k => (prodLeftIso z a).inv ≫ k)
          (prodLeftIso_hom_comp_hom z a).symm)).trans
        (Iso.inv_hom_id_assoc (prodLeftIso z a) _)))

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.fibreSectionOfHom` is the
inverse of `AlgebraicGeometry.Space.prodLeftIso` followed by the morphism of schemes underlying
`b`. -/
@[simp] theorem fibreSectionOfHom_left (z : Zs ⟶ V) (x : Xs ⟶ V) {T : BigFppfOver B S hS}
    (a : T ⟶ V) (b : pullback a z ⟶ Xs) (hb : b ≫ x = pullback.snd a z ≫ z) :
    (fibreSectionOfHom z x a b hb).left =
      (prodLeftIso z a).inv ≫ (BigFppfOver.toScheme B S hS).map b := rfl

/-- The morphism `T ×_{a, V} Z ⟶ X` of the site underlying a section of the relative morphism
functor of Stacks 0BL2 at `a`. Its underlying morphism of schemes lies over `V`, hence over `S`,
so it comes from a morphism of the site; no containment or size hypothesis is needed. -/
noncomputable def homOfFibreSection (z : Zs ⟶ V) (x : Xs ⟶ V) {T : BigFppfOver B S hS}
    (a : T ⟶ V)
    (m : Over.mk ((BigFppfOver.toScheme B S hS).map z) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶
      Over.mk ((BigFppfOver.toScheme B S hS).map x)) :
    pullback a z ⟶ Xs :=
  BigFppfOver.homOfCompEq B S hS ((prodLeftIso z a).hom ≫ m.left) (by
    have hm : (prodLeftIso z a).hom ≫ m.left ≫ (BigFppfOver.toScheme B S hS).map x =
        (BigFppfOver.toScheme B S hS).map (pullback.snd a z ≫ z) :=
      (congrArg (fun k => (prodLeftIso z a).hom ≫ k)
        (Over.w m : m.left ≫ (BigFppfOver.toScheme B S hS).map x = _)).trans
        (prodLeftIso_hom_comp_hom z a)
    rw [← toScheme_map_comp_inclusion_hom B S hS (pullback.snd a z ≫ z), ← hm,
      ← toScheme_map_comp_inclusion_hom B S hS x]
    simp only [Category.assoc])

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.homOfFibreSection` is
`AlgebraicGeometry.Space.prodLeftIso` followed by the underlying morphism of the section. -/
@[simp] theorem toScheme_map_homOfFibreSection (z : Zs ⟶ V) (x : Xs ⟶ V)
    {T : BigFppfOver B S hS} (a : T ⟶ V)
    (m : Over.mk ((BigFppfOver.toScheme B S hS).map z) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶
      Over.mk ((BigFppfOver.toScheme B S hS).map x)) :
    (BigFppfOver.toScheme B S hS).map (homOfFibreSection z x a m) =
      (prodLeftIso z a).hom ≫ m.left :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS _ _

/-- The morphism of the site underlying a section of the functor of Stacks 0BL2 lies over
`V`. -/
theorem homOfFibreSection_comp (z : Zs ⟶ V) (x : Xs ⟶ V) {T : BigFppfOver B S hS} (a : T ⟶ V)
    (m : Over.mk ((BigFppfOver.toScheme B S hS).map z) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶
      Over.mk ((BigFppfOver.toScheme B S hS).map x)) :
    homOfFibreSection z x a m ≫ x = pullback.snd a z ≫ z := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  change (BigFppfOver.toScheme B S hS).map (homOfFibreSection z x a m ≫ x) =
    (BigFppfOver.toScheme B S hS).map (pullback.snd a z ≫ z)
  rw [Functor.map_comp, toScheme_map_homOfFibreSection, Category.assoc]
  exact (congrArg (fun k => (prodLeftIso z a).hom ≫ k)
    (Over.w m : m.left ≫ (BigFppfOver.toScheme B S hS).map x = _)).trans
    (prodLeftIso_hom_comp_hom z a)

/-- **The comparison at a fixed first component.** For a morphism `a : T ⟶ V` of the big fppf
site of `S`, the morphisms `b : T ×_{a, V} Z ⟶ X` of the site lying over `V` — the second
components of the pairs of Stacks 05Y1 whose first component is `a` — are the sections of the
relative morphism functor of Stacks 0BL2 at `a`. -/
noncomputable def relativeMorphismFibreEquiv (z : Zs ⟶ V) (x : Xs ⟶ V)
    {T : BigFppfOver B S hS} (a : T ⟶ V) :
    { b : pullback a z ⟶ Xs // b ≫ x = pullback.snd a z ≫ z } ≃
      (Over.mk ((BigFppfOver.toScheme B S hS).map z) ⨯
          Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶
        Over.mk ((BigFppfOver.toScheme B S hS).map x)) where
  toFun b := fibreSectionOfHom z x a b.1 b.2
  invFun m := ⟨homOfFibreSection z x a m, homOfFibreSection_comp z x a m⟩
  left_inv b := by
    refine Subtype.ext (BigFppfOver.map_toScheme_injective B S hS ?_)
    change (BigFppfOver.toScheme B S hS).map
        (homOfFibreSection z x a (fibreSectionOfHom z x a b.1 b.2)) =
      (BigFppfOver.toScheme B S hS).map b.1
    rw [toScheme_map_homOfFibreSection, fibreSectionOfHom_left, Iso.hom_inv_id_assoc]
  right_inv m := by
    refine Over.OverMorphism.ext ?_
    change (fibreSectionOfHom z x a (homOfFibreSection z x a m)
        (homOfFibreSection_comp z x a m)).left = m.left
    rw [fibreSectionOfHom_left, toScheme_map_homOfFibreSection, Iso.inv_hom_id_assoc]

/-! ### The pairs of Stacks 05Y1 at a representable test object -/

/-- The pair of Stacks 05Y1 attached to a morphism `a : T ⟶ V` of the site together with a
morphism `b : T ×_{a, V} Z ⟶ X` of the site over `V`: the second component is read through the
identification of the fibre product of representable presheaves with the representable presheaf
of the fibre product taken in the site. -/
noncomputable def relativeMorphismOfSigma (z : Zs ⟶ V) (x : Xs ⟶ V)
    {T : BigFppfOver B S hS}
    (q : Σ a : T ⟶ V, { b : pullback a z ⟶ Xs // b ≫ x = pullback.snd a z ≫ z }) :
    RelativeMorphism B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
      (yoneda.map z) (yoneda.map x) (yoneda.obj T) where
  base := yoneda.map q.1
  morphism :=
    (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) q.1 z).inv ≫ yoneda.map q.2.1
  commutes := by
    rw [Category.assoc, ← Functor.map_comp, q.2.2, Functor.map_comp,
      ← PreservesPullback.iso_inv_snd (yoneda (C := BigFppfOver B S hS)) q.1 z, Category.assoc]

/-- The first component of `AlgebraicGeometry.Space.relativeMorphismOfSigma` is `yoneda.map a`. -/
@[simp] theorem relativeMorphismOfSigma_base (z : Zs ⟶ V) (x : Xs ⟶ V)
    {T : BigFppfOver B S hS}
    (q : Σ a : T ⟶ V, { b : pullback a z ⟶ Xs // b ≫ x = pullback.snd a z ≫ z }) :
    (relativeMorphismOfSigma z x q).base = yoneda.map q.1 := rfl

/-- The second component of `AlgebraicGeometry.Space.relativeMorphismOfSigma` is the inverse of
the comparison of fibre products under the Yoneda embedding followed by `yoneda.map b`. -/
@[simp] theorem relativeMorphismOfSigma_morphism (z : Zs ⟶ V) (x : Xs ⟶ V)
    {T : BigFppfOver B S hS}
    (q : Σ a : T ⟶ V, { b : pullback a z ⟶ Xs // b ≫ x = pullback.snd a z ≫ z }) :
    (relativeMorphismOfSigma z x q).morphism =
      (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) q.1 z).inv ≫
        yoneda.map q.2.1 := rfl

/-- **A pair of Stacks 05Y1 at a representable test object is determined by the morphism `a` of
the site and the morphism `b` of the site it is built from.** The first component determines `a`
and the second determines `b`, both because the Yoneda embedding is faithful. -/
theorem relativeMorphismOfSigma_inj (z : Zs ⟶ V) (x : Xs ⟶ V) {T : BigFppfOver B S hS}
    {q q' : Σ a : T ⟶ V, { b : pullback a z ⟶ Xs // b ≫ x = pullback.snd a z ≫ z }}
    (h : relativeMorphismOfSigma z x q = relativeMorphismOfSigma z x q') : q = q' := by
  obtain ⟨a, b, hb⟩ := q
  obtain ⟨a', b', hb'⟩ := q'
  have ha : a = a' := yoneda.map_injective (congrArg RelativeMorphism.base h)
  subst ha
  have hm : (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) a z).inv ≫ yoneda.map b =
      (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) a z).inv ≫ yoneda.map b' :=
    eq_of_heq (RelativeMorphism.mk.inj h).2
  have hbb : b = b' := yoneda.map_injective ((Iso.cancel_iso_inv_left _ _ _).mp hm)
  subst hbb
  rfl

/-- **Every pair of Stacks 05Y1 at a representable test object comes from a morphism `a` of the
site and a morphism `b` of the site over `V`.** The first component of a pair is a morphism of
representable presheaves, hence `yoneda.map` of a morphism `a` of the site, and its second
component is then a morphism out of `yoneda.obj (T ×_{a, V} Z)`, hence `yoneda.map` of a
morphism of the site. -/
theorem relativeMorphismOfSigma_surj (z : Zs ⟶ V) (x : Xs ⟶ V) {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
      (yoneda.map z) (yoneda.map x) (yoneda.obj T)) :
    ∃ q : Σ a : T ⟶ V, { b : pullback a z ⟶ Xs // b ≫ x = pullback.snd a z ≫ z },
      relativeMorphismOfSigma z x q = p := by
  obtain ⟨a, ha⟩ : ∃ a : T ⟶ V, yoneda.map a = p.base :=
    ⟨yoneda.preimage p.base, yoneda.map_preimage _⟩
  obtain ⟨b, hbm⟩ : ∃ b : pullback a z ⟶ Xs, yoneda.map b =
      (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) a z).hom ≫
        (pullback.congrHom ha (rfl : yoneda.map z = yoneda.map z)).hom ≫ p.morphism :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hb : b ≫ x = pullback.snd a z ≫ z := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hbm]
    simp only [Category.assoc, p.commutes]
    rw [← PreservesPullback.iso_hom_snd_assoc (yoneda (C := BigFppfOver B S hS)) a z
      (yoneda.map z)]
    simp
  refine ⟨⟨a, b, hb⟩, RelativeMorphism.ext_of_base_eq ha ?_⟩
  rw [relativeMorphismOfSigma_morphism]
  change (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) a z).inv ≫ yoneda.map b = _
  rw [hbm, Iso.inv_hom_id_assoc]
  rfl

/-- **The pairs of Stacks 05Y1 at a representable test object.** A pair for the representable
data `yoneda.map z` and `yoneda.map x` at `yoneda.obj T` is a morphism `a : T ⟶ V` of the site
together with a morphism `b : T ×_{a, V} Z ⟶ X` of the site lying over `V`. -/
noncomputable def relativeMorphismEquivSigma (z : Zs ⟶ V) (x : Xs ⟶ V)
    (T : BigFppfOver B S hS) :
    (Σ a : T ⟶ V, { b : pullback a z ⟶ Xs // b ≫ x = pullback.snd a z ≫ z }) ≃
      RelativeMorphism B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) (yoneda.map x) (yoneda.obj T) :=
  Equiv.ofBijective (relativeMorphismOfSigma z x)
    ⟨fun _ _ h => relativeMorphismOfSigma_inj z x h, relativeMorphismOfSigma_surj z x⟩

/-! ### The comparison -/

/-- **The comparison of the relative morphism functor of Stacks 0BL2 with the one of
Stacks 05Y2.** For objects `V`, `Z` and `X` of the big fppf site of `S` and morphisms
`z : Z ⟶ V` and `x : X ⟶ V` of the site, the sections over `T` of the relative morphism functor
of Stacks 05Y2 for the representable data — the pairs `(a, b)` of Stacks 05Y1 at
`yoneda.obj T` — are the pairs consisting of a morphism `a : T ⟶ V` of the site and a section at
`a` of the relative morphism functor `Mor_V(Z, X)` of Stacks 0BL2 over the scheme underlying
`V`.

The two functors are *not* the same object and this is not a renaming: the sum over `a` is
essential, the base of Stacks 0BL2 being the base of the slice its presheaf lives on while the
base of Stacks 05Y2 is an object of the site over `S`, which a test object of that site has many
morphisms to. -/
noncomputable def relativeMorphismEquivRelativeHom (z : Zs ⟶ V) (x : Xs ⟶ V)
    (T : BigFppfOver B S hS) :
    RelativeMorphism B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) (yoneda.map x) (yoneda.obj T) ≃
      Σ a : T ⟶ V,
        (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map z))
            (Over.mk ((BigFppfOver.toScheme B S hS).map x))).obj
          (op (Over.mk ((BigFppfOver.toScheme B S hS).map a))) :=
  (relativeMorphismEquivSigma z x T).symm.trans
    (Equiv.sigmaCongrRight fun a => relativeMorphismFibreEquiv z x a)

/-! ### Compatibility of the comparison with restriction -/

/-- **The comparison map of fibre products taken in the site is the comparison map of the fibre
products of the representable presheaves.** Both sides are morphisms into
`pullback (yoneda.map a) (yoneda.map z)`, so they are compared componentwise. -/
theorem yoneda_map_mapFst (z : Zs ⟶ V) {T T' : BigFppfOver B S hS} (t : T' ⟶ T) (a : T ⟶ V)
    (hbase : yoneda.map t ≫ yoneda.map a = yoneda.map (t ≫ a)) :
    pullback.mapFst (yoneda.map t) (yoneda.map a) (yoneda.map z) =
      (pullback.congrHom hbase (rfl : yoneda.map z = yoneda.map z)).hom ≫
        (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) (t ≫ a) z).inv ≫
          yoneda.map (pullback.mapFst t a z) ≫
            (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) a z).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.mapFst_fst]
    simp only [Category.assoc, PreservesPullback.iso_hom_fst]
    rw [← yoneda.map_comp (pullback.mapFst t a z) (pullback.fst a z), pullback.mapFst_fst,
      yoneda.map_comp (pullback.fst (t ≫ a) z) t,
      PreservesPullback.iso_inv_fst_assoc (yoneda (C := BigFppfOver B S hS)) (t ≫ a) z]
    simp
  · rw [pullback.mapFst_snd]
    simp only [Category.assoc, PreservesPullback.iso_hom_snd]
    rw [← yoneda.map_comp (pullback.mapFst t a z) (pullback.snd a z), pullback.mapFst_snd,
      PreservesPullback.iso_inv_snd (yoneda (C := BigFppfOver B S hS)) (t ≫ a) z]
    simp

/-- **Restriction of a pair at representable data is base change of its morphism `b` in the
site.** This is the compatibility of the comparison with the restriction maps of the relative
morphism functor. -/
theorem restrict_relativeMorphismOfSigma (z : Zs ⟶ V) (x : Xs ⟶ V)
    {T T' : BigFppfOver B S hS} (t : T' ⟶ T) (a : T ⟶ V) (b : pullback a z ⟶ Xs)
    (hb : b ≫ x = pullback.snd a z ≫ z) :
    RelativeMorphism.restrict (yoneda.map t)
        (relativeMorphismOfSigma z x ⟨a, b, hb⟩) =
      relativeMorphismOfSigma z x ⟨t ≫ a, pullback.mapFst t a z ≫ b, by
        rw [Category.assoc, hb, ← Category.assoc, pullback.mapFst_snd]⟩ := by
  have hbase : yoneda.map t ≫ yoneda.map a = yoneda.map (t ≫ a) := (yoneda.map_comp t a).symm
  refine RelativeMorphism.ext_of_base_eq hbase ?_
  rw [RelativeMorphism.restrict_morphism_mapFst]
  change pullback.mapFst (yoneda.map t) (yoneda.map a) (yoneda.map z) ≫
      (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) a z).inv ≫ yoneda.map b =
    (pullback.congrHom hbase (rfl : yoneda.map z = yoneda.map z)).hom ≫
      (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) (t ≫ a) z).inv ≫
        yoneda.map (pullback.mapFst t a z ≫ b)
  rw [yoneda_map_mapFst z t a hbase, yoneda.map_comp (pullback.mapFst t a z) b]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **The comparison at a fixed first component is compatible with base change.** Base changing
the morphism `b` of the site along `t` is composing the corresponding section of the functor of
Stacks 0BL2 with the comparison `prod.map (𝟙 Z) k` of products in the slice over the base
scheme. -/
theorem fibreSectionOfHom_mapFst (z : Zs ⟶ V) (x : Xs ⟶ V) {T T' : BigFppfOver B S hS}
    (t : T' ⟶ T) (a : T ⟶ V) (b : pullback a z ⟶ Xs) (hb : b ≫ x = pullback.snd a z ≫ z)
    (k : Over.mk ((BigFppfOver.toScheme B S hS).map (t ≫ a)) ⟶
      Over.mk ((BigFppfOver.toScheme B S hS).map a))
    (hk : k.left = (BigFppfOver.toScheme B S hS).map t)
    (hb' : (pullback.mapFst t a z ≫ b) ≫ x = pullback.snd (t ≫ a) z ≫ z) :
    fibreSectionOfHom z x (t ≫ a) (pullback.mapFst t a z ≫ b) hb' =
      prod.map (𝟙 (Over.mk ((BigFppfOver.toScheme B S hS).map z))) k ≫
        fibreSectionOfHom z x a b hb := by
  have key : (BigFppfOver.toScheme B S hS).map (pullback.mapFst t a z) ≫
      (prodLeftIso z a).hom =
    (prodLeftIso z (t ≫ a)).hom ≫
      (prod.map (𝟙 (Over.mk ((BigFppfOver.toScheme B S hS).map z))) k).left := by
    refine (isPullback_prodLeft z a).hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ← Over.comp_left, prod.map_fst, Category.comp_id,
        prodLeftIso_hom_fst, prodLeftIso_hom_fst, ← Functor.map_comp, pullback.mapFst_snd]
    · rw [Category.assoc, Category.assoc, ← Over.comp_left, prod.map_snd, Over.comp_left, hk,
        prodLeftIso_hom_snd, ← Category.assoc, prodLeftIso_hom_snd, ← Functor.map_comp,
        ← Functor.map_comp, pullback.mapFst_fst, Functor.map_comp]
  have key2 : (prodLeftIso z (t ≫ a)).inv ≫
      (BigFppfOver.toScheme B S hS).map (pullback.mapFst t a z) =
    (prod.map (𝟙 (Over.mk ((BigFppfOver.toScheme B S hS).map z))) k).left ≫
      (prodLeftIso z a).inv := by
    rw [Iso.inv_comp_eq]
    exact ((Iso.eq_comp_inv _).mpr key).trans (Category.assoc _ _ _)
  refine Over.OverMorphism.ext ?_
  rw [fibreSectionOfHom_left, Over.comp_left, fibreSectionOfHom_left,
    (BigFppfOver.toScheme B S hS).map_comp (pullback.mapFst t a z) b,
    ← Category.assoc, key2, Category.assoc]

/-! ### Representability -/

section Representable

variable (z : Zs ⟶ V) (x : Xs ⟶ V)
  (W : Over ((BigFppfOver.toScheme B S hS).obj V)) (hW : B.Contains W.left)

/-- A representing object of the relative morphism functor of Stacks 0BL2 over the scheme
underlying `V`, read as an object of the big fppf site of `S`. -/
def siteObjOfOver : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hW (W.hom ≫ B.inclusion.map V.hom)

/-- The structure morphism to `V` of a representing object read in the site. -/
def siteHomOfOver : siteObjOfOver W hW ⟶ V :=
  Over.homMk (ObjectProperty.homMk W.hom) (by apply ObjectProperty.hom_ext; rfl)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.siteHomOfOver` is the structure
morphism of `W`. -/
@[simp] theorem toScheme_map_siteHomOfOver :
    (BigFppfOver.toScheme B S hS).map (siteHomOfOver W hW) = W.hom := rfl

/-- A morphism of the site into a representing object, read as a morphism over the base scheme
into the representing object. -/
def overHomOfSiteHom {T : BigFppfOver B S hS} (h : T ⟶ siteObjOfOver W hW) :
    Over.mk ((BigFppfOver.toScheme B S hS).map (h ≫ siteHomOfOver W hW)) ⟶ W :=
  Over.homMk ((BigFppfOver.toScheme B S hS).map h)
    ((BigFppfOver.toScheme B S hS).map_comp h (siteHomOfOver W hW)).symm

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.overHomOfSiteHom` is the
morphism of schemes underlying `h`. -/
@[simp] theorem overHomOfSiteHom_left {T : BigFppfOver B S hS} (h : T ⟶ siteObjOfOver W hW) :
    (overHomOfSiteHom W hW h).left = (BigFppfOver.toScheme B S hS).map h := rfl

/-- The morphism of schemes underlying a morphism `a : T ⟶ V` of the site together with a
morphism over the base scheme lying over `a`. Its type does not depend on `a`, which is what
makes a dependent pair determined by it. -/
def sigmaOverLeft {T : BigFppfOver B S hS}
    (q : Σ a : T ⟶ V, (Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶ W)) :
    (BigFppfOver.toScheme B S hS).obj T ⟶ W.left :=
  q.2.left

/-- **A morphism over the base scheme into a representing object determines its first
component.** The first component `a` is recovered from the underlying morphism of schemes by
composing with the structure morphism of `W`, so a dependent pair is determined by that
morphism. -/
theorem sigma_overHom_ext {T : BigFppfOver B S hS}
    {q q' : Σ a : T ⟶ V, (Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶ W)}
    (h : sigmaOverLeft W q = sigmaOverLeft W q') : q = q' := by
  obtain ⟨a, k⟩ := q
  obtain ⟨a', k'⟩ := q'
  have h' : k.left = k'.left := h
  have hwk : k.left ≫ W.hom = (BigFppfOver.toScheme B S hS).map a := Over.w k
  have hwk' : k'.left ≫ W.hom = (BigFppfOver.toScheme B S hS).map a' := Over.w k'
  have ha : a = a' := by
    refine BigFppfOver.map_toScheme_injective B S hS ?_
    change (BigFppfOver.toScheme B S hS).map a = (BigFppfOver.toScheme B S hS).map a'
    rw [← hwk, ← hwk', h']
  subst ha
  exact congrArg (Sigma.mk a) (Over.OverMorphism.ext h')

/-- The morphism of the site into a representing object attached to a morphism `a : T ⟶ V` of
the site together with a morphism over the base scheme lying over `a`. Its underlying morphism
of schemes lies over `V`, hence over `S`. -/
noncomputable def siteHomOfSigma {T : BigFppfOver B S hS}
    (q : Σ a : T ⟶ V, (Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶ W)) :
    T ⟶ siteObjOfOver W hW :=
  BigFppfOver.homOfCompEq B S hS q.2.left (by
    have h1 : (q.2.left ≫ W.hom) ≫ B.inclusion.map V.hom =
        (BigFppfOver.toScheme B S hS).map q.1 ≫ B.inclusion.map V.hom :=
      congrArg (fun m => m ≫ B.inclusion.map V.hom)
        (Over.w q.2 : q.2.left ≫ W.hom = (BigFppfOver.toScheme B S hS).map q.1)
    exact (Category.assoc q.2.left W.hom (B.inclusion.map V.hom)).symm.trans
      (h1.trans (toScheme_map_comp_inclusion_hom B S hS q.1)))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.siteHomOfSigma` is the underlying
morphism of schemes of the second component. -/
@[simp] theorem toScheme_map_siteHomOfSigma {T : BigFppfOver B S hS}
    (q : Σ a : T ⟶ V, (Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶ W)) :
    (BigFppfOver.toScheme B S hS).map (siteHomOfSigma W hW q) = q.2.left :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS _ _

/-- **Morphisms of the site into a representing object.** A morphism `T ⟶ W` of the site is a
morphism `a : T ⟶ V` of the site together with a morphism `T ⟶ W` over the base scheme lying
over `a`. -/
noncomputable def siteHomEquivSigma (T : BigFppfOver B S hS) :
    (T ⟶ siteObjOfOver W hW) ≃
      Σ a : T ⟶ V, (Over.mk ((BigFppfOver.toScheme B S hS).map a) ⟶ W) :=
  Equiv.ofBijective (fun h => ⟨h ≫ siteHomOfOver W hW, overHomOfSiteHom W hW h⟩)
    ⟨fun h h' hh => by
      refine BigFppfOver.map_toScheme_injective B S hS ?_
      change (BigFppfOver.toScheme B S hS).map h = (BigFppfOver.toScheme B S hS).map h'
      exact congrArg (sigmaOverLeft W) hh,
      fun q => ⟨siteHomOfSigma W hW q, sigma_overHom_ext W (by
        change (overHomOfSiteHom W hW (siteHomOfSigma W hW q)).left = sigmaOverLeft W q
        rw [overHomOfSiteHom_left, toScheme_map_siteHomOfSigma]
        rfl)⟩⟩

/-- The equivalence `AlgebraicGeometry.Space.siteHomEquivSigma` sends `h` to the pair consisting
of `h ≫ siteHomOfOver W hW` and `AlgebraicGeometry.Space.overHomOfSiteHom W hW h`. -/
@[simp] theorem siteHomEquivSigma_apply (T : BigFppfOver B S hS)
    (h : T ⟶ siteObjOfOver W hW) :
    siteHomEquivSigma W hW T h = ⟨h ≫ siteHomOfOver W hW, overHomOfSiteHom W hW h⟩ := rfl

variable
  (e : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map z))
    (Over.mk ((BigFppfOver.toScheme B S hS).map x))).RepresentableBy W)

/-- **The universal morphism of the site**: the morphism `W ×_V Z ⟶ X` of the site which the
identity of the representing object corresponds to under the comparison at a fixed first
component. -/
noncomputable def universalFibreHom : pullback (siteHomOfOver W hW) z ⟶ Xs :=
  ((relativeMorphismFibreEquiv z x (siteHomOfOver W hW)).symm (e.homEquiv (𝟙 W))).1

/-- The universal morphism of the site lies over `V`. -/
theorem universalFibreHom_comp :
    universalFibreHom z x W hW e ≫ x = pullback.snd (siteHomOfOver W hW) z ≫ z :=
  ((relativeMorphismFibreEquiv z x (siteHomOfOver W hW)).symm (e.homEquiv (𝟙 W))).2

/-- The universal morphism of the site corresponds to the identity of the representing
object. -/
theorem fibreSectionOfHom_universalFibreHom :
    fibreSectionOfHom z x (siteHomOfOver W hW) (universalFibreHom z x W hW e)
        (universalFibreHom_comp z x W hW e) =
      e.homEquiv (𝟙 W) :=
  (relativeMorphismFibreEquiv z x (siteHomOfOver W hW)).apply_symm_apply (e.homEquiv (𝟙 W))

/-- **The universal pair of Stacks 05Y1.** The pair over the representing object which
corresponds to the identity of `W` under the comparison of the two relative morphism
functors. -/
noncomputable def universalRelativeMorphism :
    RelativeMorphism B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
      (yoneda.map z) (yoneda.map x) (yoneda.obj (siteObjOfOver W hW)) :=
  relativeMorphismOfSigma z x
    ⟨siteHomOfOver W hW, universalFibreHom z x W hW e, universalFibreHom_comp z x W hW e⟩

/-- **The comparison of the two relative morphism functors, read at the representing object.**
For every object `T` of the site, the morphisms `T ⟶ W` of the site are the pairs of
Stacks 05Y1 at `yoneda.obj T`: compose the identification of morphisms into the representing
object with the representability of the functor of Stacks 0BL2 and with the comparison. -/
noncomputable def restrictUniversalEquiv (T : BigFppfOver B S hS) :
    (T ⟶ siteObjOfOver W hW) ≃
      RelativeMorphism B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) (yoneda.map x) (yoneda.obj T) :=
  ((siteHomEquivSigma W hW T).trans
      (Equiv.sigmaCongrRight fun a : T ⟶ V =>
        (e.homEquiv (X := Over.mk ((BigFppfOver.toScheme B S hS).map a))).trans
          (relativeMorphismFibreEquiv z x a).symm)).trans
    (relativeMorphismEquivSigma z x T)

/-- **The comparison at the representing object is restriction of the universal pair.** This is
the naturality that makes the identification of
`AlgebraicGeometry.Space.restrictUniversalEquiv` the one induced by a single morphism of
presheaves. -/
theorem restrictUniversalEquiv_apply (T : BigFppfOver B S hS)
    (h : T ⟶ siteObjOfOver W hW) :
    restrictUniversalEquiv z x W hW e T h =
      RelativeMorphism.restrict (yoneda.map h) (universalRelativeMorphism z x W hW e) := by
  have hL : restrictUniversalEquiv z x W hW e T h =
      relativeMorphismOfSigma z x
        ⟨h ≫ siteHomOfOver W hW,
          (relativeMorphismFibreEquiv z x (h ≫ siteHomOfOver W hW)).symm
            (e.homEquiv (overHomOfSiteHom W hW h))⟩ := rfl
  rw [hL, universalRelativeMorphism, restrict_relativeMorphismOfSigma]
  refine congrArg (relativeMorphismOfSigma z x) (congrArg (Sigma.mk _) ?_)
  refine (Equiv.symm_apply_eq (relativeMorphismFibreEquiv z x _)).mpr ?_
  have hcomp := e.homEquiv_comp (overHomOfSiteHom W hW h) (𝟙 W)
  rw [Category.comp_id] at hcomp
  refine hcomp.trans (Eq.symm ?_)
  refine Eq.trans ?_
    (relativeHom_map _ _ (overHomOfSiteHom W hW h).op (e.homEquiv (𝟙 W))).symm
  refine Eq.trans ?_ (congrArg (fun m => prod.map
      (𝟙 (Over.mk ((BigFppfOver.toScheme B S hS).map z))) (overHomOfSiteHom W hW h) ≫ m)
    (fibreSectionOfHom_universalFibreHom z x W hW e))
  exact fibreSectionOfHom_mapFst z x h (siteHomOfOver W hW) (universalFibreHom z x W hW e)
    (universalFibreHom_comp z x W hW e) (overHomOfSiteHom W hW h) rfl
    (by rw [Category.assoc, universalFibreHom_comp, ← Category.assoc, pullback.mapFst_snd])

include hW e in
/-- **Stacks 05Y6 for algebraic spaces, at representable data.** Let `V`, `Z` and `X` be objects
of the big fppf site of `S` and let `z : Z ⟶ V` and `x : X ⟶ V` be morphisms of the site. If the
relative morphism functor `Mor_V(Z, X)` of Stacks 0BL2 is represented by a scheme `W` over the
scheme underlying `V` whose underlying scheme lies in the site, then the relative morphism
functor `Mor_{yoneda V}(yoneda Z, yoneda X)` of Stacks 05Y2 is an algebraic space over `S` —
indeed it is representable, by `W` read as an object of the site.

This is the source's Stacks 05Y6 transported to algebraic spaces: its hypotheses are supplied on
the scheme side, where the library proves representability of the functor of Stacks 0BL2 for
`z` finite locally free and `x` affine (Stacks 0BL3,
`Stacks.Morphisms.relativeHom_representableBy_affineHom`) and more generally under the condition
of Stacks 0BL4, with the gluing over a chart of the base already carried out there. What is added
here is the comparison of the two functors and the passage of the representing object into the
site. -/
theorem isAlgebraicSpace_relativeHom_yoneda_of_representableBy :
    IsAlgebraicSpace B S hS
      (relativeHom B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) (yoneda.map x) (isAlgebraicSpace_yoneda B S hS Zs)
        (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V)) := by
  set φ := homOfRelativeMorphism (hZ := isAlgebraicSpace_yoneda B S hS Zs)
    (hX := isAlgebraicSpace_yoneda B S hS Xs) (hQ := isAlgebraicSpace_yoneda B S hS V)
    (universalRelativeMorphism z x W hW e)
  have hiso : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    obtain ⟨T⟩ := T
    rw [isIso_iff_bijective]
    have hfun : φ.app (op T) =
        (fun p => (relativeHomSections B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
            (yoneda.map z) (yoneda.map x) (isAlgebraicSpace_yoneda B S hS Zs)
            (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V) T).symm p) ∘
          restrictUniversalEquiv z x W hW e T := by
      funext h
      exact congrArg _ (restrictUniversalEquiv_apply z x W hW e T h).symm
    rw [hfun]
    exact (Equiv.symm _).bijective.comp (restrictUniversalEquiv z x W hW e T).bijective
  exact (isAlgebraicSpace_yoneda B S hS (siteObjOfOver W hW)).of_iso (@asIso _ _ _ _ φ hiso)

end Representable

/-- **Stacks 05Y6 for algebraic spaces.** Let `V`, `Z` and `X` be objects of the big fppf site
of `S`, let `z : Z ⟶ V` be finite locally free and let `x : X ⟶ V` be affine. Then the relative
morphism functor `Mor_{yoneda V}(yoneda Z, yoneda X)` of Stacks 05Y2 is an algebraic space
over `S`.

This is the source's Stacks 05Y6 together with the gluing of Stacks 02WR, for algebraic spaces.
Neither the base nor the target is assumed affine: the scheme-level input is Stacks 0BL3
(`Stacks.Morphisms.relativeHom_representableBy_affineHom`), which is Stacks 05Y6 glued over an
affine chart of the base and already carries the gluing, and the comparison of the two relative
morphism functors is
`AlgebraicGeometry.Space.relativeMorphismEquivRelativeHom`.

The one hypothesis that remains is the size condition: the representing object produced on the
scheme side must satisfy the cutoff of the big fppf site, and the hypothesis is asked only of
the objects that are affine over the base, which is what Stacks 0BL3 produces. -/
theorem isAlgebraicSpace_relativeHom_yoneda_of_isAffineHom (z : Zs ⟶ V) (x : Xs ⟶ V)
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z)]
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map x)]
    (hsize : ∀ W : Over ((BigFppfOver.toScheme B S hS).obj V),
      _root_.AlgebraicGeometry.IsAffineHom W.hom →
      (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map z))
          (Over.mk ((BigFppfOver.toScheme B S hS).map x))).RepresentableBy W →
        B.Contains W.left) :
    IsAlgebraicSpace B S hS
      (relativeHom B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) (yoneda.map x) (isAlgebraicSpace_yoneda B S hS Zs)
        (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V)) := by
  obtain ⟨W, hWaff, ⟨eW⟩⟩ := Stacks.Morphisms.relativeHom_representableBy_affineHom
    ((BigFppfOver.toScheme B S hS).map z) ((BigFppfOver.toScheme B S hS).map x)
  exact isAlgebraicSpace_relativeHom_yoneda_of_representableBy z x W
    (hsize W hWaff eW) eW

end AlgebraicGeometry.Space

end
