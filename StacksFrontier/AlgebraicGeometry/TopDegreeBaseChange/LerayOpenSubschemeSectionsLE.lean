module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeSections

/-!
# Sections over an open and over a smaller open subscheme, at the source of the Leray comparison

`LerayOpenSubschemeSections.lean` crosses the degreewise source of the Leray comparison of
[Stacks, Tag 0D5W] for `f : X ⟶ S` over an open `V ⊆ S` with its source for the restricted
morphism `f ∣_ V` over the whole of the open subscheme `f⁻¹V`. This file does the same at an
**arbitrary** open `U ≤ f⁻¹V` of `X` in place of `f⁻¹V` itself, where the restricted morphism is
`AlgebraicGeometry.Scheme.Hom.resLE f V U e : U ⟶ V`.

The tail of conclusion (c) of [Stacks, Tag 0EX3] needs exactly that generality: its
[Stacks, Tag 089W] factor sits at `h'.resLE (f'⁻¹V) (f''⁻¹W)`, whose upstairs open `f''⁻¹W` is
strictly smaller than `h'⁻¹(f'⁻¹V)`, while the `γ⁺` side reads the same factor at the
unrestricted `h'` over `f'⁻¹V`. The ledger of `BaseChangeSectionsTail.lean` records the
measurement that fixes the shape: `IsAffineHom (h' ∣_ (f'⁻¹V))` is **not** available and cannot be,
so the passage must not go through `…AffineComparison.cohomologyIsoPushforwardOverOpen`, whose
first hypothesis is exactly that.

*Why only one route, where the `U = f⁻¹V` file has two.* At `U = f⁻¹V` the crossing is an
isomorphism and the `ψ` side presents it a second way, through [Stacks, Tag 01E5] undervied; the
two routes are then identified by `…TopDegreeBaseChange.preimageSectionsOpenSubschemeIso_eq`. Once
`U < f⁻¹V` the crossing is no longer invertible — it is the restriction of sections from `f⁻¹V` to
`U` — and the `ψ` route has no analogue, because `(f.resLE V U e)_*(F|_U)` is not `(f_* F)|_V`. So
only the `γ⁺` route generalises, and `…preimageSectionsOpenSubschemePushforwardIso` with
`…preimageSectionsOpenSubschemeIso_eq` stay special to `U = f⁻¹V`.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsRestrictLE` — restriction of
  sections from `f⁻¹V` down to `U`, read over `Γ(S, V)` through
  `AlgebraicGeometry.Scheme.Hom.appLE`. It is
  `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpenRestrictLE` whiskered by restriction of
  scalars along `f^♯` at `V`, with its target *declared* at the `appLE` spelling: the two readings
  of the scalars agree by `rfl`, and naming the target is what makes the conversion run once, in
  term mode.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsOpenSubschemeLE` — **the model
  crossing at the degreewise source of the Leray comparison, at an arbitrary `U ≤ f⁻¹V`**:
  sections over `f⁻¹V` restrict to the global sections of the restriction to the open subscheme
  `U`, read over `Γ(S, V)`. No hypothesis on `f`, on `V`, on `U` or on the module.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.appLE_comp_topIso_inv_hom` — the two routes from
  the functions on `V` to the functions on the open subscheme `U` agree, as ring homomorphisms.
  This is Mathlib's `AlgebraicGeometry.arrowResLEAppIso` repackaged; see the implementation notes
  for the two declarations in other subtrees that repackage it at the `CommRingCat` level.

## Implementation notes

*The one thing that is not free: the two readings of the scalars.* The source reads them as `f^♯`
at `V` and then the restriction map of `𝒪_X` from `f⁻¹V` to `U` — which is `f.appLE V U e` on the
nose — and then `AlgebraicGeometry.Scheme.Opens.topIso` at `U`; the target reads them as `topIso`
at `V` and then `(f.resLE V U e)^♯` at `⊤`. The two composites are equal ring maps by
`appLE_comp_topIso_inv_hom`, so the passage is `…TopDegreeBaseChange.restrictScalarsSquareIso`,
exactly as in the `U = f⁻¹V` file.

*Why that square is proved from Mathlib and not from the tree.* The same commuting square is
already in the tree twice at the `CommRingCat` level: `Stacks.Morphisms.appTop_resLE` and
`Stacks.Morphisms.topIso_symm_hom_comp_appTop_resLE`
(`AlgebraicGeometry/Morphisms/FiniteStratificationInvariant.lean`), and
`Stacks.AlgebraicGeometry.Slicing.resLE_appTop_topIso`
(`AlgebraicGeometry/Groupoids/Slicing/FlatBaseChangeOnIntersection.lean`). All three are one-line
consequences of Mathlib's `AlgebraicGeometry.arrowResLEAppIso`, and so is the ring-homomorphism
form stated here, which is the only form `CategoryTheory.ModuleCat.restrictScalars` consumes. The
two tree files sit in the Fitting-stratification and flat-descent subtrees; importing either into
the Leray chain to reach a one-line repackaging would drag unrelated subject matter into a
cohomology file, so the Mathlib iso is used directly and the overlap is noted in
`BaseChangeSectionsTail.lean` instead.

*Four `rfl`s, which is why this costs two declarations.* With the **ringed-space**
restriction `…HigherDirectImage.moduleRestriction`, `moduleRestriction X U ⋙ sectionsOverOpen
(U : Scheme) ⊤` **is** `sectionsOverOpen X (U.ι ''ᵁ ⊤)` for every open `U`, not only for a
preimage; `(opensMap (f.resLE V U e)).obj ⊤` **is** `⊤`;
`ModuleCat.restrictScalars b ⋙ ModuleCat.restrictScalars a` **is**
`ModuleCat.restrictScalars (b.comp a)`; and `(f.appLE V U e).hom` **is** the restriction map of
`𝒪_X` composed after `f^♯` at `V`. So the crossing of the two sections functors is
`…TopDegreeBaseChange.sectionsOnImageTopNatIso` at `U` and nothing about sections is re-proved.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 0D5W] carries its attribute where the Leray
comparison is proved invertible, and conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage (moduleRestriction)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen preimageSections sectionsOverOpenRestrictLE)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)

/-! ### The two routes from the functions on `V` to the functions on `U` -/

/-- **The functions on the open subscheme `U` are reached from the functions on `V` by either
route.** Pulling a section of `𝒪_S` over `V` back along `f`, restricting it to `U` and then
reading it on the open subscheme `U` is the same as reading it on the open subscheme `V` and
pulling it back along the restricted morphism `AlgebraicGeometry.Scheme.Hom.resLE f V U e`.

This is Mathlib's `AlgebraicGeometry.arrowResLEAppIso`, whose commuting square is exactly the two
routes, stated as an equality of ring homomorphisms because that is the form
`CategoryTheory.ModuleCat.restrictScalars` consumes. At `U = f⁻¹V` and `e = le_rfl` it is
`…TopDegreeBaseChange.app_comp_topIso_inv_hom`. -/
theorem appLE_comp_topIso_inv_hom :
    ((Scheme.Opens.topIso U).inv.hom).comp ((f.appLE V U e).hom) =
      (((f.resLE V U e).appTop).hom).comp ((Scheme.Opens.topIso V).inv.hom) := by
  have hw : (Scheme.Opens.topIso V).hom ≫ f.appLE V U e =
      (f.resLE V U e).appTop ≫ (Scheme.Opens.topIso U).hom :=
    (arrowResLEAppIso f V U e).hom.w
  have h : f.appLE V U e ≫ (Scheme.Opens.topIso U).inv =
      (Scheme.Opens.topIso V).inv ≫ (f.resLE V U e).appTop := by
    rw [← Iso.inv_hom_id_assoc (Scheme.Opens.topIso V) (f.appLE V U e), hw, Category.assoc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (CommRingCat.hom_comp _ _).symm.trans
    ((congrArg CommRingCat.Hom.hom h).trans (CommRingCat.hom_comp _ _))

/-! ### The crossing at the source of the Leray comparison -/

/-- **Sections over `f⁻¹V` restrict to sections over `U`, read over `Γ(S, V)`.** For a morphism of
schemes `f : X ⟶ S`, an open `V ⊆ S` and an open `U ≤ f⁻¹V` of `X`, the restriction maps
`ℱ(f⁻¹V) ⟶ ℱ(U)` of a sheaf of `𝒪_X`-modules, assembled into a transformation of functors valued
in `Γ(S, V)`-modules with the scalars on the target read along `f.appLE V U e`. -/
def preimageSectionsRestrictLE :
    preimageSections f.toLRSHom.toShHom V ⟶
      sectionsOverOpen X.toRingedSpace U ⋙
        ModuleCat.restrictScalars (f.appLE V U e).hom :=
  Functor.whiskerRight (sectionsOverOpenRestrictLE X.toRingedSpace e)
    (ModuleCat.restrictScalars (f.app V).hom)

/-- **Sections over `f⁻¹V` restrict to the global sections of the restriction to the open
subscheme `U`.** For a morphism of schemes `f : X ⟶ S`, an open `V ⊆ S` and an open `U ≤ f⁻¹V` of
`X`, the degreewise source of the Leray comparison of [Stacks, Tag 0D5W] for `f` over `V` maps to
the degreewise source of the Leray comparison for the restricted morphism
`AlgebraicGeometry.Scheme.Hom.resLE f V U e` over `⊤`, composed with the restriction to the open
subscheme `U` and read over `Γ(S, V)` by restriction of scalars along
`AlgebraicGeometry.Scheme.Opens.topIso` at `V`:

> `Γ(f⁻¹V, -) ⟶ (-)|_U` followed by `Γ((f.resLE V U e)⁻¹⊤, -)`, over `Γ(S, V)`.

It is the restriction `preimageSectionsRestrictLE`, then the crossing
`…TopDegreeBaseChange.sectionsOnImageTopNatIso` of the two sections functors at the open `U` of
`X`, then the identification `…TopDegreeBaseChange.restrictScalarsSquareIso` of the two readings
of the scalars, whose input is `appLE_comp_topIso_inv_hom`.

At `U = f⁻¹V` and `e = le_rfl` the last two factors are those of
`…TopDegreeBaseChange.preimageSectionsOpenSubschemeIso` and the first is the identity, up to
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`; once `U < f⁻¹V` the transformation is no
longer invertible. There is no hypothesis on `f`, on `V`, on `U` or on the module. -/
def preimageSectionsOpenSubschemeLE :
    preimageSections f.toLRSHom.toShHom V ⟶
      moduleRestriction X.toRingedSpace U ⋙
        preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom :=
  preimageSectionsRestrictLE f V e ≫
    Functor.whiskerRight (sectionsOnImageTopNatIso X U).inv
        (ModuleCat.restrictScalars (f.appLE V U e).hom) ≫
      Functor.whiskerLeft
        (moduleRestriction X.toRingedSpace U ⋙ sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
        (restrictScalarsSquareIso _ _ _ _ (appLE_comp_topIso_inv_hom f V e)).hom

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
