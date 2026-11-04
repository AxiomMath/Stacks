module

public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.MateUnitCounit
public import StacksFrontier.AlgebraicGeometry.AffineQcohRestriction.Basic

/-!
# Direct image commutes with restriction, and the unit and counit of Tag 01SB are local

Let `f : X ⟶ S` be a morphism of schemes, `A = f_* 𝒪_X`, `V` an open of `S` and `U = f ⁻¹ᵁ V`.
The direct image of `𝒪_X`-modules over `A`, followed by restriction to `V`, agrees with
restriction to `U` followed by the direct image over `(f|_U)_* 𝒪_U`.  This is the square of direct
images in the *restriction* direction, and it is the Beck--Chevalley comparison of the square of
right adjoints `Stacks.AlgebraicGeometry.AffineQcohRestriction.rightSquare`.

Together with the general transfer in
`StacksFrontier/AlgebraicGeometry/QcohRestrictEquiv/MateUnitCounit.lean` and the locality of
invertibility in `StacksFrontier/AlgebraicGeometry/QcohRestrictEquiv/IsoLocality.lean`, this
reduces the two remaining hypotheses `hunit` and `hcounit` of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`
to the same statements over the affine opens of `S`.

## Main definitions

* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.pushRestrict`: the square
  `f_* ⋙ (·)|_V ⟶ (·)|_U ⋙ (f|_U)_*`, as the Beck--Chevalley comparison of `rightSquare`.

## Main results

* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.pushRestrict_app_val_app`: **its component over an
  open `W` of `V` is the transport of sections of `M` along
  `f ⁻¹ᵁ (V.ι ''ᵁ W) = U.ι ''ᵁ ((f|_U) ⁻¹ᵁ W)`**, and hence
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_pushRestrict`: **the square is invertible**,
  i.e. the Beck--Chevalley condition holds for it.  So direct image commutes with restriction to
  an open and its preimage.
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_restrict_unit_iff` and
  `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_restrict_counit_iff`: the unit resp. counit of
  `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackPushforwardAdjunction` at `f`,
  restricted to `V` resp. `U`, is invertible if and only if the unit resp. counit at `f|_U` is
  invertible at the restricted module.
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_pushRestrictRing`: locality of
  invertibility for `A`-modules, with restriction in the retyped form the square uses.  This is
  `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_restrictOver` with the identity
  replaced by `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing`.
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_unit_of_isIso_unit_resPreimage` and
  `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_counit_of_isIso_counit_resPreimage`:
  **the unit and the counit are local on `S`**, for an arbitrary open cover.
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_unit_of_isIso_unit_affineOpens` and
  `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_counit_of_isIso_counit_affineOpens`: the same
  over the cover of `S` by its affine opens.

## Route

`Stacks.CategoryTheory.beckChevalley_app` writes the comparison as the composite of the unit of
`restrictOverAdjunction`, the inverse of `rightSquare` and the counit of
`restrictCompareAdjunction`.  All three of those are built from
`SheafOfModules.pushforwardPushforwardAdj`, `SheafOfModules.pushforwardComp` and
`SheafOfModules.pushforwardCongr₂`, each of which acts on a section by a single restriction map of
the sheaf `M`.  So the component is three successive restriction maps of `M`, between opens of `X`
which are equal by
`Stacks.AlgebraicGeometry.AffineQcohRestriction.preimage_image_eq_image_resLE_preimage`; the opens
of a space form a thin category, so that composite is the transport along that equality, which is
invertible.  Invertibility of the square then follows objectwise and componentwise through
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app`.

The reduction to an open cover is then
`Stacks.CategoryTheory.isIso_map_unit_iff` and `Stacks.CategoryTheory.isIso_map_counit_iff`,
whose single hypothesis is exactly this invertibility, fed into the two locality statements: for
the counit,
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_restrictOver` at the cover of `X` by
the preimages; for the unit, its restatement here at
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing`, which the lemma
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward` already allows,
being stated for an arbitrary morphism of sheaves of rings.

## Transparency gotchas

The component equation is proved elementwise and closed by a single `exact` against
`Stacks.CategoryTheory.map_map_map_apply`, a standalone statement about a functor out of a thin
category; the three restriction maps are then matched up at the transparency of term elaboration,
as in `StacksFrontier/AlgebraicGeometry/AffineQcohRestriction/Basic.lean`.
`CategoryTheory.ConcreteCategory.isIso_iff_bijective` is used only in the forward direction and
the backward step is `CategoryTheory.ConcreteCategory.bijective_of_isIso`: rewriting with the
iff backwards is rejected, the sheaf of rings being reached as a `TopCat.Sheaf`
while the motive wants the `CategoryTheory.Sheaf` spelling.

`Topology.IsOpenEmbedding.functor_isContinuous` is a lemma rather than an instance and is needed
to state a restriction to an open subscheme at all, so it is a section-confined local instance, as
in `StacksFrontier/AlgebraicGeometry/RelativeSpecFinish/Restriction.lean`.

## What is not done

**This file does not prove the equivalence assertion of [Stacks, Tag 01SB]**, and no `stacks`
attribute is attached.  Nothing here is quasi-coherent: the statements hold for an
arbitrary module, and no hypothesis on `f` beyond being a morphism of schemes is used.

What remains for that assertion is the **affine case** and nothing else of the locality argument:
for `V` an affine open of `S` with `U = f ⁻¹ᵁ V` affine — which holds for every affine `V` when
`f` is an affine morphism — one has to prove that the unit and the counit of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackPushforwardAdjunction` at `f|_U` are
invertible at quasi-coherent modules.  That is the statement that quasi-coherent modules over a
quasi-coherent algebra on an affine scheme are the modules over its global sections, the algebra
analogue of `AlgebraicGeometry.tildeEquiv`, and it exists in no form in Mathlib or in this
repository.  The third hypothesis `hL` of
`isEquivalence_affineQuasicoherentPushforward` is separate and is already proved as
`Stacks.AlgebraicGeometry.RestrictEquivalence.isQuasicoherent_pullbackModules`.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks

namespace CategoryTheory

/-- Three successive images under a functor out of a thin category agree, on elements, with the
image of any single morphism between the same two objects. -/
public theorem map_map_map_apply {C : Type*} [Category C] [Quiver.IsThin C]
    (P : C ⥤ AddCommGrpCat.{u}) {a b c d : C} (g₁ : a ⟶ b) (g₂ : b ⟶ c) (g₃ : c ⟶ d)
    (g : a ⟶ d) (y : P.obj a) : P.map g₃ (P.map g₂ (P.map g₁ y)) = P.map g y := by
  have h : P.map g₁ ≫ P.map g₂ ≫ P.map g₃ = P.map g := by
    rw [← P.map_comp, ← P.map_comp]
    exact congrArg P.map (Subsingleton.elim _ _)
  exact congr($h y)

end CategoryTheory

namespace AlgebraicGeometry.QcohRestrictEquiv

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohRestriction

attribute [local instance] Topology.IsOpenEmbedding.functor_isContinuous

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- **Direct image followed by restriction to `V`, compared with restriction to `U = f ⁻¹ᵁ V`
followed by direct image along `f|_U`.**  This is the Beck--Chevalley comparison of the square of
right adjoints `Stacks.AlgebraicGeometry.AffineQcohRestriction.rightSquare`; it is shown invertible
below. -/
public def pushRestrict : CategoryTheory.TwoSquare
    (pushforwardModules.{u} f.base X.ringCatSheaf)
    (restrictOver (f ⁻¹ᵁ V) X.ringCatSheaf)
    (SheafOfModules.pushforward.{u} (restrictCompareRing f V))
    (pushforwardModules.{u} (resPreimage f V).base (f ⁻¹ᵁ V).toScheme.ringCatSheaf) :=
  Stacks.CategoryTheory.beckChevalley (restrictCompareAdjunction f V)
    (restrictOverAdjunction (f ⁻¹ᵁ V) X.ringCatSheaf) (rightSquare f V)

/-- The square, written out as the three-fold composite of
`Stacks.CategoryTheory.beckChevalley_app`. -/
public theorem pushRestrict_app (M : SheafOfModules.{u} X.ringCatSheaf) :
    (pushRestrict f V).app M =
      (SheafOfModules.pushforward.{u} (restrictCompareRing f V)).map
          ((pushforwardModules.{u} f.base X.ringCatSheaf).map
            ((restrictOverAdjunction (f ⁻¹ᵁ V) X.ringCatSheaf).unit.app M)) ≫
        (SheafOfModules.pushforward.{u} (restrictCompareRing f V)).map
            ((rightSquare f V).inv.app
              ((restrictOver (f ⁻¹ᵁ V) X.ringCatSheaf).obj M)) ≫
          (restrictCompareAdjunction f V).counit.app _ :=
  Stacks.CategoryTheory.beckChevalley_app _ _ _ M

/-- **The component of the square over an open `W` of `V` is the transport of sections of `M`
along `f ⁻¹ᵁ (V.ι ''ᵁ W) = U.ι ''ᵁ ((f|_U) ⁻¹ᵁ W)`.**  Each of the three factors acts on a section
by one restriction map of `M`, and the opens of `X` form a thin category. -/
public theorem pushRestrict_app_val_app (M : SheafOfModules.{u} X.ringCatSheaf)
    (W : (Opens (V : S.Opens))ᵒᵖ) (x) :
    ((pushRestrict f V).app M).val.app W x =
      M.val.presheaf.map
        (eqToHom (congrArg op (preimage_image_eq_image_resLE_preimage f V W.unop))) x := by
  rw [pushRestrict_app]
  exact Stacks.CategoryTheory.map_map_map_apply M.val.presheaf _ _ _ _ x

/-- Each component of the square is invertible, being a transport of sections along an equality of
opens. -/
public instance isIso_pushRestrict_app_val_app (M : SheafOfModules.{u} X.ringCatSheaf)
    (W : (Opens (V : S.Opens))ᵒᵖ) : IsIso (((pushRestrict f V).app M).val.app W) := by
  have hiso : IsIso (M.val.presheaf.map
      (eqToHom (congrArg op (preimage_image_eq_image_resLE_preimage f V W.unop)))) :=
    inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : ⇑(((pushRestrict f V).app M).val.app W) =
      ⇑(M.val.presheaf.map
        (eqToHom (congrArg op (preimage_image_eq_image_resLE_preimage f V W.unop)))) :=
    funext (pushRestrict_app_val_app f V M W)
  rw [hfun]
  exact ConcreteCategory.bijective_of_isIso _

/-- The square is invertible at each module. -/
public instance isIso_pushRestrict_app (M : SheafOfModules.{u} X.ringCatSheaf) :
    IsIso ((pushRestrict f V).app M) :=
  isIso_of_isIso_val_app _ fun _ => isIso_pushRestrict_app_val_app f V M _

/-- **The square of direct images in the restriction direction is invertible**: direct image
commutes with restriction to an open of the base and its preimage. -/
public instance isIso_pushRestrict : IsIso (pushRestrict f V).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ => isIso_pushRestrict_app f V _

/-! ### Transport of the unit and the counit to an open of the base -/

/-- **The unit of the adjunction of Tag 01SB, restricted to `V`, is the unit at `f|_U`.**  Hence
one is invertible if and only if the other is. -/
public theorem isIso_restrict_unit_iff
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) :
    IsIso ((SheafOfModules.pushforward.{u} (restrictCompareRing f V)).map
        ((AffineQcohEquivalence.pullbackPushforwardAdjunction f).unit.app G)) ↔
      IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction (resPreimage f V)).unit.app
        ((SheafOfModules.pushforward.{u} (restrictCompareRing f V)).obj G)) :=
  Stacks.CategoryTheory.isIso_map_unit_iff
    (AffineQcohEquivalence.pullbackPushforwardAdjunction (resPreimage f V))
    (restrictCompareAdjunction f V) (restrictOverAdjunction (f ⁻¹ᵁ V) X.ringCatSheaf)
    (AffineQcohEquivalence.pullbackPushforwardAdjunction f) (rightSquare f V) G
    (isIso_pushRestrict_app f V _)

/-- **The counit of the adjunction of Tag 01SB, restricted to `U = f ⁻¹ᵁ V`, is the counit at
`f|_U`.**  Hence one is invertible if and only if the other is. -/
public theorem isIso_restrict_counit_iff (M : SheafOfModules.{u} X.ringCatSheaf) :
    IsIso ((restrictOver (f ⁻¹ᵁ V) X.ringCatSheaf).map
        ((AffineQcohEquivalence.pullbackPushforwardAdjunction f).counit.app M)) ↔
      IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction (resPreimage f V)).counit.app
        ((restrictOver (f ⁻¹ᵁ V) X.ringCatSheaf).obj M)) :=
  Stacks.CategoryTheory.isIso_map_counit_iff
    (AffineQcohEquivalence.pullbackPushforwardAdjunction (resPreimage f V))
    (restrictCompareAdjunction f V) (restrictOverAdjunction (f ⁻¹ᵁ V) X.ringCatSheaf)
    (AffineQcohEquivalence.pullbackPushforwardAdjunction f) (rightSquare f V) M
    (isIso_pushRestrict_app f V M)

/-! ### The unit and the counit are local on the base -/

/-- The preimage of an open cover of the base is an open cover. -/
public theorem isOpenCover_preimage {ι : Type*} {U : ι → S.Opens} (hU : IsOpenCover U) :
    IsOpenCover fun i => f ⁻¹ᵁ U i :=
  hU.comap (TopCat.Hom.hom f.base)

/-- Invertibility of a morphism of `f_* 𝒪_X`-modules is local on `S`, with restriction taken in
the retyped form that the comparison square uses. -/
public theorem isIso_of_isIso_pushRestrictRing
    {M N : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)} (φ : M ⟶ N)
    {ι : Type*} (U : ι → S.Opens) (hU : IsOpenCover U)
    (h : ∀ i, IsIso ((SheafOfModules.pushforward.{u} (restrictCompareRing f (U i))).map φ)) :
    IsIso φ := by
  refine isIso_of_coversTop ((Opens.coversTop_iff _ U).mpr hU) φ fun i W g ↦ ?_
  refine isIso_val_app_congr φ (congrArg op (image_preimage_of_le (leOfHom g))) ?_
  exact isIso_val_app_of_isIso_pushforward (restrictCompareRing f (U i)) φ (h i)
    (op ((U i).ι ⁻¹ᵁ W))

/-- **The unit of the adjunction of Tag 01SB is local on `S`.**  If its restriction to each member
of an open cover of `S` is invertible, it is invertible. -/
public theorem isIso_unit_of_isIso_unit_resPreimage
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))
    {ι : Type*} (U : ι → S.Opens) (hU : IsOpenCover U)
    (h : ∀ i, IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction
      (resPreimage f (U i))).unit.app
      ((SheafOfModules.pushforward.{u} (restrictCompareRing f (U i))).obj G))) :
    IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction f).unit.app G) :=
  isIso_of_isIso_pushRestrictRing f _ U hU fun i =>
    (isIso_restrict_unit_iff f (U i) G).mpr (h i)

/-- **The counit of the adjunction of Tag 01SB is local on `S`.**  If its restriction to the
preimage of each member of an open cover of `S` is invertible, it is invertible. -/
public theorem isIso_counit_of_isIso_counit_resPreimage (M : SheafOfModules.{u} X.ringCatSheaf)
    {ι : Type*} (U : ι → S.Opens) (hU : IsOpenCover U)
    (h : ∀ i, IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction
      (resPreimage f (U i))).counit.app ((restrictOver (f ⁻¹ᵁ U i) X.ringCatSheaf).obj M))) :
    IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction f).counit.app M) :=
  isIso_of_isIso_restrictOver _ (fun i => f ⁻¹ᵁ U i) (isOpenCover_preimage f hU) fun i =>
    (isIso_restrict_counit_iff f (U i) M).mpr (h i)

/-! ### Reduction to the affine opens of the base -/

/-- **The unit of the adjunction of Tag 01SB is invertible as soon as it is so over every affine
open of `S`.** -/
public theorem isIso_unit_of_isIso_unit_affineOpens
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))
    (h : ∀ U : S.affineOpens, IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction
      (resPreimage f (U : S.Opens))).unit.app
      ((SheafOfModules.pushforward.{u} (restrictCompareRing f (U : S.Opens))).obj G))) :
    IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction f).unit.app G) :=
  isIso_unit_of_isIso_unit_resPreimage f G (fun U : S.affineOpens => (U : S.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top S)) h

/-- **The counit of the adjunction of Tag 01SB is invertible as soon as it is so over the preimage
of every affine open of `S`.** -/
public theorem isIso_counit_of_isIso_counit_affineOpens (M : SheafOfModules.{u} X.ringCatSheaf)
    (h : ∀ U : S.affineOpens, IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction
      (resPreimage f (U : S.Opens))).counit.app
      ((restrictOver (f ⁻¹ᵁ (U : S.Opens)) X.ringCatSheaf).obj M))) :
    IsIso ((AffineQcohEquivalence.pullbackPushforwardAdjunction f).counit.app M) :=
  isIso_counit_of_isIso_counit_resPreimage f M (fun U : S.affineOpens => (U : S.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top S)) h

end AlgebraicGeometry.QcohRestrictEquiv

end Stacks

end
