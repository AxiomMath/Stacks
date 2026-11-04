module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfae

/-!
# A quasi-affine morphism of algebraic spaces is representable and quasi-affine

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. Condition (1) of
Stacks 03WM says that `f` is representable and that every represented base change of it is a
quasi-affine morphism of schemes, and condition (2) says that `f` is quasi-affine in the
sense of Stacks 03WL, that is, that the base change of `f` along every morphism from an
affine object of the big fppf site of `S` is represented by an object of the site whose
underlying scheme is quasi-affine.

This file proves that the two differ by *exactly* the representability of `f`:
`AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_iff`. The implication from (1) to (2) is
`AlgebraicGeometry.Space.isQuasiAffineHom_of_presheaf` in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfae`; what is proved here is the converse,
which needs no descent and no gluing.

The reason it needs neither is a coincidence of shapes which is special to quasi-affineness.
For a *representable* `f`, condition (1) asks that the morphism of schemes representing the
base change of `f` along a morphism from an arbitrary object `a` of the site be quasi-affine,
and quasi-affineness of a morphism of schemes is by definition, Stacks 01SK, the condition
that the inverse image of every *affine open* of the target be a quasi-affine scheme. Condition
(2) supplies exactly that: an affine open `U` of the scheme under `a` is itself an object of
the site, by `AlgebraicGeometry.exists_restrict_bigFppfOver`, it is affine, and the base change
of `f` along it is the inverse image of `U` under the representing morphism. So no passage from
affine test objects to arbitrary ones is required, and in particular none of the relative
gluing of Stacks 03JH which the corresponding step needs for the affine, integral and finite
analogues — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite`, where the target condition `Q` has to be
proved Zariski local because the representing object there is tested by an *absolute* affineness
condition rather than by a condition on affine opens of the target.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isQuasiAffineHom_respectsIso`: quasi-affineness of a morphism of schemes
  is invariant under isomorphisms of the source and of the target.
* `AlgebraicGeometry.Space.isQuasiAffine_preimage_of_isQuasiAffineHom`: if `f` is quasi-affine
  as a morphism of algebraic spaces and sits in a Cartesian square over a morphism of the site
  `snd : b ⟶ a`, then the inverse image under `snd` of every affine open of `a` is a
  quasi-affine scheme.
* `AlgebraicGeometry.Space.presheaf_of_isQuasiAffineHom`: a representable quasi-affine morphism
  of algebraic spaces over `S` has quasi-affine represented base changes. This is the
  implication (2) ⇒ (1) of Stacks 03WM *for a representable `f`*.
* `AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_iff`: condition (1) of Stacks 03WM is
  condition (2) together with the representability of `f`.
* `AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart`: the implication
  (3) ⇒ (1) of Stacks 03WM, reduced to two named inputs — the base change of a quasi-affine
  morphism of schemes is quasi-affine, Stacks 01SO, and the effective descent hypothesis
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at quasi-affine morphisms,
  which is the geometric input of Stacks 03I2.

## Implementation notes

Nothing in this file carries the tag 03WM, and the four conditions of that tag are not
proved equivalent *here*. They are proved equivalent in
`StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae`, as
`AlgebraicGeometry.Space.isQuasiAffineHom_tfae`, modulo one hypothesis recorded there.
`AlgebraicGeometry.Space.presheaf_of_isQuasiAffineHom` carries the named
hypothesis `CategoryTheory.Functor.relativelyRepresentable f`, which is condition (1) minus the
quasi-affineness clause, so it is not the implication (2) ⇒ (1) of the tag; it is the statement that the
clause is the only part of (1) which (2) does not already give.

Producing the representability from (2) is not an obstruction: relative 03JH is proved there
with the affineness of the representing object **dropped**. That affineness holds for affine,
integral and finite morphisms but not for immersions or quasi-affine morphisms, and the
containment bound never uses it, so dropping it costs nothing.

Likewise `AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart` is the
implication (3) ⇒ (1), and only ONE of its hypotheses is substantive. The base-change
stability of `AlgebraicGeometry.IsQuasiAffineHom` is not an open input: it is proved, as
the instance `AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange`
(`StacksFrontier/AlgebraicGeometry/Morphisms/Affine/QuasiAffineStability.lean:199`, tagged
`@[stacks 01SO]`), and is supplied by synthesis. The remaining hypothesis is the existing
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`, Stacks 03I2, which rests on
the fppf descent of Stacks 02W8.
Condition (3) is spelled in the tagged statement with an explicit representing object and isomorphism
rather than with `CategoryTheory.MorphismProperty.presheaf`; the passage between the two forms
is `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`, which needs fibre
products in `AlgebraicGeometry.BigFppfOver` — those are available by synthesis, from
`CategoryTheory.Over.instHasPullbacks` together with
`AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan` — and the base
change stability of the scheme-level property, which is the input that is missing.

Quasi-affineness of a morphism of algebraic spaces, Stacks 03WL, is **not** an instance of the
pattern `AlgebraicGeometry.Space.HoldsOnAffineBaseChange`, unlike the affineness of Stacks 03WF
and the integrality and finiteness of Stacks 03ZP: that pattern requires the representing object
to be affine, whereas here it is only quasi-affine. This is why the results of this file are
proved for quasi-affineness directly rather than for an arbitrary `Q`.

`AlgebraicGeometry.isQuasiAffineHom_respectsIso` is stated as a theorem rather than registered
as an instance, and together with the three scheme-level lemmas at the head of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfae` it belongs in
`StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine` on a dedup pass. It is needed by
any use of `AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart` at quasi-affine
morphisms, which asks for `CategoryTheory.MorphismProperty.RespectsIso` of the scheme-level
property.

## References

* [Stacks Project, Tag 01SK](https://stacks.math.columbia.edu/tag/01SK)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Quasi-affineness of a morphism of schemes is invariant under isomorphisms of the source and
of the target: an isomorphism matches up the affine opens of the two targets and the inverse
images of the two sources. -/
theorem isQuasiAffineHom_respectsIso :
    MorphismProperty.RespectsIso (@IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}) := by
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf ↦ ⟨fun U hU ↦ ?_⟩)
    (fun e f hf ↦ ⟨fun U hU ↦ ?_⟩)
  · have : Scheme.IsQuasiAffine (f ⁻¹ᵁ U) := hf.isQuasiAffine_preimage U hU
    rw [Scheme.Hom.comp_preimage]
    exact Scheme.IsQuasiAffine.of_isAffineHom (e.hom ∣_ (f ⁻¹ᵁ U))
  · have : IsAffine U.toScheme := hU
    have hU' : IsAffineOpen (e.hom ⁻¹ᵁ U) := IsAffine.of_isIso (e.hom ∣_ U)
    rw [Scheme.Hom.comp_preimage]
    exact hf.isQuasiAffine_preimage _ hU'

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `f : X ⟶ Y` be a quasi-affine morphism of algebraic spaces over `S` in the sense of
Stacks 03WL, and let `snd : b ⟶ a` be a morphism of the big fppf site of `S` representing the
base change of `f` along a morphism `g : yoneda.obj a ⟶ Y`. Then the inverse image under `snd`
of every affine open `U` of the scheme under `a` is a quasi-affine scheme.

An affine open of an object of the site is again an object of the site, by
`AlgebraicGeometry.exists_restrict_bigFppfOver`, and it is affine, so quasi-affineness of `f`
applies to it and supplies an object of the site with quasi-affine underlying scheme
representing the base change of `f` along `U`. That base change is the inverse image of `U`
under `snd`: both are fibre products of `snd` along the inclusion of `U`, which is an open
immersion with image `U`. -/
theorem isQuasiAffine_preimage_of_isQuasiAffineHom
    {f : X ⟶ Y} (hf : IsQuasiAffineHom B S hS f)
    {a b : BigFppfOver B S hS} {g : yoneda.obj a ⟶ Y} {fst : yoneda.obj b ⟶ X}
    {snd : b ⟶ a} (BC : IsPullback fst (yoneda.map snd) f g)
    (U : ((BigFppfOver.toScheme B S hS).obj a).Opens) (hU : IsAffineOpen U) :
    Scheme.IsQuasiAffine (((BigFppfOver.toScheme B S hS).map snd) ⁻¹ᵁ U) := by
  obtain ⟨a₀, j, hj, hjrange, -⟩ := exists_restrict_bigFppfOver a U
  have : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B S hS).map j) := hj
  have : IsAffine U.toScheme := hU
  let e₁ : (BigFppfOver.toScheme B S hS).obj a₀ ≅ U.toScheme :=
    IsOpenImmersion.isoOfRangeEq ((BigFppfOver.toScheme B S hS).map j) U.ι
      (by rw [hjrange, U.range_ι])
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj a₀) := IsAffine.of_isIso e₁.hom
  obtain ⟨W, hWqa, ⟨e₂⟩⟩ := hf ⟨a₀, inferInstance⟩ (yoneda.map j ≫ g)
  -- `yoneda.obj W` is the fibre product of `snd` and `j`, hence so is the scheme under `W`.
  have sqW : IsPullback (e₂.hom ≫ pullback.snd (yoneda.map j ≫ g) f)
      (e₂.hom ≫ pullback.fst (yoneda.map j ≫ g) f) f (yoneda.map j ≫ g) :=
    (IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e₂ rfl rfl).flip
  let e₃ : yoneda.obj W ≅ yoneda.obj (Limits.pullback snd j) :=
    (IsPullback.of_right' sqW BC).isoIsPullback _ _
      ((IsPullback.of_hasPullback snd j).map yoneda)
  let e₄ : (BigFppfOver.toScheme B S hS).obj W ≅
      Limits.pullback ((BigFppfOver.toScheme B S hS).map snd)
        ((BigFppfOver.toScheme B S hS).map j) :=
    ((BigFppfOver.toScheme B S hS).mapIso (yoneda.preimageIso e₃)).trans
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) snd j)
  have : Scheme.IsQuasiAffine (Limits.pullback ((BigFppfOver.toScheme B S hS).map snd)
      ((BigFppfOver.toScheme B S hS).map j)) := by
    have := hWqa
    exact Scheme.IsQuasiAffine.of_isAffineHom e₄.inv
  -- That fibre product is the inverse image of `U`: the two open immersions into the scheme
  -- under `b` have the same image.
  have hrange : Set.range (Limits.pullback.fst ((BigFppfOver.toScheme B S hS).map snd)
      ((BigFppfOver.toScheme B S hS).map j)) =
      Set.range (((BigFppfOver.toScheme B S hS).map snd ⁻¹ᵁ U).ι) := by
    have hUr : ((BigFppfOver.toScheme B S hS).map j).opensRange = U :=
      TopologicalSpace.Opens.ext hjrange
    rw [IsOpenImmersion.range_pullbackFst, hUr, Scheme.Opens.range_ι]
  exact Scheme.IsQuasiAffine.of_isAffineHom
    (IsOpenImmersion.isoOfRangeEq _ _ hrange).inv

/-- **Stacks 03WM, (2) implies (1) for a representable morphism.** A quasi-affine morphism of
algebraic spaces over `S` which is relatively representable has quasi-affine represented base
changes, which is condition (1) of Stacks 03WM.

The hypothesis `hrep` is condition (1) minus its quasi-affineness clause, so this is **not** the
implication (2) ⇒ (1) of the tag; it says that the clause is the only part of condition (1) which
condition (2) does not already give. -/
theorem presheaf_of_isQuasiAffineHom {f : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable f) (hf : IsQuasiAffineHom B S hS f) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
  ⟨hrep, fun _ _ _ _ _ BC ↦
    ⟨fun U hU ↦ isQuasiAffine_preimage_of_isQuasiAffineHom hf BC U hU⟩⟩

/-- Condition (1) of Stacks 03WM is condition (2) of Stacks 03WM together with the
representability of the morphism. -/
theorem presheaf_isQuasiAffineHom_iff {f : X ⟶ Y} :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ↔
      yoneda.relativelyRepresentable f ∧ IsQuasiAffineHom B S hS f :=
  ⟨fun h ↦ ⟨h.rep, isQuasiAffineHom_of_presheaf h⟩,
    fun h ↦ presheaf_of_isQuasiAffineHom h.1 h.2⟩

/-- **Stacks 03WM, (3) implies (1)**, modulo the two inputs named below.

If a surjective étale chart `g : yoneda.obj V ⟶ Y` of the target has the property that the
fibre product `X ×_Y V` is represented by an object `W` of the big fppf site of `S` whose
projection to `V` is a quasi-affine morphism of schemes — which is condition (3) of
Stacks 03WM, verbatim — then `f` is representable with quasi-affine represented base changes,
which is condition (1).

The two hypotheses are exactly the two geometric inputs the source uses, and nothing else is
needed:

* `hbc` is **Stacks 01SO**, the base change of a quasi-affine morphism of schemes is
  quasi-affine. It is what turns the explicit representing object of condition (3) into the
  `CategoryTheory.MorphismProperty.presheaf` form, through
  `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`.
* `hdesc` is the geometric input of **Stacks 03I2**, isolated in
  `StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent`; the source cites Stacks 02L7 and
  Stacks 0247 for it at the class of quasi-affine morphisms.

This is therefore *not* the tag's implication: it is that implication reduced to those two.
In particular the tag 03WM is not carried here and the four conditions of Stacks 03WM are not
proved equivalent. -/
theorem presheaf_isQuasiAffineHom_of_surjectiveEtaleChart
    (hbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}))
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {V W : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y} (e : yoneda.obj W ≅ pullback g f)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hq : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (e.hom ≫ pullback.fst g f)))) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have := hbc
  have := isQuasiAffineHom_respectsIso.{u}
  set q := yoneda.preimage (e.hom ≫ pullback.fst g f) with hqdef
  have hmapq : yoneda.map q = e.hom ≫ pullback.fst g f := by
    rw [hqdef, Functor.map_preimage]
  have hyq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hq
  have hfac : pullback.snd f g = ((pullbackSymmetry f g).hom ≫ e.inv) ≫ yoneda.map q := by
    rw [hmapq, Category.assoc, Iso.inv_hom_id_assoc, pullbackSymmetry_hom_comp_fst]
  have hV : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) := by
    rw [hfac]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hyq
  exact presheaf_of_surjectiveEtaleChart hdesc hX.isSheaf hY.isSheaf hs he hV

end Space

end AlgebraicGeometry

end
