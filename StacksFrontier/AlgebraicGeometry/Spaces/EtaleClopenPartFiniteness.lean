module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType

/-!
# Finiteness of the invariant quotient over the base

`StacksFrontier/AlgebraicGeometry/Spaces/EtaleClopenPartUniversallyClosed.lean` proves the
conclusion of Stacks 082H with its finiteness clause weakened to universal closedness, and
its notes identify what is left: *affineness* of the open-and-closed piece `V` over the base
`U`. The source gets it by presenting `V` as the quotient of an affine scheme `Z₁` by the
étale equivalence relation `R = Z₁ ×_V Z₁`, whose two projections are finite, and invoking
Tag 03BM to see that `V` is the affine scheme `Spec` of the ring of invariants; Tag 03GN then
gives properness of `V ⟶ U` and Tag 01WN finiteness.

This file supplies two of the steps in that chain. It does *not* identify `V` with an
invariant spectrum.

The first is the passage from affineness to finiteness, in place of Tags 03GN and 01WN. Over
an affine base it is pure commutative algebra: the invariant ring `C` sits inside the ring `A`
of the object scheme, which is finite over the base ring, and `C ⟶ A` is faithfully flat,
hence injective; so `C` is integral over the base by
`RingHom.IsIntegral.tower_bot`, and integral together with finite type is finite by
`RingHom.IsIntegral.to_finite`. The finite-type hypothesis is the one Stacks 082H carries from
its assumption that `f` is locally of finite type, and it is exactly what Tag 03GN needs to
turn universal closedness into properness.

The second is the transport between a morphism of algebraic spaces and the morphism of
objects of the site representing it, in both of the directions needed: finiteness out of the
site, and local finite type into it.

The size bound which puts the invariant spectrum inside the site is **not** proved here
because it is already available, as `AlgebraicGeometry.contains_quotientOver` of
`StacksFrontier/AlgebraicGeometry/Groupoids/Stabilizer/FiniteFlatQuotientAffine.lean`, with
`AlgebraicGeometry.size_quotientOver_le` for the inequality of sizes. It costs nothing but the
inclusion `invariantRing G ⊆ Γ(objects, ⊤)`: the size of an affine scheme is `max ℵ₀ #Γ` and a
subring injects into the ring, so no cardinal arithmetic is involved — in particular neither
`Cardinal.IsStrongPrelimit` nor `Cardinal.IsRegular` appears, and the bound holds for every
cutoff.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.IsFinite.of_comp_of_flat_surjective`: a morphism `h` of affine schemes is
  finite as soon as it becomes finite after precomposition with a flat surjective morphism and
  is locally of finite type.
* `AlgebraicGeometry.IsFinite.of_comp_of_isFiniteLocallyFree`: the same with the flat
  surjective morphism in the form Stacks 03BM supplies it, finite locally free and surjective.
* `AlgebraicGeometry.isFinite_of_isFinite_objectsToInvariantSpectrum_comp`: a morphism from
  the invariant spectrum of an affine groupoid scheme with finite locally free source and
  target to an affine scheme is finite as soon as its precomposition with the canonical
  projection is finite and it is locally of finite type. This is the conclusion Stacks 082H
  draws from Tags 03BM, 03GN and 01WN together.
* `AlgebraicGeometry.Space.isFinite_of_presheaf_isFinite`: a relatively representable morphism
  of presheaves whose represented base changes are finite morphisms of schemes is a finite
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isFinite_of_isFinite_map_of_iso` and
  `AlgebraicGeometry.Space.locallyOfFiniteType_map_of_iso`: transport of finiteness and of
  local finite type between a morphism of algebraic spaces and a morphism of objects of the
  site identified with it by two isomorphisms.
* `AlgebraicGeometry.Space.isFinite_of_iso_yoneda_of_flat_surjective_atlas`: the finiteness
  clause of Stacks 082H for a morphism of algebraic spaces which is locally of finite type and
  is identified with a morphism of affine objects of the site carrying a flat surjective
  atlas finite over the target.

## Implementation notes

The core lemma is stated for an arbitrary flat surjective `g` rather than for the canonical
projection of Stacks 03BM, because nothing in its proof is about invariants: what it uses is
that a flat surjective morphism of affine schemes induces a faithfully flat, hence injective,
map on global sections (`AlgebraicGeometry.flat_and_surjective_SpecMap_iff` together with
`RingHom.FaithfullyFlat.injective`).

Three transports between a morphism of affine schemes and the induced map of global sections
are needed, and each is `CategoryTheory.MorphismProperty.arrow_mk_iso_iff` at
`AlgebraicGeometry.arrowIsoSpecΓOfIsAffine`. At the toolchain of this development
`MorphismProperty.RespectsIso` is not found by instance search for `AlgebraicGeometry.Flat`,
`AlgebraicGeometry.Surjective` or `AlgebraicGeometry.IsFinite`, so it is supplied explicitly
from `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso` with the property
given by name; this avoids the `HasAffineProperty` route, whose instances for
`AlgebraicGeometry.IsFinite` are not available here either.

What this file does **not** do is identify the open-and-closed piece of Stacks 082H with an
invariant spectrum. That identification is Tag 0262 part (3) together with Tag 03BM and is the
remaining gap in the finiteness clause of Stacks 082H. Where it is needed it appears as a pair
of isomorphisms with representable presheaves, which is *representability* of the piece and is
strictly weaker than the finiteness concluded: the finiteness comes from the flat surjective
atlas and the finite-type hypothesis, so nothing here assumes any part of its own conclusion.
Nothing here carries the tag 082H.

## References

* [Stacks Project, Tag 01WN](https://stacks.math.columbia.edu/tag/01WN)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids AlgebraicGeometry.GroupoidScheme

universe u

namespace AlgebraicGeometry

/-! ### Descending finiteness along a flat surjective morphism of affine schemes -/

/-- A morphism of affine schemes has a base-change-stable property iff `Spec` of its global
sections map does. -/
private theorem property_iff_property_specMap_appTop {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    P f ↔ P (Spec.map f.appTop) :=
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := P)
  MorphismProperty.arrow_mk_iso_iff P (arrowIsoSpecΓOfIsAffine f)

/-- **A morphism of affine schemes which becomes finite after a flat surjective
precomposition, and is locally of finite type, is finite.** Let `g : Z ⟶ V` be flat and
surjective, let `h : V ⟶ U` be a morphism of affine schemes with `g ≫ h` finite and `h`
locally of finite type. Then `h` is finite.

This replaces Tags 03GN and 01WN in the proof of Stacks 082H, where `g` is the canonical
projection from the affine scheme `Z₁` onto the quotient `V` by the étale equivalence
relation, `h` is `V ⟶ U`, and `g ≫ h` is the finite morphism `Z₁ ⟶ U` of step 5.

On global sections `g` induces a faithfully flat, hence injective, ring map, so integrality
of `Γ(U) ⟶ Γ(Z)` descends to `Γ(U) ⟶ Γ(V)` by `RingHom.IsIntegral.tower_bot`; finite type is
`CategoryTheory.HasRingHomProperty.appTop` at `AlgebraicGeometry.LocallyOfFiniteType`, and
integral together with finite type is finite. -/
theorem IsFinite.of_comp_of_flat_surjective {Z V U : Scheme.{u}} (g : Z ⟶ V) (h : V ⟶ U)
    [IsAffine V] [IsAffine U] [Flat g] [Surjective g] [IsFinite (g ≫ h)]
    [LocallyOfFiniteType h] : IsFinite h := by
  have hZ : IsAffine Z := isAffine_of_isAffineHom (g ≫ h)
  have hfl : Flat (Spec.map g.appTop) :=
    (property_iff_property_specMap_appTop (P := @Flat) g).mp ‹_›
  have hsu : Surjective (Spec.map g.appTop) :=
    (property_iff_property_specMap_appTop (P := @Surjective) g).mp ‹_›
  have hff : (g.appTop).hom.FaithfullyFlat :=
    (flat_and_surjective_SpecMap_iff g.appTop).mp ⟨hfl, hsu⟩
  have hcomp : ((g ≫ h).appTop).hom.Finite := Scheme.Hom.finite_appTop (g ≫ h)
  have heq : ((g ≫ h).appTop).hom = (g.appTop).hom.comp (h.appTop).hom := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  have hint : (h.appTop).hom.IsIntegral :=
    RingHom.IsIntegral.tower_bot (h.appTop).hom (g.appTop).hom hff.injective
      (by rw [← heq]; exact hcomp.to_isIntegral)
  have hft : (h.appTop).hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) h inferInstance
  have hfin : RingHom.Finite (h.appTop).hom := hint.to_finite hft
  exact (property_iff_property_specMap_appTop (P := @IsFinite) h).mpr
    ((IsFinite.SpecMap_iff h.appTop).mpr hfin)

/-- **The same with the precomposed morphism finite locally free and surjective**, which is
the form in which Stacks 03BM supplies the projection onto the invariant spectrum: finite
locally free is finite, flat and locally of finite presentation. -/
theorem IsFinite.of_comp_of_isFiniteLocallyFree {Z V U : Scheme.{u}} (g : Z ⟶ V) (h : V ⟶ U)
    [IsAffine V] [IsAffine U] [Stacks.Morphisms.IsFiniteLocallyFree g] [Surjective g]
    [IsFinite (g ≫ h)] [LocallyOfFiniteType h] : IsFinite h :=
  have hg := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    g).mp inferInstance
  have : Flat g := hg.2.1
  IsFinite.of_comp_of_flat_surjective g h

/-! ### Finiteness of the invariant quotient over an affine base -/

/-- **The invariant quotient of an affine groupoid scheme with finite locally free source and
target is finite over an affine base, as soon as the object scheme is and the quotient is
locally of finite type.** This is what the proof of Stacks 082H concludes from Tags 03BM,
03GN and 01WN together: there the groupoid is `Z₁` with the étale equivalence relation
`R = Z₁ ×_V Z₁`, the invariant spectrum is the open-and-closed piece `V`, the base is the
affine `U`, and `Z₁ ⟶ U` is the finite morphism of step 5.

The canonical projection onto the invariant spectrum is finite locally free by Tag 03BM
(`AlgebraicGeometry.objectsToInvariantSpectrum_isFiniteLocallyFree`) and surjective by Tag
03BL (`AlgebraicGeometry.GroupoidScheme.surjective_objectsToInvariantSpectrum`), so
`AlgebraicGeometry.IsFinite.of_comp_of_isFiniteLocallyFree` applies. -/
theorem isFinite_of_isFinite_objectsToInvariantSpectrum_comp {S U : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] [IsAffine U]
    (h : Spec (CommRingCat.of (invariantRing G)) ⟶ U)
    (hfin : IsFinite (objectsToInvariantSpectrum G ≫ h))
    (hft : LocallyOfFiniteType h) : IsFinite h :=
  have : Surjective (objectsToInvariantSpectrum G) :=
    (surjective_iff (objectsToInvariantSpectrum G)).2
      (surjective_objectsToInvariantSpectrum G)
  IsFinite.of_comp_of_isFiniteLocallyFree (objectsToInvariantSpectrum G) h

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finiteness of a morphism of algebraic spaces from a representing scheme morphism -/

/-- **A relatively representable morphism of presheaves whose represented base changes are
finite is a finite morphism of algebraic spaces.** This is the implication from condition (1)
to condition (2) of Stacks 03ZQ for finiteness, and is formal: over an affine test object the
representing object its relative representability supplies is affine, because it is finite
over an affine scheme.

The argument is the one of `AlgebraicGeometry.Space.isFinite_of_isClosedImmersion`, with
finiteness in place of the closed-immersion property. -/
theorem isFinite_of_presheaf_isFinite {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsFinite B S hS f := by
  intro U hU ξ
  refine ⟨hf.rep.pullback ξ, hf.rep.snd ξ, hf.rep.fst ξ, ?_, ?_, hf.rep.isPullback ξ⟩
  · have hfi : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd ξ)) := hf.property_snd ξ
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hf.rep.snd ξ))
  · exact hf.property_snd ξ

/-- The commuting square of a morphism of presheaves identified, through two isomorphisms,
with a morphism of objects of the site, in the form the étale-chart conditions of Stacks 03MJ
consume it. -/
theorem yoneda_map_comp_inv_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {V₀ U₀ : BigFppfOver B S hS} {j : V₀ ⟶ U₀}
    {eX : X ≅ yoneda.obj V₀} {eY : Y ≅ yoneda.obj U₀}
    (hcomm : f ≫ eY.hom = eX.hom ≫ yoneda.map j) :
    yoneda.map j ≫ eY.inv = eX.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact hcomm.symm

/-- **A morphism of algebraic spaces identified with a finite morphism of objects of the site
is finite.** If `f : X ⟶ Y` fits into a commuting square with isomorphisms `X ≅ h_{V₀}` and
`Y ≅ h_{U₀}` over a morphism `j : V₀ ⟶ U₀` of the site whose underlying morphism of schemes
is finite, then `f` is a finite morphism of algebraic spaces.

Finiteness of a morphism of schemes is stable under base change, so
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff` turns finiteness of the
scheme morphism into the relatively representable condition for `yoneda.map j`, which the two
isomorphisms transport to `f`. -/
theorem isFinite_of_isFinite_map_of_iso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {V₀ U₀ : BigFppfOver B S hS} (j : V₀ ⟶ U₀)
    (eX : X ≅ yoneda.obj V₀) (eY : Y ≅ yoneda.obj U₀)
    (hcomm : f ≫ eY.hom = eX.hom ≫ yoneda.map j)
    (hj : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map j)) :
    IsFinite B S hS f := by
  have hpre := (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) j).mpr hj
  have hiso : Arrow.mk (yoneda.map j) ≅ Arrow.mk f :=
    Arrow.isoMk eX.symm eY.symm (by
      simp only [Arrow.mk_hom, Iso.symm_hom]
      exact (yoneda_map_comp_inv_eq B S hS hcomm).symm)
  exact isFinite_of_presheaf_isFinite B S hS f
    ((MorphismProperty.arrow_mk_iso_iff _ hiso).mp hpre)

/-- **A morphism of algebraic spaces which is locally of finite type is so on the scheme
morphism representing it.** Two isomorphisms with representable presheaves are étale charts,
so condition (1) of Stacks 03MJ applies to the square they form. -/
theorem locallyOfFiniteType_map_of_iso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {V₀ U₀ : BigFppfOver B S hS} (j : V₀ ⟶ U₀)
    (eX : X ≅ yoneda.obj V₀) (eY : Y ≅ yoneda.obj U₀)
    (hcomm : f ≫ eY.hom = eX.hom ≫ yoneda.map j)
    (hf : IsLocallyOfFiniteType B S hS f) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map j) := by
  have hE : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have hEi : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Etale.{u})
  have hE' : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have hEi' : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  exact hf V₀ U₀ eX.inv eY.inv j
    (MorphismProperty.presheaf_of_isIso _ eX.inv)
    (MorphismProperty.presheaf_of_isIso _ eY.inv)
    (yoneda_map_comp_inv_eq B S hS hcomm)

/-- **The finiteness clause of Stacks 082H, from representability of the open-and-closed
piece.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of
finite type and is identified, through isomorphisms with representable presheaves, with a
morphism `j : V₀ ⟶ U₀` of objects of the site whose underlying schemes are affine. Suppose
`V₀` carries a flat surjective morphism `g` from an object `Z₁` of the site with `g ≫ j`
finite. Then `f` is a finite morphism of algebraic spaces.

In the application to Stacks 082H, `X` is the open-and-closed piece `V`, `Y` is the base `U`,
`Z₁` is the affine scheme of step 5 which is étale onto `V` and finite over `U`, and `V₀` is
the invariant spectrum which Tag 03BM produces as the quotient of `Z₁` by the étale
equivalence relation `Z₁ ×_V Z₁`. The flat surjective `g` is the canonical projection of Tag
03BL, and `g ≫ j` is the finite morphism `Z₁ ⟶ U` of step 5.

The scheme-level work is `AlgebraicGeometry.IsFinite.of_comp_of_flat_surjective`, which stands
in for Tags 03GN and 01WN; the local-finite-type input it needs is read off the hypothesis on
`f` by `AlgebraicGeometry.Space.locallyOfFiniteType_map_of_iso`, and the conclusion is
transported back by `AlgebraicGeometry.Space.isFinite_of_isFinite_map_of_iso`.

What is **not** proved here is that the open-and-closed piece of Stacks 082H is isomorphic to
a representable presheaf; that is Tag 0262 part (3) together with Tag 03BM, and it is the
remaining gap. The isomorphisms are hypotheses here, and representability is strictly weaker
than the finiteness this concludes — the finiteness comes from the atlas `g` and the
finite-type hypothesis, not from the isomorphisms. -/
theorem isFinite_of_iso_yoneda_of_flat_surjective_atlas
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {Z₁ V₀ U₀ : BigFppfOver B S hS} (g : Z₁ ⟶ V₀) (j : V₀ ⟶ U₀)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (hgfl : Flat ((BigFppfOver.toScheme B S hS).map g))
    (hgsu : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hgj : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map (g ≫ j)))
    (eX : X ≅ yoneda.obj V₀) (eY : Y ≅ yoneda.obj U₀)
    (hcomm : f ≫ eY.hom = eX.hom ≫ yoneda.map j)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsFinite B S hS f := by
  have h₁ : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map g ≫ (BigFppfOver.toScheme B S hS).map j) := by
    rwa [← Functor.map_comp]
  have h₂ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map j) :=
    locallyOfFiniteType_map_of_iso B S hS j eX eY hcomm hf
  exact isFinite_of_isFinite_map_of_iso B S hS f j eX eY hcomm
    (_root_.AlgebraicGeometry.IsFinite.of_comp_of_flat_surjective
      ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map j))

end AlgebraicGeometry.Space

end
