module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationQuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zariski's main theorem for a quasi-finite separated morphism of algebraic spaces

Let `f : X ⟶ Y` be a quasi-finite separated morphism of algebraic spaces over a scheme `S` and
let

`X --f'--> Y' --ν--> Y`

be the normalization of `Y` in `X` with its canonical factorization of `f`. Tags 0ABS and 082J
assert that `f'` is a quasi-compact open immersion, that `ν` is integral, and that `f` is
therefore quasi-affine. All three assertions are proved here.

The two tags are the same lemma, stated word for word twice: Tag 0ABS is Lemma 67.52.2, in the
section on Zariski's main theorem for a representable morphism, and Tag 082J is Lemma 76.34.2,
in the section on Zariski's main theorem for an arbitrary morphism. Their hypotheses and their
three conclusions are identical, so both are carried by the declarations below. The proof given
here is the one Tag 0ABS gives: representability of `f` from Tag 0418, then Tag 0ABR. Tag 082J
instead quotes the non-representable form of Tag 0ABR, which this library does not have.

The open immersion comes from the quasi-finite locus: by Tag 0ABR there is an open subspace
`U' ⊆ Y'` with `(f')⁻¹(U')` the quasi-finite locus of `f` and `(f')⁻¹(U') ⟶ U'` an isomorphism,
and quasi-finiteness of `f` makes that locus the whole of `X`, so `f'` is the composite of an
isomorphism with the inclusion of `U'`. Quasi-compactness of `f'` is Tag 03KS: the composite
`f = f' ≫ ν` is quasi-compact and `ν`, being integral, is separated and hence quasi-separated.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.NormalizationInData.isIntegralHom_fromNorm_of_isQuasiFinite_isSeparated`
  is the integrality assertion of **Tags 0ABS and 082J**: the normalization morphism `ν` is
  integral.
* `AlgebraicGeometry.Space.NormalizationInData.isOpenImmersion_toNorm_of_isQuasiFinite_isSeparated`
  and
  `AlgebraicGeometry.Space.NormalizationInData.isQuasiCompact_toNorm_of_isQuasiFinite_isSeparated`
  are the two halves of the first assertion of **Tags 0ABS and 082J**: the canonical morphism
  `f'` is an open immersion, and it is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiAffineHom_of_isQuasiFinite_isSeparated` is the last assertion
  of **Tags 0ABS and 082J**: a quasi-finite separated morphism of algebraic spaces is
  quasi-affine.

## Implementation notes

**Why the normalization is data.** As in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationQuasiFiniteLocus`, the normalization of `Y`
in `X` enters through `AlgebraicGeometry.Space.NormalizationInData`, which records the
étale-chart description of Tag 0ABP: over an étale scheme chart `W ⟶ Y` the fibre product
`W ×_Y Y'` is the relative normalization of the scheme `W` in the scheme `W ×_Y X`. The
relative spectrum that constructs the normalization is not available in this library, so every
statement is made for an arbitrary datum rather than for a chosen one, which is both the
available form and the stronger statement.

**How that datum compares with the normalization of Tag 0822.** Definition 0822 is
`AlgebraicGeometry.Space.normalizationIn`, the relative spectrum of the integral closure of
`𝒪_Y` in `f_* 𝒪_X`, with `AlgebraicGeometry.Space.toNormalizationIn` for `f'`, the structure
morphism of the relative spectrum for `ν`, and
`AlgebraicGeometry.Space.toNormalizationIn_factorization` for `f = ν ∘ f'`. Those are exactly
the first five fields of `AlgebraicGeometry.Space.NormalizationInData`; the sixth, the chart
description, is not part of Definition 0822 but a theorem about it, namely Tag 0ABP. So the
datum is a strictly weaker hypothesis than "is the normalization of Tag 0822", and a statement
quantified over all data is at least as strong as the same statement about the normalization
itself — it cannot say less, whichever way the comparison is read.

**The datum is inhabited.** `AlgebraicGeometry.Space.NormalizationInData.ofRepresentable`, in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInConstruction`, constructs a
`NormalizationInData` for a morphism `yoneda.map f₀` of *representable* algebraic spaces whose
underlying morphism of schemes is quasi-compact and quasi-separated, with no further hypothesis:
the site contains the relative normalization scheme outright, by the size bound
`AlgebraicGeometry.Scheme.Hom.size_normalization_le`. Its chart condition is the scheme-level
statement that the relative normalization commutes with étale base change, Tag 03GV. So the
three theorems below are not vacuous, and
`AlgebraicGeometry.Space.zariskiMainTheorem_ofRepresentable` states their conjunction at that
datum with no normalization hypothesis carried.

**The datum is unique, for a representable morphism.** For such a morphism the datum is not
merely inhabited but determined:
`AlgebraicGeometry.Space.NormalizationInData.exists_iso_of_representable` identifies any two
data by an isomorphism compatible with both legs of the factorization, unique by
`AlgebraicGeometry.Space.NormalizationInData.existsUnique_hom_of_representable`. So for a
representable morphism the three theorems below, though quantified over an arbitrary datum, are
statements about one object.

**How far the inhabitation reaches.** Only the *target* has to be representable.
`AlgebraicGeometry.Space.NormalizationInData.ofRepresentableTarget` constructs a datum for a
quasi-finite separated morphism from an *arbitrary* algebraic space to a representable one: such
a morphism is representable by Tag 0418, so its base change along the identity of the target —
the source itself — is representable too, and
`AlgebraicGeometry.Space.NormalizationInData.ofIsoSource` transports the represented datum back.
`AlgebraicGeometry.Space.zariskiMainTheorem_ofRepresentableTarget` states the conjunction there.
What is still missing is a non-representable target, for which the datum would have to be glued
from an étale presentation `Y = U/R` by Tag 02WW and the gluing shown independent of the
presentation.

What is still missing is the bridge from Definition 0822: nothing builds a
`NormalizationInData` out of `AlgebraicGeometry.Space.normalizationIn`, because Tag 0ABP is
available here only conditionally. Part (1),
`AlgebraicGeometry.Space.normalizationInBaseChangeIso`, carries the identification of the
algebra pullback of Tag 081V with étale restriction and Tag 03LX for the structure sheaf; part
(2), `AlgebraicGeometry.Space.normalizationInRepresentableIso`, carries the comparison `hcmp`
of the direct-image algebra of the scheme normalization with the integral closure of `𝒪_Y` in
`f_* 𝒪_X`, whose remaining inputs that module's implementation notes now list — Descent,
Proposition 03DX(2) is *not* among them, being available unconditionally as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`. Definition 0822
is in any case itself conditional on the anti-equivalence of Tag 081V, which has no inhabitant
here and which occurs in the *statement* of part (2), so discharging `hcmp` alone would not
make part (2) unconditional. The bridge is therefore still absent, and the statements below,
quantified over an arbitrary datum, remain the weaker-hypothesis form.

**Integrality of `ν` is not assumed.** The chart description does not record it. It is proved
here from the chart description: over an étale chart of `Y` the morphism `ν` base changes to
the morphism `fromNormalization` of the chart, which is integral, and condition (3) of
Tag 03ZQ — `AlgebraicGeometry.Space.isIntegralHom_iff_etaleChart` — promotes integrality over
one surjective étale chart to integrality of `ν`. This is the argument the source leaves to the
construction of the normalization.

**Representability of `f`.** Tag 0ABR asks that `f` be representable; a separated locally
quasi-finite morphism of algebraic spaces is representable by Tag 0418, so the hypotheses of
Tags 0ABS and 082J supply that, which is the step Tag 0ABS's own proof takes first. They also
supply finite type: local quasi-finiteness is local finite type
conjoined with local quasi-finiteness on every étale chart, so its first half is exactly local
finite type, and quasi-compactness is the second half of quasi-finiteness.

**Quasi-affineness needs no normalization datum.** The source deduces quasi-affineness of `f`
from the factorization: for an affine scheme `Z` over `Y` the fibre product `Z ×_Y X` is a
quasi-compact open subscheme of the affine `Z ×_Y Y'`. Since `f` is representable, its
represented base changes are morphisms of schemes to which the statement for schemes, Tag 02LR,
applies directly, and that statement is proved by precisely the same factorization through the
relative normalization of the base change. So the quasi-affineness assertion is proved here
without hypothesising a normalization of `Y` in `X`, which drops a hypothesis rather than
adding one.

## References

* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
* [Stacks Project, Tag 082J](https://stacks.math.columbia.edu/tag/082J)
* [Stacks Project, Tag 0ABR](https://stacks.math.columbia.edu/tag/0ABR)
* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

attribute [local instance] pointTopology

/-! ### The quasi-finite locus of a locally quasi-finite morphism -/

/-- A locally quasi-finite morphism of algebraic spaces over `S` is quasi-finite at every point
of its source, so its quasi-finite locus is the whole source. -/
private theorem quasiFiniteLocusSubspace_eq_top (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsLocallyQuasiFinite B S hS f) :
    quasiFiniteLocusSubspace B S hS f = ⊤ :=
  have h : {x : points B S hS X | IsQuasiFiniteAt B S hS f x} = Set.univ :=
    Set.eq_univ_of_forall ((isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B S hS hX hY f).1 hf)
  calc quasiFiniteLocusSubspace B S hS f
      = openSubspaceOfPoints B S hS X {x | IsQuasiFiniteAt B S hS f x} := rfl
    _ = openSubspaceOfPoints B S hS X Set.univ := by rw [h]
    _ = ⊤ := openSubspaceOfPoints_univ B S hS X

/-- A quasi-finite separated morphism of algebraic spaces is representable (Tag 0418). -/
private theorem relativelyRepresentable_of_isQuasiFinite_isSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f) :
    yoneda.relativelyRepresentable f :=
  relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f hX hY hqf.1 hsep

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is integral is
representable with integral represented base changes, as a morphism of the presheaves it
represents. The site has fibre products and the Yoneda embedding is fully faithful, so this is
`CategoryTheory.MorphismProperty.relative_map` once integrality of morphisms of schemes is seen
to be stable under the base changes of the site. -/
theorem relative_isIntegralHom_yoneda_map {W' W : BigFppfOver B S hS} (q : W' ⟶ W)
    (hq : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map q)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map q) :=
  let P : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have _ : P.IsStableUnderBaseChange := ⟨by
    intro A C C' Z a b a' b' hsq hb
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsIntegralHom)
      (hsq.map (BigFppfOver.toScheme B S hS)) hb⟩
  MorphismProperty.relative_map (P := P) hq

namespace NormalizationInData

variable (N : NormalizationInData B S hS f)

/-! ### Integrality of the normalization morphism -/

/-- **Integrality of the normalization morphism, for a quasi-compact quasi-separated
representable morphism.** Let `f : X ⟶ Y` be a relatively representable, quasi-compact and
quasi-separated morphism of algebraic spaces over `S` and let `ν : Y' ⟶ Y`, `f' : X ⟶ Y'` be
normalization data of `Y` in `X`. Then `ν` is integral.

Over a surjective étale scheme chart `w : W ⟶ Y` the chart description of the normalization
identifies the base change of `ν` with the morphism `fromNormalization` of the induced morphism
of schemes `W ×_Y X ⟶ W`, which is integral; condition (3) of Tag 03ZQ promotes that to
integrality of `ν`. -/
theorem isIntegralHom_fromNorm_of_isQuasiCompact_isQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hqc : IsQuasiCompact B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    IsIntegralHom B S hS N.fromNorm := by
  obtain ⟨W, w, hwsurj, hwet⟩ := hY.exists_atlas
  have hsq : IsPullback (hrep.fst w) (yoneda.map (hrep.snd w)) f w := hrep.isPullback w
  have hgqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
    ((presheaf_quasiCompact_iff_isQuasiCompact B S hS hrep).2 hqc).property w (hrep.fst w)
      (hrep.snd w) hsq
  have hgqs : QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
    ((isQuasiSeparated_iff_presheaf B S hS f hX hY hrep).1 hqs).property w (hrep.fst w)
      (hrep.snd w) hsq
  obtain ⟨W', q, b, r, e, hbq, hrb, hre, heq⟩ :=
    N.chart W (hrep.pullback w) w (hrep.snd w) (hrep.fst w) hwet hsq
  have hq : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map q) := by
    rw [← heq]
    infer_instance
  have hrelq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd N.fromNorm w) := by
    refine (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      hbq.isoPullback.hom (pullback.snd N.fromNorm w)).mp ?_
    rw [hbq.isoPullback_hom_snd]
    exact relative_isIntegralHom_yoneda_map q hq
  have hWspace : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  exact (isIntegralHom_iff_etaleChart B S hS N.fromNorm N.isAlgebraicSpace hY).2
    ⟨W, w, hwsurj, hwet,
      (isIntegralHom_iff_representable B S hS (pullback.snd N.fromNorm w)
        (isAlgebraicSpace_pullback B S hS N.fromNorm w N.isAlgebraicSpace hWspace hY) hWspace).2
        ⟨hrelq.1, hrelq⟩⟩

/-- **Stacks 0ABS and 082J, integrality of the normalization morphism.** Let `f : X ⟶ Y` be a
quasi-finite separated morphism of algebraic spaces over `S` and let `ν : Y' ⟶ Y`,
`f' : X ⟶ Y'` be the normalization of `Y` in `X`. Then `ν` is integral.

Over a surjective étale scheme chart `w : W ⟶ Y` the chart description of the normalization
identifies the base change of `ν` with the morphism `fromNormalization` of the induced morphism
of schemes `W ×_Y X ⟶ W`, which is integral; condition (3) of Tag 03ZQ promotes that to
integrality of `ν`. The chart description is applicable because `f` is representable by
Tag 0418, quasi-compact, and separated, hence quasi-separated. -/
@[stacks 082J "the normalization morphism is integral"]
theorem isIntegralHom_fromNorm_of_isQuasiFinite_isSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f) :
    IsIntegralHom B S hS N.fromNorm :=
  N.isIntegralHom_fromNorm_of_isQuasiCompact_isQuasiSeparated hX hY
    (relativelyRepresentable_of_isQuasiFinite_isSeparated hX hY hqf hsep)
    hqf.2 (isQuasiSeparated_of_isSeparated B S hS hsep)

/-! ### The canonical morphism to the normalization is a quasi-compact open immersion -/

/-- **Stacks 0ABS and 082J, the open immersion.** Let `f : X ⟶ Y` be a quasi-finite separated
morphism
of algebraic spaces over `S` and let `ν : Y' ⟶ Y`, `f' : X ⟶ Y'` be the normalization of `Y`
in `X`. Then `f'` is an open immersion.

By Tag 0ABR the image `U'` in `Y'` of the quasi-finite locus of `f` is an open subspace whose
inverse image under `f'` is that locus and over which `f'` restricts to an isomorphism. Local
quasi-finiteness makes the locus the whole of `X`, so both the inclusion of the inverse image
and the restriction of `f'` are isomorphisms, and `f'` is their composite with the inclusion of
`U'`. -/
@[stacks 082J "the canonical morphism to the normalization is an open immersion"]
theorem isOpenImmersion_toNorm_of_isQuasiFinite_isSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f) :
    IsOpenImmersion B S hS N.toNorm := by
  have hrep := relativelyRepresentable_of_isQuasiFinite_isSeparated hX hY hqf hsep
  have hft : IsLocallyOfFiniteType B S hS f := fun U V a b h ha hb hcomm =>
    (hqf.1 U V a b h ha hb hcomm).1
  have htop : N.quasiFiniteImage.preimage N.toNorm = ⊤ := by
    rw [N.preimage_quasiFiniteImage_eq hX hY hrep hft hqf.2 hsep,
      quasiFiniteLocusSubspace_eq_top hX hY hqf.1]
  have _ : IsIso (N.quasiFiniteImage.preimage N.toNorm).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 htop
  have _ : IsIso (N.quasiFiniteImage.fromPreimage N.toNorm) :=
    N.isIso_fromPreimage_quasiFiniteImage hX hY hrep hft hqf.2 hsep
  have key : N.toNorm = inv (N.quasiFiniteImage.preimage N.toNorm).ι ≫
      (N.quasiFiniteImage.fromPreimage N.toNorm ≫ N.quasiFiniteImage.ι) := by
    rw [Subfunctor.fromPreimage_ι, IsIso.inv_hom_id_assoc]
  rw [key]
  exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _)
    (isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _)
      (N.isOpenSubspace_quasiFiniteImage hX hY hrep hft hqf.2 hsep).2)

/-- **Stacks 0ABS and 082J, quasi-compactness of the open immersion.** Let `f : X ⟶ Y` be a
quasi-finite
separated morphism of algebraic spaces over `S` and let `ν : Y' ⟶ Y`, `f' : X ⟶ Y'` be the
normalization of `Y` in `X`. Then `f'` is quasi-compact.

This is Tag 03KS applied to the factorization `f = f' ≫ ν`: the composite is quasi-compact
because `f` is quasi-finite, and `ν` is quasi-separated because an integral morphism is
separated. -/
@[stacks 082J "the canonical morphism to the normalization is quasi-compact"]
theorem isQuasiCompact_toNorm_of_isQuasiFinite_isSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f) :
    IsQuasiCompact B S hS N.toNorm := by
  have hcomp : IsQuasiCompact B S hS (N.toNorm ≫ N.fromNorm) := by
    rw [N.fac]
    exact hqf.2
  refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS N.toNorm N.fromNorm hX hY hcomp
    (isQuasiSeparated_of_isSeparated B S hS ?_)
  exact isSeparated_of_isIntegralHom B S hS N.fromNorm N.isAlgebraicSpace hY
    (N.isIntegralHom_fromNorm_of_isQuasiFinite_isSeparated hX hY hqf hsep)

end NormalizationInData

/-! ### Quasi-affineness -/

/-- **Stacks 0ABS and 082J, quasi-affineness.** A quasi-finite separated morphism of algebraic
spaces
over `S` is quasi-affine.

Such a morphism is representable by Tag 0418, so each of its represented base changes is a
morphism of schemes which is separated, locally of finite type, locally quasi-finite and
quasi-compact, hence quasi-affine by Tag 02LR — the statement for schemes, proved there by
exactly the factorization through the relative normalization that the source uses here. -/
@[stacks 082J "a quasi-finite separated morphism is quasi-affine",
  ega "IV 18.12.12" "more general",
  ega "IV 8.11.2" "more general"]
theorem isQuasiAffineHom_of_isQuasiFinite_isSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f) :
    IsQuasiAffineHom B S hS f := by
  have hrep := relativelyRepresentable_of_isQuasiFinite_isSeparated hX hY hqf hsep
  have hsepp := (isSeparated_iff_presheaf B S hS f hX hY hrep).1 hsep
  have hqcp := (presheaf_quasiCompact_iff_isQuasiCompact B S hS hrep).2 hqf.2
  refine isQuasiAffineHom_of_presheaf ⟨hrep, fun _ _ g fst snd sq => ?_⟩
  obtain ⟨hft, hlqf⟩ := (isLocallyQuasiFinite_yoneda_map_iff B S hS snd).1
    (IsLocallyQuasiFinite.of_isPullback B S hS sq.flip hX hY hqf.1)
  have _ : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map snd) := hsepp.property g fst snd sq
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map snd) := hqcp.property g fst snd sq
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd) := hft
  have _ : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map snd) := hlqf
  exact _root_.AlgebraicGeometry.isQuasiAffineHom_of_locallyQuasiFinite _

end AlgebraicGeometry.Space

end
