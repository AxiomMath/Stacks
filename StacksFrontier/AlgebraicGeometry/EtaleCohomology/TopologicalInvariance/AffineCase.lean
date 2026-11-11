module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.CoverDense
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCover
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromSurjectiveUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeOneOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded

/-!
# Topological invariance of the small étale site from its affine case

Let `f : X ⟶ Y` be a universal homeomorphism, that is an integral, universally injective and
surjective morphism. Base change along `f` is a fully faithful functor from the schemes étale
over `Y` to the schemes étale over `X`, and the only remaining content of its being an
equivalence is essential surjectivity.

This file reduces that essential surjectivity to its affine case. A universal homeomorphism is
an affine morphism, so an affine open of `Y` pulls back to an affine open of `X`; a scheme étale
over `X` is therefore covered by affine opens which are étale over an affine open of `X` lying
over an affine open of `Y`. Pasting the defining square of a base change over the affine open of
`Y` onto the restriction square of `f` turns a descent over that affine open into a descent over
`Y`, so each member of the covering is a descended open subscheme, and the glueing of descended
open subschemes along an open covering carries the local descents to a global one.

Consequently the whole equivalence of categories follows from the single statement that an
affine scheme étale over an affine scheme `X` descends along a universal homeomorphism to an
affine base `Y`. That statement is the essential surjectivity of the correspondence displayed as
Stacks Project, Tag 04E0, and it is carried here as the hypothesis
`Stacks.Etale.EssSurjAffineEtalePullback`. That hypothesis is proved, unconditionally, as
`Stacks.Etale.essSurjAffineEtalePullback`, and Tag 04E0 itself is registered in full on
`Stacks.Etale.affineEtalePullback_isEquivalence`.

The affine correspondence itself is also treated, as far as it goes unconditionally: base change
carries an affine étale `Y`-scheme to an affine étale `X`-scheme, and the induced functor between
the affine objects is full and faithful.

## Main definitions

* `Stacks.Etale.EssSurjAffineEtalePullback` — the affine case: every affine scheme étale over an
  affine scheme `X` is, over `X`, the base change along a universal homeomorphism `X ⟶ Y` with
  `Y` affine of an affine scheme étale over `Y`.
* `Stacks.Etale.EssSurjAffineEtalePullbackBounded` — the same statement for those étale
  morphisms whose fibre degrees are bounded by a given integer. This is the statement on which
  the source runs its induction.

## Main results

* `Stacks.Etale.universalHomeomorphism_morphismRestrict` — the restriction of a universal
  homeomorphism over an open subscheme of its target is a universal homeomorphism.
* `Stacks.Etale.mem_descendedOpens_of_resLE` — an open subscheme of a scheme over `X` which
  descends along the restriction of `f` over an open subscheme of `Y` descends along `f`.
* `Stacks.Etale.exists_etale_pullback_iso_of_essSurjAffine` — from the affine case, every scheme
  étale over `X` is the base change along `f` of a scheme étale over `Y`.
* `Stacks.Etale.etalePullback_isEquivalence_of_integral_universallyInjective_surjective` —
  Stacks Project, Tag 04DZ: base change along an integral, universally injective and surjective
  morphism is an equivalence of small étale sites, given the affine case.
* `Stacks.Etale.affineEtalePullback_fullyFaithful` — base change preserves affineness and is
  full and faithful on the affine objects of the two small étale sites; this is the part of
  Stacks Project, Tag 04E0 that needs no descent.
* `Stacks.Etale.affineEtalePullback_isEquivalence_of_essSurjAffine` — with the affine case, that
  restricted functor is an equivalence.
* `Stacks.Etale.isAffine_of_isAffine_pullback` — a scheme over `Y` whose base change along a
  universal homeomorphism `f : X ⟶ Y` is affine is itself affine.
* `Stacks.Etale.essSurjAffineEtalePullback_of_exists_etale_pullback_iso` — consequently the
  affine case is implied by its own statement with the affineness of the descended scheme
  deleted.
* `Stacks.Etale.exists_affine_etale_pullback_iso_of_isOpenImmersion` — the affine case holds
  when the étale morphism is an open immersion.
* `Stacks.Etale.exists_affine_etale_pullback_iso_of_boundsFiberDegrees_one` — the affine case
  holds when the degrees of the fibres of the étale morphism are bounded by one. This is the
  base case of the induction by which the source proves the affine case.
* `Stacks.Etale.essSurjAffineEtalePullbackBounded_one` — the same, stated as the bounded form of
  the affine case at the bound one.
* `Stacks.Etale.essSurjAffineEtalePullback_of_forall_bounded` — the affine case follows from its
  bounded forms for all bounds, because an étale morphism of affine schemes has universally
  bounded fibres.
* `Stacks.Etale.essSurjAffineEtalePullback_of_inductiveStep` — consequently the affine case
  follows from the single inductive step of the source's proof, the base case being proved here.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale` and the functor is
`CategoryTheory.MorphismProperty.Over.pullback` for the morphism property
`AlgebraicGeometry.Etale`, with the two instance arguments it needs supplied inline in every
statement, exactly as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence`.

The affine objects are cut out by a `CategoryTheory.ObjectProperty` and the restricted functor is
its `CategoryTheory.ObjectProperty.lift`, so it is literally the functor induced by base change
rather than an arbitrary functor isomorphic to it. The witness that base change preserves
affineness is produced alongside, since the lift cannot be formed without it; pinning the functor
this way means the existential statement is not weaker than the assertion it formalizes.

Because the carried hypothesis produces an *affine* descent, as the source's proof does, the
affine correspondence needs no affineness reflection along the projection of a base change.

The namespace `AlgebraicGeometry` is opened as `_root_.AlgebraicGeometry`: a namespace
`Stacks.AlgebraicGeometry` exists elsewhere in the library and would otherwise shadow it from
inside `Stacks.Etale`.

The localization step uses `AlgebraicGeometry.Scheme.Hom.resLE` for the restriction of the
structure morphism to the affine open, so that the compatibility equation is the one
`AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` discharges.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 03WS](https://stacks.math.columbia.edu/tag/03WS)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
* [Stacks Project, Tag 05YX](https://stacks.math.columbia.edu/tag/05YX)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- **The affine case of the correspondence of Stacks Project, Tag 04E0.** For a universal
homeomorphism `f : X ⟶ Y` between affine schemes, every affine scheme étale over `X` is, over
`X`, the base change along `f` of an affine scheme étale over `Y`.

This is the essential surjectivity of the functor displayed as Stacks Project, Tag 04E0, which
the source proves by induction on a bound for the degree of the fibres of an étale morphism of
affine schemes, descending at each step by effectivity of affine descent (Stacks Project,
Tag 0245). That induction is not formalized in this library, so the statement occurs as an
explicit hypothesis. -/
def EssSurjAffineEtalePullback : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), UniversalHomeomorphism f → IsAffine X → IsAffine Y →
    ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p → IsAffine U →
      ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e : pullback q f ≅ U),
        e.hom ≫ p = pullback.snd q f

variable {X Y : Scheme.{u}}

/-- The restriction of a universal homeomorphism over an open subscheme of its target is a
universal homeomorphism, being a base change of it. -/
theorem universalHomeomorphism_morphismRestrict (f : X ⟶ Y) [UniversalHomeomorphism f]
    (W : Y.Opens) : UniversalHomeomorphism (f ∣_ W) := by
  rw [universalHomeomorphism_iff]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f W).flip ((universalHomeomorphism_iff f).mp inferInstance)

/-- **A descent over an open subscheme of the target is a descent over the target.** Let
`p : U ⟶ X` be a morphism of schemes over `X`, let `W` be an open subscheme of `Y` and let `A` be
an open subscheme of `U` lying over `f ⁻¹ᵁ W`. If `A` is, over `f ⁻¹ᵁ W`, the base change along
the restriction `f ∣_ W` of a scheme étale over `W`, then `A` is a descended open subscheme of
`U` for `f`.

The defining square of the base change over `W` is pasted onto the restriction square of `f`
over `W`, which exhibits the same scheme as the fibre product over `Y`. -/
theorem mem_descendedOpens_of_resLE (f : X ⟶ Y) {U : Scheme.{u}} (p : U ⟶ X) (W : Y.Opens)
    (A : U.Opens) (hA : A ≤ p ⁻¹ᵁ (f ⁻¹ᵁ W)) {V : Scheme.{u}} (q : V ⟶ W.toScheme)
    (hq : Etale q) (e : pullback q (f ∣_ W) ≅ A.toScheme)
    (he : e.hom ≫ p.resLE (f ⁻¹ᵁ W) A hA = pullback.snd q (f ∣_ W)) :
    A ∈ descendedOpens f p := by
  have : Etale q := hq
  have hsq : IsPullback (pullback.fst q (f ∣_ W))
      (pullback.snd q (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι) (q ≫ W.ι) f :=
    (IsPullback.of_hasPullback q (f ∣_ W)).paste_vert (isPullback_morphismRestrict f W)
  refine ⟨V, q ≫ W.ι, inferInstance, hsq.isoPullback.symm ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_comp_eq, hsq.isoPullback_hom_snd,
    ← Scheme.Hom.resLE_comp_ι p hA, ← Category.assoc, he]

/-- **Essential surjectivity of base change on small étale sites from its affine case.** Let
`f : X ⟶ Y` be a universal homeomorphism. Granted the affine case, every scheme étale over `X`
is, over `X`, the base change along `f` of a scheme étale over `Y`.

A universal homeomorphism is affine, so the preimage of an affine open of `Y` is an affine open
of `X`; the affine opens of a scheme étale over `X` lying over such a preimage cover it, each one
descends by the affine case, and the glueing of descended open subschemes along an open covering
is a global descent. This is the first paragraph of both proofs of Stacks Project, Tag 04DZ. -/
theorem exists_etale_pullback_iso_of_essSurjAffine (h04E0 : EssSurjAffineEtalePullback.{u})
    (f : X ⟶ Y) [UniversalHomeomorphism f] (U : Scheme.{u}) (p : U ⟶ X) (hp : Etale p) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  have : Etale p := hp
  have := isIntegralHom_of_universalHomeomorphism f
  refine exists_etale_pullback_iso_of_descendedOpens_cover f p fun x ↦ ?_
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base (p.base x))
      (U := ⊤) (TopologicalSpace.Opens.mem_top _)
  obtain ⟨A, hA, hxA, hAle⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U) (x := x) (U := p ⁻¹ᵁ (f ⁻¹ᵁ W)) hxW
  have hAle' : A ≤ p ⁻¹ᵁ (f ⁻¹ᵁ W) := hAle
  have : UniversalHomeomorphism (f ∣_ W) := universalHomeomorphism_morphismRestrict f W
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hW.preimage f
  have : IsAffine W.toScheme := hW
  have : IsAffine A.toScheme := hA
  obtain ⟨V, q, hq, -, e, he⟩ := h04E0 (f ∣_ W) inferInstance inferInstance inferInstance
    A.toScheme (p.resLE (f ⁻¹ᵁ W) A hAle') inferInstance hA
  exact ⟨A, mem_descendedOpens_of_resLE f p W A hAle' q hq e he, hxA⟩

/-- Base change along a universal homeomorphism `f : X ⟶ Y` carries an affine scheme over `Y` to
an affine scheme over `X`: a universal homeomorphism is an affine morphism, hence so is the
projection `V ×_Y X ⟶ V`. -/
theorem isAffine_pullback_of_universalHomeomorphism (f : X ⟶ Y) [UniversalHomeomorphism f]
    {V : Scheme.{u}} (q : V ⟶ Y) (hV : IsAffine V) : IsAffine (pullback q f) := by
  have := isIntegralHom_of_universalHomeomorphism f
  have : IsAffine V := hV
  exact isAffine_of_isAffineHom (f := pullback.fst q f) (Y := V)

/-- **Full faithfulness of the affine correspondence of Stacks Project, Tag 04E0.** Let
`f : X ⟶ Y` be a universal homeomorphism of affine schemes. Base change along `f` carries an
affine scheme étale over `Y` to an affine scheme étale over `X`, and the induced functor between
the affine objects of the two small étale sites is full and faithful.

Full faithfulness is Tag 0BTY read on the affine objects, and affineness is preserved because a
universal homeomorphism is an affine morphism (Tag 04DF). This is one ingredient of Tag 04E0,
which is registered in full on `Stacks.Etale.affineEtalePullback_isEquivalence`: there the
essential surjectivity is supplied by `Stacks.Etale.essSurjAffineEtalePullback`. -/
theorem affineEtalePullback_fullyFaithful (f : X ⟶ Y) [UniversalHomeomorphism f]
    [IsAffine X] [IsAffine Y] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    let F : Y.Etale ⥤ X.Etale :=
      MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ f
    let PY : ObjectProperty Y.Etale := fun V ↦ IsAffine V.left
    let PX : ObjectProperty X.Etale := fun U ↦ IsAffine U.left
    ∃ h : ∀ V : PY.FullSubcategory, PX (F.obj V.obj),
      (PX.lift (PY.ι ⋙ F) h).Full ∧ (PX.lift (PY.ι ⋙ F) h).Faithful := by
  intro F PY PX
  have hAff : ∀ V : PY.FullSubcategory, PX (F.obj V.obj) := fun V ↦
    isAffine_pullback_of_universalHomeomorphism f V.obj.hom V.property
  have : F.Full := etalePullback_full_of_universalHomeomorphism f
  have : F.Faithful := etalePullback_faithful_of_universalHomeomorphism f
  exact ⟨hAff, inferInstance, inferInstance⟩

/-- **The affine correspondence is an equivalence, given the affine case.** Let `f : X ⟶ Y` be a
universal homeomorphism of affine schemes. Base change along `f` restricts to an equivalence
between the full subcategory of affine objects of the small étale site of `Y` and that of the
small étale site of `X`.

The hypothesis is the essential surjectivity of exactly this correspondence, that is the content
of Stacks Project, Tag 04E0; what is added is its full faithfulness. -/
theorem affineEtalePullback_isEquivalence_of_essSurjAffine
    (h04E0 : EssSurjAffineEtalePullback.{u}) (f : X ⟶ Y) [UniversalHomeomorphism f]
    [IsAffine X] [IsAffine Y] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    let F : Y.Etale ⥤ X.Etale :=
      MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ f
    let PY : ObjectProperty Y.Etale := fun V ↦ IsAffine V.left
    let PX : ObjectProperty X.Etale := fun U ↦ IsAffine U.left
    ∃ h : ∀ V : PY.FullSubcategory, PX (F.obj V.obj),
      (PX.lift (PY.ι ⋙ F) h).IsEquivalence := by
  intro F PY PX
  have hAff : ∀ V : PY.FullSubcategory, PX (F.obj V.obj) := fun V ↦
    isAffine_pullback_of_universalHomeomorphism f V.obj.hom V.property
  have : F.Full := etalePullback_full_of_universalHomeomorphism f
  have : F.Faithful := etalePullback_faithful_of_universalHomeomorphism f
  have : (PX.lift (PY.ι ⋙ F) hAff).EssSurj := by
    refine ⟨fun U ↦ ?_⟩
    have : Etale U.obj.hom := U.obj.prop
    obtain ⟨V, q, hq, hVaff, e, he⟩ := h04E0 f inferInstance inferInstance inferInstance
      U.obj.left U.obj.hom inferInstance U.property
    exact ⟨⟨MorphismProperty.Over.mk ⊤ q hq, hVaff⟩, ⟨PX.isoMk (MorphismProperty.Over.isoMk e he)⟩⟩
  exact ⟨hAff, { }⟩

/-! ### The affineness of the descended scheme is automatic -/

/-- **A scheme whose base change along a universal homeomorphism is affine is affine.** Let
`f : X ⟶ Y` be a universal homeomorphism and let `q : V ⟶ Y` be a morphism of schemes such
that `V ×_Y X` is affine. Then `V` is affine.

The projection `V ×_Y X ⟶ V` is a base change of `f`, hence surjective and universally closed,
and a scheme admitting a surjective universally closed morphism from an affine scheme is affine
by Stacks Project, Tag 05YU. -/
theorem isAffine_of_isAffine_pullback (f : X ⟶ Y) [UniversalHomeomorphism f] {V : Scheme.{u}}
    (q : V ⟶ Y) (h : IsAffine (pullback q f)) : IsAffine V := by
  obtain ⟨-, -, hsurj⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance
  have := isIntegralHom_of_universalHomeomorphism f
  have : Surjective (pullback.fst q f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback q f).flip hsurj
  have : UniversallyClosed (pullback.fst q f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @UniversallyClosed)
      (IsPullback.of_hasPullback q f).flip inferInstance
  have : IsAffine (pullback q f) := h
  exact AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed (pullback.fst q f)

/-- **The affine case does not have to produce an affine descent.** Suppose that along every
universal homeomorphism `f : X ⟶ Y` of affine schemes, every affine scheme étale over `X` is,
over `X`, the base change along `f` of *some* scheme étale over `Y`, not required to be affine.
Then `Stacks.Etale.EssSurjAffineEtalePullback` holds.

So the hypothesis carried by this file is no stronger than its own statement with the clause
`IsAffine V` deleted: the base change of the descended scheme is the affine scheme one started
from, so `Stacks.Etale.isAffine_of_isAffine_pullback` recovers the affineness. This is the
mechanism of the remark on Stacks Project, Tag 05YX, which likewise derives the affine form of
the correspondence of Tag 04E0 from its general form through Stacks Project, Tag 05YU. -/
theorem essSurjAffineEtalePullback_of_exists_etale_pullback_iso
    (h : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), UniversalHomeomorphism f → IsAffine X → IsAffine Y →
      ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p → IsAffine U →
        ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
          e.hom ≫ p = pullback.snd q f) :
    EssSurjAffineEtalePullback.{u} := by
  intro X Y f hf hX hY U p hp hU
  obtain ⟨V, q, hq, e, he⟩ := h f hf hX hY U p hp hU
  have : UniversalHomeomorphism f := hf
  have : IsAffine U := hU
  exact ⟨V, q, hq, isAffine_of_isAffine_pullback f q (IsAffine.of_isIso e.hom), e, he⟩

/-! ### The base case of the source's induction -/

/-- **The affine case for an open immersion.** Let `f : X ⟶ Y` be a universal homeomorphism and
let `p : U ⟶ X` be an open immersion with `U` affine. Then `U` is, over `X`, the base change
along `f` of an affine scheme étale over `Y` — namely of the open subscheme of `Y` which
corresponds to the open subscheme `U` of `X` under the homeomorphism `f`.

This is the case `n = 1` of the induction in the second proof of Stacks Project, Tag 04DZ,
where Stacks Project, Tag 025G turns a degree-one étale morphism into an open immersion. The
open subscheme of `Y` and the identification of its base change with `U` are
`Stacks.EtaleCohomology.exists_hom_isIso_left_of_isOpenImmersion`; what is added here is that
this open subscheme is affine, by `Stacks.Etale.isAffine_of_isAffine_pullback`. -/
theorem exists_affine_etale_pullback_iso_of_isOpenImmersion (f : X ⟶ Y)
    [UniversalHomeomorphism f] {U : Scheme.{u}} (p : U ⟶ X) [IsOpenImmersion p]
    (hU : IsAffine U) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  have hoi : IsOpenImmersion (Scheme.Etale.mk p).hom := inferInstanceAs (IsOpenImmersion p)
  obtain ⟨V, m, hm⟩ :=
    EtaleCohomology.exists_hom_isIso_left_of_isOpenImmersion f (Scheme.Etale.mk p)
  have hU' : IsAffine (Scheme.Etale.mk p).left := hU
  have hpb : IsAffine (pullback V.hom f) := @IsAffine.of_isIso _ _ m.left hm hU'
  exact ⟨V.left, V.hom, V.prop, isAffine_of_isAffine_pullback f V.hom hpb,
    @asIso _ _ _ _ m.left hm, MorphismProperty.Over.w m⟩

/-- **The base case of the source's induction.** Let `f : X ⟶ Y` be a universal homeomorphism
and let `p : U ⟶ X` be an étale morphism with `U` affine whose fibres have degree bounded by
one. Then `U` is, over `X`, the base change along `f` of an affine scheme étale over `Y`.

The bound makes `p` an open immersion, by Stacks Project, Tag 025G in the form
`AlgebraicGeometry.isOpenImmersion_of_boundsFiberDegrees_one`, and
`Stacks.Etale.exists_affine_etale_pullback_iso_of_isOpenImmersion` applies. The integer bounding
the degrees of the fibres is the one Stacks Project, Tag 03WU describes, and the induction on it
by which the source proves `Stacks.Etale.EssSurjAffineEtalePullback` in full is not formalized
here; this is its first step. -/
theorem exists_affine_etale_pullback_iso_of_boundsFiberDegrees_one (f : X ⟶ Y)
    [UniversalHomeomorphism f] {U : Scheme.{u}} (p : U ⟶ X) (hp : Etale p)
    (hdeg : BoundsFiberDegrees p ((1 : ℕ) : ℤ)) (hU : IsAffine U) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  have : Etale p := hp
  have : IsOpenImmersion p := isOpenImmersion_of_boundsFiberDegrees_one p hdeg
  exact exists_affine_etale_pullback_iso_of_isOpenImmersion f p hU

/-! ### Reduction of the affine case to the source's induction step -/

/-- **The affine case restricted to a bound on the degrees of the fibres.** For a universal
homeomorphism `f : X ⟶ Y` between affine schemes, every affine scheme étale over `X` whose
fibre degrees are bounded by `n` is, over `X`, the base change along `f` of an affine scheme
étale over `Y`.

This is the statement on which the second proof of Stacks Project, Tag 04DZ runs its induction;
`Stacks.Etale.EssSurjAffineEtalePullback` is its union over all `n`, because an étale morphism of
affine schemes has universally bounded fibres. -/
def EssSurjAffineEtalePullbackBounded (n : ℕ) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), UniversalHomeomorphism f → IsAffine X → IsAffine Y →
    ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p → IsAffine U → BoundsFiberDegrees p (n : ℤ) →
      ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e : pullback q f ≅ U),
        e.hom ≫ p = pullback.snd q f

/-- A bound on the degrees of the fibres of a morphism is also a bound by any larger integer. -/
theorem boundsFiberDegrees_mono {U Z : Scheme.{u}} {p : U ⟶ Z} {m n : ℤ}
    (h : BoundsFiberDegrees p m) (hmn : m ≤ n) : BoundsFiberDegrees p n := by
  intro z
  obtain ⟨r, hr, hrank⟩ := h z
  exact ⟨r, hr.trans hmn, hrank⟩

/-- **The base case of the source's induction, in the form the induction uses.** -/
theorem essSurjAffineEtalePullbackBounded_one : EssSurjAffineEtalePullbackBounded.{u} 1 := by
  intro X Y f hf hX hY U p hp hU hdeg
  have : UniversalHomeomorphism f := hf
  exact exists_affine_etale_pullback_iso_of_boundsFiberDegrees_one f p hp hdeg hU

/-- **The affine case is the union of its bounded forms.** An étale morphism of affine schemes
has universally bounded fibres, by Stacks Project, Tags 03WS and 03JA, so if
`Stacks.Etale.EssSurjAffineEtalePullbackBounded` holds for every `n` then
`Stacks.Etale.EssSurjAffineEtalePullback` holds. -/
theorem essSurjAffineEtalePullback_of_forall_bounded
    (h : ∀ n : ℕ, EssSurjAffineEtalePullbackBounded.{u} n) : EssSurjAffineEtalePullback.{u} := by
  intro X Y f hf hX hY U p hp hU
  have : Etale p := hp
  have : IsAffine U := hU
  have : LocallyQuasiFinite p := (locallyQuasiFinite_of_etale p).2
  have : CompactSpace U := inferInstance
  obtain ⟨n, hn⟩ := hasUniversallyBoundedFibers_of_locallyQuasiFinite p
  exact h n.toNat f hf hX hY U p hp hU (boundsFiberDegrees_mono hn (Int.self_le_toNat n))

/-- **The affine case follows from the source's induction step alone.** Granted that the affine
case for a bound of `n ≥ 1` on the fibre degrees implies the affine case for a bound of `n + 1`,
`Stacks.Etale.EssSurjAffineEtalePullback` holds.

So the hypothesis carried by this file is no stronger than the single inductive step of the
second proof of Stacks Project, Tag 04DZ: the base case `n = 1` is
`Stacks.Etale.essSurjAffineEtalePullbackBounded_one`, the degenerate case `n = 0` follows from
it because a bound of zero is a bound of one, and the passage from the bounded statements to the
unbounded one is `Stacks.Etale.essSurjAffineEtalePullback_of_forall_bounded`. The step itself —
dominating `U` by the base change of an étale `W ⟶ Y` with `W` affine (Stacks Project,
Tag 04DW), splitting off the section to drop the bound to `n - 1`, and descending the resulting
étale `W`-scheme along `W ⟶ Y` by effectivity of affine descent (Stacks Project, Tag 0245)
using the full faithfulness of `Stacks.Etale.affineEtalePullback_fullyFaithful` over
`W ×_Y W` — is not formalized here. -/
theorem essSurjAffineEtalePullback_of_inductiveStep
    (hstep : ∀ n : ℕ, 1 ≤ n → EssSurjAffineEtalePullbackBounded.{u} n →
      EssSurjAffineEtalePullbackBounded.{u} (n + 1)) :
    EssSurjAffineEtalePullback.{u} := by
  refine essSurjAffineEtalePullback_of_forall_bounded fun n ↦ ?_
  induction n with
  | zero =>
    intro X Y f hf hX hY U p hp hU hdeg
    exact essSurjAffineEtalePullbackBounded_one f hf hX hY U p hp hU
      (boundsFiberDegrees_mono hdeg (by norm_num))
  | succ k ih =>
    obtain rfl | hk := Nat.eq_zero_or_pos k
    · exact essSurjAffineEtalePullbackBounded_one
    · exact hstep k hk ih

end Stacks.Etale

end

end
