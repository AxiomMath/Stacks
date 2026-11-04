module

public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Chart
public import StacksFrontier.AlgebraicGeometry.CotangentAppIso.Sections
public import StacksFrontier.AlgebraicGeometry.DiagonalChartPresentation.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient presentation of an immersion over an affine open

The part (2) machinery of [Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) — namely
`Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel`,
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` and
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` — is stated for an immersion
`i : Z ⟶ X`, an affine open `V` of `X` and *presentation data*

* an ideal `I` of `Γ(X, V)`,
* an isomorphism `e : pullback i V.ι ≅ Spec (Γ(X, V) ⧸ I)`,
* a compatibility `he : pullback.snd i V.ι ≫ hV.isoSpec.hom = e.hom ≫ Spec.map (Quotient.mk I)`.

Nothing in the repository *produced* that data. The "What is not done" sections of
`StacksFrontier.AlgebraicGeometry.DiagonalChartPresentation.Basic` and of
`StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine` both record it as missing — the first
in the words "the isomorphism of schemes and its compatibility are not constructed" — and so every
one of those engines was uninstantiable at the diagonal of a morphism of schemes. This file
produces it, from a single hypothesis, and instantiates it at the diagonal.

**The hypothesis is the right one.** The data is produced for any immersion `i` and affine open `V`
such that the *restriction* `i ∣_ V` is a closed immersion — not for `i` closed, which the diagonal
of a non-separated morphism is not. The observation making this work is that

  `pullback.snd i V.ι ≫ hV.isoSpec.hom`

is then a closed immersion into an affine scheme, because `pullback.snd i V.ι` is `i ∣_ V`
precomposed with the isomorphism `pullbackRestrictIsoRestrict i V`; and
`AlgebraicGeometry.IsClosedImmersion.Spec_iff` says exactly that a closed immersion into `Spec R`
is `Spec` of a quotient map up to an isomorphism of the source. Its `∃ I, ∃ e, …` is, verbatim, the
presentation data: the equation it provides *is* `he`.

At the diagonal the hypothesis is discharged by
`Stacks.LeibnizDerivation.isClosedImmersion_diagRes`, which gives the restricted diagonal as a
closed immersion for `U` and `V` affine — it is split by the first projection, so surjective on
global sections, with both ends affine.

## Main results

* `Stacks.DiagonalPresentation.isClosedImmersion_pullback_snd_comp_isoSpec`: the morphism whose
  presentation `AlgebraicGeometry.IsClosedImmersion.Spec_iff` describes is a closed immersion.
* `Stacks.DiagonalPresentation.exists_presentation`: **the presentation data, for any immersion
  closed over an affine open.** Stated for an arbitrary morphism of schemes `i`, with no immersion
  hypothesis at all — `IsClosedImmersion (i ∣_ V)` is all that is used.
* `Stacks.DiagonalPresentation.isClosedImmersion_diagonal_morphismRestrict`: the diagonal
  restricted to the ambient chart, in the `∣_` spelling the engines require.
* `Stacks.DiagonalPresentation.exists_diagonalPresentation`: **the presentation data at the
  diagonal**, for `U` and `V` affine.
* `Stacks.DiagonalPresentation.presentation_ideal_eq`: **the ideal of a presentation is not a
  choice** — it is the kernel of the presented morphism's comorphism on global sections, so any two
  presentations over one affine open have the same ideal.
* `Stacks.DiagonalPresentation.presentationIdeal_eq_ker_diagAppLE`: **at the diagonal that ideal is
  the ideal of the diagonal in the chart**, `RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom`.
* `Stacks.DiagonalPresentation.exists_diagonalPresentation_ker`: the presentation data at the
  diagonal with its ideal named.
* `Stacks.DiagonalPresentation.exists_diagonalConormalSectionsIsoCotangent`: the consequence —
  the sections over the ambient chart of the pushforward along the diagonal of the conormal sheaf
  of the diagonal are `I ⧸ I²` for `I` the ideal of the diagonal in the chart.

## What is not done

* **No generator formula, and therefore no clause of [Stacks, Tag 08S2].** The iso obtained here is
  `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent`, which carries none: its own
  docstring records that it inhabits the type of [Stacks, Tag 01R3]'s part (2) assertion without
  the formula on ideal generators. An *abstract* isomorphism of the conormal sections with
  `Ω[Γ(X, U)⁄Γ(S, V)]` does **not** discharge
  `IsIso (Stacks.LeibnizDerivation.kaehlerToConormal f V U hUV)`, because `kaehlerToConormal` is
  pinned by its generator formula `kaehlerToConormal_d` and an abstract iso of modules says nothing
  about a particular map between them. That remains the missing input for Tag 08S2, exactly as
  `StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine` records it.
* **Nothing about `Ideal.Cotangent` transport.** Mathlib has `Ideal.Cotangent.equivOfEq`, for two
  *equal* ideals of one ring, and no transport along a ring
  isomorphism matching a pair of ideals; that lemma is still owed, and is what would carry
  `RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom` across
  `Stacks.DiagonalChart.tensorIsoChart` to `KaehlerDifferential.ideal Γ(S, V) Γ(X, U)` and so
  rewrite the cotangent module above as `Ω[Γ(X, U)⁄Γ(S, V)]`. A further step is then needed to
  compare the two module structures: the left-hand side here is a
  `Γ(X ×_S X, ambientChart f U)`-module and `kaehlerToConormal` lives in `ModuleCat Γ(X, U)`, and
  `Stacks.DiagonalChart.diagAppLE` relating the two rings is surjective
  (`Stacks.LeibnizDerivation.surjective_diagRes_appTop`), which is what makes a
  `Γ(X ×_S X, ambientChart f U)`-linear map between `Γ(X, U)`-modules automatically
  `Γ(X, U)`-linear. Neither step is taken here.

## Vocabulary

The conormal sheaf of [Stacks, Tag 01R2] is `Stacks.Conormal.conormalSheaf`
(`StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison`).

**No `stacks` attribute is attached.** No clause of [Stacks, Tag 08S2] is stated here, and the
part (2) assertions of [Stacks, Tag 01R3] are assertions about an identification carrying a
generator formula, which nothing here supplies. Everything below is the construction of the
*hypotheses* those assertions are stated under.

Nothing is Noetherian, separated, finite or quasi-compact. `f` is an arbitrary morphism of schemes
and `i` in the general results is an arbitrary morphism, not even an immersion.

## Transparency gotchas

`AlgebraicGeometry.Scheme.Hom.resLE` is `X.homOfLE e ≫ f ∣_ U` by definition, so
`Stacks.LeibnizDerivation.diagRes f U` and `pullback.diagonal f ∣_ ambientChart f U` are *not*
definitionally equal: passing between them needs `homOfLE le_rfl = 𝟙`, which is a lemma and not
`rfl`. `AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict` is therefore rewritten into the
*goal* rather than into the hypothesis — after
`AlgebraicGeometry.Scheme.Hom.resLE_congr` has moved the source open from `U` to
`pullback.diagonal f ⁻¹ᵁ ambientChart f U`, the two `resLE` terms differ only in a proof argument
and `exact` closes the gap by proof irrelevance. Rewriting the hypothesis instead leaves
`IsClosedImmersion (resLE …)` against `IsClosedImmersion (… ∣_ …)` and fails with a type mismatch
reporting `getLimitCone` and `inv` as unexposed.

`AlgebraicGeometry.Scheme.Hom.resLE_congr` takes the morphism and the containment proof
explicitly, ahead of the two opens equalities and the morphism property, and the property is passed
as `@IsClosedImmersion` — supplying it positionally in the wrong slot reports the property as
having sort `Type (u+1)` where an equation was expected.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

noncomputable section

namespace Stacks.DiagonalPresentation

/-! ### The comorphism of an isomorphism of schemes -/

/-- **The comorphism of an isomorphism of schemes on global sections is an isomorphism.** Instance
search does not find this: `IsIso ε.hom.appTop` fails to synthesize even with `IsIso ε.hom`
available, so the inverse is exhibited by hand as `ε.inv.appTop` and the two identities come from
the contravariance of `AlgebraicGeometry.Scheme.Hom.comp_appTop`. -/
theorem isIso_appTop_of_iso {A B : Scheme.{u}} (ε : A ≅ B) : IsIso ε.hom.appTop := by
  refine ⟨ε.inv.appTop, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_appTop, ε.inv_hom_id, Scheme.Hom.id_appTop]
  · rw [← Scheme.Hom.comp_appTop, ε.hom_inv_id, Scheme.Hom.id_appTop]

/-- The kernel of a ring map is unchanged by postcomposing with an isomorphism. -/
private theorem ker_hom_comp_of_isIso {A B C : CommRingCat.{u}} (g : A ⟶ B) (h : B ⟶ C)
    [IsIso h] : RingHom.ker (g ≫ h).hom = RingHom.ker g.hom :=
  RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso h).1

/-! ### The presentation data of a morphism closed over an affine open -/

section General

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)

/-- **The morphism presented by `AlgebraicGeometry.IsClosedImmersion.Spec_iff` is a closed
immersion.** The second projection of `pullback i V.ι` is the restriction `i ∣_ V` precomposed with
the isomorphism `AlgebraicGeometry.pullbackRestrictIsoRestrict`, so composing it with the affine
identification of `V` gives a closed immersion into `Spec Γ(X, V)` as soon as `i ∣_ V` is one.

No hypothesis on `i` itself is used; in particular `i` need not be an immersion, and when `i` is an
immersion it need not be a closed one. -/
theorem isClosedImmersion_pullback_snd_comp_isoSpec [IsClosedImmersion (i ∣_ V)] :
    IsClosedImmersion (Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom) := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict i V, Category.assoc]
  infer_instance

/-- **The presentation data that the part (2) machinery of [Stacks, Tag 01R3] takes as
hypotheses.** For a morphism of schemes `i : Z ⟶ X` and an affine open `V` of `X` over which `i`
restricts to a closed immersion, there are an ideal `I` of `Γ(X, V)`, an isomorphism of
`pullback i V.ι` with `Spec (Γ(X, V) ⧸ I)`, and the compatibility over `V` that
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent`,
`Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel` and
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` all require.

This is `AlgebraicGeometry.IsClosedImmersion.Spec_iff` applied to
`isClosedImmersion_pullback_snd_comp_isoSpec`: the equation that lemma supplies is literally the
compatibility, so no further argument is needed. The ideal it produces is not exposed by `Spec_iff`
and is correspondingly opaque here; see the module docstring. -/
theorem exists_presentation [IsClosedImmersion (i ∣_ V)] :
    ∃ (I : Ideal Γ(X, V)) (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I))),
      Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  have := isClosedImmersion_pullback_snd_comp_isoSpec i V hV
  IsClosedImmersion.Spec_iff.1 ‹_›

/-- **The ideal of a presentation is determined: it is the kernel of the presented morphism's
comorphism on global sections.** `AlgebraicGeometry.IsClosedImmersion.Spec_iff` is an `↔` and does
not say which ideal its forward direction produces, but the compatibility `he` pins it down —
taking `appTop` of `he` and using `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality` turns the
left-hand side into `Ideal.Quotient.mk I` followed by two isomorphisms, and
`RingHom.ker_comp_of_injective` then reduces the kernel to `Ideal.mk_ker`.

So the presentation data, although obtained from an existential, carries no choice in its ideal:
any two presentations over the same affine open have the same one. -/
theorem presentation_ideal_eq (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    RingHom.ker ((Scheme.ΓSpecIso Γ(X, V)).inv ≫
      (Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom).appTop).hom = I := by
  have := isIso_appTop_of_iso e
  rw [he, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc, ker_hom_comp_of_isIso]
  exact Ideal.mk_ker

end General

/-! ### The presentation data at the diagonal -/

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) {V : S.Opens}

/-- **The diagonal restricted to the ambient chart is a closed immersion**, in the `∣_` spelling
the part (2) machinery is stated at.

`Stacks.LeibnizDerivation.isClosedImmersion_diagRes` gives this for
`Stacks.LeibnizDerivation.diagRes f U`, which is the `resLE` spelling with source open `U`; the two
are related by moving the source open along
`Stacks.LeibnizDerivation.diagonal_preimage_ambientChart` with
`AlgebraicGeometry.Scheme.Hom.resLE_congr` and then discharging
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict` in the goal. -/
@[ega "IV 16.3.1" "partial"]
theorem isClosedImmersion_diagonal_morphismRestrict (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    IsClosedImmersion (pullback.diagonal f ∣_ Stacks.LeibnizDerivation.ambientChart f U) := by
  have h0 : IsClosedImmersion ((pullback.diagonal f).resLE
      (Stacks.LeibnizDerivation.ambientChart f U) U
      (Stacks.LeibnizDerivation.le_diagonal_preimage_ambientChart f U)) :=
    Stacks.LeibnizDerivation.isClosedImmersion_diagRes f U hV hU hUV
  have h1 := (Scheme.Hom.resLE_congr (pullback.diagonal f)
      (Stacks.LeibnizDerivation.le_diagonal_preimage_ambientChart f U) rfl
      (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U).symm
      @IsClosedImmersion).1 h0
  rw [← Scheme.Hom.resLE_eq_morphismRestrict (pullback.diagonal f)
    (U := Stacks.LeibnizDerivation.ambientChart f U)]
  exact h1

/-- **The presentation data at the diagonal of a morphism of schemes**, over the ambient chart of
an affine open `U` lying over an affine open `V`. This is `exists_presentation` with its hypothesis
discharged by `isClosedImmersion_diagonal_morphismRestrict`, and it is the input that
`StacksFrontier.AlgebraicGeometry.DiagonalChartPresentation.Basic` records as not constructed.

The morphism `f` is arbitrary: the diagonal is not assumed closed, and the ambient chart is affine
by `Stacks.LeibnizDerivation.isAffineOpen_ambientChart`. -/
theorem exists_diagonalPresentation (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    ∃ (I : Ideal Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U))
      (e : Limits.pullback (pullback.diagonal f)
          (Stacks.LeibnizDerivation.ambientChart f U).ι ≅
        Spec (.of (Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) ⧸ I))),
      Limits.pullback.snd (pullback.diagonal f)
            (Stacks.LeibnizDerivation.ambientChart f U).ι ≫
          (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU hUV).isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  have := isClosedImmersion_diagonal_morphismRestrict f U hV hU hUV
  exists_presentation (pullback.diagonal f) (Stacks.LeibnizDerivation.ambientChart f U)
    (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU hUV)

/-! ### The presentation ideal at the diagonal is the ideal of the diagonal -/

/-- **The comorphism presented at the diagonal, with the affine identification of the chart
stripped off.** `AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop` cancels the `ΓSpecIso` against
the affine identification, and
`AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict` replaces the pullback's second
projection by the restriction of the diagonal. -/
theorem ΓSpecIso_inv_comp_appTop_eq (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    (Scheme.ΓSpecIso Γ(Limits.pullback f f,
          Stacks.LeibnizDerivation.ambientChart f U)).inv ≫
        (Limits.pullback.snd (pullback.diagonal f)
            (Stacks.LeibnizDerivation.ambientChart f U).ι ≫
          (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU hUV).isoSpec.hom).appTop =
      (Stacks.LeibnizDerivation.ambientChart f U).topIso.inv ≫
        (pullback.diagonal f ∣_ Stacks.LeibnizDerivation.ambientChart f U).appTop ≫
          (pullbackRestrictIsoRestrict (pullback.diagonal f)
            (Stacks.LeibnizDerivation.ambientChart f U)).hom.appTop := by
  rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, Category.assoc,
    Iso.inv_hom_id_assoc, ← pullbackRestrictIsoRestrict_hom_morphismRestrict
      (pullback.diagonal f) (Stacks.LeibnizDerivation.ambientChart f U),
    Scheme.Hom.comp_appTop]

/-- **The restricted diagonal's comorphism on global sections is the diagonal's `appLE` down to
`U`**, up to two isomorphisms. `AlgebraicGeometry.Scheme.Hom.resLE_app_top` computes the comorphism
of a `resLE`, and `AlgebraicGeometry.Scheme.Hom.appLE_map'` moves the source open from
`pullback.diagonal f ⁻¹ᵁ ambientChart f U` to `U` along
`Stacks.LeibnizDerivation.diagonal_preimage_ambientChart`. -/
theorem topIso_inv_comp_morphismRestrict_appTop_eq :
    (Stacks.LeibnizDerivation.ambientChart f U).topIso.inv ≫
        (pullback.diagonal f ∣_ Stacks.LeibnizDerivation.ambientChart f U).appTop =
      Stacks.DiagonalChart.diagAppLE f U ≫
        X.presheaf.map
            (eqToHom (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U)).op ≫
          (pullback.diagonal f ⁻¹ᵁ
            Stacks.LeibnizDerivation.ambientChart f U).topIso.inv := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict (pullback.diagonal f)
      (U := Stacks.LeibnizDerivation.ambientChart f U), Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, ← Category.assoc]
  congr 1
  exact (Scheme.Hom.appLE_map' (pullback.diagonal f) le_rfl
    (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U)).symm

/-- **The ideal of any presentation of the diagonal over its ambient chart is the ideal of the
diagonal in the chart**, namely the kernel of `Stacks.DiagonalChart.diagAppLE`.

Combining the two previous lemmas exhibits the presented comorphism as `diagAppLE` followed by
three isomorphisms — a presheaf restriction map along an equality of opens, the chart's `topIso`,
and the comorphism of `pullbackRestrictIsoRestrict` — so `RingHom.ker_comp_of_injective` leaves
exactly the kernel of `diagAppLE`.

This is what makes the presentation usable:
`Stacks.DiagonalChart.kaehlerIdeal_eq_comap_ker_diagAppLE` identifies this ideal with Mathlib's
`KaehlerDifferential.ideal Γ(S, V) Γ(X, U)` across the tensor presentation
`Stacks.DiagonalChart.tensorIsoChart`, and `Ω[Γ(X, U)⁄Γ(S, V)]` *is* the `Ideal.Cotangent` of the
latter by `rfl`. -/
theorem presentationIdeal_eq_ker_diagAppLE (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    RingHom.ker ((Scheme.ΓSpecIso Γ(Limits.pullback f f,
          Stacks.LeibnizDerivation.ambientChart f U)).inv ≫
        (Limits.pullback.snd (pullback.diagonal f)
            (Stacks.LeibnizDerivation.ambientChart f U).ι ≫
          (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU
            hUV).isoSpec.hom).appTop).hom =
      RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom := by
  have hmap : IsIso (X.presheaf.map
      (eqToHom (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U)).op) := by
    rw [eqToHom_op, eqToHom_map]; infer_instance
  have hpb := isIso_appTop_of_iso
    (pullbackRestrictIsoRestrict (pullback.diagonal f)
      (Stacks.LeibnizDerivation.ambientChart f U))
  have key : (Scheme.ΓSpecIso Γ(Limits.pullback f f,
        Stacks.LeibnizDerivation.ambientChart f U)).inv ≫
      (Limits.pullback.snd (pullback.diagonal f)
          (Stacks.LeibnizDerivation.ambientChart f U).ι ≫
        (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU
          hUV).isoSpec.hom).appTop =
      Stacks.DiagonalChart.diagAppLE f U ≫
        (X.presheaf.map
            (eqToHom (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U)).op ≫
          (pullback.diagonal f ⁻¹ᵁ
              Stacks.LeibnizDerivation.ambientChart f U).topIso.inv ≫
            (pullbackRestrictIsoRestrict (pullback.diagonal f)
              (Stacks.LeibnizDerivation.ambientChart f U)).hom.appTop) := by
    rw [ΓSpecIso_inv_comp_appTop_eq f U hV hU hUV, ← Category.assoc,
      topIso_inv_comp_morphismRestrict_appTop_eq f U]
    simp only [Category.assoc]
  rw [key, ker_hom_comp_of_isIso]

/-- **The presentation data at the diagonal, with its ideal named: the ideal of the diagonal in the
chart.** This is `exists_diagonalPresentation` with the ideal rewritten along
`presentation_ideal_eq` and `presentationIdeal_eq_ker_diagAppLE`, so that the data can be fed to
the part (2) engines at an ideal the rest of the development can recognize. -/
theorem exists_diagonalPresentation_ker (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    ∃ e : Limits.pullback (pullback.diagonal f)
        (Stacks.LeibnizDerivation.ambientChart f U).ι ≅
      Spec (.of (Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) ⧸
        RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom)),
      Limits.pullback.snd (pullback.diagonal f)
            (Stacks.LeibnizDerivation.ambientChart f U).ι ≫
          (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU hUV).isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom))) := by
  obtain ⟨I, e, he⟩ := exists_diagonalPresentation f U hV hU hUV
  have hI : I = RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom :=
    (presentation_ideal_eq (pullback.diagonal f) _
        (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU hUV) I e he).symm.trans
      (presentationIdeal_eq_ker_diagAppLE f U hV hU hUV)
  subst hI
  exact ⟨e, he⟩

/-- **The conormal sections of the diagonal over its ambient chart are `I ⧸ I²` for `I` the ideal
of the diagonal in the chart.** This is
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` instantiated at the diagonal
of an arbitrary morphism of schemes — the first such instantiation — with the presentation data of
`exists_diagonalPresentation_ker`.

By `pushforward_sections_eq` the left-hand side is, up to restriction of scalars, the sections of
the conormal sheaf over `pullback.diagonal f ⁻¹ᵁ ambientChart f U`, which is `U`; so this is the
affine conormal identification [Stacks, Tag 08S2] computes with.

**It is nevertheless not enough for Tag 08S2**, and the reason is recorded in the module docstring:
`conormalAffineSectionsIsoCotangent` carries no formula on ideal generators, so the isomorphism
produced here is not known to send `Stacks.LeibnizDerivation.cls f U b` anywhere in particular, and
`IsIso (Stacks.LeibnizDerivation.kaehlerToConormal f V U hUV)` is an assertion about a map that is
pinned precisely by such a formula. -/
theorem exists_diagonalConormalSectionsIsoCotangent (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    Nonempty (((modulePushforward (pullback.diagonal f).toLRSHom.toShHom).obj
          (Stacks.Conormal.conormalSheaf (pullback.diagonal f))).val.obj
          (.op (Stacks.LeibnizDerivation.ambientChart f U)) ≅
        ModuleCat.of Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U)
          (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom).Cotangent) := by
  obtain ⟨e, he⟩ := exists_diagonalPresentation_ker f U hV hU hUV
  exact ⟨Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent
    (pullback.diagonal f) (Stacks.LeibnizDerivation.ambientChart f U)
    (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU hUV) _ e he⟩

end Diagonal

end Stacks.DiagonalPresentation

end

end
