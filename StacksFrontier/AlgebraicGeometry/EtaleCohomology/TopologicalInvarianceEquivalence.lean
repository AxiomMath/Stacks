module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Topological invariance of the étale site: assembling the equivalence

Let `f : X ⟶ Y` be a universal homeomorphism. Base change along `f` is a functor from the small
étale site of `Y` to the small étale site of `X`, and it is already known to be full and
faithful. This file supplies everything else that the equivalence of Stacks Project, Tag 04DZ
needs beyond essential surjectivity, and records essential surjectivity in elementary terms: a
scheme étale over `X` is in the essential image exactly when it is isomorphic, over `X`, to the
base change of a scheme étale over `Y`.

Two concrete families of étale schemes over `X` are shown to be base changes. Every open
subscheme of `X` is one, because `f` is a homeomorphism on points and therefore matches up the
open subschemes of `X` and of `Y`; and every open subscheme of a base change is one, because the
projection `V ×_Y X ⟶ V` is again a universal homeomorphism, so an open subscheme of `V ×_Y X`
is cut out by a unique open subscheme of `V`. The second statement is the step which makes the
essential image closed under passage to open subschemes, so an essential-surjectivity argument
may be run on an open covering of the scheme to be descended.

What is *not* proved here is essential surjectivity itself. Following the source, it is the
effectivity of étale descent along a surjective integral morphism, Stacks Project, Tag 0BTP,
which this library does not have; its own input Tag 0BTN is available as
`Stacks.Etale.exists_coprod_isFinite_and_isEmpty_closedFiber`.

## Main results

* `Stacks.Etale.etalePullback_isEquivalence_of_universalHomeomorphism_of_essSurj` — base change
  along a universal homeomorphism is an equivalence of small étale sites as soon as it is
  essentially surjective. This is Stacks Project, Tag 04DZ with its remaining content isolated.
* `Stacks.Etale.essSurj_etalePullback_of_forall_exists_pullback_iso` — the elementary criterion
  for essential surjectivity: it is enough that every scheme étale over `X` be isomorphic over
  `X` to the base change of a scheme étale over `Y`.
* `Stacks.Etale.etalePullback_isEquivalence_of_forall_exists_pullback_iso` — the two combined.
* `Stacks.Etale.exists_opens_preimage_eq_of_universalHomeomorphism` — a universal homeomorphism
  matches up the open subschemes of its source and target.
* `Stacks.Etale.exists_etale_pullback_iso_of_opens` — every open subscheme of `X` is the base
  change of a scheme étale over `Y`.
* `Stacks.Etale.exists_etale_pullback_iso_of_opens_pullback` — every open subscheme of the base
  change of a scheme étale over `Y` is again the base change of a scheme étale over `Y`.
* `Stacks.Etale.existsUnique_hom_of_pullback_hom` — a morphism between base changes over `X` is
  the base change of a unique morphism over `Y`, stated on the projections of the fibre
  products.
* `Stacks.Etale.exists_iso_of_pullback_iso` — two schemes étale over `Y` with isomorphic base
  changes are isomorphic, so a descent is rigid and the cocycle condition of a glueing argument
  is automatic.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale`, that is
`CategoryTheory.MorphismProperty.Over AlgebraicGeometry.Etale ⊤ X`, and the functor is
`CategoryTheory.MorphismProperty.Over.pullback` for the morphism property
`AlgebraicGeometry.Etale`. The two instance arguments it needs are supplied inline in every
statement, exactly as in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance`:
`AlgebraicGeometry.Etale` is stable under base change, but the corresponding
`HasPullbacksAlong` instance is not found by unification.

The elementary criterion is stated with a bare isomorphism of schemes together with the
equation making it a morphism over `X`, rather than with an isomorphism in the étale site, so
that it can be discharged by a geometric construction with no over-category bookkeeping.

An open subscheme of a base change is identified with a base change by pasting the pullback
square of `AlgebraicGeometry.isPullback_morphismRestrict` on top of the defining pullback square
of `V ×_Y X`; the resulting square exhibits it as the fibre product of the open subscheme of `V`
with `X` over `Y`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is an equivalence from the small
étale site of `Y` to the small étale site of `X` as soon as it is essentially surjective: it is
full and faithful by the topological invariance of morphisms into an étale scheme.

Together with essential surjectivity this is Stacks Project, Tag 04DZ. -/
theorem etalePullback_isEquivalence_of_universalHomeomorphism_of_essSurj
    (f : X ⟶ Y) [UniversalHomeomorphism f]
    (hsurj :
      letI : MorphismProperty.HasPullbacksAlong
          (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
      letI : MorphismProperty.IsStableUnderBaseChangeAlong
          (@Etale : MorphismProperty Scheme.{u}) f :=
        ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
      (show Y.Etale ⥤ X.Etale from
        MorphismProperty.Over.pullback
          (@Etale : MorphismProperty Scheme.{u}) ⊤ f).EssSurj) :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).IsEquivalence := by
  have : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : Y.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ f
  change F.IsEquivalence
  let : F.Full := etalePullback_full_of_universalHomeomorphism f
  let : F.Faithful := etalePullback_faithful_of_universalHomeomorphism f
  let : F.EssSurj := hsurj
  exact {}

/-- **The elementary criterion for essential surjectivity of base change on small étale sites.**
If every scheme étale over `X` is isomorphic, over `X`, to the base change along `f` of a scheme
étale over `Y`, then base change along `f` is essentially surjective.

This is the remaining content of Stacks Project, Tag 04DZ, in a form carrying no over-category
data: a construction producing `V`, `q` and the isomorphism discharges it. -/
theorem essSurj_etalePullback_of_forall_exists_pullback_iso (f : X ⟶ Y)
    (hex : ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p →
      ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
        e.hom ≫ p = pullback.snd q f) :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).EssSurj := by
  have : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : Y.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ f
  change F.EssSurj
  refine ⟨fun A => ?_⟩
  obtain ⟨V, q, hq, e, he⟩ := hex A.left A.hom A.prop
  refine ⟨MorphismProperty.Over.mk ⊤ q hq, ⟨?_⟩⟩
  exact MorphismProperty.Over.isoMk e he

/-- **Topological invariance of the étale site, reduced to one existence statement.** If `f` is a
universal homeomorphism and every scheme étale over `X` is isomorphic over `X` to the base change
of a scheme étale over `Y`, then base change along `f` is an equivalence of small étale sites.

This is Stacks Project, Tag 04DZ; the hypothesis is its essential-surjectivity half. -/
theorem etalePullback_isEquivalence_of_forall_exists_pullback_iso
    (f : X ⟶ Y) [UniversalHomeomorphism f]
    (hex : ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p →
      ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
        e.hom ≫ p = pullback.snd q f) :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).IsEquivalence :=
  etalePullback_isEquivalence_of_universalHomeomorphism_of_essSurj f
    (essSurj_etalePullback_of_forall_exists_pullback_iso f hex)

/-- A universal homeomorphism matches up the open subschemes of its source and target: every
open subscheme of the source is the preimage of a unique open subscheme of the target. -/
theorem exists_opens_preimage_eq_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] (U : X.Opens) :
    ∃! W : Y.Opens, f ⁻¹ᵁ W = U := by
  have hf : IsHomeomorph f.base :=
    UniversalHomeomorphism.universally_isHomeomorph _ _ _ .of_id_snd
  refine ⟨⟨f.base '' (U : Set X), hf.isOpenMap _ U.2⟩, ?_, ?_⟩
  · exact TopologicalSpace.Opens.ext (Set.preimage_image_eq _ hf.injective)
  · rintro W rfl
    exact TopologicalSpace.Opens.ext (Set.image_preimage_eq _ hf.surjective).symm

/-- **Every open subscheme of `X` is the base change of a scheme étale over `Y`.** If `f` is a
universal homeomorphism, an open subscheme `U` of `X` is cut out by a unique open subscheme `W`
of `Y`, and `U` is the fibre product of `W` with `X` over `Y`.

This is the case of essential surjectivity in which the étale scheme over `X` is an open
immersion. -/
theorem exists_etale_pullback_iso_of_opens (f : X ⟶ Y) [UniversalHomeomorphism f] (U : X.Opens) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U.toScheme),
      e.hom ≫ U.ι = pullback.snd q f := by
  obtain ⟨W, rfl, -⟩ := exists_opens_preimage_eq_of_universalHomeomorphism f U
  refine ⟨W.toScheme, W.ι, inferInstance,
    ((isPullback_morphismRestrict f W).isoPullback).symm, ?_⟩
  exact (isPullback_morphismRestrict f W).isoPullback_inv_snd

/-- **Every open subscheme of a base change is again a base change.** Let `q : V ⟶ Y` be étale
and let `f : X ⟶ Y` be a universal homeomorphism. An open subscheme `U` of `V ×_Y X` is cut out
by a unique open subscheme `Z` of `V`, and `U` is the fibre product of `Z` with `X` over `Y`.

Hence the essential image of base change on small étale sites is closed under passage to open
subschemes. -/
theorem exists_etale_pullback_iso_of_opens_pullback (f : X ⟶ Y) [UniversalHomeomorphism f]
    {V : Scheme.{u}} (q : V ⟶ Y) [Etale q] (U : (pullback q f).Opens) :
    ∃ (V' : Scheme.{u}) (q' : V' ⟶ Y) (_ : Etale q')
      (e : pullback q' f ≅ U.toScheme),
      e.hom ≫ (U.ι ≫ pullback.snd q f) = pullback.snd q' f := by
  have hfst : UniversalHomeomorphism (pullback.fst q f) := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback q f).flip
      ((universalHomeomorphism_iff f).mp inferInstance)
  obtain ⟨Z, rfl, -⟩ := exists_opens_preimage_eq_of_universalHomeomorphism
    (pullback.fst q f) U
  have hsq : IsPullback (pullback.fst q f ∣_ Z)
      ((pullback.fst q f ⁻¹ᵁ Z).ι ≫ pullback.snd q f) (Z.ι ≫ q) f :=
    (isPullback_morphismRestrict (pullback.fst q f) Z).paste_vert
      (IsPullback.of_hasPullback q f)
  refine ⟨Z.toScheme, Z.ι ≫ q, inferInstance, hsq.isoPullback.symm, ?_⟩
  exact hsq.isoPullback_inv_snd

/-- **Morphisms into a scheme étale over `Y` descend along a universal homeomorphism, in
elementary form.** Let `f : X ⟶ Y` be a universal homeomorphism, let `q : V ⟶ Y` be arbitrary
and let `q' : V' ⟶ Y` be étale. A morphism of the base changes over `X` is the base change of a
unique `Y`-morphism `V ⟶ V'`.

This is Stacks Project, Tag 0BTY read off the two projections of the fibre products, so that it
can be used without over-category bookkeeping: the `Y`-morphism is characterised by its
composite with `q'` and by the first-projection square. -/
@[sga "1 IX 1.7" "more general",
  sga "1 IX 4.10" "full faithfulness",
  sga "3 X 2.0" "full faithfulness"]
theorem existsUnique_hom_of_pullback_hom (f : X ⟶ Y) [UniversalHomeomorphism f]
    {V V' : Scheme.{u}} (q : V ⟶ Y) (q' : V' ⟶ Y) [Etale q']
    (φ : pullback q f ⟶ pullback q' f)
    (hφ : φ ≫ pullback.snd q' f = pullback.snd q f) :
    ∃! ψ : V ⟶ V', ψ ≫ q' = q ∧
      pullback.fst q f ≫ ψ = φ ≫ pullback.fst q' f := by
  have hq' : Etale (Over.mk q').hom := ‹Etale q'›
  have hbij := bijective_baseChange_hom_of_universalHomeomorphism f
    (Over.mk q') (Over.mk q)
  have hcond : ∀ ψ : V ⟶ V', ψ ≫ q' = q →
      (pullback.fst q f ≫ ψ) ≫ q' = pullback.snd q f ≫ f := by
    intro ψ hψ
    rw [Category.assoc, hψ, pullback.condition]
  have hmapleft : ∀ (χ : Over.mk q ⟶ Over.mk q') (hχ : χ.left ≫ q' = q),
      ((Over.pullback f).map χ).left =
        pullback.lift (pullback.fst q f ≫ χ.left) (pullback.snd q f) (hcond _ hχ) := by
    intro χ _
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  obtain ⟨χ, hχ, huniq⟩ :=
    hbij.existsUnique (Over.homMk φ (by simpa using hφ))
  have hwχ : χ.left ≫ q' = q := Over.w χ
  have hχleft : pullback.lift (pullback.fst q f ≫ χ.left) (pullback.snd q f)
      (hcond _ hwχ) = φ := by
    rw [← hmapleft χ hwχ]
    exact congrArg Over.Hom.left hχ
  refine ⟨χ.left, ⟨hwχ, ?_⟩, ?_⟩
  · rw [← hχleft, pullback.lift_fst]
  · rintro ψ ⟨hψ1, hψ2⟩
    have hmk : (Over.homMk ψ hψ1 : Over.mk q ⟶ Over.mk q') = χ := by
      refine huniq _ ?_
      apply Over.OverMorphism.ext
      rw [hmapleft (Over.homMk ψ hψ1) hψ1]
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans hψ2
      · exact (pullback.lift_snd _ _ _).trans hφ.symm
    exact congrArg Over.Hom.left hmk

/-- **A descent along a universal homeomorphism is rigid.** Two schemes étale over `Y` whose base
changes along `f` are isomorphic over `X` are themselves isomorphic over `Y`, by an isomorphism
inducing the given one.

This is the rigidity which makes the cocycle condition automatic in a glueing argument for
essential surjectivity: the isomorphisms on overlaps are forced, so no compatibility has to be
checked by hand. -/
theorem exists_iso_of_pullback_iso (f : X ⟶ Y) [UniversalHomeomorphism f]
    {V V' : Scheme.{u}} (q : V ⟶ Y) (q' : V' ⟶ Y) [Etale q] [Etale q']
    (e : pullback q f ≅ pullback q' f)
    (he : e.hom ≫ pullback.snd q' f = pullback.snd q f) :
    ∃ d : V ≅ V', d.hom ≫ q' = q ∧
      pullback.fst q f ≫ d.hom = e.hom ≫ pullback.fst q' f := by
  have hinv : e.inv ≫ pullback.snd q f = pullback.snd q' f := e.inv_comp_eq.mpr he.symm
  obtain ⟨ψ, ⟨hψq, hψfst⟩, -⟩ := existsUnique_hom_of_pullback_hom f q q' e.hom he
  obtain ⟨ψ', ⟨hψ'q, hψ'fst⟩, -⟩ := existsUnique_hom_of_pullback_hom f q' q e.inv hinv
  have hid : ∀ {W : Scheme.{u}} (r : W ⟶ Y) (_ : Etale r) (g : W ⟶ W), g ≫ r = r →
      pullback.fst r f ≫ g = pullback.fst r f → g = 𝟙 W := by
    intro W r hr g hgr hgfst
    have : Etale r := hr
    obtain ⟨g₀, -, huniq⟩ :=
      existsUnique_hom_of_pullback_hom f r r (𝟙 (pullback r f)) (Category.id_comp _)
    rw [huniq g ⟨hgr, by rw [hgfst, Category.id_comp]⟩,
      huniq (𝟙 W) ⟨Category.id_comp r, by rw [Category.comp_id, Category.id_comp]⟩]
  refine ⟨⟨ψ, ψ', ?_, ?_⟩, hψq, hψfst⟩
  · refine hid q ‹Etale q› (ψ ≫ ψ') (by rw [Category.assoc, hψ'q, hψq]) ?_
    rw [← Category.assoc, hψfst, Category.assoc, hψ'fst, ← Category.assoc, e.hom_inv_id,
      Category.id_comp]
  · refine hid q' ‹Etale q'› (ψ' ≫ ψ) (by rw [Category.assoc, hψq, hψ'q]) ?_
    rw [← Category.assoc, hψ'fst, Category.assoc, hψfst, ← Category.assoc, e.inv_hom_id,
      Category.id_comp]

end Stacks.Etale

end

end
