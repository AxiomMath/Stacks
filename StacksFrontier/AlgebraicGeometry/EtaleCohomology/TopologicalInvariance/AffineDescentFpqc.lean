module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.ZariskiToEtale
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCoverInductiveStep

/-!
# The descent step of the affine case, over a genuine fpqc covering

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineInductiveStep` reduces
the affine case of the topological invariance of the small étale site to one descent statement,
`Stacks.Etale.EtaleDescentAlongAffineCover`: an étale `W`-scheme whose base change to
`W_X = W ×_Y X` is the base change of a scheme étale over `X` descends to `Y`. There the étale
morphism `w : W ⟶ Y` along which the descent takes place is *not* surjective, so `{W ⟶ Y}` is not
an fpqc covering of `Y` and effectivity of affine descent, Stacks Project, Tag 0245, does not
apply to it; the statement therefore carries the clause that `U` lie over the image of `W_X`,
which is what makes `{W ⟶ Y}` a covering of the open subscheme of `Y` over which the descent
actually takes place.

This file performs that localization. An étale morphism is open, so it factors as a surjective
étale morphism onto the open subscheme cut out by its image followed by the inclusion of that open
subscheme — `AlgebraicGeometry.exists_surjective_etale_onto_openImage`. The restriction of `f`
over that open subscheme is again a universal homeomorphism, the clause on the image of `W_X` is
exactly what lets `p` be read as a morphism into the preimage of that open subscheme, and the
fibre product `W ×_Y X` is unchanged by the localization. What is left is the same descent
statement with `w` surjective, hence a one-member fpqc covering; that is
`Stacks.Etale.EtaleDescentAlongFpqcAffineCover`, and no affineness of the base is left in it.

## Main definitions

* `Stacks.Etale.EtaleDescentAlongFpqcAffineCover` — the descent statement over a genuine fpqc
  covering: for a universal homeomorphism `f : X ⟶ Y` and a surjective, quasi-compact étale
  `w : W ⟶ Y`, a scheme `V` étale and affine over `W` whose base change to `W ×_Y X` is also the
  base change of a scheme `U` étale over `X` descends to a scheme étale over `Y` with base change
  `U`. The three fibre products are given as pullback squares rather than as the literal
  `CategoryTheory.Limits.pullback`, so that no transport between presentations of `W ×_Y X` is
  needed at the point of use.

## Main results

* `Stacks.Etale.etaleDescentAlongAffineCover_of_fpqc` — **the localization.**
  `Stacks.Etale.EtaleDescentAlongFpqcAffineCover` implies
  `Stacks.Etale.EtaleDescentAlongAffineCover`.
* `Stacks.Etale.essSurjAffineEtalePullback_of_etaleDescentAlongFpqcAffineCover` — consequently the
  affine case of Stacks Project, Tags 04DZ and 04E0 follows from the descent statement over a
  genuine fpqc covering alone.
* `Stacks.Etale.etalePullback_isEquivalence_of_etaleDescentAlongFpqcAffineCover` — and so does the
  whole equivalence of small étale sites.

## Implementation notes

The open subscheme is not named: `AlgebraicGeometry.exists_surjective_etale_onto_openImage`
produces it together with the surjective étale morphism onto it and the factorization, and the
only property of it used besides those is that it contains the image of `w`, which that lemma also
produces. Nothing here constructs an open out of `Set.range`.

The two morphisms into the preimage of the open subscheme — the one replacing `p` and the one
replacing the projection `W ×_Y X ⟶ X` — are obtained from
`AlgebraicGeometry.IsOpenImmersion.lift`, and each is exhibited as a base change of the morphism
it replaces by `CategoryTheory.IsPullback.of_horiz_isIso_mono`, the inclusion of an open subscheme
being a monomorphism. That is what transports étaleness and quasi-compactness across the
localization, and it is also why no affineness survives into
`Stacks.Etale.EtaleDescentAlongFpqcAffineCover`: the open subscheme of an affine scheme need not
be affine, and the descent step does not need it — effectivity of affine descent asks only that
the structure morphism of the descent datum be affine, which here is the morphism `V ⟶ W` between
two affine schemes.

`w` is quasi-compact because it is a morphism of affine schemes, hence affine; its corestriction
to the open image is quasi-compact because it is a base change of `w`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- **Descent of an étale scheme along a surjective affine étale covering.** Let `f : X ⟶ Y` be a
universal homeomorphism and let `w : W ⟶ Y` be étale, surjective and quasi-compact, so that
`{W ⟶ Y}` is a one-member fpqc covering of `Y`. Let `πW`, `πX` present a scheme `WX` as
`W ×_Y X`, let `p : U ⟶ X` be étale and let `v : V ⟶ W` be étale and affine. Suppose a scheme `T`
is simultaneously the base change of `V` along `πW` and the base change of `U` along `πX`, by
squares sharing their projection `τ : T ⟶ WX`. Then `U` is the base change along `f` of a scheme
étale over `Y`.

This is the last paragraph of the second proof of Stacks Project, Tag 04DZ, with the covering
`{W ⟶ Y}` surjective as effectivity of affine descent requires. There the identification over
`W ×_Y W` of the two base changes of `V` is produced by full faithfulness of base change along the
universal homeomorphism over `W ×_Y W` — in this library
`Stacks.Etale.bijective_baseChange_hom_of_universalHomeomorphism` — and is a descent datum for `V`
relative to `W/Y`, the cocycle condition following from the uniqueness of that identification over
`W ×_Y W ×_Y W`; the datum is effective by effectivity of affine descent, Stacks Project, Tag
0245, in this library `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom`; the descended
scheme is étale over `Y` because étaleness is fpqc local on the target, in this library
`AlgebraicGeometry.etale_isLocalAtTarget_fpqc`; and its base change is identified with `U` by
descent of morphisms along an fpqc covering, in this library
`AlgebraicGeometry.DescentData.canonicalFunctor_fullyFaithful_of_flat_surjective_quasiCompact`.

No affineness of `X`, `Y`, `U` or `W` occurs: the only affineness the source's argument uses is
that of the structure morphism `v` of the descent datum, which is what Tag 0245 asks for. -/
def EtaleDescentAlongFpqcAffineCover : Prop :=
  ∀ {X Y W WX U V T : Scheme.{u}} (f : X ⟶ Y) (w : W ⟶ Y) (πW : WX ⟶ W) (πX : WX ⟶ X)
      (p : U ⟶ X) (v : V ⟶ W) (α : T ⟶ V) (τ : T ⟶ WX) (β : T ⟶ U),
    UniversalHomeomorphism f → Etale w → Surjective w → QuasiCompact w → Etale p → Etale v →
      IsAffineHom v → IsPullback πW πX w f → IsPullback α τ v πW → IsPullback β τ p πX →
        ∃ (V₀ : Scheme.{u}) (q : V₀ ⟶ Y) (_ : Etale q) (δ : U ⟶ V₀), IsPullback δ p q f

/-- A property stable under base change passes to a factorization through a monomorphism. -/
private theorem prop_of_comp_mono_eq {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {A B C : Scheme.{u}} {g : A ⟶ C} {m : C ⟶ B} [Mono m] {k : A ⟶ B}
    (hk : g ≫ m = k) (h : P k) : P g :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp _).trans hk.symm⟩) h

/-- If the image of `w` lies in the open `O`, then `W ×_Y X` maps into the preimage of `O`. -/
theorem range_pullback_snd_subset_preimage {W X Y : Scheme.{u}} (w : W ⟶ Y) (f : X ⟶ Y)
    {O : Y.Opens} (hO : ∀ y : Y, y ∈ Set.range w.base → y ∈ O) :
    Set.range (pullback.snd w f).base ⊆ Set.range (f ⁻¹ᵁ O).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro x ⟨t, rfl⟩
  refine hO _ ⟨(pullback.fst w f).base t, ?_⟩
  simpa using congrArg (fun m : (pullback w f : Scheme.{u}) ⟶ Y ↦ m.base t)
    (pullback.condition (f := w) (g := f))

/-- If `w` factors through the open `O` as `w₀`, then `W ×_Y X` is the fibre product of `w₀`
with the restriction `f ∣_ O`. -/
theorem isPullback_lift_pullback_snd {W X Y : Scheme.{u}} (w : W ⟶ Y) (f : X ⟶ Y)
    {O : Y.Opens} {w₀ : W ⟶ O} (hw₀ : w₀ ≫ O.ι = w)
    (hX : Set.range (pullback.snd w f).base ⊆ Set.range (f ⁻¹ᵁ O).ι.base) :
    IsPullback (pullback.fst w f) (IsOpenImmersion.lift (f ⁻¹ᵁ O).ι (pullback.snd w f) hX) w₀
      (f ∣_ O) := by
  have hπι := IsOpenImmersion.lift_fac (f ⁻¹ᵁ O).ι (pullback.snd w f) hX
  refine IsPullback.of_bot ?_ ?_ (isPullback_morphismRestrict f O)
  · rw [hπι, hw₀]
    exact IsPullback.of_hasPullback w f
  · rw [← cancel_mono O.ι, Category.assoc, Category.assoc, hw₀, morphismRestrict_ι,
      ← Category.assoc, hπι]
    exact pullback.condition

/-- **The descent statement needs only a genuine fpqc covering.** The hypothesis
`Stacks.Etale.EtaleDescentAlongAffineCover` carried by
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineInductiveStep` follows
from `Stacks.Etale.EtaleDescentAlongFpqcAffineCover`.

The étale morphism `w : W ⟶ Y` is open, so it corestricts to a surjective étale morphism onto the
open subscheme `O` of `Y` cut out by its image. The restriction of `f` over `O` is again a
universal homeomorphism; the clause that `U` lie over the image of `W ×_Y X` says exactly that `p`
factors through the preimage of `O`, and so does the projection `W ×_Y X ⟶ X`, which exhibits
`W ×_Y X` as the fibre product of the corestricted `w` with the restricted `f`. The given
isomorphism of base changes becomes the pair of pullback squares the fpqc form asks for, and
pasting the descent square over `O` onto the restriction square of `f` returns a descent
over `Y`. -/
theorem etaleDescentAlongAffineCover_of_fpqc
    (h : EtaleDescentAlongFpqcAffineCover.{u}) : EtaleDescentAlongAffineCover.{u} := by
  intro X Y f _ _ _ W w _ _ U p hp _ hrange V'' v'' hv'' _ e he
  obtain ⟨O, w₀, hOmem, _, _, hw₀ι⟩ := exists_surjective_etale_onto_openImage w
  have _ : QuasiCompact w₀ := prop_of_comp_mono_eq (P := @QuasiCompact) hw₀ι inferInstance
  have _ : UniversalHomeomorphism (f ∣_ O) := universalHomeomorphism_morphismRestrict f O
  have hXsub := range_pullback_snd_subset_preimage w f hOmem
  have hpsub : Set.range p.base ⊆ Set.range (f ⁻¹ᵁ O).ι.base := hrange.trans hXsub
  have hp₀ι : IsOpenImmersion.lift (f ⁻¹ᵁ O).ι p hpsub ≫ (f ⁻¹ᵁ O).ι = p :=
    IsOpenImmersion.lift_fac _ _ _
  have _ : Etale (IsOpenImmersion.lift (f ⁻¹ᵁ O).ι p hpsub) :=
    prop_of_comp_mono_eq (P := @Etale) hp₀ι hp
  have hπι : IsOpenImmersion.lift (f ⁻¹ᵁ O).ι (pullback.snd w f) hXsub ≫ (f ⁻¹ᵁ O).ι =
      pullback.snd w f :=
    IsOpenImmersion.lift_fac _ _ _
  have hsqβ₀ : IsPullback (e.hom ≫ pullback.fst p (pullback.snd w f))
      (pullback.snd v'' (pullback.fst w f)) p (pullback.snd w f) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ e rfl he
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hsqβ : IsPullback (e.hom ≫ pullback.fst p (pullback.snd w f))
      (pullback.snd v'' (pullback.fst w f))
      (IsOpenImmersion.lift (f ⁻¹ᵁ O).ι p hpsub)
      (IsOpenImmersion.lift (f ⁻¹ᵁ O).ι (pullback.snd w f) hXsub) := by
    refine IsPullback.of_bot (v₂₁ := 𝟙 (pullback w f : Scheme.{u})) ?_ ?_
      (IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, hπι]⟩)
    · rw [Category.comp_id, hp₀ι]
      exact hsqβ₀
    · rw [← cancel_mono (f ⁻¹ᵁ O).ι]
      simp only [Category.assoc, hp₀ι, hπι]
      simpa only [Category.assoc] using hsqβ₀.w
  obtain ⟨V₀, q₀, _, δ, hsqδ⟩ := h (f ∣_ O) w₀ (pullback.fst w f)
    (IsOpenImmersion.lift (f ⁻¹ᵁ O).ι (pullback.snd w f) hXsub)
    (IsOpenImmersion.lift (f ⁻¹ᵁ O).ι p hpsub) v''
    (pullback.fst v'' (pullback.fst w f)) (pullback.snd v'' (pullback.fst w f))
    (e.hom ≫ pullback.fst p (pullback.snd w f)) inferInstance inferInstance inferInstance
    inferInstance inferInstance hv'' inferInstance (isPullback_lift_pullback_snd w f hw₀ι hXsub)
    (IsPullback.of_hasPullback _ _) hsqβ
  have hfin : IsPullback δ p (q₀ ≫ O.ι) f := by
    simpa only [hp₀ι] using hsqδ.paste_vert (isPullback_morphismRestrict f O)
  exact ⟨V₀, q₀ ≫ O.ι, inferInstance, hfin.isoPullback.symm, hfin.isoPullback_inv_snd⟩

/-- **The affine case of Stacks Project, Tag 04E0 follows from the fpqc descent statement
alone.** Granted `Stacks.Etale.EtaleDescentAlongFpqcAffineCover`, the hypothesis
`Stacks.Etale.EssSurjAffineEtalePullback` holds, and with it the essential surjectivity half of
Stacks Project, Tags 04DZ and 04E0. -/
theorem essSurjAffineEtalePullback_of_etaleDescentAlongFpqcAffineCover
    (h : EtaleDescentAlongFpqcAffineCover.{u}) : EssSurjAffineEtalePullback.{u} :=
  essSurjAffineEtalePullback_of_etaleDescentAlongAffineCover
    (etaleDescentAlongAffineCover_of_fpqc h)

/-- **Topological invariance of the small étale site from the fpqc descent statement.** Granted
`Stacks.Etale.EtaleDescentAlongFpqcAffineCover`, base change along an integral, universally
injective and surjective morphism of schemes is an equivalence from the schemes étale over the
target to the schemes étale over the source. -/
theorem etalePullback_isEquivalence_of_etaleDescentAlongFpqcAffineCover
    (h : EtaleDescentAlongFpqcAffineCover.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    [UniversallyInjective f] [Surjective f] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).IsEquivalence :=
  etalePullback_isEquivalence_of_etaleDescentAlongAffineCover
    (etaleDescentAlongAffineCover_of_fpqc h) f

end Stacks.Etale

end

end
