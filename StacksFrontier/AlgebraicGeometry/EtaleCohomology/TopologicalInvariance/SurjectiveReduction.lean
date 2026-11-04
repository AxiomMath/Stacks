module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyCAffineRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.OpenSubschemeRankBound
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# The affine case of topological invariance reduces to a surjective étale morphism

Let `f : X ⟶ Y` be a universal homeomorphism of affine schemes. The affine case of the
correspondence of Stacks Project, Tag 04E0 asserts that every affine scheme étale over `X`
descends along `f`, and the source proves it by induction on a bound `n` for the degrees of the
fibres. This file reduces the inductive statement
`Stacks.Etale.EssSurjAffineEtalePullbackBounded` to its special case in which the étale morphism
`p : U ⟶ X` is moreover **surjective**.

That reduction is what makes the source's inductive step applicable at all. The step dominates
`U` by the base change `W_X` of an étale `W ⟶ Y` (Stacks Project, Tag 04DW) and then descends an
étale `W`-scheme along `W ⟶ Y` by effectivity of affine descent, Stacks Project, Tag 0245. But
Tag 0245 needs `{W ⟶ Y}` to be an fpqc covering, hence `W ⟶ Y` surjective; and the step has a
morphism `W_X ⟶ U` over `X`, so a surjective `W ⟶ Y` forces `W_X ⟶ X` surjective and therefore
`p` surjective too. For a non-surjective `p` — take `U` empty, where `W` is necessarily empty —
the covering is not an fpqc covering and Tag 0245 does not apply. Conversely, once `p` is
surjective, `W_X ⟶ U ⟶ X` is surjective and `X ⟶ Y` is surjective, so `W_X ⟶ Y` is surjective
and it factors through `W`, which makes `W ⟶ Y` surjective. This is the place where the source
says "Some details omitted".

The reduction localizes on the target in the opposite order to
`Stacks.Etale.exists_etale_pullback_iso_of_essSurjAffine`: an affine open `A` of `U` around a
point is chosen *first*, and only then an affine open `Y₁` of `Y` **inside** the open set
`f (p (A))`, so that the piece of `U` lying over `f ⁻¹ᵁ Y₁` surjects onto it. Since `p` is étale
it is an open map, and the underlying map of a universal homeomorphism is a homeomorphism, so
`f (p (A))` is indeed open.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_isOpenImmersion_comp` — a bound on the degrees of the
  fibres of a morphism is also a bound for its restriction to an open subscheme of the source.
* `AlgebraicGeometry.boundsFiberDegrees_of_comp_mono` — a bound for a morphism composed with a
  monomorphism is a bound for the morphism itself.
* `Stacks.Etale.hasPropertyC_of_universalHomeomorphism` — Stacks Project, Tag 04DW for a
  universal homeomorphism, which the library carried only privately.
* `Stacks.Etale.essSurjAffineEtalePullbackBounded_of_surjective` — the bounded affine case
  follows from its restriction to surjective étale morphisms.
* `Stacks.Etale.essSurjAffineEtalePullback_of_inductiveStep_surjective` — consequently the
  affine case, and with it the essential surjectivity of the correspondence of Tag 04E0, follows
  from the source's inductive step *for a surjective étale morphism*. Nothing in this file
  registers the tag; the step is supplied in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective`, by
  `Stacks.Etale.exists_affine_etale_pullback_iso_of_surjective`.

## Implementation notes

The two fibre-degree lemmas belong with the rest of the theory, in
`StacksDraft.AlgebraicGeometry.Morphisms.FibreDimension`. They are placed here because the first
is proved through `AlgebraicGeometry.pullbackMapOfComp`, which currently lives in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyCAffineRefinement` and so sits
above the fibre-dimension files; moving that construction into a module below
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC` would let both lemmas move
down with it.

`AlgebraicGeometry.boundsFiberDegrees_isOpenImmersion_comp` needs no étaleness, unlike every
other bound on an open piece in this library — `boundsFiberDegrees_offDiagonal_fst`,
`boundsFiberDegrees_diagonalComplement` and `boundsFiberDegrees_offSection` all count points
through the cardinality criterion of Stacks Project, Tag 03WU, which is available only for an
étale morphism. Here the fibre of the restriction is an open subscheme of the fibre, and
`AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion` bounds the rank of an
open subscheme of a finite locally free scheme over a field directly.

The affine open `A'` of `U` over which the surjective case is invoked is the intersection
`A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)`, which cannot be shrunk without losing the surjectivity. Its affineness
is not an instance of "an open subscheme of an affine scheme is affine", which is false; it is
obtained by restricting to `A`, where `A.ι ≫ p` is a morphism of affine schemes and hence an
affine morphism, and pushing the resulting affine open of `A` forward along the open immersion
`A.ι`.

## References

* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 03J7](https://stacks.math.columbia.edu/tag/03J7)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Fibre-degree bounds along an open immersion of the source -/

/-- **A bound on the degrees of the fibres survives restriction to an open subscheme of the
source.** If `n` bounds the degrees of the fibres of `q : U ⟶ Z` and `j : V ⟶ U` is an open
immersion, then `n` bounds the degrees of the fibres of `j ≫ q`.

Over a field-valued point of `Z` the fibre of `j ≫ q` is an open subscheme of the fibre of `q`,
by `AlgebraicGeometry.isOpenImmersion_pullbackMapOfComp`, and an open subscheme of a finite
locally free scheme over a field is finite locally free of no larger rank, by
`AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion`. -/
theorem boundsFiberDegrees_isOpenImmersion_comp {V U Z : Scheme.{u}} (j : V ⟶ U)
    [IsOpenImmersion j] (q : U ⟶ Z) (n : ℤ) (h : BoundsFiberDegrees q n) :
    BoundsFiberDegrees (j ≫ q) n := by
  rw [boundsFiberDegrees_iff_field_baseChange] at h ⊢
  intro k _ g
  obtain ⟨r, hr, hrank⟩ := h k g
  have _hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g q) r := hrank
  obtain ⟨r', hr', hrank'⟩ :=
    exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion (pullback.fst g q)
      (pullbackMapOfComp (v := q) (v' := j ≫ q) g j rfl) r
  refine ⟨r', le_trans (by exact_mod_cast hr') hr, ?_⟩
  rwa [pullbackMapOfComp_fst] at hrank'

/-- **A bound on the degrees of the fibres of a morphism composed with a monomorphism is a bound
for the morphism itself.** Composing both legs of the trivial cartesian square on `g` with a
monomorphism `i` leaves it cartesian, so `g` is a base change of `g ≫ i` and Stacks Project,
Tag 03J7 applies. -/
theorem boundsFiberDegrees_of_comp_mono {A W Z : Scheme.{u}} (g : A ⟶ W) (i : W ⟶ Z) [Mono i]
    (n : ℤ) (h : BoundsFiberDegrees (g ≫ i) n) : BoundsFiberDegrees g n := by
  have hsq : IsPullback (𝟙 A) g (g ≫ i) i := by
    have h' : IsPullback (𝟙 A) g (g ≫ i) (𝟙 W ≫ i) :=
      isPullback_comp_mono (IsPullback.of_id_fst (f := g)) i
    rwa [Category.id_comp] at h'
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun {_ _ : Scheme.{u}} (t : _ ⟶ _) ↦ BoundsFiberDegrees t n) hsq h

end AlgebraicGeometry

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-! ### Property (C) for a universal homeomorphism -/

/-- **A universal homeomorphism has property (C).** Every scheme étale over `X` is dominated, by
a surjection of schemes over `X`, by the base change along `f` of a scheme étale over `Y`.

A universal homeomorphism is integral, universally injective and surjective, by Stacks Project,
Tag 04DF, so its underlying map is a continuous injective closed map and hence a closed
embedding; Stacks Project, Tag 04DW in the form
`Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding` applies. The same
derivation is carried out privately inside
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.IntegralUniversallyInjective`; this is the
public statement for a universal homeomorphism, which is what the source's induction needs in
order to feed `Stacks.EtaleCohomology.exists_isAffine_etale_surjective_of_hasPropertyC`. -/
theorem hasPropertyC_of_universalHomeomorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] : Stacks.EtaleCohomology.HasPropertyC f :=
  have hd := (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp
    inferInstance
  have : IsIntegralHom f := hd.1
  have : UniversallyInjective f := hd.2.1
  Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding f
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap f.continuous f.injective
      (Scheme.Hom.isClosedMap f))

/-! ### Reduction of the bounded affine case to a surjective étale morphism -/

/-- **The bounded affine case of Stacks Project, Tag 04E0 reduces to a surjective étale
morphism.** Suppose that for every universal homeomorphism `f : X ⟶ Y` of affine schemes, every
affine scheme étale and **surjective** over `X` whose fibre degrees are bounded by `n` is, over
`X`, the base change along `f` of an affine scheme étale over `Y`. Then
`Stacks.Etale.EssSurjAffineEtalePullbackBounded` holds at `n`, with no surjectivity assumption.

For a point `x` of `U` choose an affine open `A` of `U` containing it. Since `p` is étale it is
an open map, and the underlying map of `f` is a homeomorphism, so `f (p (A))` is open in `Y`;
choose an affine open `Y₁` of `Y` inside it containing `f (p (x))`. Then `f ⁻¹ᵁ Y₁` is affine
because `f` is an affine morphism, and `A' := A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)` is an affine open of `U`
containing `x` whose restriction `A' ⟶ f ⁻¹ᵁ Y₁` of `p` is étale, affine and surjective — the
last because `Y₁ ⊆ f (p (A))` and `f` is injective force `f ⁻¹ᵁ Y₁ ⊆ p (A)`. Its fibre degrees
are still bounded by `n`, by
`AlgebraicGeometry.boundsFiberDegrees_isOpenImmersion_comp` and
`AlgebraicGeometry.boundsFiberDegrees_of_comp_mono`. The hypothesis applied to the restriction
`f ∣_ Y₁` therefore descends `A'`, which makes `A'` a descended open subscheme of `U` by
`Stacks.Etale.mem_descendedOpens_of_resLE`; these cover `U`, so
`Stacks.Etale.exists_etale_pullback_iso_of_descendedOpens_cover` descends `U` itself, and
`Stacks.Etale.isAffine_of_isAffine_pullback` recovers the affineness of the descent. -/
theorem essSurjAffineEtalePullbackBounded_of_surjective (n : ℕ)
    (hsurj : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), UniversalHomeomorphism f → IsAffine X →
      IsAffine Y → ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p → IsAffine U → Surjective p →
        BoundsFiberDegrees p (n : ℤ) →
        ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e : pullback q f ≅ U),
          e.hom ≫ p = pullback.snd q f) :
    EssSurjAffineEtalePullbackBounded.{u} n := by
  intro X Y f hf hX hY U p hp hU hdeg
  -- the underlying map of a universal homeomorphism is a homeomorphism
  have hfhomeo : IsHomeomorph f.base := hf.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  -- a universal homeomorphism is an affine morphism
  obtain ⟨hintegral, -, -⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp hf
  have _hfaff : IsAffineHom f :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hintegral).2
  -- an étale morphism is an open map
  have hpopen : IsOpenMap (fun z ↦ p.base z) := by
    have hdec := Etale.iff_flat_and_formallyUnramified.mp hp
    have : Flat p := hdec.1
    have : LocallyOfFinitePresentation p := hdec.2.2
    have : UniversallyOpen p := universallyOpen_of_flat_of_locallyOfFinitePresentation p
    exact p.isOpenMap
  obtain ⟨V, q, hq, e, he⟩ :
      ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
        e.hom ≫ p = pullback.snd q f := by
    refine exists_etale_pullback_iso_of_descendedOpens_cover f p fun x ↦ ?_
    -- an affine open of `U` around `x`
    obtain ⟨A, hA, hxA, -⟩ := exists_isAffineOpen_mem_and_subset (X := U) (x := x)
      (U := ⊤) (TopologicalSpace.Opens.mem_top _)
    have _hAaff : IsAffine A.toScheme := hA
    -- its image in `Y` is open and contains the image of `x`
    have hopenfpA : IsOpen (f.base '' (p.base '' (A : Set U))) :=
      hfhomeo.isOpenMap _ (hpopen _ A.isOpen)
    -- an affine open of `Y` inside that image
    obtain ⟨Y₁, hY₁, hxY₁, hY₁le⟩ := exists_isAffineOpen_mem_and_subset (X := Y)
      (x := f.base (p.base x)) (U := ⟨_, hopenfpA⟩) ⟨p.base x, ⟨x, hxA, rfl⟩, rfl⟩
    have _hY₁aff : IsAffine Y₁.toScheme := hY₁
    have hfY₁ : IsAffineOpen (f ⁻¹ᵁ Y₁) := hY₁.preimage f
    have _hfY₁aff : IsAffine (f ⁻¹ᵁ Y₁).toScheme := hfY₁
    have _huhY₁ : UniversalHomeomorphism (f ∣_ Y₁) :=
      universalHomeomorphism_morphismRestrict f Y₁
    -- the affine open of `U` over which the surjective case is invoked
    have hA'le : A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁) ≤ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁) := inf_le_right
    have hA'eq : A.ι ''ᵁ ((A.ι ≫ p) ⁻¹ᵁ (f ⁻¹ᵁ Y₁)) = A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁) := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι]
    have hA'aff : IsAffineOpen (A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)) :=
      hA'eq ▸ (hfY₁.preimage (A.ι ≫ p)).image_of_isOpenImmersion A.ι
    have _hA'aff : IsAffine (A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)).toScheme := hA'aff
    -- the restriction of `p` to it is surjective onto `f ⁻¹ᵁ Y₁`
    have hsurjres : Surjective (p.resLE (f ⁻¹ᵁ Y₁) (A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)) hA'le) := by
      refine ⟨fun y ↦ ?_⟩
      obtain ⟨z, ⟨a, haA, haz⟩, hzy⟩ := hY₁le y.2
      have hpa : p.base a = y.1 := hfhomeo.injective (by rw [haz]; exact hzy)
      have hmem : a ∈ A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁) :=
        ⟨haA, show f.base (p.base a) ∈ Y₁ by rw [haz, hzy]; exact y.2⟩
      exact ⟨⟨a, hmem⟩, Subtype.ext (by rw [Scheme.Hom.coe_resLE_apply]; exact hpa)⟩
    -- and still has its fibre degrees bounded by `n`
    have hdegres :
        BoundsFiberDegrees (p.resLE (f ⁻¹ᵁ Y₁) (A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)) hA'le) (n : ℤ) := by
      refine boundsFiberDegrees_of_comp_mono _ (f ⁻¹ᵁ Y₁).ι (n : ℤ) ?_
      rw [Scheme.Hom.resLE_comp_ι]
      exact boundsFiberDegrees_isOpenImmersion_comp (A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)).ι p (n : ℤ) hdeg
    obtain ⟨V, q, hq, -, e, he⟩ := hsurj (f ∣_ Y₁) inferInstance inferInstance inferInstance
      (A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)).toScheme (p.resLE (f ⁻¹ᵁ Y₁) (A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)) hA'le)
      inferInstance hA'aff hsurjres hdegres
    exact ⟨A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁),
      mem_descendedOpens_of_resLE f p Y₁ (A ⊓ p ⁻¹ᵁ (f ⁻¹ᵁ Y₁)) hA'le q hq e he, ⟨hxA, hxY₁⟩⟩
  exact ⟨V, q, hq, isAffine_of_isAffine_pullback f q (IsAffine.of_isIso e.hom), e, he⟩

/-- **What remains of the essential surjectivity of Stacks Project, Tag 04E0.** The affine case
holds as soon as the source's inductive step is available *for a surjective étale morphism*:
granted that the affine case for a bound of `n ≥ 1` on the fibre degrees implies the affine case
for a bound of `n + 1` whenever the étale morphism is in addition surjective,
`Stacks.Etale.EssSurjAffineEtalePullback` holds, and with it the essential surjectivity of the
correspondence displayed as Tag 04E0.

This is `Stacks.Etale.essSurjAffineEtalePullback_of_inductiveStep` with the surjectivity
assumption added for free by
`Stacks.Etale.essSurjAffineEtalePullbackBounded_of_surjective`. It is the form in which the
source's step is actually provable: the step descends along an étale `W ⟶ Y` dominating `U` by
Stacks Project, Tag 04DW, and effectivity of affine descent (Stacks Project, Tag 0245) requires
`W ⟶ Y` to be surjective, which holds exactly when `p` is. -/
theorem essSurjAffineEtalePullback_of_inductiveStep_surjective
    (hstep : ∀ n : ℕ, 1 ≤ n → EssSurjAffineEtalePullbackBounded.{u} n →
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), UniversalHomeomorphism f → IsAffine X → IsAffine Y →
        ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p → IsAffine U → Surjective p →
          BoundsFiberDegrees p ((n + 1 : ℕ) : ℤ) →
          ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e : pullback q f ≅ U),
            e.hom ≫ p = pullback.snd q f) :
    EssSurjAffineEtalePullback.{u} :=
  essSurjAffineEtalePullback_of_inductiveStep fun n hn ih ↦
    essSurjAffineEtalePullbackBounded_of_surjective (n + 1) (hstep n hn ih)

end Stacks.Etale

end

end
