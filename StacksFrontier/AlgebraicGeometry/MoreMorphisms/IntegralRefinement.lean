module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic

/-!
# Integral refinements of étale coverings: the Zariski-local factorisation property

[Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) refines a surjective étale
morphism `p : U ⟶ X` over a quasi-compact and quasi-separated base by a *finite* surjective
`f : Y ⟶ X` which factors through `p` Zariski-locally on `Y`. This file proves the existence of
such a refinement with `f` integral, for an arbitrary surjective étale `p`, and isolates the
Zariski-local factorisation property itself as a predicate so that it can be transported along
refinements.

The argument is the source's, run as an induction on a bound for the degrees of the fibres. The
inductive statement, `Stacks.MoreMorphisms.exists_isIntegralHom_factorsNear_of_boundsFiberDegrees`,
drops the surjectivity of the covering and asks instead that the refinement cover the *image* of
the covering and factor through it near every point lying over that image. This is what makes the
induction self-contained: the covering produced in the inductive step — the complement of the
graph inside the base change of the covering to the relative normalisation — is surjective only
over the image of the previous one, and nothing else needs to be said about the points outside.
With that formulation the source's scheme-theoretic closure of `Z` inside `Z'` is not needed, and
the only closed subscheme that enters is the reduced induced one on the complement of the image
of the new covering.

The tag's closing sentence, that the refinement may be taken finite and of finite presentation, is
`Stacks.MoreMorphisms.exists_isFinite_finitePresentation_surjective_zariskiLocallyFactors`. Its
proof presents the integral refinement produced here as a limit of morphisms finite and of finite
presentation ([Stacks, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ), available over a
quasi-compact and quasi-separated base as
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`) and descends the
covering and the factorisations to a single stage.

The first paragraph of the source argument replaces `U` by a finite disjoint union of affine
opens of `U`, which is affine, and observes that a morphism out of an affine scheme is
separated. `Stacks.MoreMorphisms.exists_isAffine_etale_surjective` carries out the replacement
and `Stacks.MoreMorphisms.exists_of_isAffine_source` records the resulting reduction: it is
enough to produce a refinement when the source is affine.

The second paragraph invokes [Stacks, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR), the
factorisation of a quasi-finite separated morphism through its relative normalisation. Mathlib
proves exactly this: `AlgebraicGeometry.Scheme.Hom.toNormalization` is an open immersion for a
quasi-compact separated locally quasi-finite morphism of finite type, and
`AlgebraicGeometry.Scheme.Hom.fromNormalization` is integral. The one hypothesis that does not
discharge itself for an étale morphism is local quasi-finiteness, which is
`AlgebraicGeometry.locallyQuasiFinite_of_etale`.

## Main definitions

* `Stacks.MoreMorphisms.ZariskiLocallyFactors` — `f : Y ⟶ X` factors through `p : U ⟶ X`
  Zariski-locally on `Y`: every point of `Y` has an open neighbourhood `V` such that
  `V ⟶ X` factors through `p`.
* `Stacks.MoreMorphisms.FactorsNear` — the same condition at a single point of `Y`.
* `Stacks.MoreMorphisms.graphComparison` — the comparison morphism `U ×_X U ⟶ U ×_X T` induced by
  `j : U ⟶ T` on the second factor, which identifies the graph of `j` with the diagonal.

## Main results

* `Stacks.MoreMorphisms.exists_isIntegralHom_surjective_zariskiLocallyFactors` — the existence
  statement of [Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) for an arbitrary
  surjective étale covering of a quasi-compact and quasi-separated scheme: it is refined by a
  surjective *integral* morphism which factors through it Zariski-locally. The refinement is
  taken finite and of finite presentation, which is the tag's closing sentence, in
  `Stacks.MoreMorphisms.exists_isFinite_finitePresentation_surjective_zariskiLocallyFactors`.
* `Stacks.MoreMorphisms.exists_isIntegralHom_factorsNear_of_boundsFiberDegrees` — the statement
  proved by induction on a bound for the degrees of the fibres, from which the previous one
  follows.
* `Stacks.MoreMorphisms.boundsFiberDegrees_openImmersionGraphCompl` — the degree drop: the
  complement of the graph has fibre degrees one smaller than the covering. Over the dense open
  `j(U)` this is the degree drop along the diagonal complement, and lower semicontinuity of the
  fibre degree spreads it to the whole of `T`.
* `Stacks.MoreMorphisms.isPullback_graphComparison` and
  `Stacks.MoreMorphisms.preimage_openImmersionGraphCompl` — `U ×_X U` is the base change of
  `U ×_X T` along `j`, and under that identification the complement of the graph becomes the
  complement of the diagonal.
* `Stacks.MoreMorphisms.exists_isOpenImmersion_isIntegralHom` — the factorisation of
  [Stacks, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR) through the relative
  normalisation, assembled from Mathlib.
* `Stacks.MoreMorphisms.exists_isAffine_etale_surjective` — a surjective étale morphism onto a
  quasi-compact scheme is refined by one with affine source.
* `Stacks.MoreMorphisms.exists_of_isAffine_source` — the reduction of the existence of an
  integral refinement with the Zariski-local factorisation property to the case of an affine
  source.
* `Stacks.MoreMorphisms.exists_isIntegralHom_surjective_zariskiLocallyFactors_of_isFinite` — the
  conclusion of [Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) when `p` is
  already finite, where the refinement may be taken to be `p` itself.
* `Stacks.MoreMorphisms.exists_isIntegralHom_surjective_zariskiLocallyFactors_of_constant_fiberRank`
  — [Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) for a covering all of whose
  fibres have one and the same degree: such a covering is finite locally free of that degree.
* `Stacks.MoreMorphisms.ZariskiLocallyFactors.comp_of_eq_comp` — the Zariski-local factorisation
  property composes through an intermediate base.
* `Stacks.MoreMorphisms.isAffine_openImmersionGraphCompl` — the complement of the graph is
  affine, and `Stacks.MoreMorphisms.openImmersionGraphCompl_ι_snd_comp` factors it through `U`.
* `Stacks.MoreMorphisms.isClopen_range_openImmersionGraph` and
  `Stacks.MoreMorphisms.mem_range_openImmersionGraphCompl_ι_snd_of_notMem_range` — the splitting
  of the base change `U ×_X T` into the graph of `j` and an open and closed complement whose
  image in `T` is an open set containing everything outside `j(U)`.

## References

* [Stacks Project, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
* [Stacks Project, Tag 07RY](https://stacks.math.columbia.edu/tag/07RY)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.MoreMorphisms

variable {U X : Scheme.{u}}

/-! ### The factorisation of Tag 02LR -/

/-- **Stacks Project, Tag 02LR.** A quasi-compact separated morphism locally of finite type and
locally quasi-finite factors as a quasi-compact open immersion followed by an integral morphism.
The factorisation is through the relative normalisation of `X` in `U`. -/
public theorem exists_isOpenImmersion_isIntegralHom (f : U ⟶ X) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f] :
    ∃ (T : Scheme.{u}) (j : U ⟶ T) (ν : T ⟶ X),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsIntegralHom ν ∧ j ≫ ν = f :=
  ⟨f.normalization, f.toNormalization, f.fromNormalization, inferInstance, inferInstance,
    inferInstance, f.toNormalization_fromNormalization⟩

/-- The factorisation of [Stacks, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR) for an
étale morphism with affine source onto a quasi-separated scheme: all four hypotheses of
`Stacks.MoreMorphisms.exists_isOpenImmersion_isIntegralHom` hold automatically there. -/
public theorem exists_isOpenImmersion_isIntegralHom_of_isAffine (f : U ⟶ X) [Etale f]
    [IsAffine U] [QuasiSeparatedSpace X] :
    ∃ (T : Scheme.{u}) (j : U ⟶ T) (ν : T ⟶ X),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsIntegralHom ν ∧ j ≫ ν = f :=
  have : LocallyQuasiFinite f := (AlgebraicGeometry.locallyQuasiFinite_of_etale f).2
  exists_isOpenImmersion_isIntegralHom f

/-- The factorisation of [Stacks, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR) for an
étale morphism with affine source, with the density of the open immersion: the morphism into the
relative normalisation is dominant, so the image of `U` is a dense open of the normalisation. -/
public theorem exists_isOpenImmersion_isIntegralHom_denseRange (f : U ⟶ X) [Etale f]
    [IsAffine U] [QuasiSeparatedSpace X] :
    ∃ (T : Scheme.{u}) (j : U ⟶ T) (ν : T ⟶ X),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsIntegralHom ν ∧ DenseRange j.base ∧ j ≫ ν = f :=
  have : LocallyQuasiFinite f := (AlgebraicGeometry.locallyQuasiFinite_of_etale f).2
  ⟨f.normalization, f.toNormalization, f.fromNormalization, inferInstance, inferInstance,
    inferInstance, f.toNormalization.denseRange, f.toNormalization_fromNormalization⟩

/-! ### Refining an étale covering so that its source is affine -/

/-- **The first reduction of Stacks, Tag 09Z0.** A surjective étale morphism onto a quasi-compact
scheme is refined by one with *affine* source: finitely many of the affine opens of `U` already
have images covering `X`, and a finite coproduct of affine schemes is affine. -/
public theorem exists_isAffine_etale_surjective (p : U ⟶ X) [Etale p] [Surjective p]
    [CompactSpace X] :
    ∃ (U' : Scheme.{u}) (q : U' ⟶ U), IsAffine U' ∧ Etale q ∧ Surjective (q ≫ p) := by
  classical
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have hp : IsOpenMap p.base := p.isOpenMap
  have hopen : ∀ i : U.affineCover.I₀, IsOpen (Set.range (U.affineCover.f i ≫ p).base) := by
    intro i
    have he : Set.range (U.affineCover.f i ≫ p).base
        = p.base '' Set.range (U.affineCover.f i).base := by
      rw [← Set.range_comp]
      rfl
    rw [he]
    exact hp _ (U.affineCover.f i).isOpenEmbedding.isOpen_range
  have hcov : (Set.univ : Set X) ⊆ ⋃ i : U.affineCover.I₀,
      Set.range (U.affineCover.f i ≫ p).base := by
    intro y _
    obtain ⟨u, rfl⟩ := (Surjective.surj (f := p)) y
    refine Set.mem_iUnion.mpr ⟨U.affineCover.idx u, ?_⟩
    obtain ⟨v, hv⟩ := U.affineCover.covers u
    exact ⟨v, by rw [Scheme.Hom.comp_apply, hv]⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : U.affineCover.I₀ => Set.range (U.affineCover.f i ≫ p).base) hopen hcov
  refine ⟨∐ (fun i : (t : Set U.affineCover.I₀) => U.affineCover.X i.1),
    Sigma.desc (fun i : (t : Set U.affineCover.I₀) => U.affineCover.f i.1),
    inferInstance, IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance), ?_⟩
  constructor
  intro y
  have hy := ht (Set.mem_univ y)
  simp only [Set.mem_iUnion, exists_prop] at hy
  obtain ⟨i, hi, v, hv⟩ := hy
  refine ⟨Sigma.ι (fun i : (t : Set U.affineCover.I₀) => U.affineCover.X i.1) ⟨i, hi⟩ v, ?_⟩
  have hcomp : Sigma.ι (fun i : (t : Set U.affineCover.I₀) => U.affineCover.X i.1) ⟨i, hi⟩ ≫
      (Sigma.desc (fun i : (t : Set U.affineCover.I₀) => U.affineCover.f i.1) ≫ p)
      = U.affineCover.f i ≫ p := by
    rw [← Category.assoc, Sigma.ι_comp_desc]
  rw [← Scheme.Hom.comp_apply, hcomp]
  exact hv

/-! ### Zariski-local factorisation -/

/-- `f : Y ⟶ X` **factors through** `p : U ⟶ X` **Zariski-locally** if every point of `Y` has an
open neighbourhood `V` such that the composite `V ⟶ Y ⟶ X` factors through `p`. This is the last
conjunct of the conclusion of
[Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0). -/
public def ZariskiLocallyFactors {Y : Scheme.{u}} (f : Y ⟶ X) (p : U ⟶ X) : Prop :=
  ∀ y : Y, ∃ (V : Y.Opens) (_ : y ∈ V) (g : V.toScheme ⟶ U), V.ι ≫ f = g ≫ p

/-- A morphism that factors through `p` globally factors through it Zariski-locally. -/
public theorem zariskiLocallyFactors_of_eq_comp {Y : Scheme.{u}} (f : Y ⟶ X) (p : U ⟶ X)
    (g : Y ⟶ U) (h : f = g ≫ p) : ZariskiLocallyFactors f p :=
  fun y => ⟨⊤, trivial, (⊤ : Y.Opens).ι ≫ g, by rw [h, Category.assoc]⟩

/-- Zariski-local factorisation is inherited along a refinement of the covering: if `f` factors
Zariski-locally through `q ≫ p` then it factors Zariski-locally through `p`. -/
public theorem ZariskiLocallyFactors.of_comp {Y U' : Scheme.{u}} {f : Y ⟶ X} {p : U ⟶ X}
    (q : U' ⟶ U) (h : ZariskiLocallyFactors f (q ≫ p)) : ZariskiLocallyFactors f p := by
  intro y
  obtain ⟨V, hy, g, hg⟩ := h y
  exact ⟨V, hy, g ≫ q, by rw [hg, Category.assoc]⟩

/-- Zariski-local factorisation composes through an intermediate base: if `g : Y ⟶ T` factors
Zariski-locally through `Φ : P ⟶ T` and the composite `Φ ≫ τ : P ⟶ X` factors through `p`, then
`g ≫ τ` factors Zariski-locally through `p`.

This is the step by which the induction of
[Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) transports a refinement found over
the relative normalisation `T` back to the original base `X`. -/
public theorem ZariskiLocallyFactors.comp_of_eq_comp {T Y P : Scheme.{u}} {g : Y ⟶ T}
    {Φ : P ⟶ T} (τ : T ⟶ X) {p : U ⟶ X} (φ : P ⟶ U) (hφ : Φ ≫ τ = φ ≫ p)
    (h : ZariskiLocallyFactors g Φ) : ZariskiLocallyFactors (g ≫ τ) p := by
  intro y
  obtain ⟨V, hy, ψ, hψ⟩ := h y
  refine ⟨V, hy, ψ ≫ φ, ?_⟩
  rw [← Category.assoc, hψ, Category.assoc, hφ, Category.assoc]

/-- **Zariski-local factorisation out of sections over opens of an intermediate base.** If the
image of every point of `Y` lies in an open subscheme of `T` over which `τ : T ⟶ X` factors
through `p`, then `g ≫ τ` factors through `p` Zariski-locally: the preimage of that open is the
required neighbourhood, and the restriction of `g` to it composes with the section.

In the induction of [Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) the open in
question is the image of the open immersion of `U` into its relative normalisation, over which
the covering has a section; this is what makes the points that an integral refinement adds over
the boundary harmless. -/
public theorem zariskiLocallyFactors_of_forall_exists_section {T Y : Scheme.{u}} (g : Y ⟶ T)
    (τ : T ⟶ X) (p : U ⟶ X)
    (H : ∀ y : Y, ∃ (O : T.Opens) (_ : g.base y ∈ O) (σ : O.toScheme ⟶ U),
      O.ι ≫ τ = σ ≫ p) :
    ZariskiLocallyFactors (g ≫ τ) p := by
  intro y
  obtain ⟨O, hy, σ, hσ⟩ := H y
  refine ⟨g ⁻¹ᵁ O, hy, (g ∣_ O) ≫ σ, ?_⟩
  rw [Category.assoc, ← hσ, morphismRestrict_ι_assoc]

/-- An open immersion has a section over its image: the covering `j ≫ ν` restricted to the open
image of `j` factors through `j` itself. -/
public theorem opensRange_ι_comp_eq_isoOpensRange_inv_comp {T : Scheme.{u}} (j : U ⟶ T)
    (ν : T ⟶ X) [IsOpenImmersion j] :
    j.opensRange.ι ≫ ν = j.isoOpensRange.inv ≫ (j ≫ ν) := by
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]

/-- **The reduction of Stacks, Tag 09Z0 to its affine case.** Let `P` be any property of
morphisms of schemes. If, for every refinement `q` of the surjective étale covering `p` with
affine source, some `f` with property `P` factors Zariski-locally through `q ≫ p`, then some `f`
with property `P` factors Zariski-locally through `p` itself.

Instantiating `P` at `fun f => IsIntegralHom f ∧ Surjective f ∧ IsFinite f ∧ …` turns this into
the statement that it suffices to prove [Stacks, Tag 09Z0] for an affine source, which is the
content of the first paragraph of the source proof. -/
public theorem exists_of_isAffine_source (p : U ⟶ X) [Etale p] [Surjective p] [CompactSpace X]
    (P : MorphismProperty Scheme.{u})
    (H : ∀ (U' : Scheme.{u}) (q : U' ⟶ U), IsAffine U' → Etale (q ≫ p) → Surjective (q ≫ p) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), P f ∧ ZariskiLocallyFactors f (q ≫ p)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), P f ∧ ZariskiLocallyFactors f p := by
  obtain ⟨U', q, hU', hq, hqp⟩ := exists_isAffine_etale_surjective p
  have : Etale q := hq
  obtain ⟨Y, f, hf, hloc⟩ := H U' q hU' inferInstance hqp
  exact ⟨Y, f, hf, hloc.of_comp q⟩

/-- **Stacks, Tag 09Z0 when the covering is already finite.** A finite surjective étale `p` is
its own integral refinement: it factors through itself Zariski-locally, trivially and globally. -/
public theorem exists_isIntegralHom_surjective_zariskiLocallyFactors_of_isFinite
    (p : U ⟶ X) [Etale p] [Surjective p] [IsFinite p] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsIntegralHom f ∧ Surjective f ∧ IsFinite f ∧
      LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
      ZariskiLocallyFactors f p :=
  ⟨U, p, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, zariskiLocallyFactors_of_eq_comp p p (𝟙 U) (Category.id_comp p).symm⟩

/-- **Stacks, Tag 09Z0 for a covering whose fibres all have one and the same degree.** A
separated surjective étale morphism all of whose fibres have degree `r` is finite locally free of
degree `r`, hence finite, and is therefore its own integral refinement: it is finite, of finite
presentation, surjective, and factors through itself.

The degrees of the fibres of an étale covering are constant on each stratum of the degree
stratification of the base, but not globally; the general case of Tag 09Z0 is proved by induction
on a bound for them, and is
`Stacks.MoreMorphisms.exists_isIntegralHom_surjective_zariskiLocallyFactors`. -/
public theorem exists_isIntegralHom_surjective_zariskiLocallyFactors_of_constant_fiberRank
    (p : U ⟶ X) [Etale p] [Surjective p] [IsSeparated p] (r : ℕ)
    (hr : ∀ x : X, Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (p.fiberToSpecResidueField x) r) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsIntegralHom f ∧ Surjective f ∧ IsFinite f ∧
      LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
      ZariskiLocallyFactors f p :=
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r := rank_of_constant_fiber_rank p r hr
  have : Stacks.Morphisms.IsFiniteLocallyFree p :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p r
  have : IsFinite p := Stacks.Morphisms.IsFiniteLocallyFree.isFinite p
  exists_isIntegralHom_surjective_zariskiLocallyFactors_of_isFinite p

/-! ### The complementary summand of the graph

The third paragraph of the source argument considers the base change `U ×_X T` of the étale
covering `p = j ≫ ν` along the integral morphism `ν : T ⟶ X` through which it was factored, and
splits it as the graph of `j` together with an open and closed complement `W`. This section
builds that complement and records the two properties the induction uses: `W ⟶ T` is étale, and
its image contains everything outside `j(U)`. -/

section Graph

variable {T : Scheme.{u}} (j : U ⟶ T) (ν : T ⟶ X)

/-- The graph `U ⟶ U ×_X T` of an open immersion `j : U ⟶ T` over a morphism `ν : T ⟶ X`, where
`U ⟶ X` is the composite `j ≫ ν`. -/
public def openImmersionGraph : U ⟶ pullback (j ≫ ν) ν :=
  pullback.lift (𝟙 _) j (Category.id_comp (j ≫ ν))

/-- The graph of `j` followed by the first projection is the identity of `U`. -/
@[simp]
public theorem openImmersionGraph_fst :
    openImmersionGraph j ν ≫ pullback.fst (j ≫ ν) ν = 𝟙 U :=
  pullback.lift_fst _ _ _

/-- The graph of `j` followed by the second projection is `j`. -/
@[simp]
public theorem openImmersionGraph_snd :
    openImmersionGraph j ν ≫ pullback.snd (j ≫ ν) ν = j :=
  pullback.lift_snd _ _ _

/-- The graph of `j` is a closed immersion, because `ν` is integral and hence separated. This is
[Stacks, Tag 01KS](https://stacks.math.columbia.edu/tag/01KS) in the case at hand. -/
public theorem isClosedImmersion_openImmersionGraph [IsIntegralHom ν] :
    IsClosedImmersion (openImmersionGraph j ν) := by
  unfold openImmersionGraph
  infer_instance

/-- The graph of `j` is étale, because it is a morphism between schemes étale over `T`: the
composite with `U ×_X T ⟶ T` is `j`, and `U ×_X T ⟶ T` is the base change of the étale
morphism `j ≫ ν`. -/
public theorem etale_openImmersionGraph [IsOpenImmersion j] [Etale (j ≫ ν)] :
    Etale (openImmersionGraph j ν) :=
  have h : Etale (openImmersionGraph j ν ≫ pullback.snd (j ≫ ν) ν) := by
    rw [openImmersionGraph_snd]; infer_instance
  MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ _ inferInstance h

/-- The range of the graph of `j` is open and closed: it is closed because the graph is a closed
immersion, and open because the graph is étale. -/
public theorem isClopen_range_openImmersionGraph [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] : IsClopen (Set.range (openImmersionGraph j ν).base) :=
  have : IsClosedImmersion (openImmersionGraph j ν) := isClosedImmersion_openImmersionGraph j ν
  have : Etale (openImmersionGraph j ν) := etale_openImmersionGraph j ν
  ⟨(IsClosedImmersion.isClosedEmbedding (f := openImmersionGraph j ν)).isClosed_range,
    (openImmersionGraph j ν).isOpenMap.isOpen_range⟩

/-- The open complement `W` of the graph of `j` inside `U ×_X T`. -/
public def openImmersionGraphCompl [IsOpenImmersion j] [IsIntegralHom ν] [Etale (j ≫ ν)] :
    (pullback (j ≫ ν) ν).Opens :=
  ⟨(Set.range (openImmersionGraph j ν).base)ᶜ,
    (isClopen_range_openImmersionGraph j ν).isClosed.isOpen_compl⟩

/-- The underlying set of the complement of the graph is the complement of the range of the
graph. -/
@[simp]
public theorem coe_openImmersionGraphCompl [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] :
    (openImmersionGraphCompl j ν : Set ↥(pullback (j ≫ ν) ν))
      = (Set.range (openImmersionGraph j ν).base)ᶜ :=
  rfl

/-- The image of the complement of the graph is open in `T`, because `W ⟶ T` is étale. -/
public theorem isOpen_range_openImmersionGraphCompl_ι_snd [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] :
    IsOpen (Set.range ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν).base) :=
  have : Etale ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) := inferInstance
  ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν).isOpenMap.isOpen_range

/-- A point of `U ×_X T` lying over a point of `T` outside `j(U)` is off the graph of `j`, so that
point of `T` is in the image of the complement `W`. -/
private theorem mem_range_openImmersionGraphCompl_ι_snd_of_snd_eq [IsOpenImmersion j]
    [IsIntegralHom ν] [Etale (j ≫ ν)] {t : T} (ht : t ∉ Set.range j.base)
    (z : ↥(pullback (j ≫ ν) ν)) (hz : (pullback.snd (j ≫ ν) ν).base z = t) :
    t ∈ Set.range ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν).base := by
  have hzW : z ∈ (openImmersionGraphCompl j ν : Set ↥(pullback (j ≫ ν) ν)) := by
    rw [coe_openImmersionGraphCompl]
    rintro ⟨u, rfl⟩
    refine ht ⟨u, ?_⟩
    rw [← hz, ← Scheme.Hom.comp_apply, openImmersionGraph_snd]
  obtain ⟨w, hw⟩ : z ∈ Set.range (openImmersionGraphCompl j ν).ι.base := by
    rwa [Scheme.Opens.range_ι]
  exact ⟨w, by rw [Scheme.Hom.comp_apply, hw, hz]⟩

/-- **The image of the complement of the graph covers everything outside `j(U)`.** A point of `T`
not in the range of `j` is hit by the complement `W`: it is hit by `U ×_X T ⟶ T`, since `j ≫ ν`
is surjective, and a preimage lying on the graph would force the point into `j(U)`. -/
public theorem mem_range_openImmersionGraphCompl_ι_snd_of_notMem_range
    [IsOpenImmersion j] [IsIntegralHom ν] [Etale (j ≫ ν)] [Surjective (j ≫ ν)]
    (t : T) (ht : t ∉ Set.range j.base) :
    t ∈ Set.range ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν).base := by
  obtain ⟨z, hz⟩ := (Surjective.surj (f := pullback.snd (j ≫ ν) ν)) t
  exact mem_range_openImmersionGraphCompl_ι_snd_of_snd_eq j ν ht z hz

/-- The inclusion of the complement of the graph is a closed immersion, its range being closed. -/
private theorem isClosedImmersion_openImmersionGraphCompl_ι [IsOpenImmersion j]
    [IsIntegralHom ν] [Etale (j ≫ ν)] : IsClosedImmersion (openImmersionGraphCompl j ν).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, coe_openImmersionGraphCompl]
    exact (isClopen_range_openImmersionGraph j ν).isOpen.isClosed_compl)

/-- The complement of the graph is affine: it is an open subscheme of the affine scheme
`U ×_X T` whose underlying set is closed, hence a closed subscheme of an affine scheme. -/
public theorem isAffine_openImmersionGraphCompl [IsOpenImmersion j] [IsAffine U]
    [IsIntegralHom ν] [Etale (j ≫ ν)] :
    IsAffine (openImmersionGraphCompl j ν).toScheme :=
  have : IsAffine (pullback (j ≫ ν) ν) := inferInstance
  have := isClosedImmersion_openImmersionGraphCompl_ι j ν
  isAffine_of_isAffineHom (openImmersionGraphCompl j ν).ι

/-- **The complement of the graph factors through `U`.** The structural morphism of `W` to `X`,
taken through `T`, is the first projection of the base change followed by `j ≫ ν`. The induction
of [Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) uses this factorisation to
transport the Zariski-local factorisation property from `W ⟶ T` to `j ≫ ν`. -/
public theorem openImmersionGraphCompl_ι_snd_comp [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] :
    ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) ≫ ν
      = ((openImmersionGraphCompl j ν).ι ≫ pullback.fst (j ≫ ν) ν) ≫ (j ≫ ν) := by
  rw [Category.assoc, Category.assoc, pullback.condition]

end Graph

/-! ### The degree drop along the graph complement

The third paragraph of the source argument needs the fibre degrees of `W ⟶ T` to be smaller by
one than those of `p = j ≫ ν`. Over the open `j(U) ⊆ T` this is the degree drop along the
*diagonal* complement, `AlgebraicGeometry.boundsFiberDegrees_diagonalComplement`: the base change
of `U ×_X T` along `j` is `U ×_X U`, and under that identification the graph of `j` becomes the
diagonal. Lower semicontinuity of the fibre degree then spreads the bound from the dense open
`j(U)` to all of `T`. -/

section GraphDegree

variable {T : Scheme.{u}} (j : U ⟶ T) (ν : T ⟶ X)

/-- The comparison morphism `U ×_X U ⟶ U ×_X T` induced by `j` on the second factor. -/
public def graphComparison : pullback (j ≫ ν) (j ≫ ν) ⟶ pullback (j ≫ ν) ν :=
  pullback.lift (pullback.fst (j ≫ ν) (j ≫ ν)) (pullback.snd (j ≫ ν) (j ≫ ν) ≫ j)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The comparison map followed by the first projection of `U ×_X T` is the first projection of
`U ×_X U`. -/
@[simp]
public theorem graphComparison_fst :
    graphComparison j ν ≫ pullback.fst (j ≫ ν) ν = pullback.fst (j ≫ ν) (j ≫ ν) :=
  pullback.lift_fst _ _ _

/-- The comparison map followed by the second projection of `U ×_X T` is the second projection of
`U ×_X U` followed by `j`. -/
@[simp]
public theorem graphComparison_snd :
    graphComparison j ν ≫ pullback.snd (j ≫ ν) ν = pullback.snd (j ≫ ν) (j ≫ ν) ≫ j :=
  pullback.lift_snd _ _ _

/-- **`U ×_X U` is the base change of `U ×_X T` along `j`.** The square whose top is the
comparison map and whose bottom is `j` is cartesian, because pasting it with the cartesian square
defining `U ×_X T` gives the cartesian square defining `U ×_X U`. -/
public theorem isPullback_graphComparison :
    IsPullback (graphComparison j ν) (pullback.snd (j ≫ ν) (j ≫ ν))
      (pullback.snd (j ≫ ν) ν) j := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (j ≫ ν) ν) ?_ (graphComparison_snd j ν)
    (IsPullback.of_hasPullback (j ≫ ν) ν)
  rw [graphComparison_fst]
  exact IsPullback.of_hasPullback (j ≫ ν) (j ≫ ν)

/-- The comparison map carries the diagonal of `j ≫ ν` to the graph of `j`. -/
public theorem diagonal_comp_graphComparison :
    pullback.diagonal (j ≫ ν) ≫ graphComparison j ν = openImmersionGraph j ν := by
  apply pullback.hom_ext
  · rw [Category.assoc, graphComparison_fst, pullback.diagonal_fst, openImmersionGraph_fst]
  · rw [Category.assoc, graphComparison_snd, ← Category.assoc, pullback.diagonal_snd,
      Category.id_comp, openImmersionGraph_snd]

/-- The range of the first projection of a cartesian square is the preimage of the range of the
opposite leg. -/
private theorem range_of_isPullback {P A B C : Scheme.{u}} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (sq : IsPullback fst snd f g) :
    Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  rw [← Scheme.Pullback.range_fst f g]
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    refine ⟨sq.isoPullback.hom.base a, ?_⟩
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_hom_fst]
  · rintro _ ⟨z, rfl⟩
    refine ⟨sq.isoPullback.inv.base z, ?_⟩
    have h2 : sq.isoPullback.inv ≫ fst = pullback.fst f g := by
      rw [Iso.inv_comp_eq]
      exact sq.isoPullback_hom_fst.symm
    rw [← Scheme.Hom.comp_apply, h2]

/-- **The diagonal is the preimage of the graph.** A point of `U ×_X U` lands on the graph of `j`
exactly when it lies on the diagonal: the square exhibiting the diagonal as the base change of the
graph along the comparison map is cartesian, `j` being a monomorphism. -/
public theorem preimage_range_openImmersionGraph [IsOpenImmersion j] :
    (graphComparison j ν).base ⁻¹' Set.range (openImmersionGraph j ν).base
      = Set.range (pullback.diagonal (j ≫ ν)).base := by
  have sq : IsPullback (pullback.diagonal (j ≫ ν)) (𝟙 U) (graphComparison j ν)
      (openImmersionGraph j ν) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd (j ≫ ν) (j ≫ ν)) ?_ ?_
      (isPullback_graphComparison j ν).flip
    · rw [pullback.diagonal_snd, openImmersionGraph_snd]
      exact IsKernelPair.id_of_mono j
    · rw [diagonal_comp_graphComparison, Category.id_comp]
  exact (range_of_isPullback sq).symm

/-- **The graph complement pulls back to the diagonal complement.** -/
public theorem preimage_openImmersionGraphCompl [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] [IsSeparated (j ≫ ν)] :
    graphComparison j ν ⁻¹ᵁ openImmersionGraphCompl j ν = diagonalComplement (j ≫ ν) := by
  refine TopologicalSpace.Opens.ext ?_
  change (graphComparison j ν).base ⁻¹' ((Set.range (openImmersionGraph j ν).base)ᶜ) = _
  rw [Set.preimage_compl, preimage_range_openImmersionGraph]
  rfl

/-- **The degree drop over the open `j(U)`.** If `n + 1` bounds the degrees of the fibres of
`j ≫ ν`, then at every point of the range of `j` the fibre of the graph complement `W ⟶ T` has
degree at most `n`.

Over `j(U)` the morphism `W ⟶ T` is the base change along `j` of the second projection
`U ×_X U ⟶ U` restricted to the complement of the diagonal, whose fibre degrees are bounded by
`n` by `AlgebraicGeometry.boundsFiberDegrees_diagonalComplement`. -/
public theorem rank_fiber_openImmersionGraphCompl_le [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] [IsSeparated (j ≫ ν)] (n : ℕ)
    (hb : BoundsFiberDegrees (j ≫ ν) ((n + 1 : ℕ) : ℤ)) (u₀ : U) (m : ℕ)
    (hm : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν).fiberToSpecResidueField
        (j.base u₀)) m) :
    m ≤ n := by
  set W := openImmersionGraphCompl j ν with hW
  -- the graph complement, restricted over `j(U)`, is the diagonal complement
  have sq : IsPullback (graphComparison j ν ∣_ W)
      ((graphComparison j ν ⁻¹ᵁ W).ι ≫ pullback.snd (j ≫ ν) (j ≫ ν))
      (W.ι ≫ pullback.snd (j ≫ ν) ν) j :=
    (isPullback_morphismRestrict (graphComparison j ν) W).paste_vert
      (isPullback_graphComparison j ν)
  have hfib : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (((graphComparison j ν ⁻¹ᵁ W).ι ≫
        pullback.snd (j ≫ ν) (j ≫ ν)).fiberToSpecResidueField u₀) m := by
    have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((W.ι ≫ pullback.snd (j ≫ ν) ν).fiberToSpecResidueField (j.base u₀)) m := hm
    exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (f := (W.ι ≫ pullback.snd (j ≫ ν) ν).fiberToSpecResidueField (j.base u₀))
      (f' := ((graphComparison j ν ⁻¹ᵁ W).ι ≫
        pullback.snd (j ≫ ν) (j ≫ ν)).fiberToSpecResidueField u₀)
      (g := Spec.map (j.residueFieldMap u₀))
      (isPullback_fiberToSpecResidueField_of_isPullback sq u₀)
  -- and the diagonal complement has fibre degrees bounded by `n`
  have hbd : BoundsFiberDegrees ((graphComparison j ν ⁻¹ᵁ W).ι ≫
      pullback.snd (j ≫ ν) (j ≫ ν)) ((n : ℕ) : ℤ) := by
    rw [hW, preimage_openImmersionGraphCompl j ν]
    exact boundsFiberDegrees_diagonalComplement (j ≫ ν) n hb
  obtain ⟨r, hrn, hr⟩ := hbd u₀
  have : m = r := finiteLocallyFree_rank_unique _ m r hfib hr
  omega

/-- The graph complement is quasi-compact when the base is: it is a closed subscheme of the base
change `U ×_X T`, which is quasi-compact over `T`. -/
public theorem compactSpace_openImmersionGraphCompl [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] [QuasiCompact (j ≫ ν)] [CompactSpace T] :
    CompactSpace (openImmersionGraphCompl j ν).toScheme := by
  have := isClosedImmersion_openImmersionGraphCompl_ι j ν
  have : CompactSpace (pullback (j ≫ ν) ν : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (j ≫ ν) ν)
  exact QuasiCompact.compactSpace_of_compactSpace (openImmersionGraphCompl j ν).ι

/-- **The degree drop of Stacks, Tag 09Z0.** Let `j : U ⟶ T` be a quasi-compact open immersion
with dense image into a quasi-compact scheme `T`, let `ν : T ⟶ X` be integral, and suppose the
composite `j ≫ ν` is a quasi-compact separated étale morphism whose fibre degrees are bounded by
`n + 1`. Then the complement `W` of the graph of `j` inside `U ×_X T` has fibre degrees over `T`
bounded by `n`.

Over the open `j(U)` this is `Stacks.MoreMorphisms.rank_fiber_openImmersionGraphCompl_le`, the
degree drop along the diagonal complement. The fibre degree of `W ⟶ T` is lower semicontinuous
(`AlgebraicGeometry.isClosed_fiber_rank_lt`), so the locus where it is at most `n` is closed; it
contains the dense open `j(U)` and is therefore everything. This replaces the appeal in the
source to the fact that the degree of the fibres of a quasi-compact separated étale morphism does
not go up under specialization. -/
public theorem boundsFiberDegrees_openImmersionGraphCompl [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] [IsSeparated (j ≫ ν)] [QuasiCompact (j ≫ ν)] [CompactSpace T] (n : ℕ)
    (hb : BoundsFiberDegrees (j ≫ ν) ((n + 1 : ℕ) : ℤ)) (hdense : DenseRange j.base) :
    BoundsFiberDegrees ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν)
      ((n : ℕ) : ℤ) := by
  have hE : Etale ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) := inferInstance
  have := (locallyQuasiFinite_of_etale
    ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν)).1
  have := (locallyQuasiFinite_of_etale
    ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν)).2
  have := compactSpace_openImmersionGraphCompl j ν
  have hub : HasUniversallyBoundedFibers
      ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) :=
    hasUniversallyBoundedFibers_of_locallyQuasiFinite _
  have hcl := isClosed_fiber_rank_lt
    ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) hub (n + 1)
  have hsub : Set.range j.base ⊆ {t : T | ∃ r < n + 1,
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (((openImmersionGraphCompl j ν).ι ≫
          pullback.snd (j ≫ ν) ν).fiberToSpecResidueField t) r} := by
    rintro _ ⟨u₀, rfl⟩
    obtain ⟨m, hm, -⟩ := existsUnique_rank_of_bounded_fiber _ hub (j.base u₀)
    exact ⟨m, by
      have := rank_fiber_openImmersionGraphCompl_le j ν n hb u₀ m hm
      omega, hm⟩
  have huniv : (Set.univ : Set T) ⊆ {t : T | ∃ r < n + 1,
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (((openImmersionGraphCompl j ν).ι ≫
          pullback.snd (j ≫ ν) ν).fiberToSpecResidueField t) r} := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hcl
  intro t
  obtain ⟨r, hrn, hr⟩ := huniv (Set.mem_univ t)
  exact ⟨r, by exact_mod_cast Nat.lt_succ_iff.mp hrn, hr⟩

/-- **The image of the complement of the graph covers everything outside `j(U)` that `j ≫ ν`
reaches.** This is `Stacks.MoreMorphisms.mem_range_openImmersionGraphCompl_ι_snd_of_notMem_range`
without the surjectivity hypothesis: a point of `T` outside `j(U)` whose image in `X` is reached
by `j ≫ ν` is reached by the complement `W`. -/
public theorem mem_range_openImmersionGraphCompl_ι_snd_of_notMem_range_of_mem_range
    [IsOpenImmersion j] [IsIntegralHom ν] [Etale (j ≫ ν)]
    (t : T) (ht : t ∉ Set.range j.base) (ht' : ν.base t ∈ Set.range (j ≫ ν).base) :
    t ∈ Set.range ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν).base := by
  obtain ⟨z, hz⟩ : t ∈ Set.range (pullback.snd (j ≫ ν) ν).base := by
    rwa [Scheme.Pullback.range_snd]
  exact mem_range_openImmersionGraphCompl_ι_snd_of_snd_eq j ν ht z hz

end GraphDegree

/-! ### Factoring near a point -/

/-- `f : Y ⟶ X` factors through `p : U ⟶ X` on an open neighbourhood of `y`. This is the body of
`Stacks.MoreMorphisms.ZariskiLocallyFactors`, isolated so that the induction of
[Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) can speak about one point at a
time. -/
public def FactorsNear {Y : Scheme.{u}} (f : Y ⟶ X) (p : U ⟶ X) (y : Y) : Prop :=
  ∃ (V : Y.Opens) (_ : y ∈ V) (g : V.toScheme ⟶ U), V.ι ≫ f = g ≫ p

/-- `f` factors through `p` Zariski-locally exactly when it factors through `p` near every point
of `Y`. -/
public theorem zariskiLocallyFactors_iff_forall_factorsNear {Y : Scheme.{u}} (f : Y ⟶ X)
    (p : U ⟶ X) : ZariskiLocallyFactors f p ↔ ∀ y : Y, FactorsNear f p y :=
  Iff.rfl

/-- A factorisation of `f` through `p` over the image of an open immersion `ι` into `Y` makes `f`
factor through `p` near every point of that image: the open neighbourhood is the open range
of `ι`. -/
public theorem factorsNear_of_isOpenImmersion {Y Y' : Scheme.{u}} (f : Y ⟶ X) (p : U ⟶ X)
    (i : Y' ⟶ Y) [IsOpenImmersion i] (g : Y' ⟶ U) (hg : i ≫ f = g ≫ p) (y : Y)
    (hy : y ∈ Set.range i.base) : FactorsNear f p y := by
  refine ⟨i.opensRange, hy, i.isoOpensRange.inv ≫ g, ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp i, Category.assoc, hg, Category.assoc]

/-- A morphism `φ : Y ⟶ T` whose value at `y` lies in the range of an open immersion `j : U ⟶ T`
makes `φ ≫ ν` factor through `j ≫ ν` near `y`: the neighbourhood is `φ ⁻¹ j(U)`, on which `φ`
lifts to `U`. -/
public theorem factorsNear_of_mem_range_of_isOpenImmersion {T Y : Scheme.{u}} (j : U ⟶ T)
    (ν : T ⟶ X) [IsOpenImmersion j] (φ : Y ⟶ T) (y : Y)
    (hy : φ.base y ∈ Set.range j.base) : FactorsNear (φ ≫ ν) (j ≫ ν) y := by
  refine factorsNear_of_isOpenImmersion _ _ (φ ⁻¹ᵁ j.opensRange).ι
    ((φ ∣_ j.opensRange) ≫ j.isoOpensRange.inv) ?_ y ?_
  · calc (φ ⁻¹ᵁ j.opensRange).ι ≫ (φ ≫ ν)
        = ((φ ⁻¹ᵁ j.opensRange).ι ≫ φ) ≫ ν := by rw [Category.assoc]
      _ = ((φ ∣_ j.opensRange) ≫ j.opensRange.ι) ≫ ν := by rw [morphismRestrict_ι]
      _ = (φ ∣_ j.opensRange) ≫ (j.opensRange.ι ≫ ν) := by rw [Category.assoc]
      _ = (φ ∣_ j.opensRange) ≫ (j.isoOpensRange.inv ≫ (j ≫ ν)) := by
            rw [opensRange_ι_comp_eq_isoOpensRange_inv_comp]
      _ = ((φ ∣_ j.opensRange) ≫ j.isoOpensRange.inv) ≫ (j ≫ ν) := by rw [Category.assoc]
  · rw [Scheme.Opens.range_ι]
    exact hy

/-! ### The induction on a bound for the fibre degrees -/

/-- The ranges of the two coprojections of a binary coproduct cover it. -/
private theorem range_inl_union_range_inr (A B : Scheme.{u}) :
    Set.range (coprod.inl : A ⟶ A ⨿ B).base ∪ Set.range (coprod.inr : B ⟶ A ⨿ B).base
      = Set.univ := by
  simpa using (isCompl_range_inl_inr A B).sup_eq_top

/-- The range of a morphism out of a binary coproduct is the union of the ranges of its two
components. -/
private theorem range_coprod_desc {A B : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X) :
    Set.range (coprod.desc a b).base = Set.range a.base ∪ Set.range b.base := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    rcases ((range_inl_union_range_inr A B).symm.subset (Set.mem_univ z)) with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact Or.inr ⟨y, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩
  · rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨(coprod.inl : A ⟶ A ⨿ B).base x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact ⟨(coprod.inr : B ⟶ A ⨿ B).base y, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

/-- A scheme which is finite locally free of rank zero over a field is empty: its ring of global
sections is a zero-dimensional vector space, hence the zero ring, whose spectrum is empty. -/
private theorem isEmpty_of_isFiniteLocallyFreeOfRank_zero {k : Type u} [Field k]
    {A : Scheme.{u}} (p : A ⟶ Spec (CommRingCat.of k))
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p 0) : IsEmpty A := by
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p 0 := h
  have : IsAffine A := isAffine_of_isAffineHom p
  let _ : Algebra k ↑Γ(A, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom.toAlgebra
  have hfr := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank p 0
  have hsub : Subsingleton ↑Γ(A, ⊤) := by
    have := hfr.1
    rw [← Module.finrank_zero_iff (R := k)]
    exact hfr.2
  have hps : IsEmpty (PrimeSpectrum ↑Γ(A, ⊤)) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mpr hsub
  exact ⟨fun a => hps.elim (A.isoSpec.hom.base a)⟩

/-- A morphism whose fibre degrees are bounded by zero has empty image: a point in the image has
a nonempty fibre, which is finite locally free of rank zero over the residue field of that point
and therefore empty. -/
private theorem notMem_range_of_boundsFiberDegrees_zero {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (hb : BoundsFiberDegrees f ((0 : ℕ) : ℤ)) (y : Y) : y ∉ Set.range f.base := by
  rintro ⟨z, rfl⟩
  obtain ⟨r, hr, hrank⟩ := hb (f.base z)
  have hr0 : r = 0 := by omega
  subst hr0
  have hempty : IsEmpty (f.fiber (f.base z)) :=
    isEmpty_of_isFiniteLocallyFreeOfRank_zero _ hrank
  exact hempty.elim ((f.fiberHomeo (f.base z)).symm ⟨z, rfl⟩)

/-- The inductive step of [Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0): given the
statement for `n`, prove it for `n + 1` and a covering already presented as a quasi-compact open
immersion with dense image followed by an integral morphism. -/
private theorem exists_isIntegralHom_factorsNear_step (n : ℕ)
    (ih : ∀ (X U : Scheme.{u}) (u : U ⟶ X), CompactSpace X → QuasiSeparatedSpace X →
      Etale u → IsSeparated u → QuasiCompact u → BoundsFiberDegrees u (n : ℤ) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsIntegralHom f ∧
        Set.range u.base ⊆ Set.range f.base ∧
        ∀ y : Y, FactorsNear f u y ∨ f.base y ∉ Set.range u.base)
    {T X' U' : Scheme.{u}} (j : U' ⟶ T) (ν : T ⟶ X') [IsOpenImmersion j] [IsIntegralHom ν]
    [Etale (j ≫ ν)] [IsSeparated (j ≫ ν)] [QuasiCompact (j ≫ ν)]
    [CompactSpace X'] [QuasiSeparatedSpace X'] (hdense : DenseRange j.base)
    (hb : BoundsFiberDegrees (j ≫ ν) ((n + 1 : ℕ) : ℤ)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X'), IsIntegralHom f ∧
      Set.range (j ≫ ν).base ⊆ Set.range f.base ∧
      ∀ y : Y, FactorsNear f (j ≫ ν) y ∨ f.base y ∉ Set.range (j ≫ ν).base := by
  have _ : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace ν
  have _ : QuasiSeparatedSpace T := (quasiSeparated_iff_quasiSeparatedSpace ν).mp inferInstance
  have hEw : Etale ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν) := inferInstance
  have _ := isClosedImmersion_openImmersionGraphCompl_ι j ν
  have hbw : BoundsFiberDegrees ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν)
      ((n : ℕ) : ℤ) := boundsFiberDegrees_openImmersionGraphCompl j ν n hb hdense
  obtain ⟨Z, ρ, _, hρrange, hρloc⟩ :=
    ih T (openImmersionGraphCompl j ν).toScheme
      ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν)
      inferInstance inferInstance inferInstance inferInstance inferInstance hbw
  set V : Set T :=
    Set.range ((openImmersionGraphCompl j ν).ι ≫ pullback.snd (j ≫ ν) ν).base with hVdef
  have hVopen : IsOpen V := isOpen_range_openImmersionGraphCompl_ι_snd j ν
  set I : Scheme.IdealSheafData T :=
    Scheme.IdealSheafData.vanishingIdeal ⟨Vᶜ, hVopen.isClosed_compl⟩ with hIdef
  have hrangeι : Set.range I.subschemeι.base = Vᶜ := by
    rw [hIdef, Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have _ : IsClosedImmersion I.subschemeι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hrangeι]; exact hVopen.isClosed_compl)
  set φ : (Z ⨿ I.subscheme : Scheme.{u}) ⟶ T := coprod.desc ρ I.subschemeι with hφdef
  have hinl : ∀ z : Z, φ.base ((coprod.inl : Z ⟶ Z ⨿ I.subscheme).base z) = ρ.base z := by
    intro z
    rw [hφdef, ← Scheme.Hom.comp_apply, coprod.inl_desc]
  have hinr : ∀ t : I.subscheme,
      φ.base ((coprod.inr : I.subscheme ⟶ Z ⨿ I.subscheme).base t) = I.subschemeι.base t := by
    intro t
    rw [hφdef, ← Scheme.Hom.comp_apply, coprod.inr_desc]
  refine ⟨Z ⨿ I.subscheme, φ ≫ ν, inferInstance, ?_, ?_⟩
  · -- the image contains the image of `j ≫ ν`
    have hφsurj : Set.range φ.base = Set.univ := by
      rw [hφdef, range_coprod_desc, hrangeι]
      refine Set.eq_univ_of_forall fun t => ?_
      by_cases h : t ∈ V
      · exact Or.inl (hρrange h)
      · exact Or.inr h
    rintro _ ⟨u₀, rfl⟩
    obtain ⟨y, hy⟩ : j.base u₀ ∈ Set.range φ.base := by rw [hφsurj]; exact Set.mem_univ _
    exact ⟨y, by simp only [Scheme.Hom.comp_apply, hy]⟩
  · -- the Zariski-local factorisation
    have key : ∀ y : (Z ⨿ I.subscheme : Scheme.{u}), φ.base y ∉ V →
        FactorsNear (φ ≫ ν) (j ≫ ν) y ∨ (φ ≫ ν).base y ∉ Set.range (j ≫ ν).base := by
      intro y hy
      by_cases hv : ν.base (φ.base y) ∈ Set.range (j ≫ ν).base
      · refine Or.inl (factorsNear_of_mem_range_of_isOpenImmersion j ν φ y ?_)
        by_contra hnot
        exact hy (mem_range_openImmersionGraphCompl_ι_snd_of_notMem_range_of_mem_range j ν _
          hnot hv)
      · exact Or.inr (by rw [Scheme.Hom.comp_apply]; exact hv)
    intro y
    rcases (range_inl_union_range_inr Z I.subscheme).symm.subset (Set.mem_univ y) with
        ⟨z, rfl⟩ | ⟨t, rfl⟩
    · rcases hρloc z with ⟨V', hzV', g, hgeq⟩ | hout
      · refine Or.inl (factorsNear_of_isOpenImmersion _ _
          (V'.ι ≫ (coprod.inl : Z ⟶ Z ⨿ I.subscheme))
          (g ≫ (openImmersionGraphCompl j ν).ι ≫ pullback.fst (j ≫ ν) ν) ?_ _ ?_)
        · have e1 : (V'.ι ≫ (coprod.inl : Z ⟶ Z ⨿ I.subscheme)) ≫ (φ ≫ ν)
              = (V'.ι ≫ ρ) ≫ ν := by
            rw [hφdef]
            simp only [Category.assoc, coprod.inl_desc_assoc]
          rw [e1, hgeq, Category.assoc, openImmersionGraphCompl_ι_snd_comp]
          simp only [Category.assoc]
        · obtain ⟨v, hv⟩ : z ∈ Set.range V'.ι.base := by
            rw [Scheme.Opens.range_ι]; exact hzV'
          exact ⟨v, by rw [Scheme.Hom.comp_apply, hv]⟩
      · exact key _ (by rw [hinl]; exact hout)
    · refine key _ ?_
      rw [hinr]
      have hmem : I.subschemeι.base t ∈ Vᶜ := by
        rw [← hrangeι]
        exact ⟨t, rfl⟩
      exact hmem

/-- **The inductive statement of Stacks, Tag 09Z0.** For every bound `n` on the degrees of the
fibres of a quasi-compact separated étale morphism `u : U ⟶ X` over a quasi-compact and
quasi-separated base — `u` is *not* assumed surjective — there is an integral morphism
`f : Y ⟶ X` whose image contains that of `u` and such that every point of `Y` either has an open
neighbourhood on which `f` factors through `u`, or is mapped outside the image of `u`.

When `u` is surjective the second alternative is vacuous and the image condition says `f` is
surjective, which is the existence statement of the tag; the extra generality is what makes the
induction go through, since the covering produced in the inductive step is surjective only over
the image of the previous one.

The induction is on `n`. For `n = 0` the source is empty and `f = 𝟙 X` will do. For `n + 1` one
factors `u` as a quasi-compact open immersion `j` with dense image into the relative
normalisation `T` followed by an integral `ν : T ⟶ X` ([Stacks,
Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)), splits the base change `U ×_X T` into the
graph of `j` and its open and closed complement `W`, and applies the induction hypothesis to
`W ⟶ T`, whose fibre degrees are bounded by `n`
(`Stacks.MoreMorphisms.boundsFiberDegrees_openImmersionGraphCompl`). The refinement `Z ⟶ T` so
obtained is completed by the reduced closed subscheme of `T` on the complement of the image
of `W`, and `Z ⨿ T∖W(T) ⟶ T ⟶ X` is the required morphism. -/
public theorem exists_isIntegralHom_factorsNear_of_boundsFiberDegrees (n : ℕ) :
    ∀ (X U : Scheme.{u}) (u : U ⟶ X), CompactSpace X → QuasiSeparatedSpace X →
      Etale u → IsSeparated u → QuasiCompact u → BoundsFiberDegrees u (n : ℤ) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsIntegralHom f ∧
        Set.range u.base ⊆ Set.range f.base ∧
        ∀ y : Y, FactorsNear f u y ∨ f.base y ∉ Set.range u.base := by
  induction n with
  | zero =>
    intro X U u _ _ _ _ _ hb
    have hru : ∀ x : X, x ∉ Set.range u.base :=
      notMem_range_of_boundsFiberDegrees_zero u hb
    exact ⟨X, 𝟙 X, inferInstance, fun x hx => absurd hx (hru x),
      fun y => Or.inr (hru _)⟩
  | succ n ih =>
    intro X U u _ _ _ _ _ hb
    have _ : LocallyOfFiniteType u := (locallyQuasiFinite_of_etale u).1
    have _ : LocallyQuasiFinite u := (locallyQuasiFinite_of_etale u).2
    -- the compactification of Tag 02LR
    have hjν : u.toNormalization ≫ u.fromNormalization = u := u.toNormalization_fromNormalization
    have _ : Etale (u.toNormalization ≫ u.fromNormalization) := by rw [hjν]; infer_instance
    have _ : IsSeparated (u.toNormalization ≫ u.fromNormalization) := by
      rw [hjν]; infer_instance
    have _ : QuasiCompact (u.toNormalization ≫ u.fromNormalization) := by
      rw [hjν]; infer_instance
    have hb' : BoundsFiberDegrees (u.toNormalization ≫ u.fromNormalization)
        ((n + 1 : ℕ) : ℤ) := by rw [hjν]; exact_mod_cast hb
    have hmain := exists_isIntegralHom_factorsNear_step n ih u.toNormalization
      u.fromNormalization u.toNormalization.denseRange hb'
    rw [hjν] at hmain
    exact hmain

/-- **Stacks, Tag 09Z0: a surjective étale covering is refined by a surjective integral morphism
which factors through it Zariski-locally.** Let `p : U ⟶ X` be a surjective étale morphism of
schemes with `X` quasi-compact and quasi-separated. Then there exist a scheme `Y` and a
surjective integral morphism `f : Y ⟶ X` such that every point of `Y` has an open neighbourhood
`V` for which `V ⟶ X` factors through `p`.

This is the general case of the tag's existence statement: neither separatedness of `p` nor any
hypothesis on its fibre degrees is assumed. The source's first reduction, to an affine — hence
separated — source, is `Stacks.MoreMorphisms.exists_of_isAffine_source`; a natural-number bound
for the degrees of the fibres over that affine source comes from
[Stacks, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA); and the induction on that bound is
`Stacks.MoreMorphisms.exists_isIntegralHom_factorsNear_of_boundsFiberDegrees`.

The tag's closing refinement, that `f` may moreover be taken finite and of finite presentation,
is `Stacks.MoreMorphisms.exists_isFinite_finitePresentation_surjective_zariskiLocallyFactors`,
proved by presenting the integral refinement produced here as a limit of morphisms finite and of
finite presentation. -/
@[stacks 09Z0 "the existence assertion: a surjective étale covering of a quasi-compact and
quasi-separated scheme is refined by a surjective integral morphism factoring through it
Zariski-locally. The closing sentence, that the refinement may be taken finite and of finite
presentation, is
`Stacks.MoreMorphisms.exists_isFinite_finitePresentation_surjective_zariskiLocallyFactors`"]
public theorem exists_isIntegralHom_surjective_zariskiLocallyFactors (p : U ⟶ X) [Etale p]
    [Surjective p] [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsIntegralHom f ∧ Surjective f ∧
      ZariskiLocallyFactors f p := by
  have main : ∃ (Y : Scheme.{u}) (f : Y ⟶ X), (IsIntegralHom f ∧ Surjective f) ∧
      ZariskiLocallyFactors f p := by
    refine exists_of_isAffine_source p
      (fun {_ _ : Scheme.{u}} f => IsIntegralHom f ∧ Surjective f) ?_
    intro U' q _ _ _
    obtain ⟨n, hn⟩ := exists_nat_boundsFiberDegrees_of_etale_of_compactSpace (q ≫ p)
    obtain ⟨Y, f, hint, hrange, hloc⟩ :=
      exists_isIntegralHom_factorsNear_of_boundsFiberDegrees n X U' (q ≫ p)
        inferInstance inferInstance inferInstance inferInstance inferInstance hn
    have hsurj : Surjective f := ⟨fun x => hrange (Surjective.surj (f := q ≫ p) x)⟩
    refine ⟨Y, f, ⟨hint, hsurj⟩, fun y => ?_⟩
    rcases hloc y with h | h
    · exact h
    · exact absurd (Surjective.surj (f := q ≫ p) (f.base y)) h
  obtain ⟨Y, f, ⟨hint, hsurj⟩, hzl⟩ := main
  exact ⟨Y, f, hint, hsurj, hzl⟩

end Stacks.MoreMorphisms

end
