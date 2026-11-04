module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesGlue
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Models over arbitrary stages: Stacks Tag 0EY1

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, **with
no finiteness hypothesis whatsoever on the stages `Sᵢ`**, and let `X` be a quasi-compact,
quasi-separated scheme locally of finite presentation over `S`.  Stacks Tag 0EY1 asserts that `X`
is the base change of a quasi-compact, quasi-separated scheme locally of finite presentation over
one of the stages.  This file proves that assertion, at the generality the source states it.

The argument is local on `X` and then glued.  The local half is here: every point of `X` has an
affine open neighbourhood whose structure morphism to `S` has such a model, and therefore `X`
admits a finite affine open cover each member of which has one.  The glueing is
`AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_finite_cover` of
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesGlue`, and the identification of
the two descents of an intersection that it rests on is
`AlgebraicGeometry.LimitDescent.exists_iso_of_isPullback_of_isPullback_of_small` of
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesIsoAlt`.

## Why the predicate is not `AlgebraicGeometry.LimitDescent.HasModel`

Over a *quasi-separated* stage, "quasi-compact, quasi-separated source and locally of finite
presentation" is the same as `AlgebraicGeometry.FinitePresentation`, by
`AlgebraicGeometry.finitePresentation_of_compactSpace`, and that is the predicate
`AlgebraicGeometry.LimitDescent.HasModel` records.  Over an arbitrary stage the two differ in both
directions: a morphism `p : Y ⟶ Sᵢ` with `Y` quasi-compact and quasi-separated need be neither
quasi-compact nor quasi-separated as a morphism (take `Sᵢ` glued from two copies of `Spec A` along
a non-quasi-compact open `U` and `Y` one of the copies: the preimage of the other copy, an affine
and hence quasi-compact open, is `U`), while conversely a morphism of finite presentation to a
stage that is not quasi-compact does not have quasi-compact source.  This is why the source states
Tag 0EY1 in terms of quasi-compact, quasi-separated `W` locally of finite presentation over `T`
and not in terms of finite presentation, and the right notion of a model over an arbitrary stage
is `AlgebraicGeometry.LimitDescent.HasQcqsModel'` of
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesTransport`: a morphism to the
limit is the base change along a cone leg of a *quasi-compact, quasi-separated* scheme *locally of
finite presentation* over a stage, which is the conclusion of Tag 0EY1 verbatim.

## Main results

* `AlgebraicGeometry.LimitDescent.hasQcqsModel_of_preimage_isAffineOpen`: **the local case of the
  essential surjectivity of Tag 0EY1 over arbitrary stages.**  A quasi-compact, quasi-separated
  scheme locally of finite presentation over `S` whose image lies in the preimage of an affine
  open of a stage has a model over a stage.
* `AlgebraicGeometry.LimitDescent.exists_isAffineOpen_hasQcqsModel_mem`: every point of a scheme
  locally of finite presentation over `S` — no finiteness hypothesis on the scheme either — has an
  affine open neighbourhood whose structure morphism has a model over a stage.
* `AlgebraicGeometry.LimitDescent.exists_finite_hasQcqsModel_cover`: a quasi-compact scheme
  locally of finite presentation over `S` has a finite affine open cover each member of which has
  a model over a stage.
* `AlgebraicGeometry.LimitDescent.exists_finite_hasQcqsModel_cover_of_initiallySmall`: the same
  cover, with the index universes independent of the scheme universe.
* `AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_small` and
  `AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_finallySmall`: **the essential surjectivity of
  Tag 0EY1 over arbitrary stages**, for a directed inverse system, under `Small.{u}` resp.
  `CategoryTheory.FinallySmall.{u}` on the index.
* `AlgebraicGeometry.LimitDescent.exists_model_of_locallyOfFinitePresentation`: the same, in the
  `CategoryTheory.Over.pullback` idiom, which is where the tag sits.  This is
  `AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation` with its two stage
  hypotheses removed, so that result is a special case of it.

## Implementation notes

The hypotheses on the stages are removed by never descending an open of the limit.  The lemma
`AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation` reaches its affine pieces
through `AlgebraicGeometry.exists_isPullback_of_isAffine_of_isAffineOpen`, which descends an
affine open of `S` to an affine open of a stage by Mathlib's
`AlgebraicGeometry.exists_isAffineOpen_preimage_eq`, and that is where quasi-separatedness of the
stages is consumed.  Here the affine open of the stage is given in advance: Mathlib's
`AlgebraicGeometry.isBasis_preimage_isAffineOpen` — which assumes nothing about the stages — says
that the preimages of the affine opens of the stages form a basis of `S`, so the affine
neighbourhood can be chosen inside such a preimage to begin with.

Given the affine open `A ⊆ Sᵢ`, the diagram `AlgebraicGeometry.opensDiagram` of the preimages of
`A` in the later stages has **affine**, hence quasi-compact and quasi-separated, stages, and its
limit is the preimage of `A` in `S` by `AlgebraicGeometry.isLimitOpensCone`.  So Tag
01ZM part (1), `AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation`, applies
to it unchanged, and the resulting model over the open `D.map a ⁻¹ᵁ A` of the stage `D.obj a.left`
becomes a model over the stage itself on composing with the open immersion — which is locally of
finite presentation, and which is where the conclusion drops from finite presentation to the
quasi-compact quasi-separated form.

The index category is at the universe of the schemes because `CategoryTheory.Over i` is: the same
restriction, for the same reason, as the one carried by
`AlgebraicGeometry.exists_isPullback_of_isAffine_of_isAffineOpen`.

## How the index universes are reconciled

The local half above is at an index category in the universe of the schemes, because
`CategoryTheory.Over i` is; the glueing is at a directed preorder with `Small.{u}`, because the
fullness and faithfulness halves of the tag it rests on are.  The two are joined by reindexing
along `CategoryTheory.InitiallySmall.fromCofilteredInitialModel`, which replaces the index by a
`u`-small cofiltered model through an initial functor and so preserves the limit: that is
`exists_finite_hasQcqsModel_cover_of_initiallySmall`.  The tag's own hypothesis is weaker still,
`CategoryTheory.FinallySmall.{u}`; it is reduced to `Small.{u}` in
`hasQcqsModel'_of_finallySmall` by restricting to a `u`-small cofinal subset of the index, which
is again a nonempty directed preorder and whose opposite includes initially into `Iᵒᵖ`.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)

The tag itself is registered on
`AlgebraicGeometry.LimitDescent.isEquivalence_baseChangeComparison` of
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesEquivalence`, which assembles the
essential surjectivity proved here with the two halves of full faithfulness into the equivalence
of categories that the tag asserts.
-/

@[expose] public section

universe v uI u

open CategoryTheory CategoryTheory.Limits CategoryTheory.InitiallySmall TopologicalSpace

namespace AlgebraicGeometry


namespace LimitDescent

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

section

variable [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]

/-- **The local case of the essential surjectivity of Stacks Tag 0EY1, over arbitrary stages.**

Let `S = lim Sᵢ` be a cofiltered limit of schemes with affine transition morphisms — nothing is
assumed of the stages — and let `X` be a quasi-compact, quasi-separated scheme locally of finite
presentation over `S` whose image lies in the open `V` of `S` cut out by an affine open `A` of one
stage.  Then `X` is the base change of a quasi-compact, quasi-separated scheme locally of finite
presentation over a stage.

The model is produced over the preimage of `A` in a later stage, where the restricted system has
affine stages so that Tag 01ZM part (1) applies, and is then pushed to the stage itself
along the open immersion. -/
public theorem hasQcqsModel_of_preimage_isAffineOpen (hc : IsLimit c) {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ c.pt)
    (hf : LocallyOfFinitePresentation f) (i : I) (A : (D.obj i).Opens) (hA : IsAffineOpen A)
    (V : c.pt.Opens) (hV : c.π.app i ⁻¹ᵁ A = V) (hfV : ∀ x, f.base x ∈ V) :
    HasQcqsModel' D c f := by
  subst hV
  have : LocallyOfFinitePresentation f := hf
  have : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  have hAlim : IsAffineOpen (c.π.app i ⁻¹ᵁ A) := hA.preimage _
  -- the restricted system has affine, hence quasi-compact and quasi-separated, stages
  have hst (j : Over i) : IsAffine ((opensDiagram D i A).obj j) := hA.preimage _
  have : IsAffine (opensCone D c i A).pt := hAlim
  -- `f` factors through the preimage of `A`, which is the limit of the restricted system
  obtain ⟨f', hpb0⟩ : ∃ f' : X ⟶ (opensCone D c i A).pt,
      IsPullback (𝟙 X) f' f (c.π.app i ⁻¹ᵁ A).ι := by
    have hr : Set.range f.base ⊆ Set.range (c.π.app i ⁻¹ᵁ A).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro - ⟨x, rfl⟩
      exact hfV x
    exact ⟨_, (IsOpenImmersion.isPullback_lift_id f (c.π.app i ⁻¹ᵁ A).ι hr).flip⟩
  have hf' : f' ≫ (c.π.app i ⁻¹ᵁ A).ι = f := by simpa using hpb0.w.symm
  have hfp' : LocallyOfFinitePresentation f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb0 inferInstance
  obtain ⟨j, Y, p, g, hp, hpb⟩ := exists_isPullback_of_finitePresentation (opensDiagram D i A)
    (opensCone D c i A) (isLimitOpensCone D c hc i A) f'
    (finitePresentation_of_compactSpace f' hfp')
  have := hst j
  have h1 : QuasiCompact p := hp.2.1
  have h2 : QuasiSeparated p := hp.2.2
  have hr' : c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ A) = c.π.app i ⁻¹ᵁ A := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hpb2 : IsPullback
      ((c.π.app j.left).resLE (D.map j.hom ⁻¹ᵁ A) (c.π.app i ⁻¹ᵁ A) hr'.ge)
      (c.π.app i ⁻¹ᵁ A).ι (D.map j.hom ⁻¹ᵁ A).ι (c.π.app j.left) :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp) (by simp [hr'])
  -- the open immersion is locally of finite presentation; `inferInstance` cannot see this
  -- through `AlgebraicGeometry.opensDiagram`, whose unfolding is not reducible
  have hι : LocallyOfFinitePresentation (Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ A)) := inferInstance
  refine ⟨j.left, Y, p ≫ (D.map j.hom ⁻¹ᵁ A).ι, g,
    QuasiCompact.compactSpace_of_compactSpace p, quasiSeparatedSpace_of_quasiSeparated p,
    MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ hp.1 hι, ?_⟩
  have h := hpb.paste_vert hpb2
  rwa [hf'] at h

/-- **Essential surjectivity of Stacks Tag 0EY1 holds locally on the source, over arbitrary
stages.**

Let `S = lim Sᵢ` be a cofiltered limit of schemes with affine transition morphisms, and let
`f : X ⟶ S` be locally of finite presentation.  Every point of `X` has an affine open
neighbourhood `U` such that `U ⟶ S` is the base change of a quasi-compact, quasi-separated scheme
locally of finite presentation over a stage.

Nothing is assumed of the stages, and nothing of `X`: the neighbourhood is chosen inside the
preimage of an affine open of a stage, which is possible because those preimages form a basis of
`S` by `AlgebraicGeometry.isBasis_preimage_isAffineOpen`. -/
public theorem exists_isAffineOpen_hasQcqsModel_mem (hc : IsLimit c) {X : Scheme.{u}}
    (f : X ⟶ c.pt) (hf : LocallyOfFinitePresentation f) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ HasQcqsModel' D c (U.ι ≫ f) := by
  have : LocallyOfFinitePresentation f := hf
  obtain ⟨B, ⟨i, A, hA, hBe⟩, hxB, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_preimage_isAffineOpen D c hc)
      (show f.base x ∈ (⊤ : c.pt.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (f ⁻¹ᵁ B : X.Opens) from hxB)
  have hUa : IsAffineOpen U := hU
  -- `U` is produced at `TopologicalSpace.Opens`, so the projections are named explicitly
  have : IsAffine (Scheme.Opens.toScheme U) := hUa
  exact ⟨U, hUa, hxU, hasQcqsModel_of_preimage_isAffineOpen D c hc (Scheme.Opens.ι U ≫ f)
    inferInstance i A hA B hBe fun y => hUle y.2⟩

/-- **A quasi-compact scheme locally of finite presentation over a cofiltered limit of schemes
with affine transition morphisms has a finite affine open cover each member of which has a model
over a stage.**

This is what the source's proof of the essential surjectivity of Stacks Tag 0EY1 obtains before
the glueing step, with no hypothesis on the stages: compare
`AlgebraicGeometry.LimitDescent.exists_stage_isAffineModels`, which produces the same cover but
needs the stages quasi-separated, the affine opens of `S` being descended there rather than chosen
inside preimages. -/
public theorem exists_finite_hasQcqsModel_cover (hc : IsLimit c) {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ c.pt) (hf : LocallyOfFinitePresentation f) :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens), IsOpenCover U ∧
      ∀ k, IsAffineOpen (U k) ∧ HasQcqsModel' D c ((U k).ι ≫ f) := by
  choose U hUaff hxU hUm using exists_isAffineOpen_hasQcqsModel_mem D c hc f hf
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩
  refine ⟨{x // x ∈ t}, inferInstance, fun k => U k.1, ?_, fun k => ⟨hUaff _, hUm _⟩⟩
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_univ_subset (ht.trans ?_))
  rw [TopologicalSpace.Opens.coe_iSup]
  exact Set.iUnion₂_subset fun y hy => Set.subset_iUnion_of_subset ⟨y, hy⟩ subset_rfl

end

/-! ### The cover, at an index category whose universes are free -/

/-- `AlgebraicGeometry.LimitDescent.exists_finite_hasQcqsModel_cover` with the index universes
independent of the scheme universe: a quasi-compact scheme locally of finite presentation over a
cofiltered limit of schemes with affine transition morphisms has a finite affine open cover each
member of which has a quasi-compact quasi-separated model over a stage.

The cover is the one produced at the universe of the schemes for the reindexing of the diagram
along `CategoryTheory.InitiallySmall.fromCofilteredInitialModel`, whose stages are stages of the
original diagram; the opens of `X` are untouched. -/
public theorem exists_finite_hasQcqsModel_cover_of_initiallySmall {J : Type uI} [Category.{v} J]
    [IsCofiltered J] [LocallySmall.{u} J] [InitiallySmall.{u} J] (E : J ⥤ Scheme.{u}) (d : Cone E)
    (hd : IsLimit d) [∀ {a b : J} (g : a ⟶ b), IsAffineHom (E.map g)] {X : Scheme.{u}}
    [CompactSpace X] (f : X ⟶ d.pt) (hf : LocallyOfFinitePresentation f) :
    ∃ (K : Type u) (_ : Finite K) (U : K → X.Opens), IsOpenCover U ∧
      ∀ k, IsAffineOpen (U k) ∧ HasQcqsModel' E d ((U k).ι ≫ f) := by
  obtain ⟨K, hK, U, hcov, hall⟩ := exists_finite_hasQcqsModel_cover
    (fromCofilteredInitialModel.{u} J ⋙ E) (d.whisker (fromCofilteredInitialModel.{u} J))
    ((Functor.Initial.isLimitWhiskerEquiv (fromCofilteredInitialModel.{u} J) d).symm hd) f hf
  refine ⟨K, hK, U, hcov, fun k => ⟨(hall k).1, ?_⟩⟩
  obtain ⟨a, h⟩ := (hall k).2
  exact ⟨(fromCofilteredInitialModel.{u} J).obj a, h⟩

/-! ### Essential surjectivity over arbitrary stages -/

/-- **Essential surjectivity of Stacks Tag 0EY1 over arbitrary stages**, under the extra
hypothesis `Small.{u} I`: a quasi-compact, quasi-separated scheme locally of finite presentation
over a directed inverse limit of schemes with affine transition morphisms — nothing is assumed of
the stages — is the base change of a quasi-compact, quasi-separated scheme locally of finite
presentation over one of the stages.

The cover of `AlgebraicGeometry.LimitDescent.exists_finite_hasQcqsModel_cover` is glued by
`AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_finite_cover`.  The smallness hypothesis is
removed in `AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_finallySmall`. -/
@[ega "IV 8.1.1" "more general", ega "IV 8.8.2" "more general", sga "3 VIB 10.0" "more general"]
public theorem hasQcqsModel'_of_small {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] [Small.{u} I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ c.pt)
    (hf : LocallyOfFinitePresentation f) : HasQcqsModel' D c f := by
  have : InitiallySmall.{u} Iᵒᵖ := CategoryTheory.initiallySmall_of_small_of_locallySmall _
  obtain ⟨K, hK, U, hcov, hall⟩ :=
    exists_finite_hasQcqsModel_cover_of_initiallySmall D c hc f hf
  have : Finite K := hK
  exact hasQcqsModel'_of_finite_cover D c hc f U hcov (fun k => (hall k).1.isCompact)
    fun k => (hall k).2

/-- **Essential surjectivity of Stacks Tag 0EY1 over arbitrary stages.**

`AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_small` with the smallness hypothesis on the index
weakened to `CategoryTheory.FinallySmall.{u}`, which is what the tag's directed *set* gives: a
`u`-small cofinal subset `s` of `I` is again a nonempty directed preorder, the inclusion of its
opposite into `Iᵒᵖ` is initial because `s` is cofinal and the order is thin, and so the restricted
diagram has the same limit. -/
public theorem hasQcqsModel'_of_finallySmall {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] [FinallySmall.{u} I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ c.pt)
    (hf : LocallyOfFinitePresentation f) : HasQcqsModel' D c f := by
  obtain ⟨s, hs, hsw⟩ :
      ∃ (s : Set I) (_ : Small.{u} s), ∀ i : I, ∃ j ∈ s, Nonempty (i ⟶ j) :=
    FinallySmall.exists_small_weakly_terminal_set I
  have hsle : ∀ i : I, ∃ j : I, j ∈ s ∧ i ≤ j :=
    fun i => (hsw i).imp fun _ ⟨hj, ⟨h⟩⟩ => ⟨hj, leOfHom h⟩
  -- The cofinal subset, with the induced order, is a nonempty directed `u`-small preorder.
  have hne : Nonempty {x : I // x ∈ s} := by
    obtain ⟨j, hj, -⟩ := hsle (Classical.arbitrary I)
    exact ⟨⟨j, hj⟩⟩
  have hdir : IsDirected {x : I // x ∈ s} (· ≤ ·) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    obtain ⟨l, hl, hkl⟩ := hsle k
    exact ⟨⟨l, hl⟩, hak.trans hkl, hbk.trans hkl⟩
  have hsm : Small.{u} {x : I // x ∈ s} := hs
  -- The inclusion, as a functor, is fully faithful, and its opposite is initial.
  let G : {x : I // x ∈ s} ⥤ I := (Subtype.mono_coe _).functor
  have hfull : G.Full := ⟨fun h => ⟨homOfLE (leOfHom h), Subsingleton.elim _ _⟩⟩
  have hfaith : G.Faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  have hinit : G.op.Initial := by
    refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful G.op fun i => ?_
    obtain ⟨j, hj, hij⟩ := hsle i.unop
    exact ⟨Opposite.op ⟨j, hj⟩, ⟨(homOfLE hij).op⟩⟩
  obtain ⟨j, h⟩ := hasQcqsModel'_of_small (G.op ⋙ D) (c.whisker G.op)
    ((Functor.Initial.isLimitWhiskerEquiv G.op c).symm hc) f hf
  exact ⟨G.op.obj j, h⟩

/-- **Essential surjectivity in Stacks Tag 0EY1, at the generality the source states.**

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms — **no
finiteness hypothesis whatsoever is made on the stages `Sᵢ`** — and let `X` be a quasi-compact,
quasi-separated scheme locally of finite presentation over `S`.  Then `X` is isomorphic, over `S`,
to the base change of a quasi-compact, quasi-separated scheme locally of finite presentation over
one of the stages `Sᵢ`.

This is `AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation` with the stage
hypotheses `CompactSpace (D.obj i)` and `QuasiSeparatedSpace (D.obj i)` removed, so that that
result is the special case of this one in which the stages are quasi-compact and quasi-separated;
over such a stage the conclusion is `AlgebraicGeometry.FinitePresentation` of the model, by
`AlgebraicGeometry.finitePresentation_of_compactSpace`.  The source assumes nothing about the
stages, which is why the statement is in terms of a quasi-compact, quasi-separated source and a
morphism locally of finite presentation rather than in terms of finite presentation.

The index hypothesis `CategoryTheory.FinallySmall.{u} I` asks that `I` have a `u`-small cofinal
set of objects; it is automatic for the directed *set* of the source, and is needed because the
comparison of the sections of the limit with the sections at the stages is a statement about an
index category at the scheme universe. -/
@[stacks 0EY1 "essential surjectivity, arbitrary stages",
  sga "4 VII 5.3" "essential surjectivity",
  ega "IV 8.1.1" "more general",
  ega "IV 8.8.2" "more general",
  ega "IV 8.8.3" "essential surjectivity",
  sga "3 VIB 10.0" "more general",
  sga "4 VII 5.2" "more general"]
public theorem exists_model_of_locallyOfFinitePresentation
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [FinallySmall.{u} I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (X : Over c.pt)
    (hXqc : CompactSpace X.left) (hXqs : QuasiSeparatedSpace X.left)
    (hX : LocallyOfFinitePresentation X.hom) :
    ∃ (i : I) (Xᵢ : Over (D.obj (.op i))),
      CompactSpace Xᵢ.left ∧ QuasiSeparatedSpace Xᵢ.left ∧
        LocallyOfFinitePresentation Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app (.op i))).obj Xᵢ) := by
  have := hXqc
  have := hXqs
  obtain ⟨i, Y, p, g, h₁, h₂, h₃, hpb⟩ := hasQcqsModel'_of_finallySmall D c hc X.hom hX
  exact ⟨i.unop, Over.mk p, h₁, h₂, h₃, ⟨Over.isoMk hpb.isoPullback (by simp)⟩⟩

end LimitDescent

end AlgebraicGeometry
