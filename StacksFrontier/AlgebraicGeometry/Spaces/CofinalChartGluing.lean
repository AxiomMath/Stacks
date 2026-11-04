module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescentTwoIso

/-!
# Gluing a morphism to a sheaf from its values on a cofinal family of affine étale charts

`AlgebraicGeometry.Space.exists_hom_of_chartHoms` glues a morphism `F ⟶ W` out of a family of
morphisms `k T b : h_T ⟶ W` given on **every** affine étale chart `b : h_T ⟶ F`.  A construction
that produces such a morphism from auxiliary data — a lift of the chart through some member of a
covering family, say — does not supply the family on every chart: only a cover of a given affine
chart admits such a lift, because the surjectivity that produces one is local.  This file refines
the gluing so that the family need only be given on a **cofinal** class of affine étale charts.

"Cofinal" is `AlgebraicGeometry.Space.IsCofinalChartFamily`: a predicate `P` on charts such that
every affine étale chart of `F` is covered, in the topology of the big fppf site, by affine étale
charts satisfying `P`.  Compatibility of the family is then asked for only between charts
satisfying `P`, and the glued morphism is characterised by its restrictions to those charts.
Nothing is assumed about `P` beyond cofinality, and the case `P = ⊤` returns the original
statements: `AlgebraicGeometry.Space.isCofinalChartFamily_top` records that `⊤` is cofinal.

## Main definitions

* `AlgebraicGeometry.Space.IsCofinalChartFamily` — the cofinality condition, stated for affine
  charts.

## Main results

* `AlgebraicGeometry.BigFppfOver.sieve_generate_ofArrows_comp_mem_topology` — two covering
  families compose.
* `AlgebraicGeometry.BigFppfOver.exists_affine_etale_refinement` — an étale covering family is
  refined by an affine one through it.  This is the step between the cover a caller gets from a
  surjectivity and the affine cover the cofinality condition asks for.
* `AlgebraicGeometry.Space.IsCofinalChartFamily.exists_cover` — a cofinal family covers *every*
  étale chart of `F`, not only the affine ones.
* `AlgebraicGeometry.Space.chartHoms_agree_of_cofinal` — two `P`-charts that agree after pulling
  back to a common object give the same morphism to `W` there.
* `AlgebraicGeometry.Space.exists_hom_yoneda_of_chartHoms_of_cofinal` — the family glues along an
  étale chart with arbitrary source.
* `AlgebraicGeometry.Space.exists_hom_of_chartHoms_of_cofinal` — along a surjective étale atlas
  the glued morphism descends to `F`.
* `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_cofinal` — the same with the
  compatibility of the family checked up to a 2-isomorphism of the induced morphisms of small
  étale ringed topoi, which is the form
  `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso` has.

## Implementation notes

### Why cofinality is stated for affine charts only

A caller refines a chart by pulling back a covering family and then passing to an affine open
cover of each member, so what it naturally proves is the condition for an affine chart.  The
proofs below need the condition at an arbitrary étale chart — the common objects occurring in
them are pullbacks, which are not affine — and
`AlgebraicGeometry.Space.IsCofinalChartFamily.exists_cover` supplies it: cover the arbitrary
chart by affine ones (`AlgebraicGeometry.BigFppfOver.exists_affine_etale_cover`), refine each by
`P`-charts, and compose the two coverings with
`CategoryTheory.GrothendieckTopology.transitive`.  So the hypothesis is the weaker of the two
forms and the theorems are correspondingly stronger.

### Why the value of the family may depend on the proof of `P`

`k` takes a proof of `P T b` as an argument, because the auxiliary data a caller uses to build
`k T b` is extracted from that proof.  No well-definedness condition is needed: `P T b` is a
`Prop`, so any two proofs of it are equal and the values agree.
`AlgebraicGeometry.Space.chartHom_congr` is the resulting congruence along an equality of charts,
which is what replaces the `congr` steps of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartGluing.lean`.

### What this is for

This is the source-side refinement that the affine-target route through the proof of
[Stacks Project, Tag 04KL] needs; the route is recorded in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/ExistenceChain.lean`.  There
`F` is an algebraic space `X`, the charts are the affine étale charts of `X`, and `P T b` says
that `b` lifts through `g⁻¹h_{V_i}` for some member `V_i` of an affine étale cover of the target;
cofinality of `P` is the surjectivity of `∐ᵢ g⁻¹h_{V_i} ⟶ *` pulled back to `T`.  That `P` and
its cofinality are
`AlgebraicGeometry.Space.HasSomeChartSection` and
`AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc` of
`StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartFamilySurjective.lean`, and the surjectivity
they consume is proved — from nothing but the `V_i` covering the final object of the small étale
site of the target — in
`StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartFamilyInverseImage.lean`, which also records
this statement with the cofinality hypothesis gone as
`AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_coversTop`.  Nothing about
ringed topoi or recovery theorems enters here.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Two covering families compose.**  If the family `π i : V i ⟶ R` covers `R` and each `V i` is
covered by `ρ i j : O i j ⟶ V i`, the composite family `ρ i j ≫ π i`, indexed by `Σ i, J i`,
covers `R`.

This is transitivity of the topology, `CategoryTheory.GrothendieckTopology.transitive`, in the
indexed-family form the statements below use: the sieve the composite family generates has, over
each member of the first family, a pullback containing the sieve the second family generates
there. -/
theorem sieve_generate_ofArrows_comp_mem_topology {R : BigFppfOver B S hS} {I : Type u}
    (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ R)
    (hcover : Sieve.generate (Presieve.ofArrows V π) ∈ topology B S hS R)
    {J : I → Type u} (O : ∀ i, J i → BigFppfOver B S hS) (ρ : ∀ i j, O i j ⟶ V i)
    (hρ : ∀ i, Sieve.generate (Presieve.ofArrows (O i) (ρ i)) ∈ topology B S hS (V i)) :
    Sieve.generate (Presieve.ofArrows (fun p : Σ i, J i => O p.1 p.2)
        fun p => ρ p.1 p.2 ≫ π p.1) ∈ topology B S hS R := by
  refine (topology B S hS).transitive hcover _ ?_
  rintro Z f ⟨_, g, _, ⟨i⟩, rfl⟩
  refine (topology B S hS).superset_covering ?_ ((topology B S hS).pullback_stable g (hρ i))
  rintro Z' f' ⟨_, a, _, ⟨j⟩, hfac⟩
  exact ⟨O i j, a, ρ i j ≫ π i, Presieve.ofArrows.mk (⟨i, j⟩ : Σ i, J i), by
    rw [← Category.assoc, hfac, Category.assoc]⟩

/-- **An étale covering family of an object of the big fppf site is refined by an affine one
through it.** Each member `V' j` of the refinement is affine and étale over `R`, and comes with
a morphism `σ j` to the member `V (ρ j)` of the given family with `σ j ≫ π (ρ j) = π' j`.

`AlgebraicGeometry.Space.IsCofinalChartFamily` asks for a cover by *affine* charts, while what a
caller gets from a surjectivity is a cover with arbitrary members; this is the step between the
two. -/
theorem exists_affine_etale_refinement {R : BigFppfOver B S hS} {I : Type u}
    (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ R)
    (hπ : ∀ i, Space.IsEtale B S hS (yoneda.map (π i)))
    (hcover : Sieve.generate (Presieve.ofArrows V π) ∈ topology B S hS R) :
    ∃ (I' : Type u) (V' : I' → BigFppfOver B S hS) (π' : ∀ j, V' j ⟶ R) (ρ : I' → I)
      (σ : ∀ j, V' j ⟶ V (ρ j)),
      (∀ j, IsAffineOver B S hS (V' j)) ∧ (∀ j, Space.IsEtale B S hS (yoneda.map (π' j))) ∧
      Sieve.generate (Presieve.ofArrows V' π') ∈ topology B S hS R ∧
      ∀ j, σ j ≫ π (ρ j) = π' j := by
  classical
  choose Jidx O τ hOaff hτ hOcover using fun i => exists_affine_etale_cover B S hS (V i)
  refine ⟨Σ i, Jidx i, fun p => O p.1 p.2, fun p => τ p.1 p.2 ≫ π p.1, fun p => p.1,
    fun p => τ p.1 p.2, fun p => hOaff p.1 p.2, fun p => ?_,
    sieve_generate_ofArrows_comp_mem_topology B S hS V π hcover O τ hOcover, fun _ => rfl⟩
  simpa only [Functor.map_comp] using
    Space.isEtale_comp B S hS (hτ p.1 p.2) (hπ p.1)

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A class of charts cofinal among the affine étale charts of `F`.**  `P` selects, for each
object `T` of the big fppf site, some of the morphisms `h_T ⟶ F`; the condition is that every
affine étale chart of `F` admits a covering family of affine étale charts selected by `P`.

The covering is a family in the topology of the site, as produced by
`AlgebraicGeometry.BigFppfOver.exists_affine_etale_cover`, and étaleness of its members is
recorded for their images under Yoneda, which is the shape **Stacks 03FR** gives it. -/
def IsCofinalChartFamily (P : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ F) → Prop) : Prop :=
  ∀ (R : BigFppfOver B S hS), IsAffineOver B S hS R →
    ∀ c : yoneda.obj R ⟶ F, IsEtale B S hS c →
      ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ R),
        (∀ i, IsAffineOver B S hS (V i)) ∧ (∀ i, IsEtale B S hS (yoneda.map (π i))) ∧
        Sieve.generate (Presieve.ofArrows V π) ∈ BigFppfOver.topology B S hS R ∧
        ∀ i, P (V i) (yoneda.map (π i) ≫ c)

/-- **The class of all charts is cofinal.**  This is
`AlgebraicGeometry.BigFppfOver.exists_affine_etale_cover`; it is what makes the refinements below
generalisations of the statements of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartGluing.lean` rather than variants of them, and it
shows that `AlgebraicGeometry.Space.IsCofinalChartFamily` is satisfiable. -/
theorem isCofinalChartFamily_top :
    IsCofinalChartFamily B S hS (F := F) fun _ _ => True := by
  intro R _ c _
  obtain ⟨I, V, π, hV, hπ, hcover⟩ := BigFppfOver.exists_affine_etale_cover B S hS R
  exact ⟨I, V, π, hV, hπ, hcover, fun _ => trivial⟩

variable {P : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ F) → Prop}

/-- **A cofinal class of charts covers every étale chart of `F`, not only the affine ones.**  Cover
the given chart by affine objects, refine each of them by a covering family of `P`-charts, and
compose the two coverings; the composite family is covering by transitivity of the topology.

The affine form is what a caller proves and this is what the gluing arguments below consume, since
the common objects they form — pullbacks of two charts — are not affine. -/
theorem IsCofinalChartFamily.exists_cover (hP : IsCofinalChartFamily B S hS P)
    (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ F) (hc : IsEtale B S hS c) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ R),
      (∀ i, IsAffineOver B S hS (V i)) ∧ (∀ i, IsEtale B S hS (yoneda.map (π i))) ∧
      Sieve.generate (Presieve.ofArrows V π) ∈ BigFppfOver.topology B S hS R ∧
      ∀ i, P (V i) (yoneda.map (π i) ≫ c) := by
  classical
  obtain ⟨I, V, π, hV, hπ, hcover⟩ := BigFppfOver.exists_affine_etale_cover B S hS R
  choose J O ρ hOaff hρ hOcover hOP using fun i =>
    hP (V i) (hV i) (yoneda.map (π i) ≫ c) (isEtale_comp B S hS (hπ i) hc)
  refine ⟨Σ i, J i, fun p => O p.1 p.2, fun p => ρ p.1 p.2 ≫ π p.1,
    fun p => hOaff p.1 p.2, fun p => ?_, ?_, fun p => ?_⟩
  · simpa only [Functor.map_comp] using isEtale_comp B S hS (hρ p.1 p.2) (hπ p.1)
  · exact BigFppfOver.sieve_generate_ofArrows_comp_mem_topology B S hS V π hcover O ρ hOcover
  · simpa only [Functor.map_comp, Category.assoc] using hOP p.1 p.2

section Glue

variable (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
  (k : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
    ∀ b : yoneda.obj T ⟶ F, IsEtale B S hS b → P T b → (yoneda.obj T ⟶ W))

/-- **The family depends on the chart alone.**  Two of its values at one object are equal as soon
as the two charts are, the proofs of étaleness and of `P` being proofs of propositions.  This is
the congruence the gluing arguments use where the family is read at two syntactically different
presentations of the same chart. -/
theorem chartHom_congr (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
    (b c : yoneda.obj T ⟶ F) (hb : IsEtale B S hS b) (hc : IsEtale B S hS c)
    (hPb : P T b) (hPc : P T c) (h : b = c) :
    k T hT b hb hPb = k T hT c hc hPc := by
  subst h
  rfl

/-- Two morphisms to `W` from an object with an étale chart `b` agree once, over every affine
`P`-chart `π` of a cofinal cover, both equal the value of the family at `π ≫ b`. -/
private theorem eq_of_chartHoms_cover (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    (hP : IsCofinalChartFamily B S hS P) {R : BigFppfOver B S hS} {b b' : yoneda.obj R ⟶ F}
    (h : b = b') (hb : IsEtale B S hS b) {f g : yoneda.obj R ⟶ W}
    (hf : ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (π : T ⟶ R)
      (hπ : IsEtale B S hS (yoneda.map π ≫ b)) (hPπ : P T (yoneda.map π ≫ b)),
      yoneda.map π ≫ f = k T hT (yoneda.map π ≫ b) hπ hPπ)
    (hg : ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (π : T ⟶ R)
      (hπ : IsEtale B S hS (yoneda.map π ≫ b')) (hPπ : P T (yoneda.map π ≫ b')),
      yoneda.map π ≫ g = k T hT (yoneda.map π ≫ b') hπ hPπ) :
    f = g := by
  subst h
  obtain ⟨I, V, π, hV, hπ, hcover, hPV⟩ := hP.exists_cover B S hS R b hb
  refine hom_ext_of_cover B S hS hW R V π hcover fun i => ?_
  have hπb := isEtale_comp B S hS (hπ i) hb
  exact (hf _ (hV i) (π i) hπb (hPV i)).trans (hg _ (hV i) (π i) hπb (hPV i)).symm

variable (hk : ∀ (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
    (hU : IsAffineOver B S hS U) (r : T ⟶ U) (b : yoneda.obj U ⟶ F)
    (hb : IsEtale B S hS b) (hrb : IsEtale B S hS (yoneda.map r ≫ b))
    (hPb : P U b) (hPrb : P T (yoneda.map r ≫ b)),
    yoneda.map r ≫ k U hU b hb hPb = k T hT (yoneda.map r ≫ b) hrb hPrb)

include hW hk

/-- **Two `P`-charts of `F` pulled back to a common object give the same morphism to `W` there.**
Cover the common object by affine `P`-charts, which is possible by cofinality; over each of them
both restrictions are an instance of the assumed compatibility of the family, and the two agree
because the two charts do.  The target being a sheaf lets the resulting local agreement be
assembled.

This is `AlgebraicGeometry.Space.chartHoms_agree` with the family given only on `P`-charts; the
only change in the proof is that the cover of the common object is taken cofinal. -/
theorem chartHoms_agree_of_cofinal (hP : IsCofinalChartFamily B S hS P)
    (T U R : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (hU : IsAffineOver B S hS U)
    (b : yoneda.obj T ⟶ F) (c : yoneda.obj U ⟶ F)
    (hb : IsEtale B S hS b) (hc : IsEtale B S hS c) (hPb : P T b) (hPc : P U c)
    (r : R ⟶ T) (s : R ⟶ U) (hrs : yoneda.map r ≫ b = yoneda.map s ≫ c)
    (hrb : IsEtale B S hS (yoneda.map r ≫ b)) :
    yoneda.map r ≫ k T hT b hb hPb = yoneda.map s ≫ k U hU c hc hPc := by
  refine eq_of_chartHoms_cover B S hS k hW hP hrs hrb ?_ ?_
  · intro V hV π hπ hPπ
    simpa only [Functor.map_comp, Category.assoc] using
      hk V T hV hT (π ≫ r) b hb (by simpa only [Functor.map_comp, Category.assoc] using hπ) hPb
        (by simpa only [Functor.map_comp, Category.assoc] using hPπ)
  · intro V hV π hπ hPπ
    simpa only [Functor.map_comp, Category.assoc] using
      hk V U hV hU (π ≫ s) c hc (by simpa only [Functor.map_comp, Category.assoc] using hπ) hPc
        (by simpa only [Functor.map_comp, Category.assoc] using hPπ)

/-- **The family glues along an étale chart with arbitrary source.**  Over a cofinal cover of `U`
by affine `P`-charts the family is a pullback-compatible family of sections of `W`, by
`AlgebraicGeometry.Space.chartHoms_agree_of_cofinal`, so the sheaf condition glues it; the glued
morphism restricts to the given value on *every* affine `P`-chart of `U`, not only on the members
of the chosen cover, because the two agree after pulling back to a cofinal cover of each chart.

This is `AlgebraicGeometry.Space.exists_hom_yoneda_of_chartHoms` with the family given only on
`P`-charts. -/
theorem exists_hom_yoneda_of_chartHoms_of_cofinal (hP : IsCofinalChartFamily B S hS P)
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ F) (hb : IsEtale B S hS b) :
    ∃ l : yoneda.obj U ⟶ W, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (r : T ⟶ U) (hrb : IsEtale B S hS (yoneda.map r ≫ b))
      (hPrb : P T (yoneda.map r ≫ b)),
      yoneda.map r ≫ l = k T hT (yoneda.map r ≫ b) hrb hPrb := by
  classical
  obtain ⟨I, V, π, hV, hπ, hcover, hPV⟩ := hP.exists_cover B S hS U b hb
  have hbi (i : I) : IsEtale B S hS (yoneda.map (π i) ≫ b) := isEtale_comp B S hS (hπ i) hb
  have hsf : Presieve.IsSheafFor W (Presieve.ofArrows V π) :=
    (Presieve.isSheafFor_iff_generate (P := W) _).mpr
      (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) W).mp hW) _ hcover)
  have hx : Presieve.Arrows.PullbackCompatible W π
      fun i => yonedaEquiv (k (V i) (hV i) (yoneda.map (π i) ≫ b) (hbi i) (hPV i)) := by
    intro i j
    have hfst : IsEtale B S hS (yoneda.map (pullback.fst (π i) (π j))) :=
      isEtale_of_isPullback_yoneda B S hS
        ((IsPullback.of_hasPullback (π i) (π j)).map yoneda).flip (hπ j)
    have he := chartHoms_agree_of_cofinal B S hS hW k hk hP (V i) (V j) (pullback (π i) (π j))
      (hV i) (hV j) (yoneda.map (π i) ≫ b) (yoneda.map (π j) ≫ b) (hbi i) (hbi j)
      (hPV i) (hPV j) (pullback.fst (π i) (π j)) (pullback.snd (π i) (π j))
      (by simp only [← Category.assoc, ← Functor.map_comp, pullback.condition])
      (isEtale_comp B S hS hfst (hbi i))
    simpa only [yonedaEquiv_naturality] using congrArg yonedaEquiv he
  obtain ⟨sec, hsec, -⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks W π).mp hsf _ hx
  refine ⟨yonedaEquiv.symm sec, fun T hT r hrb hPrb => ?_⟩
  have hl (i : I) : yoneda.map (π i) ≫ yonedaEquiv.symm sec =
      k (V i) (hV i) (yoneda.map (π i) ≫ b) (hbi i) (hPV i) := by
    refine yonedaEquiv.injective ?_
    rw [← yonedaEquiv_naturality]
    simpa only [Equiv.apply_symm_apply] using hsec i
  have hc : Sieve.generate (Presieve.ofArrows (fun i => pullback r (π i))
      fun i => pullback.fst r (π i)) ∈ BigFppfOver.topology B S hS T := by
    show Sieve.ofArrows _ _ ∈ _
    rw [Sieve.ofArrows_eq_pullback_of_isPullback π fun i => IsPullback.of_hasPullback r (π i)]
    exact (BigFppfOver.topology B S hS).pullback_stable r hcover
  refine hom_ext_of_cover B S hS hW T _ _ hc fun i => ?_
  have hfst : IsEtale B S hS (yoneda.map (pullback.fst r (π i))) :=
    isEtale_of_isPullback_yoneda B S hS
      ((IsPullback.of_hasPullback r (π i)).map yoneda).flip (hπ i)
  have he := chartHoms_agree_of_cofinal B S hS hW k hk hP T (V i) (pullback r (π i)) hT (hV i)
    (yoneda.map r ≫ b) (yoneda.map (π i) ≫ b) hrb (hbi i) hPrb (hPV i)
    (pullback.fst r (π i)) (pullback.snd r (π i))
    (by simp only [← Category.assoc, ← Functor.map_comp, pullback.condition])
    (isEtale_comp B S hS hfst hrb)
  calc yoneda.map (pullback.fst r (π i)) ≫ yoneda.map r ≫ yonedaEquiv.symm sec
      = yoneda.map (pullback.snd r (π i)) ≫ yoneda.map (π i) ≫ yonedaEquiv.symm sec := by
        simp only [← Category.assoc, ← Functor.map_comp, pullback.condition]
    _ = yoneda.map (pullback.snd r (π i)) ≫
          k (V i) (hV i) (yoneda.map (π i) ≫ b) (hbi i) (hPV i) := by rw [hl]
    _ = yoneda.map (pullback.fst r (π i)) ≫ k T hT (yoneda.map r ≫ b) hrb hPrb := he.symm

/-- **Along a surjective étale atlas the glued morphism descends to `F`.**  The morphism glued on
the atlas by `AlgebraicGeometry.Space.exists_hom_yoneda_of_chartHoms_of_cofinal` is invariant
under the kernel pair of the atlas — the two projections restrict the atlas to the same chart, and
that chart is covered by affine `P`-charts over which the two restrictions of the glued morphism
are the same value of the family — so it factors through `F` by
`AlgebraicGeometry.Space.existsUnique_hom_of_atlas_invariant`.

This is `AlgebraicGeometry.Space.exists_hom_of_chartHoms` with the family given only on
`P`-charts, and the characterisation of the glued morphism correspondingly on `P`-charts. -/
theorem exists_hom_of_chartHoms_of_cofinal (hP : IsCofinalChartFamily B S hS P)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ F) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : F ⟶ W, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (r : T ⟶ U)
      (hrb : IsEtale B S hS (yoneda.map r ≫ b)) (hPrb : P T (yoneda.map r ≫ b)),
      yoneda.map r ≫ b ≫ l = k T hT (yoneda.map r ≫ b) hrb hPrb := by
  obtain ⟨lU, hlU⟩ := exists_hom_yoneda_of_chartHoms_of_cofinal B S hS hW k hk hP U b hb
  have hcompat (R : BigFppfOver B S hS) (r s : R ⟶ U)
      (hR : IsPullback (yoneda.map r) (yoneda.map s) b b) :
      yoneda.map r ≫ lU = yoneda.map s ≫ lU := by
    have hr : IsEtale B S hS (yoneda.map r) :=
      isEtale_of_isPullback_yoneda B S hS hR.flip hb
    have hrb : IsEtale B S hS (yoneda.map r ≫ b) := isEtale_comp B S hS hr hb
    refine eq_of_chartHoms_cover B S hS k hW hP hR.w hrb ?_ ?_
    · intro V hV π hπ hPπ
      simpa only [Functor.map_comp, Category.assoc] using
        hlU V hV (π ≫ r) (by simpa only [Functor.map_comp, Category.assoc] using hπ)
          (by simpa only [Functor.map_comp, Category.assoc] using hPπ)
    · intro V hV π hπ hPπ
      simpa only [Functor.map_comp, Category.assoc] using
        hlU V hV (π ≫ s) (by simpa only [Functor.map_comp, Category.assoc] using hπ)
          (by simpa only [Functor.map_comp, Category.assoc] using hPπ)
  obtain ⟨l, hl, -⟩ := existsUnique_hom_of_atlas_invariant B S hS hF hW b hsurj
    ((isEtale_iff_presheaf_of_yoneda B S hS b).1 hb) lU hcompat
  refine ⟨l, fun T hT r hrb hPrb => ?_⟩
  rw [hl]
  exact hlU T hT r hrb hPrb

end Glue

/-- **A family of morphisms to an algebraic space `Y`, given on a cofinal class of affine étale
charts of a sheaf `F` and compatible up to 2-isomorphism, glues to a morphism `F ⟶ Y`.**

This is `AlgebraicGeometry.Space.exists_hom_of_chartHoms_of_cofinal` with its compatibility
hypothesis — an equality `h_r ≫ k U b = k T (h_r ≫ b)` of two morphisms `h_T ⟶ Y` — replaced by a
2-isomorphism of the morphisms of small étale ringed topoi the two induce.  The replacement is
`AlgebraicGeometry.Space.eq_of_twoIso_yoneda`, i.e. [Stacks Project, Tag 04M6], so nothing is
assumed and no generality is lost.

Compared with `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso`, the family is required
only on the charts selected by a cofinal `P`.  That is what a recovery theorem can actually
supply: the morphism over an affine chart `T` is built from a lift of `T` through one member of a
covering family of the target, and only a cover of `T` admits such a lift. -/
theorem exists_hom_of_chartHoms_twoIso_of_cofinal {Y : AlgebraicSpaces B S hS}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hP : IsCofinalChartFamily B S hS P)
    (k : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
      ∀ b : yoneda.obj T ⟶ F, IsEtale B S hS b → P T b → (yoneda.obj T ⟶ Y.1))
    (hk : ∀ (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (hU : IsAffineOver B S hS U) (r : T ⟶ U) (b : yoneda.obj U ⟶ F)
      (hb : IsEtale B S hS b) (hrb : IsEtale B S hS (yoneda.map r ≫ b))
      (hPb : P U b) (hPrb : P T (yoneda.map r ≫ b)),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS
          (ObjectProperty.homMk (yoneda.map r ≫ k U hU b hb hPb) :
            (schemeSpace T : AlgebraicSpaces B S hS) ⟶ Y))
        (smallEtaleRingedToposHom B S hS
          (ObjectProperty.homMk (k T hT (yoneda.map r ≫ b) hrb hPrb) :
            (schemeSpace T : AlgebraicSpaces B S hS) ⟶ Y))))
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ F) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : F ⟶ Y.1, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (r : T ⟶ U)
      (hrb : IsEtale B S hS (yoneda.map r ≫ b)) (hPrb : P T (yoneda.map r ≫ b)),
      yoneda.map r ≫ b ≫ l = k T hT (yoneda.map r ≫ b) hrb hPrb :=
  exists_hom_of_chartHoms_of_cofinal B S hS Y.property.isSheaf k
    (fun T U hT hU r c hc hrc hPc hPrc =>
      eq_of_twoIso_yoneda B S hS _ _ (hk T U hT hU r c hc hrc hPc hPrc).some)
    hP hF U b hb hsurj

end AlgebraicGeometry.Space

end
