module

public import StacksFrontier.AlgebraicGeometry.InvertibleFiniteDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.QuasiFiniteAlongExceptionalCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exceptional curve lies in the isomorphism locus

This file carries out the last steps of the proof of
[Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) (Resolution of Surfaces, Lemma
54.17.1) on top of the quasi-finiteness along the exceptional curve established in
`QuasiFiniteAlongExceptionalCurve.lean`.

The source's argument runs as follows. Let `f : X ⟶ Y` be a proper birational morphism of
integral Noetherian schemes regular of dimension two, let `V ⊆ Y` be the maximal open over which
`f` is an isomorphism, and pick a closed point `y ∉ V` (step 1). Blow up `y` to get
`b : Y' ⟶ Y`, dominate the resulting rational map by a chain of blowups (step 2,
[Stacks, Tag 0C5H]), and reduce to the case of a single blowup `π : X' ⟶ X` at a closed point
`x` above `y`, with exceptional curve `E ⊆ X'`. The composite `E ⟶ X' ⟶ Y'` lands in the
exceptional curve `E' ⊆ Y'` of `b`, and either it is constant — in which case
[Stacks, Tag 0C5J] contracts `E` and factors `f` through `b` — or it is an isomorphism onto `E'`
(step 3), and then the conormal comparison map is nonzero, `f'` is unramified and hence
quasi-finite along `E` (step 4), and item (4) of [Stacks, Tag 0BFP] forces `y ∈ V` against its
choice (step 5).

## Main results

* `Stacks.ResolutionOfSurfaces.exists_isClosed_singleton_notMem_isomorphism_open` — step 1: a
  morphism onto a quasi-compact scheme which is not an isomorphism omits a closed point from the
  maximal open over which it is an isomorphism.
* `Stacks.ResolutionOfSurfaces.mem_isomorphismLocus_of_exceptionalCurvePair` — step 5(i): in the
  situation of `Stacks.ResolutionOfSurfaces.quasiFiniteAt_of_exceptionalCurvePair`, every point
  of the exceptional curve `E' ⊆ Y'` lies in the maximal open over which `f'` is an isomorphism.
* `Stacks.ResolutionOfSurfaces.subsingleton_fiber_of_isIso_restrict` — step 5(ii), the fibre
  half: over a point of an open on which a morphism restricts to an isomorphism there is at most
  one point.
* `Stacks.ResolutionOfSurfaces.mem_isomorphismLocus_of_finite_fiber` — step 5(iii): the maximal
  isomorphism open of a proper birational morphism onto a regular Noetherian scheme contains
  every point with a finite fibre.
* `Stacks.ResolutionOfSurfaces.false_of_exceptionalCurvePair_of_notMem_isomorphismLocus` —
  steps 5(i)–(iii) assembled: **the second alternative of step 3 is impossible.**
* `Stacks.ResolutionOfSurfaces.exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve` —
  the first alternative of step 3 produces the factorization of `f` through `b`, by
  [Stacks, Tag 0C5J].
* `Stacks.ResolutionOfSurfaces.exists_comp_eq_of_exceptionalCurveDichotomy` — steps 3 to 5
  together: granted the source's dichotomy, `f` factors through the blowup `b : Y' ⟶ Y`.
* `Stacks.ResolutionOfSurfaces.exists_maximal_isomorphism_open` — the maximal open over which a
  morphism is an isomorphism exists, being an isomorphism being Zariski local on the target.

## What is and is not proved

Everything in this file is proved outright, with the single exception of
`Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow`, the second arrow of
[Stacks, Tag 067L], which is threaded through from
`QuasiFiniteAlongExceptionalCurve.lean` exactly as in the other files of this directory. It is
quantified over every triangle of immersions of schemes and mentions none of the objects of Tag
0C5R, so it is not a disguised form of anything proved here.

**No `@[stacks 0C5R]` attribute is placed in this file**, because the statement of that tag —
`Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups Y Set.univ X f` — is not reached. What is
still missing, on top of what this file provides, is exactly the `step` hypothesis of
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_pointBlowupStep`, and for that:

* the induction on the length of the chain of [Stacks, Tag 0C5H] which reduces step 2 to a
  single blowup `π : X' ⟶ X`, together with the three hypotheses that the library's form of that
  tag, `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap`, carries
  ([Stacks, Tag 0AGT], [Stacks, Tag 0AHI] and the [Stacks, Tag 0BX7] plus [Stacks, Tag 081T]
  reduction);
* the data this file consumes as hypotheses, produced from that reduction: that the exceptional
  curve of the blowup of a regular surface at a closed point is an exceptional curve of the first
  kind presented as `𝐏¹_k` (the globalization of [Stacks, Tag 0AGR] and [Stacks, Tag 0C5K]), and
  that the fibre of `b` over `y` is its exceptional curve;
* the dichotomy of step 3 itself, that a morphism `E ⟶ E'` of copies of `𝐏¹_k` is either
  constant or an isomorphism, for which
  `Stacks.ResolutionOfSurfaces.isIso_of_isFinite_of_isBirational_of_iso_projectiveLineProj` is
  the non-constant half;
* the bookkeeping for which the source says "some details omitted": that the measure `μ` of the
  factor `ψ` is strictly smaller than that of `f`.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **A morphism which is an isomorphism over an open subset has at most one point in each
fibre over that open.** -/
public theorem subsingleton_fiber_of_isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : IsIso (f ∣_ V)) {y : Y} (hy : y ∈ V) :
    (f ⁻¹' {y} : Set X).Subsingleton := by
  intro a ha b hb
  have hay : f a = y := ha
  have hby : f b = y := hb
  have ha' : a ∈ f ⁻¹' (V : Set Y) := by rwa [Set.mem_preimage, hay]
  have hb' : b ∈ f ⁻¹' (V : Set Y) := by rwa [Set.mem_preimage, hby]
  have hinj : Function.Injective ((V : Set Y).restrictPreimage f) :=
    morphismRestrict_base f V ▸ (Scheme.homeoOfIso (asIso (f ∣_ V))).injective
  have key : ((V : Set Y).restrictPreimage f) ⟨a, ha'⟩
      = ((V : Set Y).restrictPreimage f) ⟨b, hb'⟩ :=
    Subtype.ext (by simpa using hay.trans hby.symm)
  exact congrArg Subtype.val (hinj key)

/-- A morphism which is an isomorphism over an open subset has finite fibres over that open. -/
public theorem finite_fiber_of_isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : IsIso (f ∣_ V)) {y : Y} (hy : y ∈ V) :
    (f ⁻¹' {y} : Set X).Finite :=
  (subsingleton_fiber_of_isIso_restrict f V hV hy).finite

/-- **The maximal open over which a morphism is an isomorphism exists**: the property of being
an isomorphism is Zariski local on the target, so the supremum of all opens over which the
restriction is an isomorphism is again such an open. -/
@[sga "3 VIB 2.1" "special case"]
public theorem exists_maximal_isomorphism_open {X Y : Scheme.{u}} (f : Y ⟶ X) :
    ∃ U : X.Opens, IsGreatest {V : X.Opens | IsIso (f ∣_ V)} U := by
  let U : X.Opens := sSup {V : X.Opens | IsIso (f ∣_ V)}
  refine ⟨U, ?_, fun V hV => le_sSup hV⟩
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.mp x.2
  refine ⟨U.ι ⁻¹ᵁ V, hxV, ?_⟩
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))]
  show IsIso (f ∣_ U.ι ''ᵁ U.ι ⁻¹ᵁ V)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr (le_sSup hV)]
  exact hV

/-! ### Step 1: a closed point outside the isomorphism locus -/

/-- **Step 1 of [Stacks, Tag 0C5R]: the choice of the point to blow up.** If a morphism onto a
quasi-compact scheme is not an isomorphism, then the maximal open over which it is an
isomorphism omits a closed point: its complement is a nonempty closed subset of a quasi-compact
Kolmogorov space, so it contains a point closed in the ambient scheme. -/
public theorem exists_isClosed_singleton_notMem_isomorphism_open {X Y : Scheme.{u}}
    [CompactSpace Y] (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsGreatest { V : Y.Opens | IsIso (f ∣_ V) } U) (hiso : ¬ IsIso f) :
    ∃ y : Y, IsClosed ({y} : Set Y) ∧ y ∉ U := by
  have hUne : ((U : Set Y))ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro htop
    have hUtop : U = ⊤ := TopologicalSpace.Opens.ext (by simpa using htop)
    have : IsIso (f ∣_ (⊤ : Y.Opens)) := hUtop ▸ hU.1
    exact hiso
      (Stacks.AlgebraicGeometry.InvertibleFiniteDescent.isIso_of_isIso_morphismRestrict_top f)
  obtain ⟨y, hyU, hyclosed⟩ := (isClosed_compl_iff.mpr U.2).exists_closed_singleton hUne
  exact ⟨y, hyclosed, hyU⟩

/-! ### Step 5(iii): a finite fibre over a regular point lies in the isomorphism locus -/

/-- **Stacks Project, Tag 0BFP for a regular target.** The maximal open over which a proper
birational morphism with reduced source is an isomorphism contains every point with a finite
fibre, the target being regular: a regular local ring is a normal domain. -/
@[ega "III 4.4.9" "special case"]
public theorem mem_isomorphismLocus_of_finite_fiber {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian Y] (f : X ⟶ Y) [IsProper f] [IsReduced X]
    (hf : IsBirational f) (U : Y.Opens) (hU : IsGreatest { V : Y.Opens | IsIso (f ∣_ V) } U)
    (hY : IsRegular Y) (y : Y) (hfin : (f ⁻¹' {y} : Set X).Finite) : y ∈ U := by
  obtain ⟨_, _⟩ := (isNormal_iff_stalk_normal Y).mp (isNormal_of_isRegular Y hY) y
  exact mem_maximal_isomorphism_open_of_exists_isIso_restrict f U hU y
    (exists_isIso_restrict_of_finite_fiber_of_normal f hf y hfin)

/-! ### Step 5(i): the exceptional curve lies in the isomorphism locus -/

/-- A morphism compatible with two isomorphisms out of the same scheme is an isomorphism. -/
private theorem isIso_of_hom_comp_eq {A B C : Scheme.{u}} (e : A ≅ B) (e' : A ≅ C) (g : B ⟶ C)
    (he : e.hom ≫ g = e'.hom) : IsIso g := by
  have h1 : e.inv ≫ e'.hom = g := by rw [← he, Iso.inv_hom_id_assoc]
  exact h1 ▸ inferInstance

/-- If `g` is an isomorphism and `ι ≫ f' = g ≫ ι'`, then every point `ι' w` is the image under `f'`
of a point `ι z`. -/
private theorem exists_apply_eq_of_isIso_of_comp_eq {A B X' Y' : Scheme.{u}} (g : A ⟶ B)
    [IsIso g] (ι : A ⟶ X') (ι' : B ⟶ Y') (f' : X' ⟶ Y') (h : ι ≫ f' = g ≫ ι') (w : B) :
    ∃ z : A, f' (ι z) = ι' w := by
  obtain ⟨z, hz⟩ := (Scheme.homeoOfIso (asIso g)).surjective w
  refine ⟨z, ?_⟩
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact congrArg ι' hz

/-- **Step 5(i) of [Stacks, Tag 0C5R]: the exceptional curve of the target lies in the maximal
open over which the morphism is an isomorphism.** In the situation of
`Stacks.ResolutionOfSurfaces.quasiFiniteAt_of_exceptionalCurvePair` — a morphism `f' : X' ⟶ Y'`
locally of finite type, exceptional curves of the first kind `E ⊆ X'` and `E' ⊆ Y'` with
compatible presentations as `𝐏¹_k`, a morphism `g : E ⟶ E'` over them and an immersion
`j : E ⟶ Y'` equal both to `i ≫ f'` and to `g ≫ i'`, and a nonzero conormal comparison map — the
morphism `f'` is quasi-finite at every point of `E`, so item (4) of [Stacks, Tag 0BFP] applies at
every point of `E'`, the target being regular and hence normal. -/
public theorem mem_isomorphismLocus_of_exceptionalCurvePair (k : Type u) [Field k]
    (hsec : ConormalSequenceSecondArrow.{u}) {X' Y' : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian Y'] [IsReduced X'] (f' : X' ⟶ Y') [IsProper f']
    (hf' : IsBirational f') (hY' : IsRegular Y')
    (U' : Y'.Opens) (hU' : IsGreatest { V : Y'.Opens | IsIso (f' ∣_ V) } U')
    {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    {e : projectiveLineProj k ≅ D.subscheme} {e' : projectiveLineProj k ≅ D'.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (hE' : D'.IsExceptionalCurveOfFirstKind k e')
    (g : D.subscheme ⟶ D'.subscheme) (he : e.hom ≫ g = e'.hom)
    (j : D.subscheme ⟶ Y') [IsImmersion j] (hj : g ≫ D'.subschemeι = j)
    (h : D.subschemeι ≫ f' = j)
    (hne : Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      (Stacks.Immersion.toShHom_square (h.trans hj.symm)) ≠ 0)
    (w : D'.subscheme) : D'.subschemeι w ∈ U' := by
  have := isIso_of_hom_comp_eq e e' g he
  obtain ⟨z, hy⟩ := exists_apply_eq_of_isIso_of_comp_eq g D.subschemeι D'.subschemeι f'
    (h.trans hj.symm) w
  obtain ⟨_, _⟩ :=
    (isNormal_iff_stalk_normal Y').mp (isNormal_of_isRegular Y' hY') (D'.subschemeι w)
  exact mem_maximal_isomorphism_open_of_quasiFiniteAt_of_isNormal f' hf' U' hU'
    (D'.subschemeι w) (IsNormalRing.of_isIntegrallyClosed _) (D.subschemeι z) hy
    ⟨AlgebraicGeometry.finiteTypeAt_of_locallyOfFiniteType f' _,
      quasiFiniteAt_of_exceptionalCurvePair k hsec f' hE hE' g he j hj h hne z⟩

/-! ### Steps 5(ii) and 5(iii): the contradiction -/

/-- **Steps 5(ii) and 5(iii) of [Stacks, Tag 0C5R]: the second alternative of the source's
argument is impossible.**

The situation is the one the source arrives at. Downstairs, `f : X ⟶ Y` is a proper birational
morphism with `Y` regular, `U ⊆ Y` is the maximal open over which `f` is an isomorphism, and `y`
is a point outside `U`. Upstairs, `b : Y' ⟶ Y` and `π : X' ⟶ X` are morphisms fitting in a
commuting square with a proper birational `f' : X' ⟶ Y'`, with `π` surjective; `E ⊆ X'` and
`E' ⊆ Y'` are exceptional curves of the first kind with compatible presentations as `𝐏¹_k`, the
fibre of `b` over `y` is contained in `E'`, and `π` contracts `E` to the single point `x`.
Finally `g : E ⟶ E'` is a morphism over the two presentations whose conormal comparison map is
nonzero, which is the second alternative of the source's step 3.

Then: `f'` is quasi-finite along `E`, so by item (4) of [Stacks, Tag 0BFP] the curve `E'` lies
in the maximal open `U'` over which `f'` is an isomorphism (step 5(i)); hence each fibre of `f'`
over a point of `E'` is a single point, so the fibre of `f` over `y` is the single point `x`
(step 5(ii)); hence by item (4) of [Stacks, Tag 0BFP] again, now on `Y`, the point `y` lies in
`U` (step 5(iii)) — contradicting the choice of `y`. -/
public theorem false_of_exceptionalCurvePair_of_notMem_isomorphismLocus
    (k : Type u) [Field k] (hsec : ConormalSequenceSecondArrow.{u})
    {X Y X' Y' : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y] [IsReduced X]
    [AlgebraicGeometry.IsNoetherian Y'] [IsReduced X']
    (f : X ⟶ Y) [IsProper f] (hf : IsBirational f) (hY : IsRegular Y)
    (U : Y.Opens) (hU : IsGreatest { V : Y.Opens | IsIso (f ∣_ V) } U) {y : Y} (hyU : y ∉ U)
    (b : Y' ⟶ Y) (π : X' ⟶ X) (f' : X' ⟶ Y') [IsProper f'] (hf' : IsBirational f')
    (hY' : IsRegular Y') (hsq : f' ≫ b = π ≫ f) (hπ : Function.Surjective π.base)
    {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    {e : projectiveLineProj k ≅ D.subscheme} {e' : projectiveLineProj k ≅ D'.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (hE' : D'.IsExceptionalCurveOfFirstKind k e')
    (g : D.subscheme ⟶ D'.subscheme) (he : e.hom ≫ g = e'.hom)
    (j : D.subscheme ⟶ Y') [IsImmersion j] (hj : g ≫ D'.subschemeι = j)
    (h : D.subschemeι ≫ f' = j)
    (hne : Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      (Stacks.Immersion.toShHom_square (h.trans hj.symm)) ≠ 0)
    (hbfib : (b ⁻¹' {y} : Set Y') ⊆ Set.range D'.subschemeι.base)
    (x : X) (hx : ∀ t : D.subscheme, π (D.subschemeι t) = x) :
    False := by
  obtain ⟨U', hU'⟩ := exists_maximal_isomorphism_open f'
  have := isIso_of_hom_comp_eq e e' g he
  have hfib : (f ⁻¹' {y} : Set X) ⊆ {x} := by
    intro z hz
    obtain ⟨w, rfl⟩ := hπ z
    have hbw : f' w ∈ (b ⁻¹' {y} : Set Y') := by
      show b (f' w) = y
      rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
      exact hz
    obtain ⟨w₀, hw₀⟩ := hbfib hbw
    obtain ⟨t, h1⟩ := exists_apply_eq_of_isIso_of_comp_eq g D.subschemeι D'.subschemeι f'
      (h.trans hj.symm) w₀
    have h2 : w ∈ (f' ⁻¹' {D'.subschemeι w₀} : Set X') := hw₀.symm
    have heq : D.subschemeι t = w :=
      subsingleton_fiber_of_isIso_restrict f' U' hU'.1
        (mem_isomorphismLocus_of_exceptionalCurvePair k hsec f' hf' hY' U' hU' hE hE' g he j hj h
          hne w₀) h1 h2
    rw [Set.mem_singleton_iff, ← heq]
    exact hx t
  exact hyU (mem_isomorphismLocus_of_finite_fiber f hf U hU hY y
    ((Set.finite_singleton x).subset hfib))

/-! ### The factorization, once the curve collapses -/

/-- **The factorization of [Stacks, Tag 0C5R] through the blowup, once the exceptional curve
collapses.** Let `π : X' ⟶ X` be a contraction of the exceptional curve `E ⊆ X'` and let
`f' : X' ⟶ Y'` be a morphism with `f' ≫ b = π ≫ f`. If `f'` carries `E` to a single point of
`Y'`, then [Stacks, Tag 0C5J] factors `f'` as `π ≫ ψ`, and the factor `ψ : X ⟶ Y'` factors `f`
through `b`, that is `ψ ≫ b = f`: the morphism `f' ≫ b` also carries `E` to a single point, so
its factorization through the contraction is unique, and both `ψ ≫ b` and `f` are such a
factorization.

In [Stacks, Tag 0C5R] this is the conclusion of step 1 which the induction consumes: `f` factors
through the blowup `b : Y' ⟶ Y` of `Y` at the chosen closed point. -/
public theorem exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve
    {X X' Y Y' : Scheme.{u}} {D : X'.IdealSheafData} {π : X' ⟶ X}
    (hπ : IsContractionOfExceptionalCurve D π)
    (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y') (hsq : f' ≫ b = π ≫ f)
    (hconst : ∃ w : Y', ∀ z : D.subscheme, f' (D.subschemeι z) = w) :
    ∃ ψ : X ⟶ Y', π ≫ ψ = f' ∧ ψ ≫ b = f := by
  obtain ⟨w, hw⟩ := hconst
  obtain ⟨ψ, hψ, -⟩ :=
    existsUnique_comp_eq_of_isContractionOfExceptionalCurve D π hπ f' ⟨w, hw⟩
  refine ⟨ψ, hψ, ?_⟩
  obtain ⟨χ, -, huniq⟩ : ∃! χ : X ⟶ Y, π ≫ χ = f' ≫ b :=
    existsUnique_comp_eq_of_isContractionOfExceptionalCurve D π hπ (f' ≫ b)
      ⟨b w, fun z => by rw [Scheme.Hom.comp_apply, hw z]⟩
  exact (huniq (ψ ≫ b) (by change π ≫ ψ ≫ b = f' ≫ b; rw [← Category.assoc, hψ])).trans
    (huniq f hsq.symm).symm

/-! ### Steps 3 to 5 of Tag 0C5R: the factorization, from the dichotomy -/

/-- **Steps 3 to 5 of [Stacks, Tag 0C5R]: the factorization through the blowup.** Granted the
dichotomy of the source's step 3 — either the morphism `f'` carries the exceptional curve
`E ⊆ X'` to a single point of `Y'`, or there is a morphism `g : E ⟶ E'` onto the exceptional
curve of `Y'`, compatible with the presentations of both as `𝐏¹_k`, whose conormal comparison
map is nonzero — the morphism `f : X ⟶ Y` factors through `b : Y' ⟶ Y`.

The second alternative is impossible by
`Stacks.ResolutionOfSurfaces.false_of_exceptionalCurvePair_of_notMem_isomorphismLocus`: it makes
`f'` quasi-finite along `E`, hence puts the chosen point `y` in the isomorphism locus of `f`
against its choice. So the curve collapses, and
`Stacks.ResolutionOfSurfaces.exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve`
produces the factorization out of [Stacks, Tag 0C5J]. -/
public theorem exists_comp_eq_of_exceptionalCurveDichotomy
    (k : Type u) [Field k] (hsec : ConormalSequenceSecondArrow.{u})
    {X Y X' Y' : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y] [IsReduced X]
    [AlgebraicGeometry.IsNoetherian Y'] [IsReduced X']
    (f : X ⟶ Y) [IsProper f] (hf : IsBirational f) (hY : IsRegular Y)
    (U : Y.Opens) (hU : IsGreatest { V : Y.Opens | IsIso (f ∣_ V) } U) {y : Y} (hyU : y ∉ U)
    (b : Y' ⟶ Y) {π : X' ⟶ X} (f' : X' ⟶ Y') [IsProper f'] (hf' : IsBirational f')
    (hY' : IsRegular Y') (hsq : f' ≫ b = π ≫ f) (hπ : Function.Surjective π.base)
    {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    (hcontr : IsContractionOfExceptionalCurve D π)
    {e : projectiveLineProj k ≅ D.subscheme} {e' : projectiveLineProj k ≅ D'.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (hE' : D'.IsExceptionalCurveOfFirstKind k e')
    (hbfib : (b ⁻¹' {y} : Set Y') ⊆ Set.range D'.subschemeι.base)
    (x : X) (hx : ∀ t : D.subscheme, π (D.subschemeι t) = x)
    (hdich : (∃ w : Y', ∀ z : D.subscheme, f' (D.subschemeι z) = w) ∨
      ∃ (g : D.subscheme ⟶ D'.subscheme) (_ : e.hom ≫ g = e'.hom) (j : D.subscheme ⟶ Y')
        (_ : IsImmersion j) (hj : g ≫ D'.subschemeι = j) (h : D.subschemeι ≫ f' = j),
        Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
          (Stacks.Immersion.toShHom_square (h.trans hj.symm)) ≠ 0) :
    ∃ ψ : X ⟶ Y', π ≫ ψ = f' ∧ ψ ≫ b = f := by
  rcases hdich with hconst | ⟨g, he, j, _, hj, h, hne⟩
  · exact exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve hcontr f b f' hsq hconst
  · exact (false_of_exceptionalCurvePair_of_notMem_isomorphismLocus k hsec f hf hY U hU hyU b π
      f' hf' hY' hsq hπ hE hE' g he j hj h hne hbfib x hx).elim

end Stacks.ResolutionOfSurfaces

end
