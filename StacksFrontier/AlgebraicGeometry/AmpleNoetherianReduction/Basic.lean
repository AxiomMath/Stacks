module

public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Extension
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnionGlue
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleClosedImmersion.Converse
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackInvertible
public import Mathlib.RingTheory.KrullDimension.PID

/-!
# An ample invertible sheaf on a scheme whose reduction is a one-dimensional Noetherian scheme

[Stacks, Tag 09P0](https://stacks.math.columbia.edu/tag/09P0) is a remark attached to
[Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ):

> In fact, if `X` is a scheme whose reduction is a Noetherian separated scheme of dimension `1`,
> then `X` has an ample invertible sheaf.  The argument to prove this is the same as the proof of
> Proposition 09NZ except one uses Limits, Lemma 09MW instead of Cohomology of Schemes,
> Lemma 09MS.

Both halves of that remark are mathematics: an assertion, and a route.  This file carries the
route out.

## How the hypothesis differs from Tag 09NZ's

Tag 09NZ assumes `X` **itself** Noetherian, separated and of dimension at most one.  Here only
the reduction `X_red = (vanishingIdeal ⊤).subscheme` is assumed Noetherian, separated and of
dimension at most one.  That is strictly weaker, and
`Stacks.AmpleNoetherianReduction.isNoetherian_reduction`,
`isSeparated_reduction` and `topologicalKrullDim_reduction_le` prove it is weaker by deriving
all three of the hypotheses below from Tag 09NZ's.  The gap is real: a scheme whose reduction is
Noetherian need not be locally Noetherian — the nilpotents are unconstrained — so no Noetherian
hypothesis on `X` is available anywhere in the argument.

## The route, and what each step costs

Writing `i : X_red ⟶ X` for the reduction's closed immersion, which is surjective:

* `X_red` is reduced, Noetherian, separated and of dimension at most one, so
  [Tag 09NX](https://stacks.math.columbia.edu/tag/09NX) —
  `Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one` —
  gives an ample invertible `L` on `X_red`.
* `i` is a homeomorphism on underlying spaces, so `X` has Noetherian underlying space and
  dimension at most one.  That is *all* that
  [Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) —
  `Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one` —
  asks of the ambient scheme, so `L` lifts to an invertible `M` on `X` with `i^* M ≅ L`.  This
  is the step where Tag 09NZ's Noetherian hypothesis on `X` would have been spent and is not.
* `i^* M` is ample, and ampleness has to descend along `i` to `M`.  This is the only step that
  needs more than is proved in this repository, and it is exactly the step the remark singles
  out: Tag 09NZ uses [Tag 09MS](https://stacks.math.columbia.edu/tag/09MS), whose converse half
  carries `[IsLocallyNoetherian X]`, and the remark replaces it by
  [Tag 09MW](https://stacks.math.columbia.edu/tag/09MW), which has no Noetherian hypothesis
  because the source writes `X` as a directed limit of finite-type `ℤ`-schemes.  That limit
  argument is not carried out in this repository:
  `Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback`, the in-tree converse half of
  Tag 09MW, still carries `[IsLocallyNoetherian X]` together with the cohomological lift
  `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`, and `[IsLocallyNoetherian X]` is not
  available here.

So the converse half of Tag 09MW is carried as the named hypothesis
`Stacks.AmpleNoetherianReduction.AmpleDescendsAlongThickening`, quantified over all schemes, all
surjective closed immersions between them and all invertible modules — it is the *statement* of
that half of Tag 09MW, not this theorem's conclusion in disguise, and it mentions no particular
scheme.  This follows the pattern of
`Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion` and
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`, the two hypotheses under which the converse
of Tag 09MS is proved in this tree.

## Which ampleness predicate

`Stacks.Ample.IsAmple`, the [Tag 01PS](https://stacks.math.columbia.edu/tag/01PS) predicate of
`../AmpleWire/Basic.lean`, over which the whole 09MS/09MW cluster is written, with invertibility
as `Stacks.Ample.IsInvertibleModule` and `i^* M` as
`(RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj M` — the spelling the
in-tree statements of Tags 09MS and 09MW use.  Tag 09NX produces the repository's second Tag
01PS predicate, `AlgebraicGeometry.Scheme.Modules.IsAmple`; the two are interchangeable by
`Stacks.AmpleBridge.isAmple_iff_isAmple`, which is what the proof below crosses, and
`Stacks.AmpleNoetherianReduction.exists_isAmple_modules_of_reduction` restates the conclusion
over the second predicate so that consumers of Tags 09NX and 09NZ can use it directly.  No third
predicate is introduced, and the reduction is written with the repository's own spelling
`(AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X))`
`.subscheme`, the one the Tag 09NZ proof and `../Morphisms/Fibres/Reduced.lean` use.

## Main results

* `Stacks.AmpleNoetherianReduction.AmpleDescendsAlongThickening`: the converse half of
  Tag 09MW, isolated as a hypothesis.
* `Stacks.AmpleNoetherianReduction.ampleDescendsAlongThickening_of_chevalley_of_sectionsLift`:
  that hypothesis reduced to two named inputs — Chevalley's criterion for a surjective closed
  immersion with no Noetherian hypothesis, and the cohomological lift
  `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`.
* `Stacks.AmpleNoetherianReduction.surjective_subschemeι_reduction`,
  `isHomeomorph_base_subschemeι_reduction`: the reduction's immersion is surjective, hence a
  homeomorphism of underlying spaces.
* `Stacks.AmpleNoetherianReduction.noetherianSpace_of_reduction`,
  `topologicalKrullDim_le_of_reduction`: the two topological facts about `X` that Tag 09NY needs,
  from the hypotheses on `X_red` alone.
* `Stacks.AmpleNoetherianReduction.exists_isAmple_of_reduction`: **[Stacks, Tag 09P0]**, granted
  `AmpleDescendsAlongThickening`.
* `Stacks.AmpleNoetherianReduction.exists_isAmple_modules_of_reduction`: the same over the second
  Tag 01PS predicate.
* `Stacks.AmpleNoetherianReduction.isNoetherian_reduction`, `isSeparated_reduction`,
  `topologicalKrullDim_reduction_le`: Tag 09NZ's hypotheses imply Tag 09P0's, so the hypothesis
  class below contains Tag 09NZ's.
* `Stacks.AmpleNoetherianReduction.reduction_hypotheses_affineLine`: the three hypotheses on the
  reduction discharged at an explicit scheme, the affine line over a field, and
  `exists_isAmple_affineLine`, the theorem instantiated there.

## References

* [Stacks Project, Tag 09P0](https://stacks.math.columbia.edu/tag/09P0)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.Scheme.IdealSheafData
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleNoetherianReduction

/-- **The converse half of [Stacks, Tag 09MW], isolated as a hypothesis.** For every surjective
closed immersion `i : Z ⟶ X` of schemes and every invertible `𝒪_X`-module `L`, ampleness of
`i^* L` gives ampleness of `L`.

This is the statement of that half of Tag 09MW and nothing more: no Noetherian hypothesis
anywhere, which is what the source's limit argument removes from
[Stacks, Tag 09MS], and surjectivity of a closed immersion is the source's condition that `i`
induce a homeomorphism of underlying topological spaces.  The in-tree converse,
`Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback`, still carries
`[IsLocallyNoetherian X]` and the cohomological lift
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`, so it does not discharge this. -/
def AmpleDescendsAlongThickening : Prop :=
  ∀ (Z X : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
      (L : X.Modules) [IsInvertibleModule X L],
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) → IsAmple X L

/-- **The carried hypothesis reduces to two named inputs.** Granted Chevalley's criterion for a
surjective closed immersion with **no** Noetherian hypothesis, and the cohomological lift
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` for every surjective closed immersion and
every invertible module, ampleness descends along a surjective closed immersion.

So `Stacks.AmpleNoetherianReduction.AmpleDescendsAlongThickening` is not a black box: it is
exactly as far from proved as the converse of [Stacks, Tag 09MS] is, with the Noetherian
hypothesis removed from both of that converse's inputs — which is what the limit argument of
[Stacks, Tag 09MW] exists to do.  The argument is the one
`Stacks.AmpleClosedImmersion.isAmple_of_isAmple_modulePullback` runs, repeated here because that
theorem spends `[IsLocallyNoetherian X]` on its appeal to
`Stacks.AmpleClosedImmersion.isAffineOpen_of_isAffineOpen_preimage`, and
`[IsLocallyNoetherian X]` is the one hypothesis [Stacks, Tag 09P0] does not have; `hchev` is
applied to the restriction `i ∣_ X_{t'}` in its place. -/
theorem ampleDescendsAlongThickening_of_chevalley_of_sectionsLift
    (hchev : ∀ (A B : Scheme.{u}) (j : A ⟶ B), IsClosedImmersion j → Surjective j →
      IsAffine A → IsAffine B)
    (hlift : ∀ (Z X : Scheme.{u}) (i : Z ⟶ X) (L : X.Modules) (_ : IsInvertibleModule X L),
      Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L) :
    AmpleDescendsAlongThickening.{u} := by
  intro Z X i _ _ L _ h
  refine (isAmple_iff_forall_affine_nonvanishingOpen X L).mpr
    ⟨Stacks.AmpleClosedImmersion.compactSpace_of_surjective i inferInstance h.compactSpace,
      fun x => ?_⟩
  obtain ⟨z, hz⟩ := i.surjective x
  obtain ⟨n, hn, t, haff, hzt⟩ :=
    IsAmple.exists_affine_nonvanishingOpen Z (Stacks.AmpleLocallyClosed.pullbackModule i L) h z
  obtain ⟨m, hm, t', he⟩ := hlift Z X i L inferInstance n hn t haff
  have hpre : IsAffineOpen (i ⁻¹ᵁ powNonvanishingOpen X L m t') := by rw [he]; exact haff
  have hzmem : z ∈ i ⁻¹ᵁ powNonvanishingOpen X L m t' := by rw [he]; exact hzt
  refine ⟨m, hm, t', ?_, hz ▸ hzmem⟩
  exact hchev _ _ (i ∣_ powNonvanishingOpen X L m t')
    (IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _)
    (IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance _) hpre

/-! ### The reduction, and the two topological facts Tag 09NY needs -/

/-- **The closed immersion of the reduction is surjective**: its image is the support of
`vanishingIdeal ⊤`, which is all of `X`. -/
theorem surjective_subschemeι_reduction (X : Scheme.{u}) :
    Surjective (vanishingIdeal (⊤ : Closeds X)).subschemeι := by
  refine ⟨fun x => ?_⟩
  have h : Set.range (vanishingIdeal (⊤ : Closeds X)).subschemeι = (⊤ : Closeds X) :=
    range_subschemeι_vanishingIdeal (X := X) (⊤ : Closeds X)
  have hx : x ∈ Set.range (vanishingIdeal (⊤ : Closeds X)).subschemeι := by
    rw [h]; trivial
  exact hx

/-- **The closed immersion of the reduction is a homeomorphism of underlying spaces.** A closed
immersion is a closed embedding, and this one is surjective. -/
theorem isHomeomorph_base_subschemeι_reduction (X : Scheme.{u}) :
    IsHomeomorph (vanishingIdeal (⊤ : Closeds X)).subschemeι.base :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(vanishingIdeal (⊤ : Closeds X)).subschemeι.isClosedEmbedding.isEmbedding,
      (surjective_subschemeι_reduction X).1⟩

/-- **A scheme whose reduction has Noetherian underlying space has Noetherian underlying
space.** The two spaces are homeomorphic. -/
theorem noetherianSpace_of_reduction (X : Scheme.{u})
    [NoetherianSpace (vanishingIdeal (⊤ : Closeds X)).subscheme] : NoetherianSpace X :=
  ((isHomeomorph_base_subschemeι_reduction X).homeomorph _).symm.isInducing.noetherianSpace

/-- **The dimension of a scheme is the dimension of its reduction.** -/
theorem topologicalKrullDim_reduction_eq (X : Scheme.{u}) :
    topologicalKrullDim ((vanishingIdeal (⊤ : Closeds X)).subscheme : Type u) =
      topologicalKrullDim (X : Type u) :=
  IsHomeomorph.topologicalKrullDim_eq _ (isHomeomorph_base_subschemeι_reduction X)

/-- **A scheme whose reduction has dimension at most one has dimension at most one.** -/
theorem topologicalKrullDim_le_of_reduction (X : Scheme.{u})
    (hdim : topologicalKrullDim ((vanishingIdeal (⊤ : Closeds X)).subscheme : Type u) ≤ 1) :
    topologicalKrullDim (X : Type u) ≤ 1 :=
  (topologicalKrullDim_reduction_eq X) ▸ hdim

/-! ### Tag 09P0 -/

/-- **[Stacks, Tag 09P0].** A scheme whose reduction is a Noetherian separated scheme of
dimension at most one has an ample invertible sheaf, granted the converse half of
[Stacks, Tag 09MW].

The hypotheses are on the reduction only; `X` itself is not assumed Noetherian, which is exactly
what distinguishes this from [Stacks, Tag 09NZ] and what forces Tag 09MW in place of
[Stacks, Tag 09MS]. -/
@[stacks 09P0 "granted the converse half of Tag 09MW as `AmpleDescendsAlongThickening`"]
theorem exists_isAmple_of_reduction (X : Scheme.{u})
    (hdesc : AmpleDescendsAlongThickening.{u})
    [IsNoetherian (vanishingIdeal (⊤ : Closeds X)).subscheme]
    [(vanishingIdeal (⊤ : Closeds X)).subscheme.IsSeparated]
    (hdim : topologicalKrullDim ((vanishingIdeal (⊤ : Closeds X)).subscheme : Type u) ≤ 1) :
    ∃ (L : X.Modules) (hL : IsInvertibleModule X L), @IsAmple X L hL := by
  have hsurj : Surjective (vanishingIdeal (⊤ : Closeds X)).subschemeι :=
    surjective_subschemeι_reduction X
  have hdimX : topologicalKrullDim (X : Type u) ≤ 1 := topologicalKrullDim_le_of_reduction X hdim
  have : NoetherianSpace X := noetherianSpace_of_reduction X
  obtain ⟨L, hL, hLample⟩ :=
    Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      (vanishingIdeal (⊤ : Closeds X)).subscheme hdim
  have hLinv : IsInvertibleModule (vanishingIdeal (⊤ : Closeds X)).subscheme L := hL
  obtain ⟨M, hM, he⟩ :=
    Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one
      X (vanishingIdeal (⊤ : Closeds X)).subscheme
      (vanishingIdeal (⊤ : Closeds X)).subschemeι hdimX L
  have hMinv : IsInvertibleModule X M := hM
  obtain ⟨e⟩ := he
  have hPinv : IsInvertibleModule (vanishingIdeal (⊤ : Closeds X)).subscheme
      ((modulePullback (vanishingIdeal (⊤ : Closeds X)).subschemeι.toLRSHom.toShHom).obj M) :=
    RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ M
  have hPample : AlgebraicGeometry.Scheme.Modules.IsAmple
      (vanishingIdeal (⊤ : Closeds X)).subscheme
      ((modulePullback (vanishingIdeal (⊤ : Closeds X)).subschemeι.toLRSHom.toShHom).obj M) :=
    AlgebraicGeometry.Scheme.Modules.isAmple_of_iso e.symm hLample
  exact ⟨M, hM, hdesc _ X (vanishingIdeal (⊤ : Closeds X)).subschemeι M
    ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr hPample)⟩

/-- **[Stacks, Tag 09P0] over the second [Stacks, Tag 01PS] predicate.** The same statement with
`AlgebraicGeometry.Scheme.Modules.IsAmple` in place of `Stacks.Ample.IsAmple`, crossed by
`Stacks.AmpleBridge.isAmple_iff_isAmple`.  This is the spelling in which
[Stacks, Tag 09NX] and [Stacks, Tag 09NZ] state that a scheme has an ample invertible sheaf. -/
theorem exists_isAmple_modules_of_reduction (X : Scheme.{u})
    (hdesc : AmpleDescendsAlongThickening.{u})
    [IsNoetherian (vanishingIdeal (⊤ : Closeds X)).subscheme]
    [(vanishingIdeal (⊤ : Closeds X)).subscheme.IsSeparated]
    (hdim : topologicalKrullDim ((vanishingIdeal (⊤ : Closeds X)).subscheme : Type u) ≤ 1) :
    ∃ (L : X.Modules) (_ : IsInvertibleModule X L),
      AlgebraicGeometry.Scheme.Modules.IsAmple X L :=
  have ⟨L, hL, hample⟩ := exists_isAmple_of_reduction X hdesc hdim
  ⟨L, hL, (Stacks.AmpleBridge.isAmple_iff_isAmple X L).mp hample⟩

/-! ### The hypotheses are weaker than Tag 09NZ's, and are satisfiable -/

/-- **The reduction of a Noetherian scheme is Noetherian.** -/
theorem isNoetherian_reduction (X : Scheme.{u}) [IsNoetherian X] :
    IsNoetherian (vanishingIdeal (⊤ : Closeds X)).subscheme :=
  StacksTag09NX.isNoetherian_subscheme _

/-- **The reduction of a separated scheme is separated.** -/
theorem isSeparated_reduction (X : Scheme.{u}) [X.IsSeparated] :
    (vanishingIdeal (⊤ : Closeds X)).subscheme.IsSeparated :=
  StacksTag09NX.isSeparated_of_isClosedImmersion (vanishingIdeal (⊤ : Closeds X)).subschemeι

/-- **The reduction of a scheme of dimension at most one has dimension at most one.** -/
theorem topologicalKrullDim_reduction_le (X : Scheme.{u})
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    topologicalKrullDim ((vanishingIdeal (⊤ : Closeds X)).subscheme : Type u) ≤ 1 :=
  (topologicalKrullDim_reduction_eq X).trans_le hdim

/-- **The affine line over a field satisfies the hypotheses of [Stacks, Tag 09P0].** Its
coordinate ring is a Noetherian principal ideal ring, so the scheme is Noetherian, affine hence
separated, and of Krull dimension at most one; the three facts pass to the reduction. -/
theorem reduction_hypotheses_affineLine (K : Type u) [Field K] :
    IsNoetherian
        (vanishingIdeal (⊤ : Closeds (Spec (CommRingCat.of (Polynomial K))))).subscheme ∧
      (vanishingIdeal
          (⊤ : Closeds (Spec (CommRingCat.of (Polynomial K))))).subscheme.IsSeparated ∧
      topologicalKrullDim
        ((vanishingIdeal
          (⊤ : Closeds (Spec (CommRingCat.of (Polynomial K))))).subscheme : Type u) ≤ 1 := by
  have hdim : topologicalKrullDim (Spec (CommRingCat.of (Polynomial K)) : Type u) ≤ 1 := by
    have h : topologicalKrullDim (PrimeSpectrum (Polynomial K)) = ringKrullDim (Polynomial K) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (Polynomial K)
    have hle : ringKrullDim (Polynomial K) ≤ (1 : ℕ) :=
      Ring.krullDimLE_iff.mp inferInstance
    have : topologicalKrullDim (PrimeSpectrum (Polynomial K)) ≤ 1 := by
      rw [h]; exact_mod_cast hle
    exact this
  exact ⟨isNoetherian_reduction _, isSeparated_reduction _,
    topologicalKrullDim_reduction_le _ hdim⟩

/-- **[Stacks, Tag 09P0] instantiated at the affine line over a field**, with every hypothesis on
the reduction discharged.  The conclusion is of course also available directly, the affine line
being affine; the point of the instance is that the geometric hypotheses of
`Stacks.AmpleNoetherianReduction.exists_isAmple_of_reduction` are satisfiable, so the theorem is
not vacuous.  The bound proved for the affine line is `≤ 1`, from
`Ring.KrullDimLE 1` for a principal ideal ring; that its dimension is exactly one is true and is
not proved here, nor is it needed. -/
theorem exists_isAmple_affineLine (K : Type u) [Field K]
    (hdesc : AmpleDescendsAlongThickening.{u}) :
    ∃ (L : (Spec (CommRingCat.of (Polynomial K))).Modules)
      (hL : IsInvertibleModule (Spec (CommRingCat.of (Polynomial K))) L),
      @IsAmple (Spec (CommRingCat.of (Polynomial K))) L hL :=
  have ⟨hnoe, hsep, hdim⟩ := reduction_hypotheses_affineLine K
  have := hnoe
  have := hsep
  exists_isAmple_of_reduction _ hdesc hdim

end Stacks.AmpleNoetherianReduction

end
