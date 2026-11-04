module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartMapCompletedEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartMapCompletedEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverRefinement
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverSelf
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertyClassClosure

/-!
# Stacks 0ANG, condition (3) implies condition (1), with nothing assumed

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a morphism of locally
countably indexed formal algebraic spaces over `S` and let `P` be a local property of
morphisms of `WAdmᶜᵒᵘⁿᵗ` in the sense of Situation 0CBA. **Stacks 0ANG** asserts that if `P`
holds on an affine étale covering of the source of `f` whose members factor through affine
étale charts of the target (condition (3)), then `P` holds on every commutative square of
affine étale charts over `f` (condition (1)). This file proves that implication with no
hypothesis beyond the source's.

## Main definitions

* `HasChartsPresentedByClass`: every affine formal algebraic space representable étale over an
  fppf sheaf is the formal spectrum of a topological ring of a given class.

## Main results

* `hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover`: the implication (3) ⟹ (1)
  for a covering witnessing condition (3) whose members are formal spectra of rings of a class
  `C` closed under the completion of Stacks 0AN6 along an étale ring map and under isomorphism.
* `hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_hasChartsPresentedByClass`: the
  implication (3) ⟹ (1) for a class `C` of topological rings closed under the completion of
  Stacks 0AN6 along an étale ring map and under isomorphism, and a morphism whose two ends have
  their charts presented by rings of `C`.
* `hasChartsPresentedByClass_of_isLocallyCountablyIndexed`: the charts of a locally countably
  indexed formal algebraic space are presented by rings of `WAdmᶜᵒᵘⁿᵗ`.
* `hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyCountablyIndexed`:
  **Stacks 0ANG**, condition (3) implies condition (1), for every local property of
  `WAdmᶜᵒᵘⁿᵗ` and every morphism of locally countably indexed formal algebraic spaces.

## Implementation notes

The proof is the one of the source. Given a covering as in condition (3) and a square
`U₀ ⟶ V₀` as in condition (1), the covering is refined against the square to a finite affine
étale covering `{Wₛ ⟶ U₀}` whose members map to members `U (k s)` of the covering and to charts
`Zₛ` of `V₀` over `V (k s)`
(`AlgebraicGeometry.FormalSpace.exists_finite_affineEtaleRefinement_of_sourceCover`). The chart
maps `Wₛ ⟶ Zₛ` are completed étale localizations of the chart maps `U (k s) ⟶ V (k s)`, which
is the recognition of Stacks 0AN8 for presented charts
(`AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_presentation`), and
the covering of `U₀` is the completion of a faithfully flat étale ring map, which is Stacks
0AN9 (`AlgebraicGeometry.FormalSpace.isCompletedEtaleFiniteCoverOfChartMap_of_presentation`).
Axiom (1) of Situation 0CBA then carries `P` from `U (k s) ⟶ V (k s)` to `Wₛ ⟶ Zₛ`, and axioms
(2) and (3) descend it to `U₀ ⟶ V₀`.

**Invariance under isomorphism, `hPiso`.** Situation 0CBA begins: "Let `P` be a property of
morphisms of `WAdm^{count}`, invariant under isomorphism of source and target in this
category." That clause is part of what the source calls a local property, and
`TopologicalRing.PropertyIsLocal` records only the three axioms, so the clause is the separate
hypothesis `hPiso`: for bicontinuous ring isomorphisms `eB : B ≃+* B'`, `eA : A ≃+* A'` of rings
of the class and a continuous `f : B →+* A`, `P f ↔ P (eA ∘ f ∘ eB⁻¹)`. It does not follow from
the three axioms, whose completed corners are always the rings `CompletionOver _` themselves and
never an arbitrary isomorphic copy; it is needed because a chart map is presented by an
arbitrary ring of the class, unique only up to such an isomorphism (Stacks 0AN0). It is a
hypothesis of the source, not a result of it.

The predicate `AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` asks `P` of *every*
presentation of a chart map by rings of the class, so the hypothesis on the covering says
something only once the members of the covering are presented by rings of the class. That is
what `HasChartsPresentedByClass` records, and it is the content of the standing hypothesis of
Stacks 0ANG: the charts of a locally countably indexed formal algebraic space are countably
indexed by the implication (2) ⟹ (1) of Stacks 0AKX, hence formal spectra of rings of
`WAdmᶜᵒᵘⁿᵗ` by Stacks 0AN1. The general statement is kept so that the Noetherian variant of
Remark 0ANI is the same argument at a different class.

## References

* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)

/-- The charts of an fppf sheaf `X` are *presented by rings of the class `C`* when every affine
formal algebraic space representable étale over `X` is the formal spectrum of a topological
ring of the class `C`. -/
abbrev HasChartsPresentedByClass (X : FppfSheaf B S hS) : Prop :=
  ∀ (U : FppfSheaf B S hS) (a : U ⟶ X), IsAffineFormalAlgebraicSpace B S hS U →
    IsRepresentableEtale B S hS a → ∃ PU : SpfPresentation B S hS U, C PU.ring

/-- **Axiom (1) of Situation 0CBA, read on affine formal algebraic spaces.** Let `P` be a local
property of arrows of a class `C` closed under the completion of Stacks 0AN6 along an étale
ring map, invariant under isomorphism of source and target as Situation 0CBA requires of it. If
the chart map `t'` is a completed étale localization of the chart map `t` and `t` has `P`, then
so has `t'`.

Given a presentation of `t'`, the localization hands over a presentation of `t` and a
localization diagram linking the two: `P` holds for the vertical map of that diagram because it
holds on every presentation of `t`, axiom (1) of Situation 0CBA carries it to the completed
vertical map, and invariance under isomorphism carries it from there to the given presentation
of `t'`, which differs from the completed vertical map by bicontinuous isomorphisms of source
and target. -/
theorem hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsLocal P C)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      C B → C A → C B' → C A' → (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    (hCcomp : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] (φ : X →+* Y),
      TopologicalRing.IsWeaklyAdmissible X → φ.Etale → C X →
        C (TopologicalRing.CompletionOver φ))
    {U V U' V' : FppfSheaf B S hS} {t : U ⟶ V} {t' : U' ⟶ V'}
    (hloc : IsCompletedEtaleLocalizationOfChartMap B S hS C t t')
    (ht : HasPropertyOnAffineChartMap B S hS C P t) :
    HasPropertyOnAffineChartMap B S hS C P t' := by
  intro A' R' _ _ _ _ _ _ _ _ hCA' hCR' hA' D' E' eU' eV' g' hg'
  refine hloc A' R' hCA' hCR' hA' D' E' eU' eV' g' hg' _ ?_
  intro A R A₁ R₁ _ _ _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg Dia hDia eA eR heA heAs heR
    heRs heq
  have hCR₁ : C (TopologicalRing.CompletionOver Dia.toA') :=
    hCcomp Dia.toA' Dia.weaklyAdmissibleA Dia.etaleA hCR
  have hCA₁ : C (TopologicalRing.CompletionOver Dia.toB') :=
    hCcomp Dia.toB' Dia.weaklyAdmissibleB Dia.etaleB hCA
  have hPcompleted : P Dia.completedMap :=
    hP.localizationPreserves Dia hCR hCA hCR₁ hCA₁ (hDia ▸ ht A R hCA hCR hA D E eU eV g hg)
  rw [heq]
  exact (hPiso eA eR heA heAs heR heRs Dia.completedMap Dia.continuousCompletedMap hCA₁ hCR₁
    hCA' hCR').mp hPcompleted

/-- **Axioms (2) and (3) of Situation 0CBA, read on affine formal algebraic spaces.** Let `P` be
a local property of arrows of a class `C` of weakly admissible rings with countable fundamental
systems of open ideals, closed under the completion of Stacks 0AN6 along an étale ring map, and
invariant under isomorphism of source and target as Situation 0CBA requires of it. Then `P`
descends to a chart map `t : U ⟶ V` from a finite affine étale covering `{Wₛ ⟶ U}` whose members
map to representable étale charts `Zₛ ⟶ V` by maps with `P`, compatibly with `t`, as soon as
that covering is presented by completed étale localizations.

This is the chain of the proof of Stacks 0ANG. Fix a presentation `g : A →+* R` of `t` and the
presented covering it produces. For each member, axiom (2) along the localization diagram whose
source-side horizontal map is the identity of the chart ring `Wr i` carries `P` from the chart
map `μ i` down to the composite `A →+* Wr i`, invariance under isomorphism mediating between
`Zr i` and the completion presenting it and between `Wr i` and its completion over itself.
Axiom (3) gives `P` for the product `A →+* ∀ i, Wr i`, and axiom (2) once more, along the
faithfully flat étale `c : R →+* R₁` presenting the covering, brings `P` back to `g`. -/
theorem hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsLocal P C)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      C B → C A → C B' → C A' → (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    (hCwa : ∀ (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X], C X →
      TopologicalRing.IsWeaklyAdmissible X ∧ (nhds (0 : X)).IsCountablyGenerated)
    (hCcomp : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] (φ : X →+* Y),
      TopologicalRing.IsWeaklyAdmissible X → φ.Etale → C X →
        C (TopologicalRing.CompletionOver φ))
    {U V : FppfSheaf B S hS} (t : U ⟶ V) {σ : Type (u + 1)} (W Z : σ → FppfSheaf B S hS)
    (m : ∀ s, W s ⟶ Z s) (hcover : IsCompletedEtaleFiniteCoverOfChartMap B S hS C t W Z m)
    (hPm : ∀ s, HasPropertyOnAffineChartMap B S hS C P (m s)) :
    HasPropertyOnAffineChartMap B S hS C P t := by
  classical
  have hCself : ∀ (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X], C X →
      ∃ e : X ≃+* TopologicalRing.CompletionOver (RingHom.id X),
        (∀ x : X, e x = TopologicalRing.CompletionOver.canonicalMap (RingHom.id X) x) ∧
          Continuous e ∧ Continuous e.symm := by
    intro X _ _ _ _ hX
    exact TopologicalRing.exists_ringEquiv_completionOver_id (hCwa X hX).1 (hCwa X hX).2
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  refine hcover A R hCA hCR hA D E eU eV g hg _ ?_
  intro ι _ κ Zr Wr Bz R₁ _ _ _ _ _ _ _ _ _ _ _ hCZ hCW hCWpi hZwa Dz Ew eW eZ μ hμ bz hbz
    ez hezc hezcs c hc hcff ew hewc hewcs hewg
  have hidEtale : ∀ (X : Type u) [CommRing X], (RingHom.id X).Etale :=
    fun X _ ↦ RingHom.Etale.of_bijective Function.bijective_id
  have hself : ∀ i, ∃ e : Wr i ≃+* TopologicalRing.CompletionOver (RingHom.id (Wr i)),
      (∀ x : Wr i, e x =
          TopologicalRing.CompletionOver.canonicalMap (RingHom.id (Wr i)) x) ∧
        Continuous e ∧ Continuous e.symm := fun i ↦ hCself (Wr i) (hCW i)
  choose ιW hιWeq hιWc hιWcs using hself
  obtain ⟨ιA, hιAeq, hιAc, hιAcs⟩ := hCself A hCA
  set ψ : ∀ i, A →+* Wr i := fun i ↦ (μ i).toRingHom.comp ((ez i).toRingHom.comp
    (TopologicalRing.CompletionOver.canonicalMap (bz i))) with hψ
  have hψcont : ∀ i, Continuous (ψ i) := fun i ↦
    (μ i).continuous.comp ((hezc i).comp (TopologicalRing.continuous_canonicalMap (bz i)))
  have hCA₀ : C (TopologicalRing.CompletionOver (RingHom.id A)) :=
    hCcomp (RingHom.id A) hA (hidEtale A) hCA
  have hψP : ∀ i, P (ψ i) := by
    intro i
    have hPμ : P (μ i).toRingHom :=
      hPm (κ i) (Zr i) (Wr i) (hCZ i) (hCW i) (hZwa i) (Dz i) (Ew i) (eW i) (eZ i) (μ i) (hμ i)
    have hCWid : C (TopologicalRing.CompletionOver (RingHom.id (Wr i))) :=
      hCcomp (RingHom.id (Wr i)) (hCwa (Wr i) (hCW i)).1 (hidEtale (Wr i)) (hCW i)
    have hCbz : C (TopologicalRing.CompletionOver (bz i)) := hCcomp (bz i) hA (hbz i) hCA
    have hPc : P ((ιW i).toRingHom.comp ((μ i).toRingHom.comp (ez i).toRingHom)) := by
      have hinv := (hPiso (ez i).symm (ιW i) (hezcs i)
        (by simpa using hezc i) (hιWc i) (hιWcs i) (μ i).toRingHom (μ i).continuous
        (hCZ i) (hCW i) hCbz hCWid).mp hPμ
      simpa [RingHom.comp_assoc] using hinv
    exact hP.faithfullyFlatDescent
      { toA' := RingHom.id (Wr i)
        toB' := bz i
        map := ψ i
        completedMap := (ιW i).toRingHom.comp ((μ i).toRingHom.comp (ez i).toRingHom)
        weaklyAdmissibleA := (hCwa (Wr i) (hCW i)).1
        weaklyAdmissibleB := hA
        countableA := (hCwa (Wr i) (hCW i)).2
        countableB := (hCwa A hCA).2
        etaleA := hidEtale (Wr i)
        etaleB := hbz i
        continuousMap := hψcont i
        continuousCompletedMap := (hιWc i).comp ((μ i).continuous.comp (hezc i))
        commutes := by
          refine RingHom.ext fun x ↦ ?_
          simp only [RingHom.coe_comp, Function.comp_apply, hψ]
          exact (hιWeq i _).symm }
      (hCW i) hCA hCWid hCbz (RingHom.FaithfullyFlat.of_bijective Function.bijective_id) hPc
  have hPpi : P (RingHom.pi ψ) :=
    hP.finiteProduct hA (hCwa A hCA).2 Wr (fun i ↦ (hCwa (Wr i) (hCW i)).1)
      (fun i ↦ (hCwa (Wr i) (hCW i)).2) ψ hψcont hCA hCW hψP
  have hCRc : C (TopologicalRing.CompletionOver c) := hCcomp c (hCwa R hCR).1 hc hCR
  have hPcomp : P (ew.symm.toRingHom.comp ((RingHom.pi ψ).comp ιA.symm.toRingHom)) := by
    have hinv := (hPiso ιA ew.symm hιAc hιAcs hewcs
      (by simpa using hewc) (RingHom.pi ψ) (continuous_pi fun i ↦ hψcont i)
      hCA hCWpi hCA₀ hCRc).mp hPpi
    simpa [RingHom.comp_assoc] using hinv
  exact hP.faithfullyFlatDescent
    { toA' := c
      toB' := RingHom.id A
      map := g.toRingHom
      completedMap := ew.symm.toRingHom.comp ((RingHom.pi ψ).comp ιA.symm.toRingHom)
      weaklyAdmissibleA := (hCwa R hCR).1
      weaklyAdmissibleB := hA
      countableA := (hCwa R hCR).2
      countableB := (hCwa A hCA).2
      etaleA := hc
      etaleB := hidEtale A
      continuousMap := g.continuous
      continuousCompletedMap := hewcs.comp ((continuous_pi fun i ↦ hψcont i).comp hιAcs)
      commutes := by
        refine RingHom.ext fun x ↦ ?_
        have hx := RingHom.congr_fun hewg x
        simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingHom.coe_coe, ← hιAeq, RingEquiv.symm_apply_apply] at hx ⊢
        rw [← hx, RingEquiv.symm_apply_apply] }
    hCR hCA hCRc hCA₀ hcff hPcomp

/-- **The implication (3) ⟹ (1) of Stacks 0ANG for a covering presented by rings of a class.**
Let `C` be a class of topological rings each of which is weakly admissible with a countable
fundamental system of open ideals, closed under the completion of Stacks 0AN6 along an étale
ring map and under isomorphism of topological rings, and let `P` be a local property of arrows
of `C` in the sense of Situation 0CBA, invariant under isomorphism of source and target
(`hPiso`). Let `{u i : U i ⟶ X}` be an affine étale covering of the source of `f : X ⟶ Y` with
factorizations `U i ⟶ V i ⟶ Y` through affine formal algebraic spaces representable étale over
`Y`, `P` holding on each `t i : U i ⟶ V i` — the data of condition (3) — and suppose that every
`U i` and every `V i` is the formal spectrum of a ring of `C`. Then `f` satisfies condition (1).

The covering is refined against a square of condition (1) by
`AlgebraicGeometry.FormalSpace.exists_finite_affineEtaleRefinement_of_sourceCover`. Each member
`U (k s) ⟶ V (k s)` of the covering being refined is presented by rings of `C`, Stacks 0AN0
presenting the chart map itself, so each square `Wₛ ⟶ Zₛ` over it is a completed étale
localization by Stacks 0AN8; the finite covering of `U₀` is presented by Stacks 0AN9. The
locality axioms of Situation 0CBA, read on affine formal algebraic spaces, conclude. Only the
members of the given covering need to be presented: the refined charts are presented by the
recognition of Stacks 0AN8 itself.

NO TAG IS ATTACHED: the class of rings and the presentation of the covering are parameters here;
**Stacks 0ANG** at the source's own hypotheses is
`hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyCountablyIndexed`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsLocal P C)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      C B → C A → C B' → C A' → (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    (hCwa : ∀ (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X], C X →
      TopologicalRing.IsWeaklyAdmissible X ∧ (nhds (0 : X)).IsCountablyGenerated)
    (hCcomp : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] (φ : X →+* Y),
      TopologicalRing.IsWeaklyAdmissible X → φ.Etale → C X →
        C (TopologicalRing.CompletionOver φ))
    (hCiso : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] [TopologicalSpace Y] [IsTopologicalRing Y]
      [IsLinearTopology Y Y] (e : X ≃+* Y), Continuous e → Continuous e.symm → C X → C Y)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
    (t : ∀ i, U i ⟶ V i) (hUcover : IsAffineEtaleCover B S hS U u)
    (hVaffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (V i))
    (hVetale : ∀ i, IsRepresentableEtale B S hS (v i))
    (hVsquare : ∀ i, u i ≫ f = t i ≫ v i)
    (hVproperty : ∀ i, HasPropertyOnAffineChartMap B S hS C P (t i))
    (hUpres : ∀ i, ∃ PU : SpfPresentation B S hS (U i), C PU.ring)
    (hVpres : ∀ i, ∃ PV : SpfPresentation B S hS (V i), C PV.ring) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P f := by
  intro U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  obtain ⟨σ, hσ, k, W, Z, p, q, m, r, c, hWcover, hZaffine, hq, hr, hc, hsq₁, hsq₂⟩ :=
    exists_finite_affineEtaleRefinement_of_sourceCover B S hS f U V u v t hUcover hVaffine
      hVetale hVsquare a b τ hU₀ hV₀ ha hb hsquare
  refine hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap B S hS C P hP
    hPiso hCwa hCcomp τ W Z m
    (isCompletedEtaleFiniteCoverOfChartMap_of_presentation B S hS C hCwa hCcomp hCiso hσ p m c
      hWcover hZaffine hc hsq₂) fun s ↦ ?_
  -- the member `U (k s) ⟶ V (k s)` of the covering, presented by rings of the class
  obtain ⟨PU, hCU⟩ := hUpres (k s)
  obtain ⟨PV, hCV⟩ := hVpres (k s)
  obtain ⟨eU⟩ := PU.iso
  obtain ⟨eV⟩ := PV.iso
  obtain ⟨g, hgeq, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq (hCwa _ hCV).1
    (hCwa _ hCU).1 (eU.inv ≫ t (k s) ≫ eV.hom)
  have hloc : IsCompletedEtaleLocalizationOfChartMap B S hS C (t (k s)) (m s) :=
    isCompletedEtaleLocalizationOfChartMap_of_presentation B S hS C hCwa (q s) (r s)
      (hWcover.1 s) (hZaffine s) (hq s) (hr s) (hsq₁ s) hCV hCU PV.system PU.system eU eV g
      (by rw [hgeq]; simp)
  exact hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap B S hS C P hP
    hPiso hCcomp hloc (hVproperty (k s))

/-- **The implication (3) ⟹ (1) of Stacks 0ANG for a class of rings presenting the charts.** The
hypotheses on `C` and `P` are those of
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover`. If
the charts of the two ends of `f : X ⟶ Y` are presented by rings of `C`, then condition (3) of
Stacks 0ANG for `f` implies condition (1): the members of any covering witnessing condition (3)
are charts of `X` and of `Y`.

NO TAG IS ATTACHED, for the reason given on
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_hasChartsPresentedByClass
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsLocal P C)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      C B → C A → C B' → C A' → (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    (hCwa : ∀ (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X], C X →
      TopologicalRing.IsWeaklyAdmissible X ∧ (nhds (0 : X)).IsCountablyGenerated)
    (hCcomp : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] (φ : X →+* Y),
      TopologicalRing.IsWeaklyAdmissible X → φ.Etale → C X →
        C (TopologicalRing.CompletionOver φ))
    (hCiso : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] [TopologicalSpace Y] [IsTopologicalRing Y]
      [IsLinearTopology Y Y] (e : X ≃+* Y), Continuous e → Continuous e.symm → C X → C Y)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : HasChartsPresentedByClass B S hS C X) (hY : HasChartsPresentedByClass B S hS C Y)
    (hf : HasPropertyAfterSourceCover B S hS C P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P f := by
  obtain ⟨I, U, u, hUcover, hfac⟩ := hf
  choose V v t hVaffine hVetale hVsquare hVproperty using hfac
  exact hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover B S hS C P hP hPiso hCwa
    hCcomp hCiso f U V u v t hUcover hVaffine hVetale hVsquare hVproperty
    (fun i ↦ hX (U i) (u i) (hUcover.1 i) (hUcover.2.1 i))
    (fun i ↦ hY (V i) (v i) (hVaffine i) (hVetale i))

/-- **The charts of a locally countably indexed formal algebraic space are presented by rings
of `WAdmᶜᵒᵘⁿᵗ`.** An affine formal algebraic space representable étale over a locally countably
indexed formal algebraic space is countably indexed, by the implication (2) ⟹ (1) of
**Stacks 0AKX**, hence the formal spectrum of a weakly admissible topological ring with a
countable fundamental system of open ideals, by the implication (1) ⟹ (2) of **Stacks 0AN1**.
This is the observation the source makes before Lemma 0ANB. -/
theorem hasChartsPresentedByClass_of_isLocallyCountablyIndexed {X : FppfSheaf B S hS}
    (hX : IsLocallyCountablyIndexed B S hS X) :
    HasChartsPresentedByClass B S hS TopologicalRing.IsCountablyWeaklyAdmissible X := by
  intro U a hU ha
  obtain ⟨PU, hwa, hcount⟩ := hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS U
    ⟨hU, isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS X hX U a
      hU ha⟩
  exact ⟨PU, hwa, hcount⟩

/-- **Stacks 0ANG, condition (3) implies condition (1).** Let `f : X ⟶ Y` be a morphism of
locally countably indexed formal algebraic spaces over `S` and let `P` be a local property of
morphisms of `WAdmᶜᵒᵘⁿᵗ` (Situation 0CBA: `hP` for the three axioms and `hPiso` for "invariant
under isomorphism of source and target in this category"). If there are an affine étale covering
`{Uᵢ ⟶ X}` as in Definition 0AIM and factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` through affine formal
algebraic spaces representable étale over `Y` with `P` on each `Uᵢ ⟶ Vᵢ`, then for every
commutative square with affine formal algebraic spaces `U`, `V` and representable étale maps
`U ⟶ X`, `V ⟶ Y`, the morphism `U ⟶ V` has `P`.

This is `hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_hasChartsPresentedByClass` at
the class `WAdmᶜᵒᵘⁿᵗ`, whose three closure conditions are theorems: membership of the class is weak
admissibility with a countable fundamental system of open ideals by definition, closure under
completion along an étale ring map is two clauses of **Stacks 0ANB**, and closure under isomorphism
is `TopologicalRing.isCountablyWeaklyAdmissible_of_ringEquiv`. The charts of `X` and `Y` are
presented by rings of the class because `X` and `Y` are locally countably indexed. -/
@[stacks 0ANG "condition (3) implies condition (1), for a morphism of locally countably \
indexed formal algebraic spaces and a local property of WAdm^count, as the source states it: \
hP and hPiso together are Situation 0CBA's notion of a local property"]
theorem hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyCountablyIndexed
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsLocal P TopologicalRing.IsCountablyWeaklyAdmissible)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      TopologicalRing.IsCountablyWeaklyAdmissible B →
      TopologicalRing.IsCountablyWeaklyAdmissible A →
      TopologicalRing.IsCountablyWeaklyAdmissible B' →
      TopologicalRing.IsCountablyWeaklyAdmissible A' →
      (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hf : HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
      f :=
  hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_hasChartsPresentedByClass B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible P hP hPiso (fun _ _ _ _ _ hX ↦ hX)
    (fun φ _ _ hX ↦ TopologicalRing.isCountablyWeaklyAdmissible_completionOver φ hX)
    (fun e he he' hX ↦ TopologicalRing.isCountablyWeaklyAdmissible_of_ringEquiv e he he' hX) f
    (hasChartsPresentedByClass_of_isLocallyCountablyIndexed B S hS hX)
    (hasChartsPresentedByClass_of_isLocallyCountablyIndexed B S hS hY) hf

end AlgebraicGeometry.FormalSpace

end
