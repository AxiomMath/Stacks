module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicBaseChangeSquares
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ChartAnnihilationDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GeneralBaseAssembly

/-!
# Stacks 088C, `hDev` and Stacks 088E from one base-change hypothesis at the completion chart

`CompletionProper/AffineSpecTransport.lean` and `CompletionProper/ChartAnnihilationDescent.lean`
reduce [Stacks, Tag 088B] at a general base — and with it [Stacks, Tag 088C], the binder `hDev`
of [Stacks, Tag 088E] and the first input of
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison` — to
a hypothesis over the completion chart `c = Spec (B ^∧) ⟶ V` of each affine open `V` of the base,
with `B = Γ(X, V)`. This file chains what those two files leave behind into the conclusions, and
measures what is still missing.

## What is assembled here

**The annihilation clause is discharged.** The chart's assembly
`Stacks.Algebraization.exists_pullbackCharacterization_of_adicCompletionChartSquares` discards the
annihilation half of the solution over `Spec (B ^∧)` with `obtain ⟨α', hα', -⟩`, because its
comparison `ι` of the two completed direct images is only a morphism. Ask `ι` to be an
isomorphism — which is what degree-zero flat base change and Stacks 0887 produce, see
`Stacks.Algebraization.isIso_adicBaseChangeCompletedComparison` — and the annihilation of `α'`
becomes the annihilation of `ψ = α' ≫ ι` for free, by
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff`. That is
`…exists_pullbackCharacterization_isKernelCokernel_of_adicCompletionChartSquares`.
Composed with the return of the annihilation along the chart,
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_morphismRestrict_of_adicCompletionChart`,
it removes the annihilation clause — "piece 3" of `CompletionProper/AffineLocalSolution.lean`, the
sheafification of `Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion` — from the
residue of the 088E route altogether: it is no longer an obligation of its own but a consequence of
the complete affine case over `Spec (B ^∧)`, where the base *is* complete.

**One hypothesis is left.** `Stacks.Algebraization.HasAdicCompletionChartBaseChange` asks, over
the chart of each affine open `V`, for the base change of `π ∣_ V` along `c` together with its
two comparisons and the two squares that identify its `δ` and `γ` with the pullbacks along `c` of
those of `π ∣_ V`. From it,
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChartBaseChange` gives
`Stacks.Algebraization.HasAffineLocalDirectImageSolution`,
`…isDirectImageComparison_of_adicCompletionChartBaseChange` gives
`Stacks.Algebraization.IsDirectImageComparison`, and then
`…isEquivalence_completionFunctor_of_adicCompletionChartBaseChange` is Stacks 088C,
`…hDev_of_adicCompletionChartBaseChange` is `hDev`, and
`…isEquivalence_completionFunctorProperOver_of_adicCompletionChartBaseChange` is Stacks 088E —
the last granted in addition the Chow residual `hTransport`, which is untouched here.

**Stacks 088B over an affine base, in full.**
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_adicBaseChangeGamma`
is the characterization *and* the annihilation of Stacks 088B for a proper morphism
`π : X' ⟶ Spec B` with `B` Noetherian and **not** assumed complete, with the source's condition
`hc` over `Spec (B ^∧)` as its only binder. It is
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeGamma` with the
annihilation clause kept: the annihilation over `Spec (B ^∧)` crosses `ι` because `ι` is an
isomorphism, and comes home along `Spec (B ^∧) ⟶ Spec B` by
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_adicCompletionSpecMapPullback`, the
`adicCompletionSpecMap` twin of the chart's descent. Both squares `hδ` and `hγ` are the theorems
of `CompletionProper/AdicBaseChangeSquares.lean`, so nothing of the source's second paragraph is
left over an affine base.

## What remains, and where the two halves fail to meet

The two routes to the local solution stand on opposite sides of **one** transport, and that is the
whole of what is left.

* The base-change machinery of `CompletionProper/AdicBaseChangeSituation.lean` and
  `CompletionProper/AdicBaseChangeSquares.lean` — the base change `X' ×_{Spec B} Spec (B ^∧)`, the
  comparisons `ι` and `θ`, and the two squares `hδ` and `hγ` — is built for a proper morphism
  `π : X' ⟶ Spec B`, over `Spec B` *itself*.
* The chart machinery of `CompletionProper/AffineSpecTransport.lean` asks for those same data at
  `c = Spec (B ^∧) ⟶ V`, over the affine open `V`, for the restricted morphism `π ∣_ V`. Since
  `V ≅ Spec Γ(X, V)` is not an identity, `π ∣_ V` is a morphism to `V` and not to `Spec Γ(X, V)`,
  so it does not instantiate `π` above.

The chart was introduced precisely to avoid transporting the situation across
`AlgebraicGeometry.IsAffineOpen.isoSpec`; but the squares exist only on the `Spec B` side, so the
transport is needed either way. What is needed is one of:

1. the base change of `π ∣_ V` along `c` with its squares, i.e.
   `CompletionProper/AdicBaseChangeSquares.lean` restated for a flat morphism
   `Spec (B ^∧) ⟶ Y` with `Y ≅ Spec B`, which is
   `Stacks.Algebraization.HasAdicCompletionChartBaseChange`; or
2. the transport of the conclusion of
   `…exists_isDirectImageCharacterized_isKernelCokernel_of_adicBaseChangeGamma` at
   `π := (π ∣_ V) ≫ e.hom` back across `e = V.2.isoSpec` — the module `X'` and `𝓕` are unchanged
   by that composition, so what has to travel is only the base side: `Coh(V, 𝒥|_V)` against
   `Coh(Spec Γ(X, V), 𝒥(V) 𝒪)`, and `(π ∣_ V)_*𝓕` against `((π ∣_ V) ≫ e.hom)_*𝓕`, together with
   the compatibility of `Stacks.Coherent.directImageComparison` with composing the base morphism
   with an isomorphism.

This is "the geometric half of piece 1" of `CompletionProper/AffineLocalTransport.lean`, and
nothing in the tree supplies it: there is no transport of
`Stacks.Coherent.IsDirectImageCharacterized` along an isomorphism of the base.

The residual `hTransport` of Stacks 088E — the Chow compactification datum of
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison` — is
independent of all of this and remains a binder.

No `stacks` attribute is attached anywhere in this file: every result is an assembly or a
reduction of a hypothesis, and the tags of the statements involved are registered on the
declarations named in the docstrings below.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

section ChartSquares

open Stacks.Coherent

/-- Pasting the three squares `hδ`, `hα` and `hγ` along the composite `a ≫ i`. -/
private theorem comp_comp_eq_of_squares {C : Type*} [Category C] {A B X Y Z W : C}
    (a : A ⟶ B) (i : B ⟶ X) (P : X ⟶ Y) (D : B ⟶ Z) (θ : Z ⟶ Y) (g : A ⟶ W) (E : W ⟶ Z)
    (r : A ⟶ Y) (hδ : i ≫ P = D ≫ θ) (hα : a ≫ D = g ≫ E) (hγ : g ≫ E ≫ θ = r) :
    (a ≫ i) ≫ P = r := by
  rw [Category.assoc, hδ, ← Category.assoc, hα, Category.assoc, hγ]

variable {Y : Scheme.{u}} [IsNoetherian Y] (B : Type u) [CommRing B] [IsNoetherianRing B]
  (I : Ideal B) (e : Y ≅ Spec (.of B)) {𝒥 : Y.IdealSheafData}
  (h : (adicIdealSheaf B I).comap e.hom = 𝒥)
  {X' : Scheme.{u}} [IsNoetherian X'] (p : X' ⟶ Y) [IsProper p]
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (G : CoherentAdicSystems 𝒥)
  (β : (coherentAdicPullback p 𝒥).obj G ≅ (completionFunctor X' (𝒥.comap p)).obj 𝓕)

include h

/-- **The morphism `ψ` over the chart's base, the pulled-back characterizing equation, and the
annihilation of `ψ`, from the two base-change squares at the chart.**

This is `Stacks.Algebraization.exists_pullbackCharacterization_of_adicCompletionChartSquares`
with the annihilation half of the solution over `Spec (B ^∧)` **kept**. That assembly throws it
away with `obtain ⟨α', hα', -⟩`, for want of a way home: its comparison `ι` of the two completed
direct images is only a morphism, and composing with a bare morphism changes the levelwise
kernels and cokernels. Here `ι` is asked to be an isomorphism — which is what it is in the
intended application, see `Stacks.Algebraization.isIso_adicBaseChangeCompletedComparison` — and
then `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff` carries the annihilation
of `α'` to `ψ = α' ≫ ι` with the same exponent and the same ideal sheaf `𝒦`.

The characterizing equation is proved exactly as in that assembly: `hδ` moves `ι` past the
`δ` of the situation over `Y`, the characterization `hα'` of `α'` replaces the composite by the
`γ` of the situation over `Spec (B ^∧)`, and `hγ` identifies that with the pullback along the
chart of the `γ` over `Y`.

**What this buys.** The annihilation clause of the hypothesis of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChartAnnihilation` is
now supplied by the same assembly that supplies the characterizing equation, so the annihilation
is no longer a separate obligation of the 088E route — in particular the sheafification of
`Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion`, recorded as piece 3 in
`CompletionProper/AffineLocalSolution.lean`, is not needed for it. What is left of the hypothesis
is the base change at the chart and its two squares; see the module docstring.

No `stacks` attribute is attached: this is the assembly of a hypothesis out of two squares, not a
statement of the source. -/
public theorem exists_pullbackCharacterization_isKernelCokernel_of_adicCompletionChartSquares
    {X'' : Scheme.{u}} [IsNoetherian X'']
    (π' : X'' ⟶ Spec (.of (AdicCompletion I B))) [IsProper π']
    (𝓕' : AlgebraicGeometry.SheafOfModules.CoherentModules X''.ringCatSheaf)
    (β' : (coherentAdicPullback π' (𝒥.comap (adicCompletionChart B I e))).obj
        ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G) ≅
      (completionFunctor X'' ((𝒥.comap (adicCompletionChart B I e)).comap π')).obj 𝓕')
    (𝒦 : (Spec (.of (AdicCompletion I B))).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion I B))).ringCatSheaf,
      ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G ≅
          (completionFunctor (Spec (.of (AdicCompletion I B)))
            (𝒥.comap (adicCompletionChart B I e))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π').unit.app 𝒜.obj)))
    (ι : ((completionFunctor (Spec (.of (AdicCompletion I B)))
          (𝒥.comap (adicCompletionChart B I e))).obj
        (properPushforwardCoherent π' 𝓕')).obj ⟶
      ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj
        ((completionFunctor Y 𝒥).obj (properPushforwardCoherent p 𝓕))).obj)
    [IsIso ι]
    (θ : ∀ n : ℕ, (Scheme.Modules.pushforward π').obj
          (idealPowerQuotient ((𝒥.comap (adicCompletionChart B I e)).comap π') (n + 1) 𝓕'.obj) ⟶
      (Scheme.Modules.pullback (adicCompletionChart B I e)).obj
        ((Scheme.Modules.pushforward p).obj (idealPowerQuotient (𝒥.comap p) (n + 1) 𝓕.obj)))
    (hδ : ∀ n : ℕ, ι.app (op n) ≫
          (Scheme.Modules.pullback (adicCompletionChart B I e)).map
            (eqToHom (completionFunctor_obj Y 𝒥 (properPushforwardCoherent p 𝓕) n) ≫
              directImageQuotientComparison p 𝒥 (n + 1) 𝓕.obj) =
        (eqToHom (completionFunctor_obj (Spec (.of (AdicCompletion I B)))
              (𝒥.comap (adicCompletionChart B I e))
              (properPushforwardCoherent π' 𝓕') n) ≫
            directImageQuotientComparison π' (𝒥.comap (adicCompletionChart B I e))
              (n + 1) 𝓕'.obj) ≫ θ n)
    (hγ : ∀ n : ℕ,
        (directImageComparison π' (𝒥.comap (adicCompletionChart B I e))
              ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G) 𝓕' β').app (op n) ≫
            eqToHom (pushforward_completion_obj π' (𝒥.comap (adicCompletionChart B I e))
              𝓕' n) ≫ θ n =
          (Scheme.Modules.pullback (adicCompletionChart B I e)).map
            ((directImageComparison p 𝒥 G 𝓕 β).app (op n) ≫
              eqToHom (pushforward_completion_obj p 𝒥 𝓕 n))) :
    ∃ ψ : ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G).obj ⟶
        ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj
          ((completionFunctor Y 𝒥).obj (properPushforwardCoherent p 𝓕))).obj,
      (∀ n : ℕ, ψ.app (op n) ≫
            (Scheme.Modules.pullback (adicCompletionChart B I e)).map
              (eqToHom (completionFunctor_obj Y 𝒥 (properPushforwardCoherent p 𝓕) n) ≫
                directImageQuotientComparison p 𝒥 (n + 1) 𝓕.obj) =
          (Scheme.Modules.pullback (adicCompletionChart B I e)).map
            ((directImageComparison p 𝒥 G 𝓕 β).app (op n) ≫
              eqToHom (pushforward_completion_obj p 𝒥 𝓕 n))) ∧
        IsKernelCokernelAnnihilatedByPower 𝒦 ψ := by
  obtain ⟨α', hα', hann'⟩ :=
    exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase B I e h π' 𝒦 𝓕'
      ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G) β' hc
  refine ⟨α' ≫ ι, fun n => ?_,
    (isKernelCokernelAnnihilatedByPower_comp_iso_iff 𝒦 α' (asIso ι)).2 hann'⟩
  rw [NatTrans.comp_app]
  exact comp_comp_eq_of_squares _ _ _ _ _ _ _ _ (hδ n) (hα' n) (hγ n)

end ChartSquares

/-! ### The same, at the completion chart of an affine open of a general base -/

section AffineOpenSquares

open Stacks.Coherent

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)
  (V : X.affineOpens) [IsNoetherianRing ↥Γ(X, V.1)]

/-- **The previous theorem at the completion chart of an affine open `V` of a general base**,
i.e. `…exists_pullbackCharacterization_isKernelCokernel_of_adicCompletionChartSquares`, for the
restricted morphism `π ∣_ V` and the restricted data of
`Stacks.Coherent.restrictDirectImageIso`.

Read at `Y = V`, `B = Γ(X, V)`, `I = 𝒥(V)` and the chart
`Stacks.Algebraization.affineOpenAdicCompletionChart`; the ideal sheaf matches by
`Stacks.Algebraization.comap_adicIdealSheaf_isoSpec`. Taking `𝒦` to be
`(𝒦|_V)` pulled back along the chart, the two clauses of the hypothesis of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChartAnnihilation` are
exactly the two conjuncts of the conclusion; that is the content of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChartBaseChange`.

No `stacks` attribute is attached: this is the assembly of a hypothesis, not a statement of the
source. -/
public theorem
    exists_pullbackCharacterization_isKernelCokernel_morphismRestrict_of_adicCompletionChartSquares
    {X'' : Scheme.{u}} [IsNoetherian X'']
    (π' : X'' ⟶ Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))) [IsProper π']
    (𝓕' : AlgebraicGeometry.SheafOfModules.CoherentModules X''.ringCatSheaf)
    (β' : (coherentAdicPullback π'
          ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj
        ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
          ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)) ≅
      (completionFunctor X''
        (((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)).comap π')).obj 𝓕')
    (𝒦 : (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))).ringCatSheaf,
      ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
            ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G) ≅
          (completionFunctor (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
            ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π').unit.app 𝒜.obj)))
    (ι : ((completionFunctor (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
          ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj
        (properPushforwardCoherent π' 𝓕')).obj ⟶
      ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
        ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
          (properPushforwardCoherent (π ∣_ V.1)
            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj)
    [IsIso ι]
    (θ : ∀ n : ℕ, (Scheme.Modules.pushforward π').obj
          (idealPowerQuotient
            (((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)).comap π')
            (n + 1) 𝓕'.obj) ⟶
      (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).obj
        ((Scheme.Modules.pushforward (π ∣_ V.1)).obj
          (idealPowerQuotient ((J.comap V.1.ι).comap (π ∣_ V.1)) (n + 1)
            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj)))
    (hδ : ∀ n : ℕ, ι.app (op n) ≫
          (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
            (eqToHom (completionFunctor_obj V.1.toScheme (J.comap V.1.ι)
                (properPushforwardCoherent (π ∣_ V.1)
                  (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)) n) ≫
              directImageQuotientComparison (π ∣_ V.1) (J.comap V.1.ι) (n + 1)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj) =
        (eqToHom (completionFunctor_obj
              (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
              ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))
              (properPushforwardCoherent π' 𝓕') n) ≫
            directImageQuotientComparison π'
              ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)) (n + 1) 𝓕'.obj) ≫ θ n)
    (hγ : ∀ n : ℕ,
        (directImageComparison π' ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))
              ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
                ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)) 𝓕' β').app (op n) ≫
            eqToHom (pushforward_completion_obj π'
              ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)) 𝓕' n) ≫ θ n =
          (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
            ((directImageComparison (π ∣_ V.1) (J.comap V.1.ι)
                ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
                (restrictDirectImageIso π V.1 J G 𝓕 β)).app (op n) ≫
              eqToHom (pushforward_completion_obj (π ∣_ V.1) (J.comap V.1.ι)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕) n))) :
    ∃ ψ : ((coherentAdicPullback (affineOpenAdicCompletionChart J V)
          (J.comap V.1.ι)).obj ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)).obj ⟶
        ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
          ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
            (properPushforwardCoherent (π ∣_ V.1)
              (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj,
      (∀ n : ℕ, ψ.app (op n) ≫
            (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
              (eqToHom (completionFunctor_obj V.1.toScheme (J.comap V.1.ι)
                  (properPushforwardCoherent (π ∣_ V.1)
                    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)) n) ≫
                directImageQuotientComparison (π ∣_ V.1) (J.comap V.1.ι) (n + 1)
                  (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj) =
          (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
            ((directImageComparison (π ∣_ V.1) (J.comap V.1.ι)
                ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
                (restrictDirectImageIso π V.1 J G 𝓕 β)).app (op n) ≫
              eqToHom (pushforward_completion_obj (π ∣_ V.1) (J.comap V.1.ι)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕) n))) ∧
        IsKernelCokernelAnnihilatedByPower 𝒦 ψ :=
  exists_pullbackCharacterization_isKernelCokernel_of_adicCompletionChartSquares
    ↥Γ(X, V.1) (J.ideal V) V.2.isoSpec (comap_adicIdealSheaf_isoSpec J V.2) (π ∣_ V.1)
    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
    ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
    (restrictDirectImageIso π V.1 J G 𝓕 β) π' 𝓕' β' 𝒦 hc ι θ hδ hγ

end AffineOpenSquares

/-! ### The whole residue of the 088E route, as one hypothesis -/

section Residue

open Stacks.Coherent Stacks.Cohomology.FormalFunctions

/-- **The whole residue of the route to [Stacks, Tag 088C], `hDev` and [Stacks, Tag 088E], as one
hypothesis.**

Over every affine open `V` of the base, with `B = Γ(X, V)` and `c` the completion chart
`Spec (B ^∧) ⟶ V` of `Stacks.Algebraization.affineOpenAdicCompletionChart`, the hypothesis asks
for

* a proper morphism `π' : X'' ⟶ Spec (B ^∧)` with `X''` Noetherian, a coherent
  `𝒪_{X''}`-module `𝓕'` and an isomorphism `β'` over `Spec (B ^∧)` — in the intended application
  the base change of `π ∣_ V`, of `𝓕|_{π ⁻¹ V}` and of `Stacks.Coherent.restrictDirectImageIso`
  along `c`;
* the source's own condition `hc` on the unit of `(π')^* ⊣ (π')_*` away from the support of the
  chart-pullback of `𝒦|_V`;
* a comparison `ι : (π'_*𝓕') ^∧ ⟶ c^*(((π ∣_ V)_*(𝓕|_{π ⁻¹ V})) ^∧)` which is an
  **isomorphism**, and a comparison `θ_n` of the two direct images of the levels; and
* the two squares `hδ` and `hγ` saying that `ι` and `θ` carry the `δ` and the `γ` of the situation
  over `Spec (B ^∧)` to the pullbacks along `c` of the `δ` and the `γ` of the situation over `V`.

Every other part of [Stacks, Tag 088B] at a general base is proved: the glueing of the first
paragraph, the descent of the morphism and of the equation across the chart, the return of the
annihilation along the chart, and — granted that `ι` is an isomorphism — the annihilation itself,
which comes from the complete affine case over `Spec (B ^∧)`.

**This is not available, and the module docstring says why.** Each of `ι`, `θ`, `hδ` and `hγ` is
a theorem of `CompletionProper/AdicBaseChangeSituation.lean` and
`CompletionProper/AdicBaseChangeSquares.lean` — but for a proper morphism to `Spec B` itself, and
`π ∣_ V` is a morphism to `V`, which `AlgebraicGeometry.IsAffineOpen.isoSpec` identifies with
`Spec B` only up to an isomorphism that nothing in the tree transports the problem across.

No `stacks` attribute is attached: this is a hypothesis, not a statement of the source. -/
public def HasAdicCompletionChartBaseChange : Prop :=
  ∀ {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
    (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕),
    IsIso (π ∣_ K.support.compl) → ∀ V : X.affineOpens,
      letI : IsNoetherianRing ↥Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
      ∃ (X'' : Scheme.{u}) (hN : IsNoetherian X''),
        ∃ (π' : X'' ⟶ Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))) (hP : IsProper π'),
          haveI := hN
          haveI := hP
          ∃ (𝓕' : AlgebraicGeometry.SheafOfModules.CoherentModules X''.ringCatSheaf)
            (β' : (coherentAdicPullback π'
                  ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj
                ((coherentAdicPullback (affineOpenAdicCompletionChart J V)
                  (J.comap V.1.ι)).obj
                  ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)) ≅
              (completionFunctor X''
                (((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)).comap π')).obj 𝓕'),
            (∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
                (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))).ringCatSheaf,
              ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
                    ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G) ≅
                  (completionFunctor (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
                    ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj 𝒜) →
                IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι
                    (((K.comap V.1.ι).comap
                      (affineOpenAdicCompletionChart J V)).support.compl))).map
                  ((Scheme.Modules.pullbackPushforwardAdjunction π').unit.app 𝒜.obj))) ∧
              ∃ (ι : ((completionFunctor
                    (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
                    ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj
                  (properPushforwardCoherent π' 𝓕')).obj ⟶
                ((coherentAdicPullback (affineOpenAdicCompletionChart J V)
                  (J.comap V.1.ι)).obj
                  ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
                    (properPushforwardCoherent (π ∣_ V.1)
                      (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj) (_ : IsIso ι)
                (θ : ∀ n : ℕ, (Scheme.Modules.pushforward π').obj
                      (idealPowerQuotient
                        (((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)).comap π')
                        (n + 1) 𝓕'.obj) ⟶
                  (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).obj
                    ((Scheme.Modules.pushforward (π ∣_ V.1)).obj
                      (idealPowerQuotient ((J.comap V.1.ι).comap (π ∣_ V.1)) (n + 1)
                        (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj))),
                (∀ n : ℕ, ι.app (op n) ≫
                      (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
                        (eqToHom (completionFunctor_obj V.1.toScheme (J.comap V.1.ι)
                            (properPushforwardCoherent (π ∣_ V.1)
                              (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)) n) ≫
                          directImageQuotientComparison (π ∣_ V.1) (J.comap V.1.ι) (n + 1)
                            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj) =
                    (eqToHom (completionFunctor_obj
                          (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
                          ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))
                          (properPushforwardCoherent π' 𝓕') n) ≫
                        directImageQuotientComparison π'
                          ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)) (n + 1)
                          𝓕'.obj) ≫ θ n) ∧
                  ∀ n : ℕ,
                    (directImageComparison π'
                          ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))
                          ((coherentAdicPullback (affineOpenAdicCompletionChart J V)
                            (J.comap V.1.ι)).obj
                            ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)) 𝓕' β').app
                        (op n) ≫
                        eqToHom (pushforward_completion_obj π'
                          ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)) 𝓕' n) ≫
                        θ n =
                      (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
                        ((directImageComparison (π ∣_ V.1) (J.comap V.1.ι)
                            ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
                            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
                            (restrictDirectImageIso π V.1 J G 𝓕 β)).app (op n) ≫
                          eqToHom (pushforward_completion_obj (π ∣_ V.1) (J.comap V.1.ι)
                            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕) n))

/-- **`Stacks.Algebraization.HasAffineLocalDirectImageSolution` from the base change at the
completion chart of each affine open.** The first clause of the hypothesis of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChartAnnihilation` and
its annihilation clause are the two conjuncts delivered by
`…exists_pullbackCharacterization_isKernelCokernel_morphismRestrict_of_adicCompletionChartSquares`
at `𝒦 = ` the chart-pullback of `𝒦|_V`, so the whole of that hypothesis follows from
`Stacks.Algebraization.HasAdicCompletionChartBaseChange`.

No `stacks` attribute is attached: this is a reduction of a hypothesis, not a statement of the
source. -/
public theorem hasAffineLocalDirectImageSolution_of_adicCompletionChartBaseChange
    (h : HasAdicCompletionChartBaseChange.{u}) : HasAffineLocalDirectImageSolution.{u} := by
  refine hasAffineLocalDirectImageSolution_of_adicCompletionChartAnnihilation ?_
  intro X' X _ _ π _ J K G 𝓕 β hiso V
  let : IsNoetherianRing ↥Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨X'', hN, π', hP, 𝓕', β', hc, ι, hιiso, θ, hδ, hγ⟩ := h π J K G 𝓕 β hiso V
  have := hN
  have := hP
  have := hιiso
  exact
    exists_pullbackCharacterization_isKernelCokernel_morphismRestrict_of_adicCompletionChartSquares
      π J G 𝓕 β V π' 𝓕' β' _ hc ι θ hδ hγ

/-- **[Stacks, Tag 088B] at a general base from the base change at the completion chart of each
affine open.** `Stacks.Algebraization.isDirectImageComparison_of_hasAffineLocalDirectImageSolution`
read through `…hasAffineLocalDirectImageSolution_of_adicCompletionChartBaseChange`:
`Stacks.Algebraization.IsDirectImageComparison` — the form of Stacks 088B that Stacks 088C,
`hDev` and `hSupp` consume — now has the single hypothesis
`Stacks.Algebraization.HasAdicCompletionChartBaseChange`.

No `stacks` attribute is attached: the tag is registered on
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions`. -/
public theorem isDirectImageComparison_of_adicCompletionChartBaseChange
    (h : HasAdicCompletionChartBaseChange.{u}) : IsDirectImageComparison.{u} :=
  isDirectImageComparison_of_hasAffineLocalDirectImageSolution
    (hasAffineLocalDirectImageSolution_of_adicCompletionChartBaseChange h)

/-! ### Stacks 088C, `hDev` and Stacks 088E from that one hypothesis -/

/-- **[Stacks, Tag 088C] from the base change at the completion chart of each affine open.** For
`A` Noetherian and complete along `I` and `f : Z ⟶ Spec A` proper, the completion functor
`Coh(𝒪_Z) ⥤ Coh(Z, I 𝒪_Z)` of Stacks 0880 is an equivalence, granted
`Stacks.Algebraization.HasAdicCompletionChartBaseChange` and nothing else.

`Stacks.Algebraization.isEquivalence_completionFunctor_of_isDirectImageComparison` at
`Stacks.Algebraization.isDirectImageComparison_of_adicCompletionChartBaseChange`.

No `stacks` attribute is attached: Stacks 088C is registered on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`. -/
public theorem isEquivalence_completionFunctor_of_adicCompletionChartBaseChange
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h : HasAdicCompletionChartBaseChange.{u})
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor Z (baseIdealSheaf A I f)).IsEquivalence :=
  isEquivalence_completionFunctor_of_isDirectImageComparison A I
    (isDirectImageComparison_of_adicCompletionChartBaseChange h) f

/-- **The hypothesis `hDev` of [Stacks, Tag 088E] from the base change at the completion chart of
each affine open.** The inductive step of the Noetherian induction of Stacks 088C, asked on every
closed subscheme of `Z` proper over `A`, holds granted
`Stacks.Algebraization.HasAdicCompletionChartBaseChange` and nothing else; it carries no
antecedent of its own, the dévissage hypothesis being unused.

`Stacks.Algebraization.hDev_of_isDirectImageComparison` at
`Stacks.Algebraization.isDirectImageComparison_of_adicCompletionChartBaseChange`.

No `stacks` attribute is attached: Stacks 088C is registered on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`, and this is its conclusion
read on the closed subschemes. -/
public theorem hDev_of_adicCompletionChartBaseChange
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of A))
    (h : HasAdicCompletionChartBaseChange.{u}) :
    ∀ (K : Z.IdealSheafData) (hK : IsProper (K.subschemeι ≫ f)),
      letI : IsProper (K.subschemeι ≫ f) := hK
      letI : IsLocallyNoetherian K.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
      ∀ L : K.subscheme.IdealSheafData,
        (∀ L' : K.subscheme.IdealSheafData, L < L' →
            ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems
                (baseIdealSheaf A I (K.subschemeι ≫ f)),
              IsSystemAnnihilatedBy L' 𝓖.obj →
                (completionFunctor K.subscheme
                  (baseIdealSheaf A I (K.subschemeι ≫ f))).essImage 𝓖) →
          ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems
              (baseIdealSheaf A I (K.subschemeι ≫ f)),
            IsSystemAnnihilatedBy L 𝓕.obj →
              (completionFunctor K.subscheme
                (baseIdealSheaf A I (K.subschemeι ≫ f))).essImage 𝓕 :=
  hDev_of_isDirectImageComparison A I f
    (isDirectImageComparison_of_adicCompletionChartBaseChange h)

/-- **[Stacks, Tag 088E], Grothendieck's existence theorem, from the base change at the
completion chart of each affine open and the Chow transport.** For `A` Noetherian and complete
along `I` and `f : Z ⟶ Spec A` separated, locally of finite type and quasi-compact, the functor of
Stacks 088D is an equivalence, granted

* `Stacks.Algebraization.HasAdicCompletionChartBaseChange`, and
* `hTransport`, the Chow datum of the second half of the source's proof, in the repaired
  disjunctive form of `Stacks.Algebraization.chowComparison_of_isDirectImageComparison`.

`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison` at
`Stacks.Algebraization.isDirectImageComparison_of_adicCompletionChartBaseChange`. `hTransport` is
a residual of its own and is not addressed here.

No `stacks` attribute is attached: Stacks 088E is registered on
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver`. -/
public theorem isEquivalence_completionFunctorProperOver_of_adicCompletionChartBaseChange
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : HasAdicCompletionChartBaseChange.{u})
    (hTransport : letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
      letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
      letI : IsNoetherian Z := { }
      ∀ (K : Z.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
        IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
          IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
            ∃ (W : Scheme.{u}) (π : W ⟶ Z) (_ : IsProper π) (_ : IsNoetherian W) (U : Z.Opens),
              IsIso (π ∣_ U) ∧
                (∀ e : ℕ, K < K ⊔ (Scheme.IdealSheafData.vanishingIdeal
                    (⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Z)) ^ (e + 1)) ∧
                  ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules W.ringCatSheaf,
                    HasProperSupport (π ≫ f) G.obj ∧
                      Nonempty ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕 ≅
                        (completionFunctor W ((baseIdealSheaf A I f).comap π)).obj G)) :
    (completionFunctorProperOver A I f).IsEquivalence :=
  isEquivalence_completionFunctorProperOver_of_isDirectImageComparison A I f
    (isDirectImageComparison_of_adicCompletionChartBaseChange h) hTransport

end Residue

/-! ### The annihilation half of Stacks 088B at the actual base change -/

section AffineBase

open Stacks.Coherent

variable (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)

/-- **The return of the annihilation along `g = Spec (B ^∧) ⟶ Spec B`.** Let `B` be Noetherian,
`J ⊆ B` an ideal and `α : F ⟶ G` a morphism of objects of `Coh(Spec B, J 𝒪)`. Let `ψ` be a
morphism of their pullbacks along `g` agreeing with `g^*α` level by level. If the levelwise
kernels and cokernels of `ψ` are annihilated by a power of `g ⁻¹𝒦 𝒪`, then those of `α` are
annihilated by the **same** power of `𝒦`.

This is the `Stacks.Algebraization.adicCompletionSpecMap` twin of
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_adicCompletionChartPullback`:
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_pullback_app` at `g`, whose two
hypotheses are `Stacks.Algebraization.flat_adicCompletionSpecMap` (Algebra 00MB) and
`Stacks.Algebraization.pullback_map_injective_of_coherentIdealPowerTorsion` (More on Algebra 05EC
in sheaf form). The agreement `hpb` is consumed by `congrArg` at each level, so no identification
of `((coherentAdicPullback g 𝒥).obj F).obj` with `F.obj ⋙ Scheme.Modules.pullback g` as functors
is needed.

**Unconditional, and no completeness hypothesis on `B`.** -/
public theorem isKernelCokernelAnnihilatedByPower_of_adicCompletionSpecMapPullback
    (K : (Spec (.of B)).IdealSheafData)
    {F G : CoherentAdicSystems (adicIdealSheaf B J)} (α : F.obj ⟶ G.obj)
    (ψ : ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj F).obj ⟶
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G).obj)
    (hpb : ∀ n : ℕᵒᵖ,
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map (α.app n) = ψ.app n)
    (hann : IsKernelCokernelAnnihilatedByPower (K.comap (adicCompletionSpecMap B J)) ψ) :
    IsKernelCokernelAnnihilatedByPower K α := by
  have := flat_adicCompletionSpecMap B J
  obtain ⟨t, ht, hkc⟩ := hann
  refine isKernelCokernelAnnihilatedByPower_of_pullback_app (adicCompletionSpecMap B J)
    (adicIdealSheaf B J)
    (fun {_ _} hM hN {_ _} huv =>
      pullback_map_injective_of_coherentIdealPowerTorsion B J hM hN huv)
    K α t ht (fun k => ?_) (fun k => ?_)
  · exact cast (congrArg (fun z => idealPowerMultiple (K.comap (adicCompletionSpecMap B J)) t
      (kernel z) = ⊥) (hpb (op k))).symm (hkc k).1
  · exact cast (congrArg (fun z => idealPowerMultiple (K.comap (adicCompletionSpecMap B J)) t
      (cokernel z) = ⊥) (hpb (op k))).symm (hkc k).2

variable {X' : Scheme.{u}} [IsNoetherian X'] (π : X' ⟶ Spec (.of B)) [IsProper π]
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)

/-- **The comparison `ι` of the two completed direct images at the base change along
`g = Spec (B ^∧) ⟶ Spec B` is an isomorphism.**
`Stacks.Algebraization.adicBaseChangeCompletedComparison` is by construction the composite of the
completion along `J B ^∧ 𝒪` of the degree-zero flat base change
`π'_*𝓕' ≅ g^*(π_*𝓕)` of Cohomology of Schemes 02KH
(`Stacks.Algebraization.adicBaseChangeProperPushforwardIso`) with the identification
`(g^*𝒜) ^∧ ≅ g^*(𝒜 ^∧)` of Stacks 0887 (`Stacks.Coherent.completionPullbackIso`), both
isomorphisms; the `.hom` of an isomorphism of coherent adic systems is an isomorphism of the
underlying inverse systems, which is the instance
`CategoryTheory.ObjectProperty.FullSubcategory`'s inclusion supplies.

This is what the annihilation half of Stacks 088B needs of `ι`, and all that
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison` was missing in
order to keep it. -/
public instance isIso_adicBaseChangeCompletedComparison :
    IsIso (adicBaseChangeCompletedComparison B J π 𝓕) := by
  have := isNoetherian_adicBaseChange B J π
  unfold adicBaseChangeCompletedComparison
  infer_instance

/-- **[Stacks, Tag 088B] over an affine base, in full — the characterization *and* the
annihilation — with no completeness hypothesis on the base ring.** Let `B` be Noetherian, `J ⊆ B`
an ideal, `π : X' ⟶ Spec B` proper with `X'` Noetherian, `𝓕` a coherent `𝒪_{X'}`-module, `(𝒢_n)`
an object of `Coh(Spec B, J 𝒪)`, `β : π^*(𝒢_n) ≅ 𝓕 ^∧` and `𝒦 ⊆ 𝒪_{Spec B}` quasi-coherent.
Granted the source's condition `hc` on the unit of the adjunction of the base change
`π' = π ×_{Spec B} Spec (B ^∧)` away from the support of `𝒦 𝒪_{Spec B ^∧}`, there is a morphism

`α : (𝒢_n) ⟶ ((π_*𝓕) ^∧)`

characterized in the source's sense and with its levelwise kernels and cokernels annihilated by a
power of `𝒦`.

This is `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeGamma` with the
annihilation clause kept rather than discarded, and it completes the source's second paragraph
over an affine base. Three things make it possible, and all three are recent:

* the two squares `hδ` and `hγ` at the actual base change,
  `Stacks.Algebraization.adicBaseChangeCompletedComparison_directImageQuotientComparison` and
  `Stacks.Algebraization.adicBaseChangeDirectImageComparison_square`, so that nothing of the
  paragraph is a binder;
* `Stacks.Algebraization.isIso_adicBaseChangeCompletedComparison`, which lets the annihilation of
  the solution `α'` over `Spec (B ^∧)` cross `ι` to `ψ = α' ≫ ι`
  (`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff`); and
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_adicCompletionSpecMapPullback`,
  which brings it home from `Spec (B ^∧)` to `Spec B` along the descended `α`, whose pullback is
  `ψ` by the second clause of
  `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionPullback`.

So the sheafification of `Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion` —
"piece 3" of `CompletionProper/AffineLocalSolution.lean` — is not needed: the annihilation is the
complete affine case's own, returned along a flat morphism faithful on power-torsion coherent
modules.

**What is still a binder, and what it is not.** `hc` is a binder, as it is in every statement of
this paragraph in the tree; it follows from the source's own hypothesis that `π'` is an
isomorphism over the complement of the support, by
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit`, once that
hypothesis is transported from `π` to its base change — which is not done here. What is **not**
missing is any part of the second paragraph itself: over an affine base the paragraph is closed.
The remaining obstruction to `Stacks.Algebraization.HasAffineLocalDirectImageSolution` is that an
affine open `V` of a general base is not `Spec Γ(X, V)` on the nose; see the module docstring.

No `stacks` attribute is attached: the affine-base form of Stacks 088B is registered on
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`,
and this is that statement at a base that is not assumed complete. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_of_adicBaseChangeGamma
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕)
    (K : (Spec (.of B)).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion J B))).ringCatSheaf,
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G ≅
          (completionFunctor (Spec (.of (AdicCompletion J B)))
            ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι
            (K.comap (adicCompletionSpecMap B J)).support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (adicBaseChangeMap B J π)).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π (adicIdealSheaf B J) G 𝓕 β α ∧
        IsKernelCokernelAnnihilatedByPower K α := by
  obtain ⟨α', hα', hann'⟩ :=
    exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase B J
      (adicBaseChangeMap B J π) (K.comap (adicCompletionSpecMap B J))
      (adicBaseChangeCoherent B J π 𝓕)
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G)
      (adicBaseChangeAlgebraizationIso B J π 𝓕 G β) hc
  obtain ⟨α, hα, hpb⟩ :=
    exists_isDirectImageCharacterized_of_adicCompletionPullback B J π 𝓕 G β
      (α' ≫ adicBaseChangeCompletedComparison B J π 𝓕) fun n => by
        rw [NatTrans.comp_app]
        exact comp_comp_eq_of_squares _ _ _ _ _ _ _ _
          (adicBaseChangeCompletedComparison_directImageQuotientComparison B J π 𝓕 n) (hα' n)
          (adicBaseChangeDirectImageComparison_square B J π 𝓕 G β n)
  exact ⟨α, hα, isKernelCokernelAnnihilatedByPower_of_adicCompletionSpecMapPullback B J K α _ hpb
    ((isKernelCokernelAnnihilatedByPower_comp_iso_iff (K.comap (adicCompletionSpecMap B J)) α'
      (asIso (adicBaseChangeCompletedComparison B J π 𝓕))).2 hann')⟩

end AffineBase

end Stacks.Algebraization

end
