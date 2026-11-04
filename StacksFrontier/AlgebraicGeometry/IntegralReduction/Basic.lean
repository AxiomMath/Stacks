module

public import StacksFrontier.AlgebraicGeometry.IntegralReduction.Transport
public import StacksFrontier.AlgebraicGeometry.CoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 01YE] reduced to the case of an integral scheme

The source proof of [Stacks, Tag 01YE] runs in three paragraphs. The first replaces the coherent
module `F` by the subsheaf of sections annihilated by the ideal of `Z`; the second observes that
such an `F` is a direct image `i_* G` and that it suffices to construct the ideal, the
multiplicity and the embedding **on `Z`**, whence "we have reduced to the case `X = Z`"; the
third does the integral case.

This file is the second paragraph, in full. The statement it reduces *to* is
`HasIntegralGenericIdealCoproductSub`, which is the conclusion of [Stacks, Tag 01YE] for an
integral Noetherian scheme and its own generic point — i.e. exactly the hypothesis of the
source's third paragraph.

## Main definitions

* `HasIntegralGenericIdealCoproductSub`: the `Z = X` case of [Stacks, Tag 01YE].

## Main results

* `exists_ideal_coproduct_of_annihilatedByKer`: **the reduction.** Given the integral case, a
  coherent module on a Noetherian scheme annihilated by the ideal of an integral closed
  subscheme admits the ideal, the multiplicity and the generically invertible embedding that
  [Stacks, Tag 01YE] asks for.

## Implementation notes

**Nothing here is a new theorem; the content is a composition**, and three of its four
ingredients are already in the library:

1. a coherent module annihilated by the kernel ideal of a closed immersion is the direct image
   of a *coherent* module on the subscheme —
   `Stacks.AlgebraicGeometry.Tag087TCoherentImage.exists_isCoherent_pushforward_iso`, which is
   the half of [Stacks, Tag 087T] this dévissage consumes;
2. the direct image of a finite coproduct of copies of a coherent ideal sheaf on a closed
   subscheme is coherent —
   `Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_pushforward_coproduct_const`
   composed with
   `AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit`;
3. direct image is left exact, hence preserves the monomorphism —
   `Stacks.SchemeCohomology.pushforward_preservesFiniteLimits` through
   `CategoryTheory.preserves_mono_of_preservesLimit` (no `PreservesMonomorphisms` instance for
   `Scheme.Modules.pushforward` is available).

The fourth, the transport of *invertibility near the generic point* across the direct image, is
`Stacks.AlgebraicGeometry.Tag01YEIntegralReduction.isIso_restrictFunctor_map_pushforward`.

**The open `U` is not constructed by hand.** What is needed is an open of `X` whose preimage is
the open `V` of `W` that the integral case supplies, and `Topology.IsInducing.functorObj` is
exactly that — the union of all opens with that preimage — with
`Topology.IsInducing.map_functorObj` computing the preimage. A closed immersion is in particular
inducing, so nothing about closedness is used; the complement of the image of `Vᶜ`, which is
what the source implicitly takes, is never formed.

**Noetherianness of the subscheme is derived, not assumed.** `IsNoetherian` is
`IsLocallyNoetherian` together with `CompactSpace`; the former comes from
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` along `i`, the latter from the
closed embedding of underlying spaces. So the integral case may be stated with the full
Noetherian hypothesis the source grants it, which makes it the weaker statement.

**No tag is attached.** [Stacks, Tag 01YE] has a single unlabelled assertion, so a conditional
form does not cover it, and the declaration below carries two hypotheses the tag's statement does
not have: `HasIntegralGenericIdealCoproductSub` and the annihilation condition. Both are
genuine: the first is the source's third paragraph and the second is removed by its first.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01YEIntegralReduction

/-- **The `Z = X` case of [Stacks, Tag 01YE].** On an integral Noetherian scheme `W` with
generic point `ξ`, every coherent module contains a finite coproduct of copies of one coherent
ideal sheaf, by a monomorphism that becomes invertible on a neighbourhood of `ξ`.

This is the statement of the source's third paragraph, and the one thing
`exists_ideal_coproduct_of_annihilatedByKer` is conditional on. The stalk hypothesis of
[Stacks, Tag 01YE] is absent because it is automatic here: `𝒪_{W, ξ}` is the function field of
`W`, so its maximal ideal is zero and annihilates everything. -/
def HasIntegralGenericIdealCoproductSub : Prop :=
  ∀ (W : Scheme.{u}), IsNoetherian W → IsIntegral W →
    ∀ ξ : W, IsGenericPoint ξ (Set.univ : Set W) →
      ∀ G : W.Modules, G.IsCoherent →
        ∃ (r : ℕ) (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
          I.toSheafOfModules.IsCoherent ∧
          ∃ ψ : (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ G, Mono ψ ∧
            ∃ V : W.Opens, ξ ∈ V ∧ IsIso ((Scheme.Modules.restrictFunctor V.ι).map ψ)

variable {X W : Scheme.{u}} (i : W ⟶ X)

/-- The source of a closed immersion into a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_isClosedImmersion [IsNoetherian X] [IsClosedImmersion i] :
    IsNoetherian W := by
  have _h₁ : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian i
  have _h₂ : CompactSpace W :=
    (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i).compactSpace
  constructor

/-- **The reduction of [Stacks, Tag 01YE] to the case of an integral scheme.**

Given the integral case, let `F` be a coherent module on a Noetherian scheme `X` annihilated by
the ideal of an integral closed subscheme `i : W ⟶ X`, and let `ξ` be the generic point of `W`.
Then there are a multiplicity `r`, a coherent ideal sheaf `I` on `W` and a monomorphism
`i_*(I^{⊕ r}) ⟶ F` whose source is coherent and which becomes invertible on a neighbourhood of
`i ξ` — the conclusion of [Stacks, Tag 01YE] verbatim.

This is the source's second paragraph: after the annihilation hypothesis, `F` *is* a direct
image, so the construction may be carried out on `W` and pushed forward. -/
theorem exists_ideal_coproduct_of_annihilatedByKer
    (h : HasIntegralGenericIdealCoproductSub.{u})
    [IsNoetherian X] [IsClosedImmersion i] [IsIntegral W]
    (ξ : W) (hξ : IsGenericPoint ξ (Set.univ : Set W))
    (F : X.Modules) [F.IsCoherent]
    (hann : Tag087TCoherentImage.AnnihilatedByKer i F) :
    ∃ (r : ℕ) (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsCoherent ∧
      ((Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent ∧
      ∃ φ : (Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ F,
        Mono φ ∧ ∃ U : X.Opens, i ξ ∈ U ∧
          IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
  have hWN : IsNoetherian W := isNoetherian_of_isClosedImmersion i
  -- `F` is the direct image of a coherent module on `W`.
  obtain ⟨G, hGc, ⟨e⟩⟩ := Tag087TCoherentImage.exists_isCoherent_pushforward_iso i F hann
  -- The integral case, applied on `W`.
  obtain ⟨r, I, hIc, ψ, hmono, V, hξV, hiso⟩ := h W hWN ‹_› ξ hξ G hGc
  -- An open of `X` whose preimage is `V`.
  have hind : Topology.IsInducing (ConcreteCategory.hom i.base) :=
    (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i).isInducing
  have hpre : i ⁻¹ᵁ hind.functorObj V = V := hind.map_functorObj V
  refine ⟨r, I, hIc, ?_, (Scheme.Modules.pushforward i).map ψ ≫ e.hom, ?_,
    hind.functorObj V, ?_, ?_⟩
  · -- Coherence of the direct image of the coproduct.
    exact IrreducibleDevissage.isCoherent_pushforward_coproduct_const i I.toSheafOfModules
      (ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit i I
        (isQuasicoherent_of_isCoherent _)) r
  · -- Direct image is left exact, so it preserves the monomorphism.
    have hpl : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.pushforward i) :=
      inferInstance
    have hmono' : Mono ((Scheme.Modules.pushforward i).map ψ) :=
      @preserves_mono_of_preservesLimit _ _ _ _ (Scheme.Modules.pushforward i) _ _ ψ
        hpl.preservesLimit hmono
    exact mono_comp' (hg := hmono') (hf := inferInstance)
  · -- `ξ ∈ V = i ⁻¹ᵁ U`, so `i ξ ∈ U`.
    exact (congrArg (fun s : W.Opens => ξ ∈ s) hpre.symm ▸ hξV : ξ ∈ i ⁻¹ᵁ hind.functorObj V)
  · -- Invertibility near `i ξ`, transported through the direct image.
    rw [Functor.map_comp]
    have h₁ := isIso_restrictFunctor_map_pushforward i ψ V hiso (hind.functorObj V)
      hpre.le
    exact IsIso.comp_isIso' h₁ inferInstance

end Stacks.AlgebraicGeometry.Tag01YEIntegralReduction

end
