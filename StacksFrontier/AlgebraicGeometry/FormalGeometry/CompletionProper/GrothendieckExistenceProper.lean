module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedPushforwardEssSurj
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Devissage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageChowNonNilpotent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageChowStep
public import StacksCore.Tactic.StacksAttribute

/-!
# Grothendieck's existence theorem for a proper morphism

**Stacks 088C.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, let
`f : X ⟶ Spec A` be a proper morphism and put `𝓘 = I · 𝒪_X`. Then the completion functor of
Stacks 0880, `Coh(𝒪_X) ⥤ Coh(X, 𝓘)`, is an equivalence.

`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`
(`CompletionProper/Devissage.lean`) proves this from two hypotheses: `hFF`, the theorem on formal
functions in degree zero, and `hDev`, the inductive step of the source's Noetherian induction over
the quasi-coherent ideal sheaves of `X`. **This file discharges both**, so that the statement
below has exactly the source's hypotheses.

`hFF` is `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper`. `hDev` is
`Stacks.Coherent.essImage_completionFunctor_of_devissageStep`, which follows the source's
inductive step line by line. Let `𝒦` be an ideal sheaf such that every object of `Coh(X, 𝓘)`
killed by a strictly larger ideal sheaf is in the essential image, and let `(𝓕_n)` be killed by
`𝒦`.

* *Replacing `X` by `Z = V(𝒦)`* (Stacks 087T, for adic systems): `(𝓕_n)` is the direct image of
  an object `(𝓝_n)` of `Coh(Z, 𝓘 𝒪_Z)`, by
  `Stacks.Coherent.essImage_coherentAdicPushforwardClosed_subscheme`.
* If `Z` is empty, `(𝓝_n)` is a completion for trivial reasons,
  `Stacks.Coherent.essImage_completionFunctor_of_isEmpty`.
* Otherwise *Chow's lemma, 0885, 02O5 and 088B* on `Z ⟶ Spec A`, which is proper, give a dense
  open `U ⊆ Z`, a coherent `𝓗` and `α : (𝓝_n) ⟶ 𝓗^` with kernel and cokernel killed by a power
  of the ideal sheaf `ℒ` of the reduced complement `Z ∖ U`:
  `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_of_isProper`.
* *The powers of `ℒ` lie in `Ξ`* and *088A concludes*: since `U` is a nonempty open, no power of
  `ℒ` vanishes, so every power pushes forward to an ideal sheaf of `X` strictly larger than `𝒦`,
  where the induction hypothesis applies; this is hypothesis (1) of Stacks 088A on `Z`, and 088A
  makes `(𝓝_n)` a completion. That is
  `Stacks.Coherent.essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel_of_dense`, with
  full faithfulness on `X` from Stacks 0883.
* Direct image along `Z ⟶ X` commutes with completion
  (`Stacks.Coherent.completionPushforwardNatIso`), so `(𝓕_n)` is a completion on `X`.

## Main results

* `Stacks.Coherent.essImage_completionFunctor_of_devissageStep` — the inductive step `hDev`.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper` — **Stacks 088C.**

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01Y8](https://stacks.math.columbia.edu/tag/01Y8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

/-- **The inductive step of [Stacks, Tag 088C].** Let `A` be a Noetherian ring complete with
respect to `I` and `f : X ⟶ Spec A` proper, with `𝓘 = I · 𝒪_X`. Let `𝒦` be a quasi-coherent ideal
sheaf on `X` such that every object of `Coh(X, 𝓘)` killed by an ideal sheaf strictly larger than
`𝒦` is in the essential image of the completion functor. Then so is every object killed by `𝒦`.

This is the hypothesis `hDev` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`; see the module docstring
for the outline, which is the source's. -/
public theorem essImage_completionFunctor_of_devissageStep
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ K : X.IdealSheafData,
      (∀ K' : X.IdealSheafData, K < K' →
          ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
            IsSystemAnnihilatedBy K' 𝓖.obj →
              (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) →
        ∀ 𝓕 : CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K 𝓕.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓕 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  intro K hIH 𝓕 hK
  obtain ⟨hff⟩ := fullyFaithful_completionFunctor_of_isProper A I f
  let : IsLocallyNoetherian K.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion K.subschemeι
  obtain ⟨N, ⟨e⟩⟩ :=
    essImage_coherentAdicPushforwardClosed_subscheme (baseIdealSheaf A I f) K 𝓕 hK
  have hN : (completionFunctor K.subscheme
      ((baseIdealSheaf A I f).comap K.subschemeι)).essImage N := by
    rcases isEmpty_or_nonempty K.subscheme with hZ | hZ
    · exact essImage_completionFunctor_of_isEmpty _ N
    · obtain ⟨U, hU, H, α, hα⟩ := exists_isKernelCokernelAnnihilatedByPower_of_isProper A I
        (K.subschemeι ≫ f) _
        (Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f K.subschemeι) N
      exact essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel_of_dense
        (baseIdealSheaf A I f) K hff hIH U hU.nonempty N H α hα
  obtain ⟨M, ⟨eM⟩⟩ := hN
  exact ⟨(coherentPushforwardClosed K.subschemeι).obj M,
    ⟨(completionPushforwardNatIso K.subschemeι (baseIdealSheaf A I f)).app M ≪≫
      (coherentAdicPushforwardClosed K.subschemeι (baseIdealSheaf A I f)).mapIso eM ≪≫ e⟩⟩

end Stacks.Coherent

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-- **Stacks 088C: Grothendieck's existence theorem for a proper morphism.** Let `A` be a
Noetherian ring complete with respect to an ideal `I`, let `f : X ⟶ Spec A` be a proper morphism
of schemes and set `𝓘 = I · 𝒪_X`. Then the completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of
Stacks 0880 is an equivalence.

This is `Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage` with both of its
hypotheses discharged: `hFF` by the theorem on formal functions in degree zero over a complete
base, `isIso_globalSectionsToLimit_of_isProper`, and `hDev` by
`Stacks.Coherent.essImage_completionFunctor_of_devissageStep`. -/
@[stacks 088C "Grothendieck's existence theorem: A Noetherian and complete with respect to I, \
f : X -> Spec A proper and the ideal sheaf I O_X; the completion functor of 0880 from coherent \
O_X-modules to coherent I O_X-adic systems is an equivalence"]
public theorem isEquivalence_completionFunctor_of_isProper
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence :=
  isEquivalence_completionFunctor_of_devissage A I f
    (isIso_globalSectionsToLimit_of_isProper A I f)
    (Stacks.Coherent.essImage_completionFunctor_of_devissageStep A I f)

end Stacks.Algebraization

end
