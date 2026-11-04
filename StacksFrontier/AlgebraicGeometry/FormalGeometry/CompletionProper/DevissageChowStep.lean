module

public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Refinements
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMap
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective

/-!
# The Chow step of the dévissage of Tag 088C

In the inductive step of the proof of [Stacks, Tag 088C] the source, having replaced `X` by the
closed subscheme `V(𝒦)`, writes:

> Apply Chow's lemma to find a proper surjective morphism `f : X' → X` which is an isomorphism
> over a dense open `U ⊆ X` such that `X'` is projective over `A`. Let `𝒦` be the quasi-coherent
> sheaf of ideals cutting out the reduced complement `X ∖ U`. By the projective case of
> Grothendieck's existence theorem there exists a coherent module `𝓕'` on `X'` such that
> `(𝓕')^ ≅ (f^*𝓕_n)`. By Proposition 02O5 the `𝒪_X`-module `𝓗 = f_*𝓕'` is coherent and by
> Lemma 088B there exists a morphism `(𝓕_n) → 𝓗^` of `Coh(X, ℐ)` whose kernel and cokernel are
> annihilated by a power of `𝒦`.

**This file carries out that paragraph**, for an arbitrary scheme `Z` proper over `Spec A`: it is
`Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_of_isProper`. Every ingredient is
unconditional in this library:

* Chow's lemma, [Stacks, Tag 0200], is `AlgebraicGeometry.hasDenseChowModification`;
* that the Chow modification is projective over `A` is
  `AlgebraicGeometry.isProjective_chowModification` ([Stacks, Tag 0201]), applied to the
  composite `Z' ⟶ Z ⟶ Spec A` over the identity of `Spec A`;
* the projective case, [Stacks, Tag 0885], is
  `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`;
* the coherence of `f_*𝓕'`, [Stacks, Tag 02O5], and the map `α`, [Stacks, Tag 088B], are both
  inside `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_comparisonMap`.

The ideal sheaf `𝒦` of the reduced complement is Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` of `Z ∖ U`, whose zero locus is `Z ∖ U`,
so that "isomorphism over `U`" is the hypothesis `IsIso (f ∣_ 𝒦.support.compl)` of Tag 088B.

The file also records `Stacks.Coherent.essImage_completionFunctor_of_isEmpty`: on the empty
scheme every coherent adic system is in the essential image of the completion functor. The
inductive step needs this case separately, because on the empty scheme no ideal sheaf has a
nonvanishing power, which the subsequent application of [Stacks, Tag 088A] requires.

## Main results

* `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_of_isProper` — the Chow step.
* `Stacks.Coherent.essImage_completionFunctor_of_isEmpty` — the empty case.

## Implementation notes

Nothing here is registered against a Stacks tag: both statements are steps inside the proof of
[Stacks, Tag 088C]. The ideal sheaf along which the system is given is an arbitrary `J` equal to
`I · 𝒪_Z`, rather than `baseIdealSheaf A I g` itself, because in the application `J` arrives as
the inverse image `(I · 𝒪_X).comap (V(𝒦) ⟶ X)`, which is only propositionally equal to
`I · 𝒪_{V(𝒦)}` (`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap`), and the category of
coherent adic systems depends on the ideal sheaf.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 0201](https://stacks.math.columbia.edu/tag/0201)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

/-- A scheme proper over the spectrum of a Noetherian ring is Noetherian. -/
private theorem isNoetherian_of_isProper_spec (A : Type u) [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g] : IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := QuasiCompact.compactSpace_of_compactSpace g
  { }

/-- **The Chow step of [Stacks, Tag 088C].** Let `A` be a Noetherian ring complete with respect to
an ideal `I`, let `g : Z ⟶ Spec A` be proper and let `(𝓝_n)` be an object of `Coh(Z, I · 𝒪_Z)`.
Then there are a dense open `U ⊆ Z`, a coherent `𝒪_Z`-module `𝓗` and a morphism
`α : (𝓝_n) ⟶ 𝓗^` of `Coh(Z, I · 𝒪_Z)` whose levelwise kernels and cokernels are annihilated by a
power of the ideal sheaf of the reduced complement `Z ∖ U`.

Chow's lemma gives a proper surjective `π : Z' ⟶ Z`, an isomorphism over a dense open `U`, with
`Z'` immersed in a projective space over `A`; `Z'` is then projective over `A`, so by
[Stacks, Tag 0885] the system `(π^*𝓝_n)` is the completion of a coherent `𝓕'` on `Z'`, and
[Stacks, Tag 088B] applied to `π`, `𝓕'` and that isomorphism produces `α` with target the
completion of `𝓗 = π_*𝓕'`, which is coherent by [Stacks, Tag 02O5]. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_of_isProper
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of A)) [IsProper g] (J : Z.IdealSheafData)
    (hJ : J = baseIdealSheaf A I g) (N : CoherentAdicSystems J) :
    letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
    ∃ (U : Z.Opens) (_ : Dense (U : Set Z))
      (H : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf)
      (α : N ⟶ (completionFunctor Z J).obj H),
      IsKernelCokernelAnnihilatedByPower
        (Scheme.IdealSheafData.vanishingIdeal U.compl) α.hom := by
  subst hJ
  have : IsNoetherian Z := isNoetherian_of_isProper_spec A g
  obtain ⟨n, Z', π, i, U, hπ, -, himm, hcomm, hdense, hiso⟩ := hasDenseChowModification g
  have := hπ
  have := himm
  have hproj : AlgebraicGeometry.IsProjective (π ≫ g) :=
    isProjective_chowModification (f := 𝟙 (Spec (.of A))) (π ≫ g) i
      (by rw [Category.comp_id, hcomm])
  have : IsNoetherian Z' := isNoetherian_of_isProper_spec A (π ≫ g)
  have hEq : (completionFunctor Z' ((baseIdealSheaf A I g).comap π)).IsEquivalence := by
    rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap]
    exact isEquivalence_completionFunctor_of_isProjective_of_vanishing A I (π ≫ g) hproj
  obtain ⟨F', ⟨β⟩⟩ := Functor.EssSurj.mem_essImage
    (F := completionFunctor Z' ((baseIdealSheaf A I g).comap π))
    ((coherentAdicPullback π (baseIdealSheaf A I g)).obj N)
  have : F'.obj.IsCoherent := F'.property
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal U.compl).support.compl = U := by
    ext x
    simp [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hf : IsIso (π ∣_ (Scheme.IdealSheafData.vanishingIdeal U.compl).support.compl) := by
    rw [hsupp]
    exact hiso
  obtain ⟨α, hα⟩ := exists_isKernelCokernelAnnihilatedByPower_comparisonMap
    (baseIdealSheaf A I g) (Scheme.IdealSheafData.vanishingIdeal U.compl) π hf N F'.obj β.symm
  exact ⟨U, hdense, _, α, hα⟩

/-- **On the empty scheme every coherent adic system is a completion.** A scheme with no points
carries exactly one morphism between any two sheaves of modules
(`AlgebraicGeometry.subsingleton_hom_of_isEmpty`), so any two coherent adic systems are
isomorphic, the zero maps being mutually inverse. -/
public theorem essImage_completionFunctor_of_isEmpty {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    [IsEmpty Z] (J : Z.IdealSheafData) (N : CoherentAdicSystems J) :
    (completionFunctor Z J).essImage N := by
  have hsub : ∀ P Q : CoherentAdicSystems J, Subsingleton (P ⟶ Q) := fun P Q =>
    ⟨fun a b => ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))⟩
  let zero : ∀ P Q : CoherentAdicSystems J, P ⟶ Q := fun P Q =>
    ObjectProperty.homMk
      { app := fun _ => 0
        naturality := fun _ _ _ => Subsingleton.elim _ _ }
  refine ⟨⟨N.obj.obj (op 0), N.property.1 0⟩, ⟨
    { hom := zero _ _
      inv := zero _ _
      hom_inv_id := (hsub _ _).elim _ _
      inv_hom_id := (hsub _ _).elim _ _ }⟩⟩

end Stacks.Coherent

end
