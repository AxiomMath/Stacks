module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompletelyDecomposedCover
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatCycleClasses
public import StacksFrontier.AlgebraicGeometry.Flatness.RaynaudGrusonFlattening0815

/-!
# Relative cycles and the cycle class map after a proper completely decomposed cover

Let `f : X ⟶ S` be of finite type with `S` Noetherian, let `r ≥ 0` and let `α` be a family of
`r`-cycles on the fibres of `X/S`. [Tag 0H59](https://stacks.math.columbia.edu/tag/0H59) asserts,
for `α` a relative `r`-cycle, that there is a proper, completely decomposed morphism `g : S' ⟶ S`
— completely decomposed in the sense of [Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI) —
such that `g^*α` lies in the image of the cycle class map of
[Tag 0H58](https://stacks.math.columbia.edu/tag/0H58). Tag 0H59 itself is
`Stacks.Chow.exists_isProper_isCompletelyDecomposed_relativeCycleClassMap_eq`.

Its proof is a Noetherian induction,
`AlgebraicGeometry.exists_isProper_isCompletelyDecomposed_of_integral_case`, for a property `P` of
morphisms into `S` that holds on morphisms out of the empty scheme and is inherited by binary
coproducts. This file states the property `P` of Tag 0H59, proves its empty clause, and proves the
geometric input of the integral case.

## Main definitions

* `Stacks.Chow.PullbackInCycleClassImage` — the conclusion of Tag 0H59 read as a property of a
  single morphism `g : T ⟶ S`: the base change `g^*α` is in the image of the cycle class map on
  `X ×_S T / T`.

## Main results

* `Stacks.Chow.pullbackInCycleClassImage_of_isEmpty` — the property holds for a morphism out of
  the empty scheme.
* `Stacks.Chow.exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage` — the shape of
  Tag 0H59, from the coproduct clause and the integral case.
* `AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_flat_of_hasFlatteningBlowup` — the
  flattening blowup of Tag 0815 supplies a morphism `b : S' ⟶ S` which is proper, is an
  isomorphism over `U`, and carries a closed subscheme of `X ×_S S'` flat over `S'`.

## Implementation notes

`Stacks.Chow.PullbackInCycleClassImage` is phrased with `Stacks.Chow.cycleClassMap`, the
homomorphism of Tag 0H6V whose values are families of `r`-cycles on fibres and which needs no
Noetherian hypothesis, rather than with the cycle class map `Stacks.Chow.relativeCycleClassMap` of
Tag 0H58 into `z(X/S, r)`. By `Stacks.Chow.relativeCycleClassMap_val` the latter is the former
followed by the injective inclusion `z(X/S, r) ⊆ FamilyOfCycles`, so the two give the same
membership in the image.

Properness of the blowup is `Stacks.Blowup.IsAdmissibleBlowup.isProper`, from finite presentation
of the centre through the affine-local half of Tag 01TV, rather than projectivity of the blowup
(Tag 02NS) as in the source. That the blowup is an isomorphism over the open its centre avoids is
Tag 02OS, `Stacks.Blowup.isIso_blowUpToBase_restrict_of_subset_compl_support_reesData`. The blowup
used is `Stacks.Blowup.blowUp`, against which the flattening predicates of Tag 0815 and the strict
transform are stated; `Stacks.Blowup.blowUpIso` compares it with the other construction.

The coproduct clause of the induction is `Stacks.Chow.pullbackInCycleClassImage_coprod_desc` and
its integral case is `Stacks.Chow.exists_isProper_pullbackInCycleClassImage_of_isIntegral`, which
uses generic flatness (Tag 052A), the flattening theorem
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup` (the content of Tag 081R that the source
uses), Tag 080N and Tag 0H55.

## References

* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Equation 0H58](https://stacks.math.columbia.edu/tag/0H58)
* [Stacks Project, Definition 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
* [Stacks Project, Lemma 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Theorem 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Lemma 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Lemma 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Proposition 052A](https://stacks.math.columbia.edu/tag/052A)
* [Stacks Project, Lemma 0H55](https://stacks.math.columbia.edu/tag/0H55)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### The flattening blowup of Tag 0815 -/

namespace AlgebraicGeometry

/-- **The flattening blowup of Tag 0815.** Let `f : X ⟶ S` be a morphism and `U ⊆ S` an open
over which `X` can be flattened by a `U`-admissible blowing up, that is, for which
`AlgebraicGeometry.HasFlatteningBlowup f U` holds. Then there are a morphism `b : S' ⟶ S` and a
closed subscheme `Z ⊆ X ×_S S'` such that

* `b` is proper,
* `b` is an isomorphism over `U`, and
* `Z` is flat over `S'`. -/
theorem exists_isProper_isIso_morphismRestrict_flat_of_hasFlatteningBlowup
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (h : HasFlatteningBlowup f U) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (Z : Scheme.{u}) (j : Z ⟶ pullback f b),
      IsProper b ∧ IsIso (b ∣_ U) ∧ IsClosedImmersion j ∧ Flat (j ≫ pullback.snd f b) := by
  obtain ⟨I, hfp, hdisj, hflat⟩ := h
  refine ⟨Stacks.Blowup.blowUp I, Stacks.Blowup.blowUpToBase I,
    Stacks.Blowup.strictTransform f I, Stacks.Blowup.strictTransformι f I,
    (Stacks.Blowup.isAdmissibleBlowup_blowUpToBase hfp hdisj).isProper,
    Stacks.Blowup.isIso_blowUpToBase_restrict_of_subset_compl_support_reesData I U
      fun _ hz ↦ Set.disjoint_left.mp hdisj hz,
    ?_, hflat⟩
  rw [Stacks.Blowup.strictTransformι]
  infer_instance

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The conclusion of Tag 0H59 as a property of a morphism into the base -/

/-- **The conclusion of Tag 0H59, as a property of one morphism into the base.** For `α` a family
of `r`-cycles on the fibres of `X/S` and `g : T ⟶ S`, the base change `g^*α` lies in the image of
the cycle class map of `X ×_S T / T`. -/
def PullbackInCycleClassImage {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r) {T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  ∃ c : FreeAbelianGroup (HilbertCycleDatum (pullback.snd f g) r),
    cycleClassMap (pullback.snd f g) r c = baseChangeFamily f g r α

/-- **The empty clause of the Noetherian induction for Tag 0H59.** A morphism out of the empty
scheme has `Stacks.Chow.PullbackInCycleClassImage`. -/
theorem pullbackInCycleClassImage_of_isEmpty {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r)
    {T : Scheme.{u}} (g : T ⟶ S) (hT : IsEmpty T) :
    PullbackInCycleClassImage f r α g :=
  ⟨0, funext fun t ↦ hT.elim t⟩

/-- **The shape of Tag 0H59, from the coproduct clause and the integral case.** Let `S` be
Noetherian, let `f : X ⟶ S` be of finite type and let `α` be a family of `r`-cycles on the fibres
of `X/S`. Granted

* `hcoprod`, that `Stacks.Chow.PullbackInCycleClassImage` is inherited by a binary coproduct of
  two morphisms into `S`, and
* `hintegral`, the integral case: over every integral closed subscheme of `S` there is a proper
  morphism, an isomorphism over a dense open, whose composite to `S` has
  `Stacks.Chow.PullbackInCycleClassImage`,

there is a proper, completely decomposed `g : S' ⟶ S` with `g^*α` in the image of the cycle class
map. -/
theorem exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage {X S : Scheme.{u}}
    [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (r : ℕ)
    (α : FamilyOfCycles f r)
    (hcoprod : ∀ {T₁ T₂ : Scheme.{u}} (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ S),
      PullbackInCycleClassImage f r α g₁ → PullbackInCycleClassImage f r α g₂ →
      PullbackInCycleClassImage f r α (coprod.desc g₁ g₂))
    (hintegral : ∀ I : S.IdealSheafData, IsIntegral I.subscheme →
      ∃ (T : Scheme.{u}) (g : T ⟶ I.subscheme), IsProper g ∧
        PullbackInCycleClassImage f r α (g ≫ I.subschemeι) ∧
        ∃ U : I.subscheme.Opens, Dense (U : Set I.subscheme) ∧ IsIso (g ∣_ U)) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsProper g ∧ PullbackInCycleClassImage f r α g ∧ IsCompletelyDecomposed g :=
  exists_isProper_isCompletelyDecomposed_of_integral_case
    (fun {_} g ↦ PullbackInCycleClassImage f r α g)
    (fun g hT ↦ pullbackInCycleClassImage_of_isEmpty f r α g hT) hcoprod hintegral

end Stacks.Chow

end
