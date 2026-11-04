module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Refinements of a Chow modification

Fix the situation of **Chow's lemma over a Noetherian base**: a separated morphism `f : X ⟶ S`
of finite type over a Noetherian scheme `S`, a proper surjective `π : X' ⟶ X`, an immersion
`i : X' ⟶ 𝐏ⁿ_S` with `π ≫ f = i ≫ (𝐏ⁿ_S ↘ S)`, and a dense open `U ⊆ X` over which `π` is an
isomorphism. The modification is then better than it looks, in three ways.

First, `π` is H-projective, hence projective. Its graph `X' ⟶ 𝐏ⁿ_S ×_S X = 𝐏ⁿ_X`, induced by `i`
and `π`, is proper — it becomes `π` after the projection to `X`, which is separated — and a
monomorphism — it becomes the immersion `i` after the projection to `𝐏ⁿ_S` — hence a closed
immersion into a projective space over `X`.

Second, `π⁻¹(U)` may be assumed scheme-theoretically dense in `X'`: replace `X'` by the
scheme-theoretic closure of `π⁻¹(U)`, which changes neither `n` nor `U` and keeps `π` proper,
surjective and an isomorphism over `U`.

Third, if `X` is reduced then `X'` may be chosen reduced, because the closure just described has
reduced source `π⁻¹(U) ≅ U`, an open subscheme of `X`.

## Main definitions

* `AlgebraicGeometry.chowGraph` is the graph `X' ⟶ 𝐏ⁿ_X` of a modification and its immersion
  into `𝐏ⁿ_S`.

## Main results

* `AlgebraicGeometry.isClosedImmersion_chowGraph`: the graph is a closed immersion.
* `AlgebraicGeometry.isProjectiveMorphism_chowModification`: `π` is H-projective.
* `AlgebraicGeometry.isProjective_chowModification`: `π` is projective.
* `AlgebraicGeometry.exists_isSchemeTheoreticallyDense_chowModification`: the modification may be
  replaced by one in which `π⁻¹(U)` is scheme-theoretically dense.
* `AlgebraicGeometry.exists_isReduced_chowModification`: over a reduced `X` that replacement is
  reduced.

## Implementation notes

Projective space is `AlgebraicGeometry.ProjectiveSpace`, the spelling in which
`AlgebraicGeometry.HasDenseChowModification` states the conclusion of Chow's lemma, while
H-projectivity `AlgebraicGeometry.IsProjectiveMorphism` is stated with the definitionally equal
`AlgebraicGeometry.projectiveSpaceOver`. The two spellings meet in exactly one place, the proof
of `AlgebraicGeometry.isProjectiveMorphism_chowModification`, which hands
`AlgebraicGeometry.chowGraph` and `AlgebraicGeometry.chowGraph_over` to the definition of
H-projectivity; everything else stays inside one spelling.

The scheme-theoretic closure of an open subscheme `V` is the scheme-theoretic image
`AlgebraicGeometry.Scheme.Hom.image` of `V.ι`. Its inclusion is quasi-compact because `X'` is
locally Noetherian, which follows from the hypotheses on `f` and the properness of `π`; this is
the only use made of the Noetherian hypothesis.

## References

* [Stacks Project, Tag 0201](https://stacks.math.columbia.edu/tag/0201)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X S X' : Scheme.{u}} {n : ℕ} {f : X ⟶ S}

/-! ### H-projectivity of the modification -/

/-- The **graph** of a modification `π : X' ⟶ X` carrying an immersion `i : X' ⟶ 𝐏ⁿ_S` over `S`:
the morphism `X' ⟶ 𝐏ⁿ_S ×_S X` with components `i` and `π`, read through the identification
`𝐏ⁿ_S ×_S X = 𝐏ⁿ_X`. -/
def chowGraph (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S)
    (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) : X' ⟶ ProjectiveSpace n X :=
  pullback.lift i π hcomm.symm ≫ (ProjectiveSpace.baseChangeIso n f).hom

/-- The graph of a modification lies over `π`. -/
theorem chowGraph_over (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S)
    (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    chowGraph π i hcomm ≫ (ProjectiveSpace n X ↘ X) = π := by
  rw [chowGraph, Category.assoc, ProjectiveSpace.baseChangeIso_hom_over, pullback.lift_snd]

/-- The morphism `X' ⟶ 𝐏ⁿ_S ×_S X` underlying the graph recovers the immersion into `𝐏ⁿ_S`. -/
theorem chowLift_comp_fst (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S)
    (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    pullback.lift i π hcomm.symm ≫ pullback.fst (ProjectiveSpace n S ↘ S) f = i :=
  pullback.lift_fst _ _ _

/-- The morphism `X' ⟶ 𝐏ⁿ_S ×_S X` underlying the graph recovers the modification `π`. -/
theorem chowLift_comp_snd (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S)
    (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    pullback.lift i π hcomm.symm ≫ pullback.snd (ProjectiveSpace n S ↘ S) f = π :=
  pullback.lift_snd _ _ _

/-- **The graph of a proper modification is a closed immersion.** It is proper, because the
projection `𝐏ⁿ_S ×_S X ⟶ X` is separated and the composite is `π`, and a monomorphism, because
the composite with the projection to `𝐏ⁿ_S` is the immersion `i`. -/
@[stacks 0201 "part (1): `X' ⟶ 𝐏ⁿ_S ×_S X = 𝐏ⁿ_X` is a closed immersion"]
theorem isClosedImmersion_chowGraph (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S) [IsProper π]
    [IsImmersion i] (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    IsClosedImmersion (chowGraph π i hcomm) := by
  have hsep : IsSeparated (pullback.snd (ProjectiveSpace n S ↘ S) f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated)
      (IsPullback.of_hasPullback (ProjectiveSpace n S ↘ S) f) inferInstance
  have hmono : Mono (pullback.lift i π hcomm.symm) :=
    mono_of_mono_fac (chowLift_comp_fst π i hcomm)
  have hproper : IsProper (pullback.lift i π hcomm.symm) := by
    have : IsProper
        (pullback.lift i π hcomm.symm ≫ pullback.snd (ProjectiveSpace n S ↘ S) f) := by
      rw [chowLift_comp_snd π i hcomm]
      infer_instance
    have := hsep
    exact IsProper.of_comp _ (pullback.snd (ProjectiveSpace n S ↘ S) f)
  have : IsClosedImmersion (pullback.lift i π hcomm.symm) :=
    (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨hproper, hmono⟩
  rw [chowGraph]
  infer_instance

/-- **The modification in Chow's lemma is H-projective.** Its graph is a closed immersion into
the projective space `𝐏ⁿ_X` over `X`, compatibly with the structure morphism. -/
@[stacks 0201 "part (1): `π` is H-projective"]
theorem isProjectiveMorphism_chowModification (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S)
    [IsProper π] [IsImmersion i] (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    IsProjectiveMorphism π :=
  ⟨n, chowGraph π i hcomm, isClosedImmersion_chowGraph π i hcomm, chowGraph_over π i hcomm⟩

/-- **The modification in Chow's lemma is projective**: an H-projective morphism is projective. -/
@[stacks 0201 "part (1): `π` is projective"]
theorem isProjective_chowModification (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S) [IsProper π]
    [IsImmersion i] (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    IsProjective π :=
  (isProjectiveMorphism_chowModification π i hcomm).isProjective

/-! ### Scheme-theoretic density of the inverse image of the dense open -/

/-- The scheme-theoretic closure of `π⁻¹(U)` in `X'` is again a modification of `X` immersed in
`𝐏ⁿ_S` over `S`, still an isomorphism over `U`, in which `π⁻¹(U)` is scheme-theoretically
dense. -/
private theorem schemeTheoreticClosure_spec (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S) (U : X.Opens)
    [IsProper π] [IsImmersion i] (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S))
    (hU : Dense (U : Set X)) (hiso : IsIso (π ∣_ U)) :
    IsProper ((π ⁻¹ᵁ U).ι.imageι ≫ π) ∧ Surjective ((π ⁻¹ᵁ U).ι.imageι ≫ π) ∧
      IsImmersion ((π ⁻¹ᵁ U).ι.imageι ≫ i) ∧
      ((π ⁻¹ᵁ U).ι.imageι ≫ π) ≫ f =
        ((π ⁻¹ᵁ U).ι.imageι ≫ i) ≫ (ProjectiveSpace n S ↘ S) ∧
      IsIso (((π ⁻¹ᵁ U).ι.imageι ≫ π) ∣_ U) ∧
      Scheme.Opens.IsSchemeTheoreticallyDense (((π ⁻¹ᵁ U).ι.imageι ≫ π) ⁻¹ᵁ U) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have hdom : IsDominant ((π ⁻¹ᵁ U).ι.imageι ≫ π) := by
    have hbase : IsDominant ((π ⁻¹ᵁ U).ι ≫ π) := by
      have : IsDominant U.ι := Opens.isDominant_ι hU
      have h : IsDominant ((π ∣_ U) ≫ U.ι) := inferInstance
      rwa [morphismRestrict_ι] at h
    have hcomp : IsDominant ((π ⁻¹ᵁ U).ι.toImage ≫ (π ⁻¹ᵁ U).ι.imageι ≫ π) := by
      rw [← Category.assoc, Scheme.Hom.toImage_imageι]
      exact hbase
    exact IsDominant.of_comp (π ⁻¹ᵁ U).ι.toImage ((π ⁻¹ᵁ U).ι.imageι ≫ π)
  have hrestrict : IsIso (((π ⁻¹ᵁ U).ι.imageι ≫ π) ∣_ U) := by
    have himg : IsIso ((π ⁻¹ᵁ U).ι.imageι ∣_ (π ⁻¹ᵁ U)) :=
      Stacks.SchemeTheoreticImage.isIso_imageι_restrict (π ⁻¹ᵁ U)
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' himg hiso
  have hdense :
      Scheme.Opens.IsSchemeTheoreticallyDense (((π ⁻¹ᵁ U).ι.imageι ≫ π) ⁻¹ᵁ U) := by
    rw [Scheme.Hom.comp_preimage]
    exact Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDense_preimage_imageι (π ⁻¹ᵁ U)
  refine ⟨inferInstance, ?_, inferInstance, ?_, hrestrict, hdense⟩
  · have := hdom
    infer_instance
  · rw [Category.assoc, Category.assoc, hcomm]

/-- **In Chow's lemma the inverse image of the dense open may be assumed scheme-theoretically
dense.** Replace `X'` by the scheme-theoretic closure of `π⁻¹(U)`; the dimension `n` of the
ambient projective space and the dense open `U` are unchanged. -/
@[stacks 0201 "part (2): `π⁻¹(U)` may be assumed scheme-theoretically dense in `X'`",
  ega "II 5.6.2" "f⁻¹(U) dense in X'"]
theorem exists_isSchemeTheoreticallyDense_chowModification (f : X ⟶ S) [IsNoetherian S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (π : X' ⟶ X)
    (i : X' ⟶ ProjectiveSpace n S) (U : X.Opens) [IsProper π] [IsImmersion i]
    (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) (hU : Dense (U : Set X))
    (hiso : IsIso (π ∣_ U)) :
    ∃ (Y : Scheme.{u}) (ρ : Y ⟶ X) (j : Y ⟶ ProjectiveSpace n S),
      IsProper ρ ∧ Surjective ρ ∧ IsImmersion j ∧
        ρ ≫ f = j ≫ (ProjectiveSpace n S ↘ S) ∧ Dense (U : Set X) ∧ IsIso (ρ ∣_ U) ∧
        Scheme.Opens.IsSchemeTheoreticallyDense (ρ ⁻¹ᵁ U) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    schemeTheoreticClosure_spec f π i U hcomm hU hiso
  exact ⟨_, _, _, h₁, h₂, h₃, h₄, hU, h₅, h₆⟩

/-! ### Reducedness of the modification -/

/-- **In Chow's lemma over a reduced scheme the modification may be chosen reduced.** The
scheme-theoretic closure of `π⁻¹(U)` has reduced source, since `π⁻¹(U) ≅ U` is an open subscheme
of the reduced scheme `X`, and the scheme-theoretic image of a reduced scheme is reduced. -/
@[stacks 0201 "part (3): if `X` is reduced then `X'` may be chosen reduced",
  ega "II 5.6.2" "reduced X' clause"]
theorem exists_isReduced_chowModification (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X] (π : X' ⟶ X)
    (i : X' ⟶ ProjectiveSpace n S) (U : X.Opens) [IsProper π] [IsImmersion i]
    (hcomm : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) (hU : Dense (U : Set X))
    (hiso : IsIso (π ∣_ U)) :
    ∃ (Y : Scheme.{u}) (ρ : Y ⟶ X) (j : Y ⟶ ProjectiveSpace n S),
      IsProper ρ ∧ Surjective ρ ∧ IsImmersion j ∧
        ρ ≫ f = j ≫ (ProjectiveSpace n S ↘ S) ∧ Dense (U : Set X) ∧ IsIso (ρ ∣_ U) ∧
        Scheme.Opens.IsSchemeTheoreticallyDense (ρ ⁻¹ᵁ U) ∧ IsReduced Y := by
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsReduced (π ⁻¹ᵁ U).toScheme := isReduced_of_isOpenImmersion (π ∣_ U)
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    schemeTheoreticClosure_spec f π i U hcomm hU hiso
  exact ⟨_, _, _, h₁, h₂, h₃, h₄, hU, h₅, h₆, inferInstance⟩

end AlgebraicGeometry

end
