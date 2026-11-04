module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SegreProdIso.Main

/-!
# H-projective morphisms are proper

A morphism of schemes is *H-projective* when it admits, over its base, a closed immersion
into a finite-dimensional relative projective space. Such a morphism is proper, because
`ℙⁿ_S ⟶ S` is proper and a closed immersion is finite, hence proper. The same holds when
H-projectivity is only available locally on the base, since properness is Zariski-local at
the target.

## Main definitions

* `AlgebraicGeometry.IsProjectiveMorphism` is H-projectivity: a closed immersion over the
  base into `ℙⁿ_S` for some `n`.
* `AlgebraicGeometry.IsLocallyProjectiveMorphism` is H-projectivity after restricting to the
  members of some open cover of the base.

## Main results

* `AlgebraicGeometry.isProper_projectiveSpaceOver` records that the structure morphism of
  projective space is proper.
* `AlgebraicGeometry.isProper_of_isProjectiveMorphism`: an H-projective morphism is proper.
* `AlgebraicGeometry.isProper_of_isLocallyProjectiveMorphism`: a locally H-projective
  morphism is proper.
* `AlgebraicGeometry.IsProjectiveMorphism.baseChange`: H-projectivity is stable under base
  change, whence `AlgebraicGeometry.IsProjectiveMorphism.isLocallyProjectiveMorphism`.
* `AlgebraicGeometry.IsProjectiveMorphism.comp`: a composition of H-projective morphisms is
  H-projective, through the Segre embedding.
* `AlgebraicGeometry.IsProjectiveMorphism.of_comp`: if `f ≫ g` is H-projective and `g` is
  separated then `f` is H-projective.
* `AlgebraicGeometry.projectiveSpaceOverBaseChangeIso` and
  `AlgebraicGeometry.projectiveSpaceOverBaseChangeIso_hom_over` restate the base change of
  projective space in the spelling used here.

## Implementation notes

Projective space is `AlgebraicGeometry.projectiveSpaceOver`, the scheme carrying tag 01NF.
Its properness is `AlgebraicGeometry.ProjectiveSpace.instIsProperOver`, which is stated for
the definitionally equal `AlgebraicGeometry.ProjectiveSpace`; the two are the same base
change of the same `Proj`, so the transfer is by definitional unfolding and
`isProper_projectiveSpaceOver` records it once for the rest of the file.

`IsProjectiveMorphism` is clause (2) of Definition 01W8, H-projectivity. Clause (1),
projectivity through the projective bundle `ℙ(ℰ)` of a finite-type quasi-coherent module, and
clause (3), its local form, are **not** formalized here: they are
`AlgebraicGeometry.IsProjective` and `AlgebraicGeometry.IsLocallyProjective` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic`, downstream of this file.
Consequently `isProper_of_isLocallyProjectiveMorphism` is Lemma 01WC for a hypothesis that
Lemma 01WB shows to be equivalent to the one 01WC states; the lemma at the hypothesis it does
state is `AlgebraicGeometry.isProper_of_isLocallyProjective` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective`, which carries tag 01WC and
is downstream of this file because Lemma 01WB
(`Stacks.LocallyProjectiveHProjective.isLocallyProjective_iff_isLocallyProjectiveMorphism`) is.
The comparison of clause (2) with clause (1) is likewise available downstream, as
`Stacks.IsProjectiveMorphism.isProjective` of
`StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective` (Tag 01W9, second clause) resting on
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` and
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst` of
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceMorphism` (Tag 01OE, both
halves). `IsLocallyProjectiveMorphism` keeps its name rather than `IsLocallyProjective`, which
belongs to clause (3): the two are equivalent but not the same predicate.

`AlgebraicGeometry.IsProjectiveMorphism.of_comp` carries the `"H-projective case"` clause of
Lemma 0C4Q: the source states that lemma for projectivity in the sense of clause (1), and the
proof transposed to clause (2) is the one given here. The transposed proof is the source's own —
the closed immersion `X ⟶ ℙⁿ_S` is lifted across the base change `ℙⁿ_S ×_S Y ≅ ℙⁿ_Y` and the
lift is a closed immersion because its composite with the separated first projection is one —
with `ℙ(ℰ)` replaced by `ℙⁿ`. The clause (1) form of the tag, which is the one the source states,
is `AlgebraicGeometry.IsProjective.of_comp` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange`; neither of the two implies the
other, since clause (1) and clause (2) are not known to agree in this repository.

Lemma 01WE, stability under composition, uses the Segre embedding
`Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding` of Lemma 01WD, which is why this
file depends on `StacksFrontier.AlgebraicGeometry.SegreProdIso.Main`.

## References

* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 01WE](https://stacks.math.columbia.edu/tag/01WE)
* [Stacks Project, Tag 01WF](https://stacks.math.columbia.edu/tag/01WF)
* [Stacks Project, Tag 0C4Q](https://stacks.math.columbia.edu/tag/0C4Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 01W8 (H-projective).** A morphism `f : X ⟶ S` is H-projective if
for some `n` there is a closed immersion `X ⟶ ℙⁿ_S` over `S`. -/
@[stacks 01W8 "H-projective"]
def IsProjectiveMorphism (f : X ⟶ S) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ projectiveSpaceOver n S,
    IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = f

/-- A morphism of schemes is locally H-projective if its base change to every member of some
open cover of the base is H-projective. This is the hypothesis of Lemma 01WC with clause (1)
of Definition 01W8 replaced by clause (2); see the implementation notes. -/
def IsLocallyProjectiveMorphism (f : X ⟶ S) : Prop :=
  ∃ 𝒰 : S.OpenCover.{u}, ∀ i : 𝒰.I₀, IsProjectiveMorphism (pullback.snd f (𝒰.f i))

/-- Projective space is proper over its base. This is
`AlgebraicGeometry.ProjectiveSpace.instIsProperOver` transported to the tag-01NF spelling of
projective space, which is the same scheme. -/
theorem isProper_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    IsProper (projectiveSpaceOver n S ↘ S) :=
  ProjectiveSpace.instIsProperOver n S

/-- **An H-projective morphism is proper.** A closed immersion is finite, hence proper, and
projective space is proper over its base. -/
theorem isProper_of_isProjectiveMorphism (f : X ⟶ S) (hf : IsProjectiveMorphism f) :
    IsProper f := by
  obtain ⟨n, i, hi, rfl⟩ := hf
  have := hi
  have := isProper_projectiveSpaceOver n S
  infer_instance

/-- `ℙⁿ_S ×_S T ≅ ℙⁿ_T`, in the tag-01NF spelling of projective space. This is
`AlgebraicGeometry.ProjectiveSpace.baseChangeIso`; it is restated here so that the proofs
below stay inside one spelling, which `rw` needs. -/
noncomputable def projectiveSpaceOverBaseChangeIso (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    pullback (projectiveSpaceOver n S ↘ S) g ≅ projectiveSpaceOver n T :=
  ProjectiveSpace.baseChangeIso n g

/-- The identification `ℙⁿ_S ×_S T ≅ ℙⁿ_T` is compatible with the two structure morphisms
down to `T`. -/
theorem projectiveSpaceOverBaseChangeIso_hom_over (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    (projectiveSpaceOverBaseChangeIso n g).hom ≫ (projectiveSpaceOver n T ↘ T) =
      pullback.snd (projectiveSpaceOver n S ↘ S) g :=
  ProjectiveSpace.baseChangeIso_hom_over n g

namespace IsProjectiveMorphism

/-- A closed immersion into `ℙⁿ_S ×_S T` whose second projection is `f` makes `f` H-projective. -/
private theorem of_closedImmersion_pullback {A T S : Scheme.{u}} {f : A ⟶ T} {n : ℕ} {g : T ⟶ S}
    (k : A ⟶ pullback (projectiveSpaceOver n S ↘ S) g) [IsClosedImmersion k]
    (hk : k ≫ pullback.snd (projectiveSpaceOver n S ↘ S) g = f) : IsProjectiveMorphism f :=
  ⟨n, k ≫ (projectiveSpaceOverBaseChangeIso n g).hom, inferInstance, by
    rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, hk]⟩

/-- **Stacks Project, Tag 01WF. H-projectivity is stable under base change.** A closed
immersion `X ⟶ ℙⁿ_S` over `S` base changes to a closed immersion
`X ×_S T ⟶ ℙⁿ_S ×_S T ≅ ℙⁿ_T` over `T`. -/
@[stacks 01WF]
theorem baseChange {f : X ⟶ S} (hf : IsProjectiveMorphism f) {T : Scheme.{u}} (g : T ⟶ S) :
    IsProjectiveMorphism (pullback.snd f g) := by
  obtain ⟨n, i, hi, rfl⟩ := hf
  have := hi
  exact of_closedImmersion_pullback
    ((pullbackRightPullbackFstIso (projectiveSpaceOver n S ↘ S) g i).inv ≫
      pullback.snd i (pullback.fst (projectiveSpaceOver n S ↘ S) g))
    (pullbackRightPullbackFstIso_inv_snd_snd (projectiveSpaceOver n S ↘ S) g i)

/-- An H-projective morphism is locally H-projective: the one-member cover of the base by its
own identity will do, since H-projectivity is stable under base change. -/
theorem isLocallyProjectiveMorphism {f : X ⟶ S} (hf : IsProjectiveMorphism f) :
    IsLocallyProjectiveMorphism f :=
  ⟨Scheme.coverOfIsIso.{u} (P := @IsOpenImmersion) (𝟙 S), fun _ => hf.baseChange _⟩

/-- **Stacks Project, Tag 01WE. A composition of H-projective morphisms is H-projective.**

Closed immersions `i : X ⟶ ℙⁿ_Y` over `Y` and `j : Y ⟶ ℙᵐ_Z` over `Z` are composed as follows.
The identification `ℙⁿ_Z ×_Z Y ≅ ℙⁿ_Y` turns `i` into a closed immersion of `X` into
`ℙⁿ_Z ×_Z Y`; base changing `j` along `ℙⁿ_Z ⟶ Z` embeds that closed into `ℙⁿ_Z ×_Z ℙᵐ_Z`; and the
Segre embedding of [Stacks, Tag 01WD] embeds the product closed into `ℙ^{nm+n+m}_Z`. -/
@[stacks 01WE]
theorem comp {Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsProjectiveMorphism f)
    (hg : IsProjectiveMorphism g) : IsProjectiveMorphism (f ≫ g) := by
  obtain ⟨n, i, hi, hif⟩ := hf
  obtain ⟨m, j, hj, hjg⟩ := hg
  obtain ⟨s, hs, hsover⟩ := Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding n m Z
  have := hi
  have := hj
  have := hs
  obtain ⟨b, hb, hbfst⟩ :
      ∃ b : pullback (projectiveSpaceOver n Z ↘ Z) g ⟶
          pullback (projectiveSpaceOver n Z ↘ Z) (projectiveSpaceOver m Z ↘ Z),
        IsClosedImmersion b ∧
          b ≫ pullback.fst (projectiveSpaceOver n Z ↘ Z) (projectiveSpaceOver m Z ↘ Z) =
            pullback.fst (projectiveSpaceOver n Z ↘ Z) g := by
    have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
      ⟨fun a c ha hc => @IsClosedImmersion.comp _ _ _ a c ha hc⟩
    refine ⟨pullback.map _ g _ (projectiveSpaceOver m Z ↘ Z) (𝟙 _) j (𝟙 Z) (by simp)
      (by simpa using hjg.symm), ?_, by simp [pullback.map, pullback.lift_fst]⟩
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance hj
      (Category.id_comp _).symm hjg.symm
  have := hb
  have hesnd : (projectiveSpaceOverBaseChangeIso n g).inv ≫
      pullback.snd (projectiveSpaceOver n Z ↘ Z) g = (projectiveSpaceOver n Y ↘ Y) := by
    rw [← projectiveSpaceOverBaseChangeIso_hom_over n g, Iso.inv_hom_id_assoc]
  have key : ((projectiveSpaceOverBaseChangeIso n g).inv ≫ b ≫ s) ≫
      (projectiveSpaceOver (n * m + n + m) Z ↘ Z) = (projectiveSpaceOver n Y ↘ Y) ≫ g := by
    rw [Category.assoc, Category.assoc, hsover, ← Category.assoc b, hbfst,
      pullback.condition, ← Category.assoc, hesnd]
  refine ⟨n * m + n + m, i ≫ (projectiveSpaceOverBaseChangeIso n g).inv ≫ b ≫ s,
    inferInstance, ?_⟩
  rw [Category.assoc, key, ← Category.assoc, hif]

/-- **Stacks Project, Tag 0C4Q, H-projective case.** If `f ≫ g` is H-projective and `g` is
separated then `f` is H-projective.

The closed immersion `i : X ⟶ ℙⁿ_S` over `S` lifts to `k : X ⟶ ℙⁿ_S ×_S Y` because `i` and `f`
agree over `S`. The first projection of that fibre product is a base change of `g`, hence
separated, and `k` composed with it is `i`; so `k` is a closed immersion by
`AlgebraicGeometry.IsClosedImmersion.of_comp`. Finally `ℙⁿ_S ×_S Y ≅ ℙⁿ_Y` over `Y`. -/
@[stacks 0C4Q "H-projective case"]
theorem of_comp {Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsSeparated g]
    (h : IsProjectiveMorphism (f ≫ g)) : IsProjectiveMorphism f := by
  obtain ⟨n, i, hi, hifg⟩ := h
  have := hi
  have hsep : IsSeparated (pullback.fst (projectiveSpaceOver n S ↘ S) g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated)
      (IsPullback.of_hasPullback (projectiveSpaceOver n S ↘ S) g).flip ‹IsSeparated g›
  have := hsep
  have hk : IsClosedImmersion (pullback.lift i f hifg) := by
    have : IsClosedImmersion
        (pullback.lift i f hifg ≫ pullback.fst (projectiveSpaceOver n S ↘ S) g) := by
      rw [pullback.lift_fst]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.fst (projectiveSpaceOver n S ↘ S) g)
  have := hk
  exact of_closedImmersion_pullback (pullback.lift i f hifg) (pullback.lift_snd _ _ _)

end IsProjectiveMorphism

/-- **A locally H-projective morphism is proper.** Properness is Zariski-local at the target,
so this reduces to `AlgebraicGeometry.isProper_of_isProjectiveMorphism` on each member of the
cover.

Lemma 01WC is stated for *locally projective* morphisms, i.e. for clause (3) of Definition
01W8, which Lemma 01WB identifies with the hypothesis here; that form of the lemma is
`AlgebraicGeometry.isProper_of_isLocallyProjective` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective`, which is downstream of
this file because Lemma 01WB is. -/
theorem isProper_of_isLocallyProjectiveMorphism (f : X ⟶ S)
    (hf : IsLocallyProjectiveMorphism f) : IsProper f := by
  obtain ⟨𝒰, h⟩ := hf
  exact IsZariskiLocalAtTarget.of_openCover (P := @IsProper) 𝒰 fun i =>
    isProper_of_isProjectiveMorphism _ (h i)

end AlgebraicGeometry

end
