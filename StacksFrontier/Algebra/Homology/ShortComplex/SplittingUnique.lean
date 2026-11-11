module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# A section or a retraction of a short exact sequence determines a unique splitting

Let `𝒜` be an abelian category and `0 → A → B → C → 0` a short exact sequence `S` in `𝒜`.
A morphism `s : C → B` right inverse to `S.g` is the section of a unique splitting of `S`, and a
morphism `π : B → A` left inverse to `S.f` is the retraction of a unique splitting of `S`.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.existsUnique_splitting_s_eq`: a section `s` of `S.g`
  is the section of exactly one splitting of `S`.
* `CategoryTheory.ShortComplex.ShortExact.existsUnique_splitting_r_eq`: a retraction `π` of
  `S.f` is the retraction of exactly one splitting of `S`.
* `CategoryTheory.ShortComplex.ShortExact.existsUnique_retraction_of_section` and
  `existsUnique_section_of_retraction`: the same statements phrased, as in the source, as the
  existence of a unique second morphism completing the given one to a direct sum decomposition.

## Implementation notes

Existence is `CategoryTheory.ShortComplex.Splitting.ofExactOfSection` and
`CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction`, and uniqueness is
`CategoryTheory.ShortComplex.Splitting.ext_s` and `CategoryTheory.ShortComplex.Splitting.ext_r`.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] {S : ShortComplex 𝒜}

namespace ShortExact

/-- In an abelian category, a section `s` of the second map of a short exact sequence is the
section of exactly one splitting of the sequence. -/
@[stacks 010G "(1), as a unique splitting with the given section"]
theorem existsUnique_splitting_s_eq (hS : S.ShortExact) (s : S.X₃ ⟶ S.X₂)
    (s_g : s ≫ S.g = 𝟙 S.X₃) : ∃! σ : S.Splitting, σ.s = s :=
  have := hS.mono_f
  ⟨Splitting.ofExactOfSection S hS.exact s s_g this, rfl,
    fun _ hσ => Splitting.ext_s _ _ hσ⟩

/-- In an abelian category, a retraction `π` of the first map of a short exact sequence is the
retraction of exactly one splitting of the sequence. -/
@[stacks 010G "(2), as a unique splitting with the given retraction"]
theorem existsUnique_splitting_r_eq (hS : S.ShortExact) (π : S.X₂ ⟶ S.X₁)
    (f_π : S.f ≫ π = 𝟙 S.X₁) : ∃! σ : S.Splitting, σ.r = π :=
  have := hS.epi_g
  ⟨Splitting.ofExactOfRetraction S hS.exact π f_π this, rfl,
    fun _ hσ => Splitting.ext_r _ _ hσ⟩

/-- In an abelian category, given a section `s` of the second map of a short exact sequence,
there is a unique `π` such that `(s, π)` splits the sequence: `π` is a retraction of the first
map and `π ≫ S.f + S.g ≫ s = 𝟙`. -/
@[stacks 010G "(1)"]
theorem existsUnique_retraction_of_section (hS : S.ShortExact) (s : S.X₃ ⟶ S.X₂)
    (s_g : s ≫ S.g = 𝟙 S.X₃) :
    ∃! π : S.X₂ ⟶ S.X₁, S.f ≫ π = 𝟙 S.X₁ ∧ π ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  obtain ⟨σ, hσ, huniq⟩ := hS.existsUnique_splitting_s_eq s s_g
  refine ⟨σ.r, ⟨σ.f_r, hσ ▸ σ.id⟩, fun π ⟨f_π, hid⟩ => ?_⟩
  have := huniq ⟨π, s, f_π, s_g, hid⟩ rfl
  rw [← this]

/-- In an abelian category, given a retraction `π` of the first map of a short exact sequence,
there is a unique `s` such that `(s, π)` splits the sequence: `s` is a section of the second map
and `π ≫ S.f + S.g ≫ s = 𝟙`. -/
@[stacks 010G "(2)"]
theorem existsUnique_section_of_retraction (hS : S.ShortExact) (π : S.X₂ ⟶ S.X₁)
    (f_π : S.f ≫ π = 𝟙 S.X₁) :
    ∃! s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ ∧ π ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  obtain ⟨σ, hσ, huniq⟩ := hS.existsUnique_splitting_r_eq π f_π
  refine ⟨σ.s, ⟨σ.s_g, hσ ▸ σ.id⟩, fun s ⟨s_g, hid⟩ => ?_⟩
  have := huniq ⟨π, s, f_π, s_g, hid⟩ rfl
  rw [← this]

end ShortExact

end CategoryTheory.ShortComplex

add_to_stacks 010G "(1), uniqueness: a splitting is determined by its section"
  CategoryTheory.ShortComplex.Splitting.ext_s
add_to_stacks 010G "(2), uniqueness: a splitting is determined by its retraction"
  CategoryTheory.ShortComplex.Splitting.ext_r
