module

public import StacksFrontier.AlgebraicGeometry.Curves.VeryAmpleSixthPower
public import StacksFrontier.AlgebraicGeometry.Curves.RegularSectionGeneration.Generation
public import StacksFrontier.AlgebraicGeometry.VeroneseVeryAmple.Basic
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic

/-!
# Stacks Tag 0E8V: the sixth power of an ample invertible sheaf with a regular section

Let `k` be a field, `X` a proper scheme over `k` of dimension `1` with `H⁰(X, 𝒪_X) = k`, and `ℒ`
an invertible `𝒪_X`-module which has a regular global section, has `H¹(X, ℒ) = 0` and is ample.
[Stacks, Tag 0E8V] says that `ℒ^{⊗ 6}` is very ample on `X` over `k`. This file proves it with no
hypothesis beyond the source's.

The source's two halves are both theorems:

* the generation of the section ring in degrees `1`, `2`, `3` is
  `Stacks.RegularSectionGeneration.adjoin_grading_le_three_eq_top`, made finite here
  (`exists_generators_le_three`); in particular the condition
  `Stacks.Curves.VeryAmpleSixthPower.SectionRingGeneratedInDegreesLeThree` of
  `StacksFrontier/AlgebraicGeometry/Curves/VeryAmpleSixthPower.lean` holds
  (`sectionRingGeneratedInDegreesLeThree`);
* the closing sentence — `X = Proj S`, so generation of `S^{(6)}` in degree one makes `ℒ^{⊗ 6}`
  very ample — is `Stacks.VeroneseVeryAmple.isRelativelyVeryAmple_tensorPowModule_of_generators`.

Between them sits `Stacks.Curves.VeryAmpleSixthPower.veroneseGeneratedInDegOne_six`, the
arithmetic that makes the exponent `6`.

## Main results

* `Stacks.Curves.VeryAmpleSixthPower.isRelativelyVeryAmple_tensorPowModule_six_of_regularSection`:
  **[Stacks, Tag 0E8V].**

## References

* [Stacks Project, Tag 0E8V](https://stacks.math.columbia.edu/tag/0E8V)
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Ample
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (grading)

universe u

namespace Stacks.Curves.VeryAmpleSixthPower

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}}

/-- **The section ring of an ample invertible module on a proper scheme over a field is generated
over its degree-zero part by finitely many homogeneous elements of positive degree.** -/
theorem exists_homogeneous_generators (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) :
    ∃ (r : ℕ) (g : Fin r → sectionRing L) (deg : Fin r → ℕ), (∀ i, 1 ≤ deg i) ∧
      (∀ i, g i ∈ grading L (deg i)) ∧
        Algebra.adjoin (Stacks.Veronese.gradeZero (grading L)) (Set.range g) = ⊤ := by
  let : Algebra k (sectionRing L) :=
    ((Stacks.SectionRingZero.sectionRingZeroHom X L).comp
      (Stacks.AlgebraicGeometry.GradedProperCohomology.specAlgebraRingHom k f)).toAlgebra
  have : Algebra.FiniteType k (sectionRing L) := RingHom.finiteType_algebraMap.mp
    (Stacks.AlgebraicGeometry.ProperAmpleCohomology.ringHomFiniteType_sectionRing f L hL)
  have : IsNoetherianRing (sectionRing L) := Algebra.FiniteType.isNoetherianRing k _
  have h : Algebra.FiniteType ((grading L) 0) (sectionRing L) :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing (grading L)
  exact Stacks.Veronese.homogeneous_generators_of_finiteType (grading L) h

/-- **The cohomological half of the proof of [Stacks, Tag 0E8V].** For `X` proper of dimension at
most one over `k` and `ℒ` ample invertible with a regular global section and `H¹(X, ℒ) = 0`, the
section ring `Γ_*(X, ℒ)` is generated over its degree-zero part by finitely many homogeneous
elements of degrees `1`, `2` and `3`.

The generation in degrees `≤ 3` is
`Stacks.RegularSectionGeneration.adjoin_grading_le_three_eq_top`; finitely many elements suffice
in each of these degrees because the section ring is of finite type over `k`
(`exists_homogeneous_generators`), so that each graded piece is spanned by finitely many
monomials (`Stacks.VeroneseVeryAmple.exists_span_of_generators`). -/
theorem exists_generators_le_three (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : X.Modules) [IsInvertibleModule X L] (s : 𝟙_ X.Modules ⟶ L) [Mono s]
    (hdim : topologicalKrullDim X ≤ 1)
    (hH1 : IsZero (AlgebraicGeometry.cohomologyOverField k f L 1)) (hL : IsAmple X L) :
    ∃ (r : ℕ) (g : Fin r → sectionRing L) (deg : Fin r → ℕ), (∀ i, 1 ≤ deg i) ∧
      (∀ i, deg i ≤ 3) ∧ (∀ i, g i ∈ grading L (deg i)) ∧
        Algebra.adjoin (Stacks.Veronese.gradeZero (grading L)) (Set.range g) = ⊤ := by
  classical
  obtain ⟨r₀, G, D, hD1, hG, hGgen⟩ := exists_homogeneous_generators k f L hL
  obtain ⟨N₁, b₁, h₁⟩ := Stacks.VeroneseVeryAmple.exists_span_of_generators L G D hD1 hG hGgen 1
  obtain ⟨N₂, b₂, h₂⟩ := Stacks.VeroneseVeryAmple.exists_span_of_generators L G D hD1 hG hGgen 2
  obtain ⟨N₃, b₃, h₃⟩ := Stacks.VeroneseVeryAmple.exists_span_of_generators L G D hD1 hG hGgen 3
  let ι := Fin (N₁ + 1) ⊕ Fin (N₂ + 1) ⊕ Fin (N₃ + 1)
  let g' : ι → sectionRing L := Sum.elim (fun j => DirectSum.of (powSections L) 1 (b₁ j))
    (Sum.elim (fun j => DirectSum.of (powSections L) 2 (b₂ j))
      (fun j => DirectSum.of (powSections L) 3 (b₃ j)))
  let d' : ι → ℕ := Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2) (fun _ => 3))
  let e := Fintype.equivFin ι
  have key : ∀ j : ι, 1 ≤ d' j ∧ d' j ≤ 3 ∧ g' j ∈ grading L (d' j) := by
    rintro (j | j | j) <;>
      exact ⟨by simp [d'], by simp [d'], Stacks.ExternalGrading.of_mem_summand _ _⟩
  refine ⟨Fintype.card ι, g' ∘ e.symm, d' ∘ e.symm, fun i => (key _).1, fun i => (key _).2.1,
    fun i => (key _).2.2, ?_⟩
  rw [e.symm.surjective.range_comp g', eq_top_iff,
    ← Stacks.RegularSectionGeneration.adjoin_grading_le_three_eq_top k f s hdim hH1]
  refine Algebra.adjoin_le ?_
  have hspan : ∀ {D N : ℕ} (b : Fin (N + 1) → powSections L D) (c : Fin (N + 1) → ι),
      (∀ j, g' (c j) = DirectSum.of (powSections L) D (b j)) →
      (grading L D : Set (sectionRing L)) ⊆
        (Submodule.span (Stacks.Veronese.gradeZero (grading L))
          (Set.range fun j => DirectSum.of (powSections L) D (b j)) : Set (sectionRing L)) →
      (grading L D : Set (sectionRing L)) ⊆
        Algebra.adjoin (Stacks.Veronese.gradeZero (grading L)) (Set.range g') := by
    intro D N b c hc h z hz
    refine Algebra.adjoin_mono ?_ (Algebra.span_le_adjoin _ _ (h hz))
    rintro _ ⟨j, rfl⟩
    exact ⟨c j, hc j⟩
  rintro z ((hz | hz) | hz)
  · exact hspan b₁ Sum.inl (fun _ => rfl) h₁ hz
  · exact hspan b₂ (Sum.inr ∘ Sum.inl) (fun _ => rfl) h₂ hz
  · exact hspan b₃ (Sum.inr ∘ Sum.inr) (fun _ => rfl) h₃ hz

/-- **The cohomological half of the proof of [Stacks, Tag 0E8V] holds**: the condition
`Stacks.Curves.VeryAmpleSixthPower.SectionRingGeneratedInDegreesLeThree` is a theorem. -/
theorem sectionRingGeneratedInDegreesLeThree (k : Type u) [Field k] :
    SectionRingGeneratedInDegreesLeThree k := by
  intro X f _ _ L _ s hdim hs hH1 hL
  have := hs
  exact exists_generators_le_three k f L s hdim.le hH1 hL

/-- **[Stacks, Tag 0E8V].** Let `k` be a field, let `X` be a proper scheme over `k` of dimension
`1` with `H⁰(X, 𝒪_X) = k`, and let `ℒ` be an invertible `𝒪_X`-module. Assume that `ℒ` has a
regular global section, that `H¹(X, ℒ) = 0` and that `ℒ` is ample. Then `ℒ^{⊗ 6}` is very ample
on `X` over `k`.

The regular global section is a monomorphism `s : 𝒪_X ⟶ ℒ`; `H⁰(X, 𝒪_X) = k` is the hypothesis
that the map `k ⟶ Γ(X, 𝒪_X)` is an isomorphism; very ampleness is relative very ampleness for
`f : X ⟶ Spec k` in the sense of [Stacks, Tag 01VM].

The proof is the source's. The section ring `S = Γ_*(X, ℒ)` is generated over `S₀` in degrees
`1`, `2`, `3` (`exists_generators_le_three`, the first two paragraphs of the source), so its sixth
Veronese subring is generated in degree one (`veroneseGeneratedInDegOne_six`), and that makes
`ℒ^{⊗ 6}` very ample
(`Stacks.VeroneseVeryAmple.isRelativelyVeryAmple_tensorPowModule_of_generators`,
the source's closing sentence, which runs through `X = Proj S` of [Stacks, Tag 0C6J]). -/
@[stacks 0E8V]
theorem isRelativelyVeryAmple_tensorPowModule_six_of_regularSection (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (L : X.Modules) [IsInvertibleModule X L] (s : 𝟙_ X.Modules ⟶ L)
    (hdim : topologicalKrullDim X = 1) (hs : Mono s)
    (hH1 : IsZero (AlgebraicGeometry.cohomologyOverField k f L 1)) (hample : IsAmple X L) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (6 : ℤ)) := by
  have := hs
  obtain ⟨r, g, deg, hdeg1, hdeg3, hg, hgen⟩ :=
    exists_generators_le_three k f L s hdim.le hH1 hample
  exact Stacks.VeroneseVeryAmple.isRelativelyVeryAmple_tensorPowModule_of_generators L k f
    hample g deg hdeg1 hg hgen (d := 6) (by omega)
    (veroneseGeneratedInDegOne_six (grading L) g deg hdeg1 hdeg3 hg hgen)

end Stacks.Curves.VeryAmpleSixthPower

end
