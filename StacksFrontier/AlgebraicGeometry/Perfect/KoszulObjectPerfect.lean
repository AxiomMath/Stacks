module

public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.RingTheory.Koszul.Truncation.DerivedKoszulObject
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.AffineFiniteProjective

/-!
# The sheafified Koszul complex is a perfect object of `D(𝒪_{Spec A})`

Let `A` be a commutative ring and let `f₁, …, f_r ∈ A`. The object
`Stacks.Koszul.Truncation.koszulObject f` of the derived category of `𝒪_{Spec A}`-modules is the
Koszul complex `K_•(f₁, …, f_r)`, re-indexed in the cohomological degrees `-r, …, 0`, sheafified
termwise and localized. This file proves it is a **perfect** object.

The complex it is the image of is already *strictly* perfect: its degree `-j` term is the `j`-th
exterior power of `Aʳ`, a finite free `A`-module, so termwise sheafification turns it into a
direct summand of a finite free `𝒪_{Spec A}`-module, and there are only finitely many nonzero
degrees. No covering is needed, and the one-member covering by `⊤` witnesses perfectness.

## Main results

* `Stacks.Koszul.Truncation.isStrictlyPerfect_tildeKoszulComplex` — the sheafified Koszul complex
  is strictly perfect. No derived category is involved, so this holds at every model.
* `Stacks.Koszul.Truncation.isPerfect_koszulObject` — `Stacks.Koszul.Truncation.koszulObject` is a
  perfect object of `D(𝒪_{Spec A})`.

## Implementation notes

**The model is the locally small one.** `Stacks.Koszul.Truncation.isPerfect_koszulObject` carries
no `CategoryTheory.HasDerivedCategory` binder, so instance search supplies the global instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`; this is the model at which
[Stacks, Tag 09IS] and [Stacks, Tag 0A9A] have content, and the model the Koszul detection
statements of `StacksFrontier/AlgebraicGeometry/DerivedQCoh/KoszulDetectionTwoOpens.lean` are read
at. A free binder would not do: it would cover the spelling
`AlgebraicGeometry.Scheme.Modules (Spec A)` that `Stacks.Koszul.Truncation.koszulObject` is stated
at and not the spelling `Stacks.StrictlyPerfect.OXMod (Spec A).toRingedSpace` that
`Stacks.Cohomology.PerfectComplexes.IsPerfect` is stated at, and
`AlgebraicGeometry.Scheme.Modules` is not reducible for instance search. The strictly perfect
statement, being about a complex of modules rather than about a derived category, has no such
binder and is model-free.

`Stacks.Koszul.Truncation.finite_extend_seqComplex_X` is the one piece with no counterpart in
Mathlib: projectivity of the terms of an extended complex is an instance there
(`HomologicalComplex.extend`), and finiteness of the terms of a complex of modules is not.
It is proved here for the Koszul complex only; a general version belongs beside the Mathlib
instance, in `StacksFrontier/Algebra/Homology/`.

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open StrictlyPerfect

universe u

namespace Stacks.Koszul.Truncation

variable {A : Type u} [CommRing A] {r : ℕ}

/-- Every term of the Koszul complex of `f₁, …, f_r` is projective: it is an exterior power of
the finite free module `Aʳ`, hence free. -/
theorem projective_seqComplex_X (f : Fin r → A) (j : ℕ) :
    Projective ((Koszul.seqComplex f).X j) := by
  show Projective (ModuleCat.of A (⋀[A]^j (Fin r → A)))
  have : Module.Projective A (⋀[A]^j (Fin r → A)) :=
    Module.Projective.of_basis (Module.Free.chooseBasis _ _)
  infer_instance

/-- A degree outside the image of the embedding carries no term of the extended Koszul complex. -/
private theorem isZero_extend_seqComplex_X_of_not_exists (f : Fin r → A) {i : ℤ}
    (h : ¬∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i) :
    IsZero (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i) :=
  (Koszul.seqComplex f).isZero_extend_X ComplexShape.embeddingDownNat i (by simpa using h)

/-- Outside the cohomological degrees `-r, …, 0` the extension of the Koszul complex of
`f₁, …, f_r` vanishes: a degree in the image of the embedding is `-j` for a chain degree `j`
exceeding `r`, where the Koszul complex itself vanishes, and a degree outside the image carries
no term at all. -/
theorem isZero_extend_seqComplex_X (f : Fin r → A) (i : ℤ) (hi : i < -(r : ℤ) ∨ 0 < i) :
    IsZero (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  classical
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    have hr : r < j := by
      change -(j : ℤ) = i at hj
      rcases hi with hi | hi <;> omega
    exact (Koszul.seqComplex_isZero_of_lt f j hr).of_iso
      ((Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat hj)
  · exact isZero_extend_seqComplex_X_of_not_exists f h

/-- Every term of the extension of the Koszul complex of `f₁, …, f_r` to the cohomological
degrees is a finite `A`-module: in the image of the embedding it is an exterior power of `Aʳ`,
and outside it is the zero module. -/
theorem finite_extend_seqComplex_X (f : Fin r → A) (i : ℤ) :
    Module.Finite A (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  classical
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    have : Module.Finite A ((Koszul.seqComplex f).X j) := by
      show Module.Finite A (⋀[A]^j (Fin r → A))
      infer_instance
    exact Module.Finite.equiv
      (((Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat hj).toLinearEquiv.symm)
  · let : Subsingleton (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_extend_seqComplex_X_of_not_exists f h)
    exact Module.Finite.of_finite

/-- **The sheafified Koszul complex of `f₁, …, f_r` is a strictly perfect complex of
`𝒪_{Spec A}`-modules.** It is the termwise sheafification of a complex of finite free
`A`-modules concentrated in the degrees `-r, …, 0`, and `M ↦ M^~` carries a finite projective
module to a direct summand of a finite free `𝒪_{Spec A}`-module. -/
theorem isStrictlyPerfect_tildeKoszulComplex (f : Fin r → A) :
    IsStrictlyPerfect (X := (Spec (CommRingCat.of A)).toRingedSpace)
      (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)) := by
  classical
  refine Stacks.AffineTilde.isStrictlyPerfect_tildeComplex_of_projective _ ?_ fun i => ?_
  · refine Set.Finite.subset (Set.finite_Icc (-(r : ℤ)) 0) fun i hi => ?_
    by_contra hn
    simp only [Set.mem_Icc, not_and_or, not_le] at hn
    exact hi (isZero_extend_seqComplex_X f i
      (by rcases hn with hn | hn; exacts [Or.inl hn, Or.inr hn]))
  · refine ⟨finite_extend_seqComplex_X f i, ?_⟩
    let : ∀ j, Projective ((Koszul.seqComplex f).X j) := projective_seqComplex_X f
    let : Projective (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i) :=
      inferInstance
    exact ModuleCat.projective_of_module_projective
      (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i)

/-- **The Koszul object of `f₁, …, f_r` is a perfect object of `D(𝒪_{Spec A})`**, at the locally
small model. It is the localization of a strictly perfect complex, and the one-member covering of
`Spec A` by `⊤` witnesses perfectness of that complex. -/
theorem isPerfect_koszulObject (f : Fin r → A) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec (CommRingCat.of A)).toRingedSpace) (koszulObject f) :=
  AlgebraicGeometry.RingedSpace.isPerfect_Q_obj_of_isStrictlyPerfect
    (isStrictlyPerfect_tildeKoszulComplex f)

end Stacks.Koszul.Truncation

end
