module

public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedSystem
public import StacksFrontier.Homology.Perfect.KoszulSpreadingOut

/-!
# The stages of the derived Koszul system are perfect

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`
and let `X = Spec A`. Every stage `Iₑ` of the inverse system
`Koszul.DerivedSystem.koszulDerivedSystem` of sheafified truncated Koszul complexes is a perfect
object of `D(𝒪_X)`.

## Main results

* `Koszul.isPerfect_extend_koszulIdealComplex`: the complex `I^•(f)`, placed in the cohomological
  degrees `-r, …, 0`, is a perfect object of `D(A)`.
* `Koszul.DerivedSystem.isPerfect_koszulDerivedSystem_obj`: each stage `Iₑ` is a perfect object
  of `D(𝒪_X)`.

## Implementation notes

`I^•(f)` is the Koszul complex of `f` with its degree-zero term deleted and the remaining terms
shifted down, so its chain degree `n` *is* the `(n + 1)`st exterior power of `Aʳ`: finite free,
and zero once `n ≥ r`. Extending along `ComplexShape.embeddingDownNat` places it in the
cohomological degrees `-(r-1), …, 0`, where `-r` is used as the (non-tight) lower bound, and the
argument for perfectness over `A` is the one `StacksDraft.Perfect.isPerfect_extend_koszul` makes
for the untruncated complex. The passage to `D(𝒪_X)` is [Stacks, Tag 08EB], perfectness being
preserved and reflected by derived sheafification on an affine scheme.

## References

* [Stacks Project, Tag 08CY](https://stacks.math.columbia.edu/tag/08CY)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Koszul

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {r : ℕ}

/-- `I^•(f)` vanishes in chain degrees `≥ r`: its chain degree `n` is the `(n + 1)`st exterior
power of a free module of rank `r`. -/
theorem koszulIdealComplex_isZero_of_le (f : Fin r → A) (j : ℕ) (hj : r ≤ j) :
    IsZero ((koszulIdealComplex f).X j) :=
  seqComplex_isZero_of_lt f (j + 1) (by omega)

/-- Every term of `I^•(f)` is a finite `A`-module: it is an exterior power of `Aʳ`. -/
theorem finite_koszulIdealComplex_X (f : Fin r → A) (j : ℕ) :
    Module.Finite A ((koszulIdealComplex f).X j) := by
  change Module.Finite A (⋀[A]^(j + 1) (Fin r → A))
  infer_instance

/-- Every term of `I^•(f)` is projective: it is an exterior power of a finite free module. -/
theorem projective_koszulIdealComplex_X (f : Fin r → A) (j : ℕ) :
    Projective ((koszulIdealComplex f).X j) := by
  change Projective (ModuleCat.of A (⋀[A]^(j + 1) (Fin r → A)))
  have : Module.Projective A (⋀[A]^(j + 1) (Fin r → A)) :=
    Module.Projective.of_basis (Module.Free.chooseBasis _ _)
  infer_instance

/-- Each term of the extension of `I^•(f)` is either isomorphic to a term of `I^•(f)` in a chain
degree `j` mapping to it, or zero. -/
private theorem exists_iso_or_isZero_extend_koszulIdealComplex_X (f : Fin r → A) (i : ℤ) :
    (∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i ∧
      Nonempty (((koszulIdealComplex f).extend ComplexShape.embeddingDownNat).X i ≅
        (koszulIdealComplex f).X j)) ∨
    IsZero (((koszulIdealComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  classical
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    exact Or.inl ⟨j, hj, ⟨((koszulIdealComplex f).extendXIso ComplexShape.embeddingDownNat hj)⟩⟩
  · exact Or.inr ((koszulIdealComplex f).isZero_extend_X ComplexShape.embeddingDownNat i
      (by simpa using h))

/-- Outside the cohomological degrees `-r, …, 0` the extension of `I^•(f)` vanishes: a degree in
the image of the embedding is `-j` for a chain degree `j` exceeding `r`, and a degree outside
the image carries no term at all. -/
private theorem isZero_extend_koszulIdealComplex_X (f : Fin r → A) (i : ℤ)
    (hi : i < -(r : ℤ) ∨ 0 < i) :
    IsZero (((koszulIdealComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  rcases exists_iso_or_isZero_extend_koszulIdealComplex_X f i with ⟨j, hj, ⟨e⟩⟩ | h
  · have hr : r ≤ j := by
      change -(j : ℤ) = i at hj
      rcases hi with hi | hi <;> omega
    exact (koszulIdealComplex_isZero_of_le f j hr).of_iso e
  · exact h

/-- Every term of the extension of `I^•(f)` to the cohomological degrees is projective. -/
theorem projective_extend_koszulIdealComplex_X (f : Fin r → A) (i : ℤ) :
    Projective (((koszulIdealComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  rcases exists_iso_or_isZero_extend_koszulIdealComplex_X f i with ⟨j, -, ⟨e⟩⟩ | h
  · exact Projective.of_iso e.symm (projective_koszulIdealComplex_X f j)
  · exact h.projective

/-- Every term of the extension of `I^•(f)` to the cohomological degrees is a finite
`A`-module. -/
theorem finite_extend_koszulIdealComplex_X (f : Fin r → A) (i : ℤ) :
    Module.Finite A (((koszulIdealComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  rcases exists_iso_or_isZero_extend_koszulIdealComplex_X f i with ⟨j, -, ⟨e⟩⟩ | h
  · have := finite_koszulIdealComplex_X f j
    exact Module.Finite.equiv e.toLinearEquiv.symm
  · have := ModuleCat.isZero_iff_subsingleton.mp h
    exact Module.Finite.of_finite

/-- **The complex `I^•(f)` is a perfect object of `D(A)`.** Placed in the cohomological degrees
`-r, …, 0` it is a bounded complex of finite projective modules, its term in degree `-j` being
the `(j + 1)`st exterior power of `Aʳ`. -/
theorem isPerfect_extend_koszulIdealComplex (f : Fin r → A) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj
        ((koszulIdealComplex f).extend ComplexShape.embeddingDownNat)) := by
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    (koszulIdealComplex f).extend ComplexShape.embeddingDownNat
  have hge : P.IsStrictlyGE (-(r : ℤ)) := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => isZero_extend_koszulIdealComplex_X f i (Or.inl hi)
  have hle : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => isZero_extend_koszulIdealComplex_X f i (Or.inr hi)
  have hproj (i : ℤ) : Module.Projective A (P.X i) := by
    have := projective_extend_koszulIdealComplex_X f i
    exact ModuleCat.projective_of_module_projective (P.X i)
  exact ⟨P, -(r : ℤ), 0, hge, hle, finite_extend_koszulIdealComplex_X f, hproj, ⟨Iso.refl _⟩⟩

namespace DerivedSystem

/-- **Every stage of the derived Koszul system is a perfect object of `D(𝒪_X)`.** The stage with
exponent `e + 1` is the derived sheafification of `I^•(f₁^{e+1}, …, f_r^{e+1})`, which is a
perfect object of `D(A)`; derived sheafification on an affine scheme preserves and reflects
perfectness by [Stacks, Tag 08EB]. -/
theorem isPerfect_koszulDerivedSystem_obj {A : CommRingCat.{u}} {r : ℕ} (f : Fin r → A)
    (e : ℕ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (AlgebraicGeometry.Spec A).toRingedSpace)
      ((koszulDerivedSystem f).obj (op e)) :=
  (AlgebraicGeometry.isPerfect_tilde_iff
    (DerivedCategory.Q.obj
      ((koszulIdealComplexPower f e).extend ComplexShape.embeddingDownNat))).mpr
    (isPerfect_extend_koszulIdealComplex _)

end DerivedSystem

end Koszul

end
