module

public import StacksFrontier.Algebra.Homology.KoszulConeTensor
public import StacksFrontier.RingTheory.Koszul.DerivedQuotientModel
public import StacksFrontier.RingTheory.Koszul.Homotopy

/-!
# Finiteness, bounds and cohomology of the iterated cone `Kos(f)` over a ring

Let `A` be a commutative ring and `f₁, …, f_r ∈ A`. The iterated mapping cone
`Kos(f) = 𝟙 ⊗ Kos(f)` of multiplication by the `fᵢ` on `A[0]` is a complex of finite modules
concentrated in degrees `[-r, 0]` whose cohomology modules are annihilated by the ideal
`(f₁, …, f_r)`: it is isomorphic to the cochain Koszul complex, on whose cohomology each `fᵢ`
acts by zero ([Stacks, Tag 0663]).

## Main results

* `Stacks.KoszulCone.isZero_X_koszulTensor_of_lt`, `Stacks.KoszulCone.isStrictlyLE_koszulTensor`:
  the upper bound.
* `Stacks.KoszulCone.nonempty_koszulTensor_iso_of_iso`: invariance under isomorphisms of `K`.
* `Stacks.KoszulCone.finite_X_koszulTensor`: the terms are finite when those of `K` are.
* `Stacks.KoszulCone.span_le_annihilator_homology_koszulTensor`: the ideal of the sequence
  annihilates the cohomology of `Kos(f)`.

## References

* [Stacks Project, Tag 0663](https://stacks.math.columbia.edu/tag/0663)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.KoszulCone

section Bounds

variable {A : Type*} [CommRing A] {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜]
  [HasBinaryBiproducts 𝒜] [Linear A 𝒜]

/-- **`K ⊗_A Kos(x)` vanishes in degrees above `m`** when `K` does. -/
theorem isZero_X_koszulTensor_of_lt (K : CochainComplex 𝒜 ℤ) (m : ℤ)
    (hK : ∀ i : ℤ, m < i → IsZero (K.X i)) :
    ∀ (r : ℕ) (x : Fin r → A) (i : ℤ), m < i → IsZero ((koszulTensor r x K).X i) := by
  intro r
  induction r with
  | zero => exact fun _ i hi ↦ hK i hi
  | succ r ih =>
      intro x i hi
      refine IsZero.of_iso ?_ (koszulTensorSuccXIso r x K i)
      rw [biprod_isZero_iff]
      exact ⟨ih (Fin.init x) (i + 1) (by omega), ih (Fin.init x) i hi⟩

/-- **An upper degree bound for `K ⊗_A Kos(x)`.** -/
theorem isStrictlyLE_koszulTensor (K : CochainComplex 𝒜 ℤ) (m : ℤ) [K.IsStrictlyLE m]
    (r : ℕ) (x : Fin r → A) : (koszulTensor r x K).IsStrictlyLE m := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi ↦ isZero_X_koszulTensor_of_lt K m
    (fun i hi ↦ CochainComplex.isZero_of_isStrictlyLE K m i hi) r x i hi

/-- **`K ⊗_A Kos(x)` is functorial in isomorphisms of `K`.** -/
theorem nonempty_koszulTensor_iso_of_iso {K K' : CochainComplex 𝒜 ℤ} (e : K ≅ K') :
    ∀ (r : ℕ) (x : Fin r → A), Nonempty (koszulTensor r x K ≅ koszulTensor r x K')
  | 0, _ => ⟨e⟩
  | r + 1, x => by
    obtain ⟨e'⟩ := nonempty_koszulTensor_iso_of_iso e r (Fin.init x)
    exact ⟨mappingConeSmulIso e' (x (Fin.last r))⟩

end Bounds

variable {A : Type u} [CommRing A]

/-- **The terms of `K ⊗_A Kos(x)` are finite** when those of `K` are. -/
theorem finite_X_koszulTensor (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i, Module.Finite A (K.X i)) :
    ∀ (r : ℕ) (x : Fin r → A) (i : ℤ), Module.Finite A ((koszulTensor r x K).X i) := by
  intro r
  induction r with
  | zero => exact fun _ i ↦ hK i
  | succ r ih =>
      intro x i
      have := ih (Fin.init x) (i + 1)
      have := ih (Fin.init x) i
      exact Module.Finite.equiv ((koszulTensorSuccXIso r x K i).trans
        (ModuleCat.biprodIsoProd _ _)).toLinearEquiv.symm

/-- **The ideal of a sequence annihilates the cohomology of the cochain Koszul complex.** -/
theorem span_le_annihilator_homology_seqCochainComplex {r : ℕ} (f : Fin r → A) (i : ℤ) :
    Ideal.span (Set.range f) ≤
      Module.annihilator A ((Koszul.seqCochainComplex f).homology i) := by
  by_cases hi : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = i
  · obtain ⟨n, hn⟩ := hi
    let e :=
      ((Koszul.seqComplex f).extendHomologyIso ComplexShape.embeddingDownNat hn).toLinearEquiv
    rw [e.annihilator_eq]
    exact fun a ha ↦ (Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator f).2 n ha
  · simp only [not_exists] at hi
    have hz : IsZero ((Koszul.seqCochainComplex f).homology i) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _
        ((Koszul.seqComplex f).isZero_extend_X ComplexShape.embeddingDownNat i hi)
    have : Subsingleton ((Koszul.seqCochainComplex f).homology i) :=
      ModuleCat.subsingleton_of_isZero hz
    rw [Module.annihilator_eq_top_iff.mpr this]
    exact le_top

/-- **The ideal of a sequence annihilates the cohomology of the iterated cone
`Kos(f) = 𝟙 ⊗ Kos(f)`.** -/
theorem span_le_annihilator_homology_koszulTensor {r : ℕ} (f : Fin r → A) (i : ℤ) :
    Ideal.span (Set.range f) ≤ Module.annihilator A
      ((koszulTensor r f (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))).homology i) := by
  obtain ⟨e⟩ := nonempty_tensorObj_seqCochainComplex_iso_koszulTensor r f
    (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))
  let E : Koszul.seqCochainComplex f ≅ koszulTensor r f (𝟙_ _) := (λ_ _).symm ≪≫ e
  let eH : (koszulTensor r f (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))).homology i ≃ₗ[A]
      (Koszul.seqCochainComplex f).homology i :=
    (HomologicalComplex.homologyMapIso E.symm i).toLinearEquiv
  rw [eH.annihilator_eq]
  exact span_le_annihilator_homology_seqCochainComplex f i

end Stacks.KoszulCone
