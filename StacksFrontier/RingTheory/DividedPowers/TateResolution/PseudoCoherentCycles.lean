module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.Homology.PseudoCoherent.FiniteFree
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.NoetherianCycles

/-! # The augmented complex of a graded differential algebra over its coefficients

Let `A` be a differential graded algebra over a commutative coefficient algebra `P` sitting in
degree zero, and let `ε : A₀ → M` be a `P`-linear augmentation killing the boundaries. Placing `M`
in degree `0` and the degree-`i` piece of `A` in degree `-i - 1` gives a cochain complex of
`P`-modules, bounded above by `0`:

`⋯ → A₁ → A₀ → M → 0`.

Each homogeneous piece of `A` is a finite free `P`-module in the situation of Tag 09PN, so if `M`
is a pseudo-coherent `P`-module then the whole complex is pseudo-coherent, by Stacks 064Y. If in
addition it is exact in every degree above `-m - 1` — which for `m = 0` is surjectivity of `ε` and
`ker ε = d A₁`, and above that is exactness of `A` in the degrees below `m` — then Stacks 064S (1)
makes its degree-`(-m - 1)` cohomology a finite `P`-module, and that forces the degree-`m` cycles
of `A` to be finitely generated over `P`.

This is the replacement, under pseudo-coherence, for
`DividedPowers.TateResolution.fg_coefficientCycles`, which gets the same conclusion from
Noetherianness of `P` by "a submodule of a finitely generated module".

## Main definitions

* `DividedPowers.TateResolution.coefficientDifferential` — the differential between two
  consecutive homogeneous pieces, `P`-linearly.
* `DividedPowers.TateResolution.augmentedChainComplex` — the augmented complex, `ℕ`-indexed.
* `DividedPowers.TateResolution.augmentedCochainComplex` — the same complex, placed in the
  non-positive integer degrees.

## Main results

* `DividedPowers.TateResolution.isPseudoCoherent_augmentedCochainComplex` — the augmented complex
  is pseudo-coherent when `M` is and the homogeneous pieces are finite free, Stacks 064Y.
* `DividedPowers.TateResolution.finite_coefficientCycles_of_isModulePseudoCoherent` and
  `DividedPowers.TateResolution.fg_coefficientCycles_of_isModulePseudoCoherent` — the degree-`m`
  cycles are then finitely generated over `P`, given exactness below `m`, Stacks 064S (1).

## References

* [Stacks Project, Tag 064Y](https://stacks.math.columbia.edu/tag/064Y)
* [Stacks Project, Tag 064S](https://stacks.math.columbia.edu/tag/064S)
* [Stacks Project, Tag 0BZ9](https://stacks.math.columbia.edu/tag/0BZ9)
-/

open CategoryTheory CategoryTheory.Limits StacksDraft.PseudoCoherence

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section Differential

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra Aᵢ d]

/-- **The differential between two consecutive homogeneous pieces, over the coefficient
algebra.** The differential lowers degree by one and is linear over coefficients of degree
zero. -/
public def coefficientDifferential (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ) :
    ↥(coefficientGrade Aᵢ h0 (n + 1)) →ₗ[P] ↥(coefficientGrade Aᵢ h0 n) where
  toFun x := ⟨d x.1, IsDifferentialGradedAlgebra.d_mem (𝒜 := Aᵢ) (d := d) x.2⟩
  map_add' x y := Subtype.ext (map_add d x.1 y.1)
  map_smul' p x := Subtype.ext (map_coefficient_smul Aᵢ d h0 p x.2)

/-- The underlying element of a value of `coefficientDifferential` is the differential. -/
@[simp]
public theorem coe_coefficientDifferential {h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0} {n : ℕ}
    (x : ↥(coefficientGrade Aᵢ h0 (n + 1))) :
    (coefficientDifferential Aᵢ d h0 n x : A) = d x.1 := rfl

/-- The differential squares to zero on the homogeneous pieces. -/
public theorem coefficientDifferential_comp (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ)
    (x : ↥(coefficientGrade Aᵢ h0 (n + 1 + 1))) :
    coefficientDifferential Aᵢ d h0 n (coefficientDifferential Aᵢ d h0 (n + 1) x) = 0 :=
  Subtype.ext (IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := Aᵢ) (d := d) x.1)

/-- **The degree-`n + 1` cycles are the image of the kernel of the differential out of the
degree-`n + 1` piece.** This is the translation between the cycles as a submodule of `A` and the
cycles of the augmented complex. -/
public theorem coefficientCycles_eq_map_ker (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ) :
    coefficientCycles Aᵢ d h0 (n + 1) =
      (LinearMap.ker (coefficientDifferential Aᵢ d h0 n)).map
        (coefficientGrade Aᵢ h0 (n + 1)).subtype := by
  ext x
  simp only [mem_coefficientCycles, Submodule.mem_map, LinearMap.mem_ker,
    Submodule.coe_subtype]
  constructor
  · rintro ⟨hx, hdx⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hdx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val hy⟩

end Differential

section Complex

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra Aᵢ d] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
  (M : Type w) [AddCommGroup M] [Module P M]

/-- The terms of the augmented complex: the augmentation target in degree `0`, and the
degree-`n` homogeneous piece in degree `n + 1`. -/
public def augmentedTerm : ℕ → ModuleCat.{w} P
  | 0 => ModuleCat.of P M
  | n + 1 => ModuleCat.of P ↥(coefficientGrade Aᵢ h0 n)

variable (ε : ↥(coefficientGrade Aᵢ h0 0) →ₗ[P] M)

/-- The differentials of the augmented complex: the augmentation at the bottom, and the
differential of `A` above it. -/
public def augmentedDiff :
    ∀ n : ℕ, augmentedTerm Aᵢ h0 M (n + 1) ⟶ augmentedTerm Aᵢ h0 M n
  | 0 => ModuleCat.ofHom ε
  | n + 1 => ModuleCat.ofHom (coefficientDifferential Aᵢ d h0 n)

variable (hε : ∀ x : ↥(coefficientGrade Aᵢ h0 1),
  ε (coefficientDifferential Aᵢ d h0 0 x) = 0)

include hε in
/-- The augmented data really is a complex: the augmentation kills the boundaries, and the
differential of `A` squares to zero. -/
public theorem augmentedDiff_comp (n : ℕ) :
    augmentedDiff Aᵢ d h0 M ε (n + 1) ≫ augmentedDiff Aᵢ d h0 M ε n = 0 := by
  match n with
  | 0 =>
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact hε x
  | n + 1 =>
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact coefficientDifferential_comp Aᵢ d h0 n x

/-- **The augmented complex of `A`**, with the augmentation target in degree `0` and the
degree-`n` homogeneous piece in degree `n + 1`. -/
public def augmentedChainComplex : ChainComplex (ModuleCat.{w} P) ℕ :=
  ChainComplex.of (augmentedTerm Aᵢ h0 M) (augmentedDiff Aᵢ d h0 M ε)
    (augmentedDiff_comp Aᵢ d h0 M ε hε)

/-- The degree-`n` term of the augmented complex. -/
public theorem augmentedChainComplex_X (n : ℕ) :
    (augmentedChainComplex Aᵢ d h0 M ε hε).X n = augmentedTerm Aᵢ h0 M n := rfl

/-- The degree-`n + 1` differential of the augmented complex. -/
public theorem augmentedChainComplex_d (n : ℕ) :
    (augmentedChainComplex Aᵢ d h0 M ε hε).d (n + 1) n = augmentedDiff Aᵢ d h0 M ε n :=
  ChainComplex.of_d _ _ n

/-- **The augmented complex, placed in the non-positive integer degrees**, with the augmentation
target in degree `0` and the degree-`n` homogeneous piece in degree `-n - 1`. -/
public noncomputable def augmentedCochainComplex : CochainComplex (ModuleCat.{w} P) ℤ :=
  (augmentedChainComplex Aᵢ d h0 M ε hε).extend ComplexShape.embeddingDownNat

/-- The degree-`-n` term of the augmented cochain complex is the degree-`n` term of the
augmented chain complex. -/
public noncomputable def augmentedCochainComplexXIso (n : ℕ) :
    (augmentedCochainComplex Aᵢ d h0 M ε hε).X (-n) ≅ augmentedTerm Aᵢ h0 M n :=
  (augmentedChainComplex Aᵢ d h0 M ε hε).extendXIso ComplexShape.embeddingDownNat rfl

/-- The augmented cochain complex vanishes in every positive degree. -/
public theorem isZero_augmentedCochainComplex_X {i : ℤ} (hi : 0 < i) :
    IsZero ((augmentedCochainComplex Aᵢ d h0 M ε hε).X i) :=
  (augmentedChainComplex Aᵢ d h0 M ε hε).isZero_extend_X ComplexShape.embeddingDownNat i
    (fun n hn => by simp only [ComplexShape.embeddingDownNat_f] at hn; omega)

/-- The augmented cochain complex is bounded above by degree `0`. -/
public theorem isStrictlyLE_augmentedCochainComplex :
    (augmentedCochainComplex Aᵢ d h0 M ε hε).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun _ hi =>
    isZero_augmentedCochainComplex_X Aᵢ d h0 M ε hε hi

/-- A chain complex of modules is exact at `i + 1` when the image of the differential into it is
the kernel of the differential out of it. -/
private theorem exactAt_succ_of_range_eq_ker {C : ChainComplex (ModuleCat.{w} P) ℕ} (i : ℕ)
    (h : LinearMap.range (C.d (i + 2) (i + 1)).hom = LinearMap.ker (C.d (i + 1) i).hom) :
    C.ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i
    (by simp only [ChainComplex.prev]; rfl) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact h

end Complex

section Exactness

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra Aᵢ d] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
  (M : Type w) [AddCommGroup M] [Module P M]
  (ε : ↥(coefficientGrade Aᵢ h0 0) →ₗ[P] M)
  (hε : ∀ x : ↥(coefficientGrade Aᵢ h0 1), ε (coefficientDifferential Aᵢ d h0 0 x) = 0)

include hε

/-- **The augmented complex is exact at the augmentation target** exactly when the augmentation
is onto. -/
public theorem exactAt_zero_augmentedChainComplex (hsurj : Function.Surjective ε) :
    (augmentedChainComplex Aᵢ d h0 M ε hε).ExactAt 0 := by
  have hf : (augmentedChainComplex Aᵢ d h0 M ε hε).d 1 0 = ModuleCat.ofHom ε :=
    augmentedChainComplex_d Aᵢ d h0 M ε hε 0
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp only [ChainComplex.prev]; rfl)
    (by simp), ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, hf]
  refine le_antisymm (fun x _ => LinearMap.mem_ker.2 rfl) fun x _ => ?_
  obtain ⟨y, hy⟩ := hsurj x
  exact ⟨y, hy⟩

/-- **The augmented complex is exact at the degree-zero piece of `A`** exactly when the kernel of
the augmentation is the image of the differential out of degree one. -/
public theorem exactAt_one_augmentedChainComplex
    (hker : LinearMap.ker ε = LinearMap.range (coefficientDifferential Aᵢ d h0 0)) :
    (augmentedChainComplex Aᵢ d h0 M ε hε).ExactAt 1 :=
  exactAt_succ_of_range_eq_ker 0 (by
    rw [augmentedChainComplex_d, augmentedChainComplex_d]
    exact hker.symm)

/-- **The augmented complex is exact at the degree-`n + 1` piece of `A`** exactly when `A` is
exact in degree `n + 1`. -/
public theorem exactAt_succ_succ_augmentedChainComplex (n : ℕ)
    (hex : LinearMap.range (coefficientDifferential Aᵢ d h0 (n + 1)) =
      LinearMap.ker (coefficientDifferential Aᵢ d h0 n)) :
    (augmentedChainComplex Aᵢ d h0 M ε hε).ExactAt (n + 2) :=
  exactAt_succ_of_range_eq_ker (n + 1) (by
    rw [augmentedChainComplex_d, augmentedChainComplex_d]
    exact hex)

end Exactness

section PseudoCoherent

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra Aᵢ d] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
  (M : Type w) [AddCommGroup M] [Module P M]
  (ε : ↥(coefficientGrade Aᵢ h0 0) →ₗ[P] M)
  (hε : ∀ x : ↥(coefficientGrade Aᵢ h0 1), ε (coefficientDifferential Aᵢ d h0 0 x) = 0)

/-- Pseudo-coherence of a module object of `ModuleCat P` depends only on its isomorphism
class. This is `StacksDraft.PseudoCoherence.IsModulePseudoCoherent.ofIso` with the module
universe independent of the ring's. -/
public theorem isModulePseudoCoherent_of_iso [HasDerivedCategory (ModuleCat.{w} P)]
    {N₁ N₂ : ModuleCat.{w} P} (e : N₁ ≅ N₂)
    (h : IsModulePseudoCoherent (R := P) N₁) : IsModulePseudoCoherent (R := P) N₂ :=
  IsPseudoCoherent.ofIso h ((DerivedCategory.singleFunctor (ModuleCat.{w} P) 0).mapIso e)

/-- A zero module object is pseudo-coherent, being finite free. -/
public theorem isModulePseudoCoherent_of_isZero [HasDerivedCategory (ModuleCat.{w} P)]
    {N : ModuleCat.{w} P} (h : IsZero N) : IsModulePseudoCoherent (R := P) N :=
  have : Subsingleton N := ModuleCat.isZero_iff_subsingleton.mp h
  have : Module.Finite P N := Module.Finite.of_finite
  have : Module.Free P N := Module.Free.of_subsingleton P _
  isModulePseudoCoherent_of_finite_free (R := P) N

/-- Every term of the augmented complex is a pseudo-coherent `P`-module, when the augmentation
target is one and the homogeneous pieces of `A` are finite free over `P`. -/
public theorem isModulePseudoCoherent_augmentedTerm [HasDerivedCategory (ModuleCat.{w} P)]
    (hM : IsModulePseudoCoherent (R := P) M)
    (hfin : ∀ i : ℕ, Module.Finite P ↥(coefficientGrade Aᵢ h0 i))
    (hfree : ∀ i : ℕ, Module.Free P ↥(coefficientGrade Aᵢ h0 i)) (n : ℕ) :
    IsModulePseudoCoherent (R := P) (augmentedTerm Aᵢ h0 M n) := by
  match n with
  | 0 => exact hM
  | n + 1 =>
      have := hfin n
      have := hfree n
      exact isModulePseudoCoherent_of_finite_free (R := P) ↥(coefficientGrade Aᵢ h0 n)

include hε in
/-- **The augmented complex is pseudo-coherent**, being bounded above with pseudo-coherent
terms. This is Stacks 064Y applied to `⋯ → A₁ → A₀ → M → 0`. -/
public theorem isPseudoCoherent_augmentedCochainComplex [HasDerivedCategory (ModuleCat.{w} P)]
    (hM : IsModulePseudoCoherent (R := P) M)
    (hfin : ∀ i : ℕ, Module.Finite P ↥(coefficientGrade Aᵢ h0 i))
    (hfree : ∀ i : ℕ, Module.Free P ↥(coefficientGrade Aᵢ h0 i)) :
    IsPseudoCoherent
      (DerivedCategory.Q.obj (augmentedCochainComplex Aᵢ d h0 M ε hε)) := by
  refine (pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove
    (augmentedCochainComplex Aᵢ d h0 M ε hε)
    ⟨0, isStrictlyLE_augmentedCochainComplex Aᵢ d h0 M ε hε⟩).2 fun i => ?_
  by_cases hi : ∃ n : ℕ, -(n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hi
    exact isModulePseudoCoherent_of_iso (augmentedCochainComplexXIso Aᵢ d h0 M ε hε n).symm
      (isModulePseudoCoherent_augmentedTerm Aᵢ h0 M hM hfin hfree n)
  · refine isModulePseudoCoherent_of_isZero
      (isZero_augmentedCochainComplex_X Aᵢ d h0 M ε hε (i := i) ?_)
    by_contra hle
    exact hi ⟨(-i).toNat, by omega⟩

/-- **The augmented complex is exact in every degree up to `n + 1`** when the augmentation is
onto, its kernel is the image of the differential out of degree one, and `A` is exact in every
degree up to `n`. -/
public theorem exactAt_augmentedChainComplex (n : ℕ)
    (hsurj : Function.Surjective ε)
    (hker : LinearMap.ker ε = LinearMap.range (coefficientDifferential Aᵢ d h0 0))
    (hexact : ∀ i : ℕ, i + 1 ≤ n → LinearMap.range (coefficientDifferential Aᵢ d h0 (i + 1)) =
      LinearMap.ker (coefficientDifferential Aᵢ d h0 i)) :
    ∀ j : ℕ, j ≤ n + 1 → (augmentedChainComplex Aᵢ d h0 M ε hε).ExactAt j
  | 0, _ => exactAt_zero_augmentedChainComplex Aᵢ d h0 M ε hε hsurj
  | 1, _ => exactAt_one_augmentedChainComplex Aᵢ d h0 M ε hε hker
  | i + 2, hj => exactAt_succ_succ_augmentedChainComplex Aᵢ d h0 M ε hε i
      (hexact i (by omega))

include hε in
/-- The homology of the augmented cochain complex vanishes in every degree above `-n - 2`, when
the augmented chain complex is exact in every degree up to `n + 1`. -/
public theorem isZero_homology_augmentedCochainComplex (n : ℕ)
    (hex : ∀ j : ℕ, j ≤ n + 1 → (augmentedChainComplex Aᵢ d h0 M ε hε).ExactAt j)
    {i : ℤ} (hi : -((n + 2 : ℕ) : ℤ) < i) :
    IsZero ((HomologicalComplex.homologyFunctor (ModuleCat.{w} P) (ComplexShape.up ℤ) i).obj
      (augmentedCochainComplex Aᵢ d h0 M ε hε)) := by
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  by_cases hj : ∃ j : ℕ, -(j : ℤ) = i
  · obtain ⟨j, rfl⟩ := hj
    have hjn : j ≤ n + 1 := by push_cast at hi; omega
    exact ((augmentedChainComplex Aᵢ d h0 M ε hε).extend_exactAt_iff
      ComplexShape.embeddingDownNat (j := j) rfl).2 (hex j hjn)
  · exact (augmentedChainComplex Aᵢ d h0 M ε hε).extend_exactAt
      ComplexShape.embeddingDownNat i (fun j hj' => hj ⟨j, hj'⟩)

include hε in
/-- **The degree-`n + 1` homology of the augmented complex is a finite `P`-module**, when the
complex is pseudo-coherent and exact in every degree above it. This is Stacks 064S (1). -/
public theorem finite_homology_augmentedChainComplex [HasDerivedCategory (ModuleCat.{w} P)]
    (n : ℕ) (hM : IsModulePseudoCoherent (R := P) M)
    (hfin : ∀ i : ℕ, Module.Finite P ↥(coefficientGrade Aᵢ h0 i))
    (hfree : ∀ i : ℕ, Module.Free P ↥(coefficientGrade Aᵢ h0 i))
    (hex : ∀ j : ℕ, j ≤ n + 1 → (augmentedChainComplex Aᵢ d h0 M ε hε).ExactAt j) :
    Module.Finite P ((augmentedChainComplex Aᵢ d h0 M ε hε).homology (n + 2)) := by
  have hpcf : IsPseudoCoherentFrom
      (DerivedCategory.Q.obj (augmentedCochainComplex Aᵢ d h0 M ε hε))
      (-((n + 2 : ℕ) : ℤ)) :=
    (pseudoCoherent_iff_all _).1
      (isPseudoCoherent_augmentedCochainComplex Aᵢ d h0 M ε hε hM hfin hfree) _
  have hvanish : ∀ i : ℤ, -((n + 2 : ℕ) : ℤ) < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} P) i).obj
        (DerivedCategory.Q.obj (augmentedCochainComplex Aᵢ d h0 M ε hε))) := fun i hi =>
    (isZero_homology_augmentedCochainComplex Aᵢ d h0 M ε hε n hex hi).of_iso
      (bridgeIso (augmentedCochainComplex Aᵢ d h0 M ε hε) i)
  have hQ := _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom
    (DerivedCategory.Q.obj (augmentedCochainComplex Aᵢ d h0 M ε hε))
    (-((n + 2 : ℕ) : ℤ)) hpcf hvanish
  have hL : Module.Finite P
      ((augmentedCochainComplex Aᵢ d h0 M ε hε).homology (-((n + 2 : ℕ) : ℤ))) :=
    Module.Finite.equiv
      (bridgeIso (augmentedCochainComplex Aᵢ d h0 M ε hε) (-((n + 2 : ℕ) : ℤ))).toLinearEquiv
  rw [show augmentedCochainComplex Aᵢ d h0 M ε hε =
    (augmentedChainComplex Aᵢ d h0 M ε hε).extend ComplexShape.embeddingDownNat from rfl] at hL
  exact Module.Finite.equiv
    ((augmentedChainComplex Aᵢ d h0 M ε hε).extendHomologyIso
      ComplexShape.embeddingDownNat (j := n + 2) (j' := -((n + 2 : ℕ) : ℤ)) rfl).toLinearEquiv

/-- **The middle kernel of a short complex of modules is finite** when its first term and its
homology are: the homology is the quotient of that kernel by the image of the first term. -/
public theorem finite_ker_of_finite_homology {S : ShortComplex (ModuleCat.{w} P)}
    (hX₁ : Module.Finite P S.X₁) (hH : Module.Finite P S.homology) :
    Module.Finite P ↥(LinearMap.ker S.g.hom) := by
  have hquot : Module.Finite P
      (↥(LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles) :=
    Module.Finite.equiv (ShortComplex.moduleCatHomologyIso S).toLinearEquiv
  have hrange : Module.Finite P ↥(LinearMap.range S.moduleCatToCycles) :=
    Module.Finite.of_surjective _ S.moduleCatToCycles.surjective_rangeRestrict
  exact Module.Finite.of_submodule_quotient (LinearMap.range S.moduleCatToCycles)

include hε in
/-- **The degree-`n + 1` cycles of `A` are a finite `P`-module.** The homology of the augmented
complex there is finite by Stacks 064S (1), and the boundaries are finite because the
degree-`n + 2` piece of `A` is, so the cycles are an extension of two finite modules. -/
public theorem finite_ker_coefficientDifferential_of_isModulePseudoCoherent
    [HasDerivedCategory (ModuleCat.{w} P)] (n : ℕ) (hM : IsModulePseudoCoherent (R := P) M)
    (hfin : ∀ i : ℕ, Module.Finite P ↥(coefficientGrade Aᵢ h0 i))
    (hfree : ∀ i : ℕ, Module.Free P ↥(coefficientGrade Aᵢ h0 i))
    (hex : ∀ j : ℕ, j ≤ n + 1 → (augmentedChainComplex Aᵢ d h0 M ε hε).ExactAt j) :
    Module.Finite P ↥(LinearMap.ker (coefficientDifferential Aᵢ d h0 n)) := by
  have hH : Module.Finite P
      ((augmentedChainComplex Aᵢ d h0 M ε hε).homology (n + 2)) :=
    finite_homology_augmentedChainComplex Aᵢ d h0 M ε hε n hM hfin hfree hex
  have hSH : Module.Finite P
      (((augmentedChainComplex Aᵢ d h0 M ε hε).sc' (n + 3) (n + 2) (n + 1)).homology) :=
    Module.Finite.equiv ((augmentedChainComplex Aᵢ d h0 M ε hε).homologyIsoSc'
      (n + 3) (n + 2) (n + 1) (by simp) (by simp)).toLinearEquiv
  have hcyc := finite_ker_of_finite_homology
    (S := (augmentedChainComplex Aᵢ d h0 M ε hε).sc' (n + 3) (n + 2) (n + 1))
    (hfin (n + 2)) hSH
  rw [show ((augmentedChainComplex Aᵢ d h0 M ε hε).sc' (n + 3) (n + 2) (n + 1)).g =
      ModuleCat.ofHom (coefficientDifferential Aᵢ d h0 n) from
    augmentedChainComplex_d Aᵢ d h0 M ε hε (n + 1)] at hcyc
  exact hcyc

include hε in
/-- **Under pseudo-coherence of the augmentation target the degree-`n + 1` cycles of `A` are
finitely generated over the coefficient algebra**, given exactness of the augmented complex in
the degrees below. This is the conclusion that
`DividedPowers.TateResolution.fg_coefficientCycles` obtains from Noetherianness of `P`. -/
public theorem fg_coefficientCycles_of_isModulePseudoCoherent
    [HasDerivedCategory (ModuleCat.{w} P)] (n : ℕ) (hM : IsModulePseudoCoherent (R := P) M)
    (hfin : ∀ i : ℕ, Module.Finite P ↥(coefficientGrade Aᵢ h0 i))
    (hfree : ∀ i : ℕ, Module.Free P ↥(coefficientGrade Aᵢ h0 i))
    (hsurj : Function.Surjective ε)
    (hker : LinearMap.ker ε = LinearMap.range (coefficientDifferential Aᵢ d h0 0))
    (hexact : ∀ i : ℕ, i + 1 ≤ n → LinearMap.range (coefficientDifferential Aᵢ d h0 (i + 1)) =
      LinearMap.ker (coefficientDifferential Aᵢ d h0 i)) :
    (coefficientCycles Aᵢ d h0 (n + 1)).FG := by
  have hcyc : Module.Finite P ↥(LinearMap.ker (coefficientDifferential Aᵢ d h0 n)) :=
    finite_ker_coefficientDifferential_of_isModulePseudoCoherent Aᵢ d h0 M ε hε n hM hfin hfree
      (exactAt_augmentedChainComplex Aᵢ d h0 M ε hε n hsurj hker hexact)
  rw [coefficientCycles_eq_map_ker Aᵢ d h0 n]
  exact (Module.Finite.iff_fg.1 hcyc).map _

end PseudoCoherent

end DividedPowers.TateResolution

end
