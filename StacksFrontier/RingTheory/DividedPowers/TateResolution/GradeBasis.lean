module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FreeGrade

/-!
# Monotone bases for the homogeneous pieces of a variable extension

A directed union of free submodules need not be free, but it is free when the members carry a
*monotone family of bases*. We construct bases of the homogeneous pieces of the one-variable
extensions of a graded algebra: the degree-zero base case, the odd (exterior) step, and the even
(divided-power) step. Each step keeps the old basis *pointwise*: the degree-`m` basis of the
extension contains the image of the degree-`m` basis of the coefficient algebra under the
coefficient embedding, and the remaining elements involve the new variable.

## Main definitions

* `DividedPowers.TateResolution.degreeZeroBasis` — the basis family of the grading concentrated
  in degree zero.
* `DividedPowers.TateResolution.OddVariableExtension.inclusionLinearMap` and
  `generatorMulLinearMap` — the two `R`-linear maps whose images split a homogeneous piece of an
  odd variable extension.
* `DividedPowers.TateResolution.OddVariableExtension.oddStepBasis` — the basis family of an odd
  variable extension.
* `DividedPowers.TateResolution.EvenVariableAlgebra.coeffZeroOutside` — the elements whose
  divided-power coefficients vanish outside a prescribed set.
* `DividedPowers.TateResolution.EvenVariableAlgebra.evenStepBasis` — the basis family of an even
  variable extension.

## Main results

* `DividedPowers.TateResolution.span_degreeZeroBasis` and `linearIndepOn_degreeZeroBasis`.
* `DividedPowers.TateResolution.OddVariableExtension.grade_eq_sup_map` — a homogeneous piece of
  an odd variable extension is the join of the images of the two linear maps.
* `DividedPowers.TateResolution.OddVariableExtension.span_oddStepBasis` and
  `linearIndepOn_oddStepBasis`.
* `DividedPowers.TateResolution.EvenVariableAlgebra.grade_eq_iSup_map` — a homogeneous piece of
  an even variable extension is the join of the images of the divided-power monomials.
* `DividedPowers.TateResolution.EvenVariableAlgebra.span_evenStepBasis` and
  `linearIndepOn_evenStepBasis`.
* `DividedPowers.TateResolution.free_submodule_of_directed_bases` — a submodule exhausted by a
  directed family carrying a monotone family of bases is free.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

/-- The span of a conditionally empty set is conditionally trivial. -/
private theorem span_ite_empty {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (p : Prop) [Decidable p] (s : Set M) :
    Submodule.span R (if p then s else ∅) = if p then Submodule.span R s else ⊥ := by
  split_ifs <;> simp

/-- The image under an injective linear map of a conditionally empty set is independent when the
set is independent whenever nonempty. -/
private theorem linearIndepOn_image_ite {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : LinearMap.ker f = ⊥) (p : Prop) [Decidable p] (s : Set M)
    (h : p → LinearIndepOn R id s) : LinearIndepOn R id (f '' if p then s else ∅) := by
  split_ifs with hp
  · exact (h hp).image (by rw [hf]; exact disjoint_bot_right)
  · rw [Set.image_empty]; exact linearIndepOn_empty R id

section DegreeZero

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The basis family of the grading concentrated in degree zero: a prescribed basis of the
algebra in degree zero, and nothing in positive degrees. -/
public def degreeZeroBasis (s : Set A) : ℕ → Set A := fun m => if m = 0 then s else ∅

/-- A basis of the algebra spans the grading concentrated in degree zero, degree by degree. -/
public theorem span_degreeZeroBasis (s : Set A) (hs : Submodule.span R s = ⊤) (m : ℕ) :
    Submodule.span R (degreeZeroBasis A s m) = degreeZeroGrade R A m := by
  rw [degreeZeroBasis]
  match m with
  | 0 => rw [ite_eq_left rfl, hs, degreeZeroGrade_zero]
  | n + 1 =>
      rw [ite_eq_right (Nat.succ_ne_zero n), Submodule.span_empty, degreeZeroGrade_succ]

/-- The basis family of the grading concentrated in degree zero is independent in every
degree. -/
public theorem linearIndepOn_degreeZeroBasis (s : Set A) (hind : LinearIndepOn R id s) (m : ℕ) :
    LinearIndepOn R id (degreeZeroBasis A s m) := by
  rw [degreeZeroBasis]
  match m with
  | 0 => rw [ite_eq_left rfl]; exact hind
  | n + 1 => rw [ite_eq_right (Nat.succ_ne_zero n)]; exact linearIndepOn_empty R id

end DegreeZero

section Odd

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

open OddVariableExtension

attribute [local implicit_reducible] TwistedModule

namespace OddVariableExtension

/-- The coefficient embedding of an odd variable extension, as an `R`-linear map. -/
public noncomputable def inclusionLinearMap (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    A →ₗ[R] OddVariableExtension Aᵢ d :=
  (inclusionAlgHom Aᵢ d).toLinearMap

/-- The coefficient embedding of an odd variable extension followed by multiplication by the new
variable, as an `R`-linear map. Its image is the shifted part of the extension. -/
public noncomputable def generatorMulLinearMap (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) :
    A →ₗ[R] OddVariableExtension Aᵢ d :=
  (LinearMap.mulRight R (generator Aᵢ d)).comp (inclusionAlgHom Aᵢ d).toLinearMap

/-- A homogeneous piece of an odd variable extension is the join of the degree-`m` piece of the
coefficient algebra and the degree-`m - d` piece multiplied by the new variable, the latter
being zero below the degree of the variable. -/
public theorem grade_eq_sup_map (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d m : ℕ) :
    grade Aᵢ d m = (Aᵢ m).map (inclusionLinearMap Aᵢ d) ⊔
      (if d ≤ m then Aᵢ (m - d) else ⊥).map (generatorMulLinearMap Aᵢ d) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := (mem_grade_iff Aᵢ d m x).mp hx
    rw [← inclusion_fst_add_inclusion_snd_mul_generator Aᵢ d x]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨x.fst, h1, rfl⟩)
      (Submodule.mem_sup_right ⟨show A from x.snd, h2, rfl⟩)
  · refine sup_le ?_ ?_
    · exact Submodule.map_le_iff_le_comap.2 fun a ha => inclusion_mem_grade Aᵢ d m ha
    · rw [Submodule.map_le_iff_le_comap]
      intro a ha
      show generatorMulLinearMap Aᵢ d a ∈ grade Aᵢ d m
      by_cases hdm : d ≤ m
      · have ha' : a ∈ Aᵢ (m - d) := by
          rwa [ite_eq_left hdm] at ha
        have h : inclusion Aᵢ d a * generator Aᵢ d ∈ grade Aᵢ d (m - d + d) :=
          mul_mem_grade Aᵢ d (inclusion_mem_grade Aᵢ d (m - d) ha')
            (generator_mem_grade Aᵢ d)
        rwa [show m - d + d = m by lia] at h
      · have ha' : a = 0 := by
          rwa [ite_eq_right hdm, Submodule.mem_bot] at ha
        rw [ha', map_zero]
        exact Submodule.zero_mem _

/-- The odd step's basis family: the old basis in degree `m`, together with the old basis in
degree `m - d` multiplied by the new variable. -/
public def oddStepBasis (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (b : ℕ → Set A) (d m : ℕ) :
    Set (OddVariableExtension Aᵢ d) :=
  inclusionLinearMap Aᵢ d '' b m ∪
    generatorMulLinearMap Aᵢ d '' (if d ≤ m then b (m - d) else ∅)

/-- The odd step's basis family spans the homogeneous pieces of the extension. -/
public theorem span_oddStepBasis (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (b : ℕ → Set A)
    (hb : ∀ k, Submodule.span R (b k) = Aᵢ k) (d m : ℕ) :
    Submodule.span R (oddStepBasis Aᵢ b d m) = grade Aᵢ d m := by
  rw [oddStepBasis, Submodule.span_union, Submodule.span_image, Submodule.span_image, hb,
    grade_eq_sup_map, span_ite_empty]
  simp only [hb]

/-- The coefficient embedding of an odd variable extension is injective. -/
public theorem ker_inclusionLinearMap (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    LinearMap.ker (inclusionLinearMap Aᵢ d) = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun _ ha => congrArg (fun z : OddVariableExtension Aᵢ d => z.fst) ha

/-- Multiplying the coefficient embedding by the new variable is injective. -/
public theorem ker_generatorMulLinearMap (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    LinearMap.ker (generatorMulLinearMap Aᵢ d) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro a ha
  have h := congrArg (fun z : OddVariableExtension Aᵢ d => show A from z.snd) ha
  change (show A from (inclusion Aᵢ d a * generator Aᵢ d).snd) = (0 : A) at h
  rw [mul_snd] at h
  change a * (1 : A) + (0 : A) * _ = (0 : A) at h
  simpa using h

/-- The coefficient part and the shifted part of an odd variable extension are disjoint: they
are the two components of the underlying twisted square-zero extension. -/
public theorem disjoint_range_inclusion_generatorMul (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) :
    Disjoint (LinearMap.range (inclusionLinearMap Aᵢ d))
      (LinearMap.range (generatorMulLinearMap Aᵢ d)) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a, rfl⟩ ⟨a', ha'⟩
  have h := congrArg (fun z : OddVariableExtension Aᵢ d => z.fst) ha'
  change (inclusion Aᵢ d a' * generator Aᵢ d).fst = (inclusion Aᵢ d a).fst at h
  change a' * (0 : A) = a at h
  rw [mul_zero] at h
  rw [← h, map_zero]

/-- The odd step's basis family is independent in every degree. -/
public theorem linearIndepOn_oddStepBasis (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (b : ℕ → Set A) (hind : ∀ k, LinearIndepOn R id (b k)) (d m : ℕ) :
    LinearIndepOn R id (oddStepBasis Aᵢ b d m) := by
  refine LinearIndepOn.id_union ?_ ?_ ?_
  · refine (hind m).image ?_
    rw [ker_inclusionLinearMap]
    exact disjoint_bot_right
  · exact linearIndepOn_image_ite _ (ker_generatorMulLinearMap Aᵢ d) _ _ fun _ => hind _
  · refine (disjoint_range_inclusion_generatorMul Aᵢ d).mono ?_ ?_
    · rw [Submodule.span_image]; exact LinearMap.map_le_range
    · rw [Submodule.span_image]; exact LinearMap.map_le_range

end OddVariableExtension

end Odd

section Even

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

namespace EvenVariableAlgebra

/-- The elements of an even variable extension whose divided-power coefficients vanish outside a
prescribed set of exponents. -/
public def coeffZeroOutside (s : Set ℕ) : Submodule R (EvenVariableAlgebra A) where
  carrier := {x | ∀ n ∉ s, x.coeff n = 0}
  zero_mem' _ _ := rfl
  add_mem' := by
    intro x y hx hy n hn
    rw [coeff_add, Finsupp.add_apply, hx n hn, hy n hn, add_zero]
  smul_mem' := by
    intro r x hx n hn
    rw [coeff_smul, Finsupp.smul_apply, hx n hn, smul_zero]

/-- The `n`-th divided power of the new variable times anything has all its other coefficients
zero. -/
public theorem monomial_image_le_coeffZeroOutside (n : ℕ) (s : Set A) :
    Submodule.span R (monomialLinearMap (R := R) n '' s) ≤
      coeffZeroOutside (R := R) {n} := by
  rw [Submodule.span_le]
  rintro x ⟨a, -, rfl⟩ k hk
  show (monomial n a).coeff k = 0
  rw [coeff_monomial]
  exact Finsupp.single_eq_of_ne (show k ≠ n by simpa using hk)

/-- Prescribing disjoint sets of exponents gives disjoint submodules. -/
public theorem disjoint_coeffZeroOutside {i : ℕ} {t : Set ℕ} (hit : i ∉ t) :
    Disjoint (coeffZeroOutside (R := R) (A := A) {i}) (coeffZeroOutside (R := R) (A := A) t) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  refine EvenVariableAlgebra.ext (Finsupp.ext fun n => ?_)
  show x.coeff n = (0 : EvenVariableAlgebra A).coeff n
  by_cases hn : n = i
  · subst hn
    rw [hy n hit]
    rfl
  · rw [hx n (by simpa using hn)]
    rfl

/-- Enlarging the prescribed set of exponents enlarges the submodule. -/
public theorem coeffZeroOutside_mono {s t : Set ℕ} (h : s ⊆ t) :
    coeffZeroOutside (R := R) (A := A) s ≤ coeffZeroOutside (R := R) (A := A) t :=
  fun _ hx n hn => hx n fun hns => hn (h hns)

/-- The divided-power monomial map and its linear version have the same image. -/
public theorem image_monomialLinearMap (n : ℕ) (s : Set A) :
    monomialLinearMap (R := R) n '' s = monomial n '' s :=
  Set.image_congr' (fun _ => rfl)

/-- The span of a set of divided-power monomials is the image of the span. -/
public theorem span_monomial_image (n : ℕ) (s : Set A) :
    Submodule.span R (monomial n '' s) =
      (Submodule.span R s).map (monomialLinearMap (R := R) n) := by
  rw [← image_monomialLinearMap (R := R) n s, Submodule.span_image]

/-- Multiplying by a divided power of the new variable is injective. -/
public theorem ker_monomialLinearMap (n : ℕ) :
    LinearMap.ker (monomialLinearMap (R := R) (A := A) n) = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun a ha => monomial_injective n (by simpa using ha)

/-- A homogeneous piece of an even variable extension is the join, over the exponents `n` of the
new variable, of the images of the degree-`m - n * d` pieces of the coefficient algebra. -/
public theorem grade_eq_iSup_map (𝒜 : ℕ → Submodule R A) (d m : ℕ) :
    grade 𝒜 d m =
      ⨆ n : ℕ, (if n * d ≤ m then 𝒜 (m - n * d) else ⊥).map
        (monomialLinearMap (R := R) n) := by
  apply le_antisymm
  · intro x hx
    rw [← sum_monomial x]
    exact Submodule.sum_mem _ fun n _ =>
      Submodule.mem_iSup_of_mem n ⟨x.coeff n, (mem_grade_iff 𝒜 d m x).mp hx n, rfl⟩
  · refine iSup_le fun n => Submodule.map_le_iff_le_comap.2 fun a ha => ?_
    show monomial n a ∈ grade 𝒜 d m
    rwa [monomial_mem_grade_iff]

/-- The even step's basis family: the old basis in degree `m - n * d` multiplied by the `n`-th
divided power of the new variable, for every `n` with `n * d ≤ m`. -/
public def evenStepBasis (b : ℕ → Set A) (d m : ℕ) : Set (EvenVariableAlgebra A) :=
  ⋃ n : ℕ, monomial n '' (if n * d ≤ m then b (m - n * d) else ∅)

/-- The even step's basis family spans the homogeneous pieces of the extension. -/
public theorem span_evenStepBasis (𝒜 : ℕ → Submodule R A) (b : ℕ → Set A)
    (hb : ∀ k, Submodule.span R (b k) = 𝒜 k) (d m : ℕ) :
    Submodule.span R (evenStepBasis b d m) = grade 𝒜 d m := by
  rw [evenStepBasis, Submodule.span_iUnion, grade_eq_iSup_map]
  refine iSup_congr fun n => ?_
  rw [span_monomial_image, span_ite_empty]
  simp only [hb]

/-- The even step's basis family is independent in every degree. -/
public theorem linearIndepOn_evenStepBasis (b : ℕ → Set A)
    (hind : ∀ k, LinearIndepOn R id (b k)) (d m : ℕ) :
    LinearIndepOn R id (evenStepBasis b d m) := by
  refine linearIndepOn_id_iUnion_finite (fun n => ?_) (fun i t _ hit => ?_)
  · rw [← image_monomialLinearMap (R := R) n]
    exact linearIndepOn_image_ite _ (ker_monomialLinearMap n) _ _ fun _ => hind _
  · refine (disjoint_coeffZeroOutside hit).mono
      (monomial_image_le_coeffZeroOutside i _) (iSup₂_le fun k hk => ?_)
    exact (monomial_image_le_coeffZeroOutside k _).trans
      (coeffZeroOutside_mono (Set.singleton_subset_iff.mpr hk))

end EvenVariableAlgebra

end Even

section DirectedUnion

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A submodule exhausted by a directed family of submodules each of which carries a basis, the
bases increasing with the family, is free. -/
public theorem free_submodule_of_directed_bases
    {σ : Type w} [Preorder σ] [IsDirected σ (· ≤ ·)]
    (Q : Submodule R M) (N : σ → Submodule R M) (b : σ → Set M) (hb : Monotone b)
    (hspan : ∀ s, Submodule.span R (b s) = N s)
    (hind : ∀ s, LinearIndepOn R id (b s))
    (hsup : ⨆ s, N s = Q) :
    Module.Free R Q := by
  have hdir : Directed (· ⊆ ·) b := hb.directed_le
  have hiu : LinearIndepOn R id (⋃ s, b s) :=
    linearIndepOn_iUnion_of_directed hdir hind
  have hspan' : Submodule.span R (⋃ s, b s) = Q := by
    simpa only [Submodule.span_iUnion, hspan] using hsup
  have hfree : Module.Free R (Submodule.span R (⋃ s, b s)) := by
    have hli : LinearIndependent R (fun y : ((⋃ s, b s : Set M)) => id (y : M)) := hiu
    have hrange : (Set.range fun y : ((⋃ s, b s : Set M)) => id (y : M)) = ⋃ s, b s :=
      Subtype.range_val
    exact Module.Free.of_basis (hrange ▸ Module.Basis.span hli)
  exact hspan' ▸ hfree

end DirectedUnion

end DividedPowers.TateResolution

end
