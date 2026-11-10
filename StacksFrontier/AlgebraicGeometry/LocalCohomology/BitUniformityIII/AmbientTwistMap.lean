module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientSections
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Functoriality
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.SheafMapIsIso
public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Statement
public import StacksFrontier.RingTheory.GradedAlgebra.ModuleTruncation
public import StacksCore.Tactic.StacksAttribute

/-!
# The first map `𝒪_X(q+1) ⟶ 𝒪_X(q)` of the second sequence of Tag 0GA7

Let `A` be a commutative ring, `I ⊆ A` an ideal, `S = ⨁_{n ≥ 0} Iⁿ` the Rees algebra and
`X = Proj(S)` the blowup of `Spec(A)` in `I`. The proof of [Stacks, Tag 0GA7] uses the short
exact sequence

  `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`

on `X`, whose first map comes from the identification `𝒪_X(1) = 𝒪_X(-Y)` of [Stacks, Tag 02OS]
part (3). This file constructs that first map — canonically, with no choice of a generator
anywhere.

## Why it is not simply a map of graded modules

`𝒪_X(q)` is the sheaf associated to the twist `S(q)` of the regular module, whose degree-`i`
piece is `S_{i+q}`, zero for `i + q < 0`. A degree-preserving `S`-linear map `S(q+1) → S(q)` is
determined by the image of `1 ∈ S_0 = S(q+1)_{-q-1}`, whose target `S(q)_{-q-1} = S_{-1}` is
zero; so the only such map is zero. The honest map is the family of inclusions
`I^{i+q+1} ⊆ I^{i+q}`, which in the Rees model is *division by `X`*: the degree-`n` piece of
`S ⊆ A[X]` consists of the monomials `monomial n r` with `r ∈ Iⁿ`, and the inclusion
`Iⁿ ⊆ I^{n-1}` reads `monomial n r ↦ monomial (n-1) r`, i.e. `Polynomial.divX`. That family
fails `S`-linearity in exactly one degree, `i = -q-1`, where its source is `S_0 = A` and its
target is `S_{-1} = 0`.

## The repair

Truncate. `Stacks.GradedModule.truncationAbove` removes exactly the offending degree: the
truncation of `S(q+1)` above degree `-q` has underlying module the irrelevant ideal `S₊`, whose
elements are the polynomials in `S` with vanishing constant term, and `divX` *is* `S`-linear on
it — `divX (c · p) = c · divX p` once `p` is divisible by `X`. So there are two
degree-preserving maps out of the truncation:

* its inclusion into `S(q+1)`, bijective in every degree `≥ -q`, hence inducing an
  **isomorphism** `(S₊(q+1))~ ≅ 𝒪_X(q+1)` by
  `isIso_associatedModuleSheafMap_of_eventually_bijective` in the namespace
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections`;
* `divX`, into `S(q)`.

`ambientTwistMap` is the first inverted and composed with the second.

## Main definitions

* `Stacks.Blowup.reesTruncation`: the truncation of `S(t+1)` above degree `-t`, as a submodule
  of `S`; its underlying module is `S₊` for every `t`.
* `Stacks.Blowup.reesShift`: `divX`, as an `S`-linear map `S₊ →ₗ[S] S`.
* `Stacks.LocalCohomology.UniformityIII.ambientTwistMap`: **the map `𝒪_X(q+1) ⟶ 𝒪_X(q)`.**

## Main results

* `Stacks.Blowup.coeff_zero_eq_zero_of_mem_reesTruncation`: an element of the truncation has
  vanishing constant term; this is what makes `divX` linear on it.
* `Stacks.Blowup.reesShift_mem_twistGrading`: `divX` is degree-preserving from the truncation's
  grading into that of `S(t)`.
* `Stacks.Blowup.isIso_reesTruncationComparison`: the inclusion of the truncation induces an
  isomorphism of associated sheaves.
* `Stacks.LocalCohomology.UniformityIII.app_top_ambientTwistMap_ambientSections`: **the
  left-hand square** of the diagram in the proof of [Stacks, Tag 0GA7] clause (2) for the
  ambient sequence — the composite `I^{q+1} → H⁰(X, 𝒪_X(q+1)) → H⁰(X, 𝒪_X(q))` is the canonical
  map of `Iᑫ` along `I^{q+1} ⊆ Iᑫ`.

## Implementation notes

That an element of the truncation has vanishing constant term is proved from
`Stacks.GradedModule.truncationAbove_eq_span`: the homogeneous generators of degree `≥ -t` sit
in `reesGrading I n` for `n ≥ 1`, where the constant term vanishes by definition, and the
property survives the `S`-span because `(c * p).coeff 0 = c.coeff 0 * p.coeff 0`.

`S`-linearity of `divX` on the truncation is cancellation of `X`: `X * divX p = p` when
`p.coeff 0 = 0`, so `X * divX (c * p) = c * p = X * (c * divX p)`, and `X * a = X * b` forces
`a = b` by comparing coefficients — no domain hypothesis on `A` is needed.

The truncation is taken above `-t` for the twist `S(t+1)`, so the degrees it keeps are the `i`
with `i + t + 1 ≥ 1`. Its grading is `Stacks.GradedModule.truncationAboveGrading`, which is
automatically trivial below the cut; the degree-preservation statement for `divX` therefore
splits on `-t ≤ i`, the other branch being
`Stacks.GradedModule.truncationAboveGrading_eq_bot`.

`twistShiftMap` is marked `irreducible`, and every statement about it is proved against
`twistShiftMap_eq` rather than by unfolding: with the comparison isomorphism exposed, the
unifier spends its whole heartbeat budget on `isDefEq` in any goal mentioning the map inside a
`≫` or a `.val.app`. For the same reason the proofs below are written with explicit `congrArg`
steps rather than with `rw` on morphisms — `rw`'s motive check on a morphism of
`SheafOfModules` is where that cost lands. The inverse of the comparison is never computed: the
section of `𝒪_X(q+1)` attached to `x ∈ I^{q+1}` is exhibited as the *image* of a section of the
truncation, and `comparison_hom_comp_twistShiftMap` cancels the isomorphism against it.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGrading integerGrading
  homogeneousSubmodule associatedModuleSheaf)
open Stacks.GradedModule
open Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections
  degreeZeroToGlobalSections_naturality)
open Opposite (op)

universe u

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### Division by `X` on the Rees algebra -/

/-- Dividing by `X` keeps an element inside the Rees algebra: the `i`-th coefficient of
`divX f` is the `(i+1)`-st of `f`, which lies in `I^{i+1} ⊆ Iⁱ`. -/
theorem divX_mem_reesAlgebra {f : A[X]} (hf : f ∈ reesAlgebra I) : divX f ∈ reesAlgebra I := by
  intro i
  rw [coeff_divX]
  exact Ideal.pow_le_pow_right (Nat.le_succ i) (hf (i + 1))

/-- Multiplication by `X` is injective on `A[X]`, for any commutative ring `A`: the
`(n+1)`-st coefficient of `X * p` is the `n`-th of `p`. -/
theorem X_mul_right_injective : Function.Injective fun p : A[X] => X * p := by
  intro p r h
  refine Polynomial.ext fun n => ?_
  have h' := congrArg (fun z : A[X] => z.coeff (n + 1)) h
  simpa only [coeff_X_mul] using h'

/-- An element of `A[X]` with vanishing constant term is `X` times its quotient by `X`. -/
theorem X_mul_divX_of_coeff_zero {f : A[X]} (hf : f.coeff 0 = 0) : X * divX f = f := by
  have h := X_mul_divX_add f
  rw [hf, map_zero, add_zero] at h
  exact h

/-- **`divX` is `A[X]`-linear on the polynomials with vanishing constant term**: cancelling `X`
from `X * divX (c * f) = c * f = X * (c * divX f)`. -/
theorem divX_mul_of_coeff_zero (c : A[X]) {f : A[X]} (hf : f.coeff 0 = 0) :
    divX (c * f) = c * divX f := by
  refine X_mul_right_injective ?_
  have hcf : (c * f).coeff 0 = 0 := by rw [mul_coeff_zero, hf, mul_zero]
  calc X * divX (c * f) = c * f := X_mul_divX_of_coeff_zero hcf
    _ = c * (X * divX f) := by rw [X_mul_divX_of_coeff_zero hf]
    _ = X * (c * divX f) := by ring

/-- Dividing `monomial (n+1) r` by `X` gives `monomial n r`: this is the inclusion
`I^{n+1} ⊆ Iⁿ` read in the Rees model. -/
theorem divX_monomial_succ (n : ℕ) (r : A) :
    divX (monomial (n + 1) r : A[X]) = monomial n r := by
  ext m
  rw [coeff_divX, coeff_monomial, coeff_monomial]
  by_cases h : n = m <;> simp [h]

/-! ### The truncation of a twist of the Rees algebra -/

variable (t : ℤ)

/-- **The truncation of the twist `S(t+1)` of the Rees algebra above degree `-t`.** The degrees
it keeps are the `i` with `i + t + 1 ≥ 1`, so its underlying module is the irrelevant ideal
`S₊` for every `t`, and in particular it is where the single degree obstructing an `S`-linear
map `S(t+1) → S(t)` has been removed. -/
abbrev reesTruncation : Submodule (reesAlgebra I) (reesAlgebra I) :=
  truncationAbove (reesGrading I) (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t)

/-- The grading of the truncation. -/
abbrev reesTruncationGrading : ℤ → AddSubgroup (reesTruncation I t) :=
  truncationAboveGrading (reesGrading I)
    (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t)

/-- A homogeneous element of the Rees algebra of positive degree has vanishing constant term. -/
theorem coeff_zero_eq_zero_of_mem_reesGrading {n : ℕ} (hn : 1 ≤ n) {f : reesAlgebra I}
    (hf : f ∈ reesGrading I n) : ((f : A[X])).coeff 0 = 0 :=
  hf 0 (by omega)

/-- In a degree where the twist `S(t)` of the Rees algebra is not forced to vanish, membership
in it is membership in the corresponding homogeneous piece of `S`. -/
theorem mem_twistGrading_iff {t i : ℤ} (hi : (0 : ℤ) ≤ i + t) (f : reesAlgebra I) :
    f ∈ twistGrading (S := reesAlgebra I) (reesGrading I) t i ↔
      f ∈ reesGrading I (i + t).toNat := by
  change f ∈ integerGrading (reesGrading I) (i + t) ↔ _
  rw [show integerGrading (S := reesAlgebra I) (reesGrading I) (i + t) =
      homogeneousSubmodule (S := reesAlgebra I) (reesGrading I) (i + t).toNat from by
    simp [integerGrading, hi]]
  exact AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule _ _ _

/-- **An element of the truncation has vanishing constant term.** The homogeneous generators of
degree `≥ -t` lie in `reesGrading I n` for `n ≥ 1`, where the constant term vanishes, and the
property survives the `S`-span because `(c * p).coeff 0 = c.coeff 0 * p.coeff 0`. -/
theorem coeff_zero_eq_zero_of_mem_reesTruncation {f : reesAlgebra I}
    (hf : f ∈ reesTruncation I t) : ((f : A[X])).coeff 0 = 0 := by
  have hspan : f ∈ Submodule.span (reesAlgebra I) (⋃ j ∈ Set.Ici (-t),
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1) j : Set (reesAlgebra I))) := by
    rw [← truncationAbove_eq_span (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t)]
    exact hf
  clear hf
  induction hspan using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.mp hz
    have hj' : -t ≤ j := Set.mem_Ici.mp hj
    have hzj' : z ∈ reesGrading I (j + (t + 1)).toNat :=
      (mem_twistGrading_iff I (by omega) z).mp hzj
    exact coeff_zero_eq_zero_of_mem_reesGrading I (by omega) hzj'
  | zero => simp
  | add x y _ _ hx hy => rw [AddMemClass.coe_add, coeff_add, hx, hy, add_zero]
  | smul c x _ hx =>
    change ((c : A[X]) * (x : A[X])).coeff 0 = 0
    rw [mul_coeff_zero, hx, mul_zero]

/-- **`divX` as an `S`-linear map `S₊ →ₗ[S] S`.** This is the family of inclusions
`I^{n} ⊆ I^{n-1}`, read in the Rees model; it is linear because its source has had the single
non-linear degree removed. -/
def reesShift : reesTruncation I t →ₗ[reesAlgebra I] reesAlgebra I where
  toFun f := ⟨divX ((f : reesAlgebra I) : A[X]), divX_mem_reesAlgebra I (f : reesAlgebra I).2⟩
  map_add' f g := by
    apply Subtype.ext
    change divX (((f : reesAlgebra I) : A[X]) + ((g : reesAlgebra I) : A[X])) = _
    rw [divX_add]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    change divX ((c : A[X]) * ((f : reesAlgebra I) : A[X])) =
      (c : A[X]) * divX (((f : reesAlgebra I) : A[X]))
    exact divX_mul_of_coeff_zero _ (coeff_zero_eq_zero_of_mem_reesTruncation I t f.2)

/-- The underlying polynomial of `reesShift I t f` is `divX` of the underlying polynomial of
`f`. -/
@[simp]
theorem coe_reesShift (f : reesTruncation I t) :
    ((reesShift I t f : reesAlgebra I) : A[X]) = divX ((f : reesAlgebra I) : A[X]) := rfl

/-- **`divX` is degree-preserving**, from the grading of the truncation of `S(t+1)` into that of
`S(t)`: in a kept degree `i ≥ -t` the source piece is `S_{i+t+1}` with `i + t + 1 ≥ 1`, and
`divX` carries it into `S_{i+t}`; below the cut the source piece is zero. -/
theorem reesShift_mem_twistGrading (i : ℤ) (f : reesTruncation I t)
    (hf : f ∈ reesTruncationGrading I t i) :
    reesShift I t f ∈ twistGrading (S := reesAlgebra I) (reesGrading I) t i := by
  have hf₀ : f ∈ truncationAboveGrading (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t) i := hf
  rcases lt_or_ge i (-t) with hi | hi
  · have hbot := truncationAboveGrading_eq_bot (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t) hi
    rw [hbot, AddSubgroup.mem_bot] at hf₀
    rw [hf₀, map_zero]
    exact zero_mem _
  · have hf' : (f : reesAlgebra I) ∈ reesGrading I (i + (t + 1)).toNat :=
      (mem_twistGrading_iff I (by omega) _).mp
        ((mem_truncationAboveGrading_iff (reesGrading I)
          (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t) i f).mp hf₀)
    have hnat : (i + (t + 1)).toNat = (i + t).toNat + 1 := by omega
    refine (mem_twistGrading_iff I (by omega) _).mpr fun m hm => ?_
    rw [coe_reesShift, coeff_divX]
    exact hf' (m + 1) (by omega)

/-- **The inclusion of the truncation into `S(t+1)` induces an isomorphism of associated
sheaves.** It is bijective in every degree `≥ -t`: injective because it is an inclusion, and
surjective because a homogeneous element of a kept degree already lies in the truncation. -/
theorem isIso_reesTruncationComparison :
    IsIso (associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (reesTruncation I t).subtype
      (truncationAbove_subtype_mem (reesGrading I)
        (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t))) :=
  AlgebraicGeometry.ProjStalkGlobalSections.isIso_associatedModuleSheafMap_of_eventually_bijective
    (reesGrading I) (reesTruncationGrading I t)
    (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (reesTruncation I t).subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t))
    (N₀ := -t)
    (fun _ _ _ _ h => eq_zero_of_truncationAbove_subtype_eq_zero (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t) h)
    (fun _j hj _ hm => exists_mem_truncationAboveGrading (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t) hj hm)

/-- **The comparison `(S₊(t+1))~ ≅ 𝒪_X(t+1)`.** -/
def reesTruncationComparison :
    associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t) ≅
      twistingSheaf (reesGrading I) (t + 1) :=
  haveI := isIso_reesTruncationComparison I t
  asIso (associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
    (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (reesTruncation I t).subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t)))

/-- **The canonical map `𝒪_X(t+1) ⟶ 𝒪_X(t)`** on the blowup: the comparison
`(S₊(t+1))~ ≅ 𝒪_X(t+1)` inverted, followed by the map `divX` induces. No generator of the
centre is chosen anywhere. -/
def twistShiftMap : twistingSheaf (reesGrading I) (t + 1) ⟶ twistingSheaf (reesGrading I) t :=
  (reesTruncationComparison I t).inv ≫
    associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
      (twistGrading (S := reesAlgebra I) (reesGrading I) t) (reesShift I t)
      (reesShift_mem_twistGrading I t)

/-- The forward direction of the comparison isomorphism is the induced map itself. -/
theorem reesTruncationComparison_hom :
    (reesTruncationComparison I t).hom =
      associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
        (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (reesTruncation I t).subtype
        (truncationAbove_subtype_mem (reesGrading I)
          (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t)) := rfl

/-- The defining factorisation of `twistShiftMap`. The definition is `irreducible`, so that the
unifier does not unfold the whole comparison isomorphism when the map appears as an argument;
this lemma is the only way in. -/
theorem twistShiftMap_eq :
    twistShiftMap I t =
      (reesTruncationComparison I t).inv ≫
        associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
          (twistGrading (S := reesAlgebra I) (reesGrading I) t) (reesShift I t)
          (reesShift_mem_twistGrading I t) := rfl

attribute [irreducible] twistShiftMap

/-- Precomposing `twistShiftMap` with the comparison isomorphism leaves the map `divX`
induces. This is the form in which the two naturality statements meet, and it avoids ever
unfolding the inverse of the comparison. -/
theorem comparison_hom_comp_twistShiftMap :
    (reesTruncationComparison I t).hom ≫ twistShiftMap I t =
      associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
        (twistGrading (S := reesAlgebra I) (reesGrading I) t) (reesShift I t)
        (reesShift_mem_twistGrading I t) := by
  simp only [twistShiftMap_eq, Iso.hom_inv_id_assoc]

/-- Equal morphisms of sheaves of modules agree on sections. -/
private theorem val_app_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {F G : SheafOfModules R} {φ ψ : F ⟶ G} (h : φ = ψ) {U : Cᵒᵖ}
    (s : F.val.obj U) : φ.val.app U s = ψ.val.app U s :=
  congrArg (fun χ : F ⟶ G => χ.val.app U s) h

/-- **`twistShiftMap` on the canonical section of a degree-zero element of the truncation**: it
is the canonical section of the image of that element under `divX`. -/
theorem app_top_twistShiftMap_degreeZeroToGlobalSections (m : reesTruncationGrading I t 0) :
    (twistShiftMap I t).val.app (op ⊤)
        ((reesTruncationComparison I t).hom.val.app (op ⊤)
          (degreeZeroToGlobalSections (reesGrading I) (reesTruncationGrading I t) m)) =
      degreeZeroToGlobalSections (reesGrading I)
        (twistGrading (S := reesAlgebra I) (reesGrading I) t)
        ⟨reesShift I t m.1, reesShift_mem_twistGrading I t 0 m.1 m.2⟩ := by
  refine Eq.trans ?_ (degreeZeroToGlobalSections_naturality (reesGrading I)
    (reesTruncationGrading I t) (twistGrading (S := reesAlgebra I) (reesGrading I) t)
    (reesShift I t) (reesShift_mem_twistGrading I t) m)
  exact val_app_congr (comparison_hom_comp_twistShiftMap I t) _

/-! ### The left-hand square: the canonical sections of `Iᑫ` -/

/-- A homogeneous element of Rees degree `q+1` is a degree-zero element of the twist `S(q+1)`. -/
theorem mem_twistGrading_zero_reesGradingEquivPow (n : ℕ) (y : (I ^ n : Ideal A)) :
    (reesGradingEquivPow I n y : reesAlgebra I) ∈
      twistGrading (S := reesAlgebra I) (reesGrading I) (n : ℤ) 0 := by
  refine (mem_twistGrading_iff I (by omega) _).mpr ?_
  rw [show (0 + (n : ℤ)).toNat = n from by omega]
  exact (reesGradingEquivPow I n y).2

/-- A homogeneous element of Rees degree `q+1` is a degree-zero element of the **truncation** of
`S(q+1)`: degree `0` is above the cut `-q`. -/
def truncationSection (q : ℕ) (x : (I ^ (q + 1) : Ideal A)) :
    reesTruncationGrading I (q : ℤ) 0 :=
  ⟨⟨(reesGradingEquivPow I (q + 1) x : reesAlgebra I),
      mem_truncationAbove_of_mem (reesGrading I)
        (twistGrading (S := reesAlgebra I) (reesGrading I) ((q : ℤ) + 1)) (-(q : ℤ))
        (by omega) (mem_twistGrading_zero_reesGradingEquivPow I (q + 1) x)⟩,
    mem_twistGrading_zero_reesGradingEquivPow I (q + 1) x⟩

/-- `divX` sends the degree-zero element of the truncation attached to `x ∈ I^{q+1}` to the one
of `S(q)` attached to `x` read in `Iᑫ`. -/
theorem reesShift_truncationSection (q : ℕ) (x : (I ^ (q + 1) : Ideal A)) :
    reesShift I (q : ℤ) (truncationSection I q x) =
      (reesGradingEquivPow I q ⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) x.2⟩ :
        reesAlgebra I) := by
  apply Subtype.ext
  change divX (monomial (q + 1) (x : A)) = monomial q (x : A)
  exact divX_monomial_succ q (x : A)

end Stacks.Blowup

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The first map of the sequence `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`** used in the proof of
[Stacks, Tag 0GA7], as a morphism of sheaves of modules on the blowup `X`. It is
`Stacks.Blowup.twistShiftMap` at `t = q`, so it is canonical: no generator of `I` and no local
trivialisation enters its construction. -/
def ambientTwistMap (q : ℕ) : blowupTwist I (q + 1) ⟶ blowupTwist I q :=
  Stacks.Blowup.twistShiftMap I (q : ℤ)

/-- `ambientTwistMap` is `Stacks.Blowup.twistShiftMap` at `t = q`, which is where the
`irreducible` attribute sits: `ambientTwistMap` itself unfolds in one step to a map the unifier
will not look inside. -/
theorem ambientTwistMap_eq (q : ℕ) :
    ambientTwistMap I q = Stacks.Blowup.twistShiftMap I (q : ℤ) := rfl


/-- **The left-hand square of the diagram in the proof of [Stacks, Tag 0GA7], clause (2), for
the ambient sequence**, read on `⊤`-sections. The composite
`I^{q+1} → H⁰(X, 𝒪_X(q+1)) → H⁰(X, 𝒪_X(q))` is the canonical map of `Iᑫ` precomposed with the
inclusion `I^{q+1} ⊆ Iᑫ`.

This is a theorem and not an input: the canonical section of a homogeneous element is natural in
the graded module, and `divX` sends `monomial (q+1) x` to `monomial q x`. The inverse of the
comparison isomorphism never has to be computed — the section of `𝒪_X(q+1)` coming from
`x ∈ I^{q+1}` is exhibited as the *image* of a section of the truncation under the comparison,
and `Stacks.Blowup.comparison_hom_comp_twistShiftMap` cancels the two. -/
theorem app_top_ambientTwistMap_ambientSections (q : ℕ) (x : (I ^ (q + 1) : Ideal A)) :
    (ambientTwistMap I q).val.app (op ⊤) (ambientSections I (q + 1) x) =
      ambientSections I q ⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) x.2⟩ := by
  have hsec : ambientSections I (q + 1) x =
      (Stacks.Blowup.reesTruncationComparison I (q : ℤ)).hom.val.app (op ⊤)
        (degreeZeroToGlobalSections (Stacks.Blowup.reesGrading I)
          (Stacks.Blowup.reesTruncationGrading I (q : ℤ))
          (Stacks.Blowup.truncationSection I q x)) := by
    have h := degreeZeroToGlobalSections_naturality (Stacks.Blowup.reesGrading I)
      (Stacks.Blowup.reesTruncationGrading I (q : ℤ))
      (twistGrading (S := reesAlgebra I) (Stacks.Blowup.reesGrading I) ((q : ℤ) + 1))
      (Stacks.Blowup.reesTruncation I (q : ℤ)).subtype
      (truncationAbove_subtype_mem (Stacks.Blowup.reesGrading I)
        (twistGrading (S := reesAlgebra I) (Stacks.Blowup.reesGrading I) ((q : ℤ) + 1))
        (-(q : ℤ)))
      (Stacks.Blowup.truncationSection I q x)
    have h1 := Stacks.Blowup.val_app_congr
      (Stacks.Blowup.reesTruncationComparison_hom I (q : ℤ))
      (degreeZeroToGlobalSections (Stacks.Blowup.reesGrading I)
        (Stacks.Blowup.reesTruncationGrading I (q : ℤ)) (Stacks.Blowup.truncationSection I q x))
        (U := op ⊤)
    rw [h1, h]
    rfl
  have hstep := Stacks.Blowup.app_top_twistShiftMap_degreeZeroToGlobalSections I (q : ℤ)
    (Stacks.Blowup.truncationSection I q x)
  have helt : (⟨Stacks.Blowup.reesShift I (q : ℤ) (Stacks.Blowup.truncationSection I q x).1,
      Stacks.Blowup.reesShift_mem_twistGrading I (q : ℤ) 0
        (Stacks.Blowup.truncationSection I q x).1
        (Stacks.Blowup.truncationSection I q x).2⟩ :
      twistGrading (S := reesAlgebra I) (Stacks.Blowup.reesGrading I) (q : ℤ) 0) =
      ⟨(Stacks.Blowup.reesGradingEquivPow I q
            ⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) x.2⟩ : reesAlgebra I),
        Stacks.Blowup.mem_twistGrading_zero_reesGradingEquivPow I q
          ⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) x.2⟩⟩ :=
    Subtype.ext (Stacks.Blowup.reesShift_truncationSection I q x)
  rw [hsec]
  exact hstep.trans
    (congrArg (fun z => degreeZeroToGlobalSections (Stacks.Blowup.reesGrading I)
      (twistGrading (S := reesAlgebra I) (Stacks.Blowup.reesGrading I) (q : ℤ)) z) helt)

end Stacks.LocalCohomology.UniformityIII

end
