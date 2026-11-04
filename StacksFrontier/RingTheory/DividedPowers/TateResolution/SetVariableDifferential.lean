module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableDerivation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.FiniteStage

/-!
# Differentials on an extension by a set of divided power variables

Let `A` be a strictly graded-commutative nonnegatively graded algebra with a differential `dA`
and divided powers `γ` on its positive even part compatible with `dA`, and let `C` be the
algebra obtained from `A` by adjoining variables of positive degree — an exterior variable in
each odd degree, a divided-power variable in each even degree.  A family of cycles in `A`, the
one attached to a variable of degree `d` being of degree `d - 1`, then determines exactly one
differential on `C` which restricts to `dA` on the coefficients, sends each variable to its
cycle, and is again a divided-power differential graded algebra.

This is the statement of Tag 09PM for a whole set of variables at once; the single-variable case
is in `VariableDifferential.lean`, where the differential is written down by an explicit formula
in each of the two parities.  For a set of variables no such formula is available, and the file
carries two routes to the differential, under different hypotheses on the extension.

The first route handles variables of *arbitrary prescribed degrees* and obtains the differential
from the universal property of the extension: an algebra map `C → C⟨ε⟩` into the degree-one odd
extension of `C` whose first coordinate is the identity is precisely a degree-lowering
derivation of `C`, and compatibility of that map with the canonical divided powers of `C⟨ε⟩` is
precisely compatibility of the derivation with those of `C`.  The universal property supplies
such a map, because the corresponding map on coefficients is `a ↦ ι a + ε(ι (dA a)) T`, which is
multiplicative exactly by the Leibniz rule for `dA`.  This is
`existsUnique_differential_mixedDegreeSetVariableExtension`.

The second route handles the variables of a *single* degree `d`, with the extension packaged as
an `IsSetVariableExtension`, and needs no universal property.  There
`existsUnique_gradedDerivation_setVariableExtension` already extends a graded derivation across
the adjunction, with no cycle condition on the prescribed values — which is what the square-zero
lift of Tag 09PS needs, the lifted operator there not being square-zero — so all that remains is
to see that a family of *cycles* makes the extended derivation square-zero.  This is
`existsUnique_differential_setVariableExtension`, the form Tate's construction uses: its
inductive step adjoins variables of degree `n + 1` killing the cycles of degree `n`, and the
cycles of a degree are adjoined all at once.

## Main definitions

* `DividedPowers.TateResolution.signLinearMap` — the grading sign as an `R`-linear map.
* `DividedPowers.TateResolution.oddShiftFst` and
  `DividedPowers.TateResolution.oddShiftSnd` — the two coordinates of the degree-one odd
  extension, as an algebra map and an `R`-linear map.
* `DividedPowers.TateResolution.oddShiftAlgHom` — the algebra map `a ↦ ι a + ε(ι (dA a)) T`
  encoding a differential on the coefficients.

## Main results

* `DividedPowers.TateResolution.existsUnique_differential_mixedDegreeSetVariableExtension` — a
  family of cycles, the one indexed by `j` of degree `deg j - 1`, determines the unique
  divided-power-compatible differential on an extension by a set of variables whose degrees are
  prescribed by `deg`.
* `DividedPowers.TateResolution.existsUnique_differential_setVariableExtension` — a closed
  element of degree `d - 1` for each adjoined variable determines the unique
  divided-power-compatible differential on a set-variable divided power extension of degree `d`.
* `DividedPowers.TateResolution.comp_self_mul_of_mem_grade` — the square of a graded derivation
  of degree minus one is an *unsigned* derivation of degree minus two on homogeneous elements.
* `DividedPowers.TateResolution.IsSetVariableExtension.differential_sq_eq_zero` — the extension
  of a differential to a set-variable divided power extension, along a family of cycles, is
  square-zero.
* `DividedPowers.TateResolution.differential_mul_signRingHom` — the signed Leibniz rule in the
  sign-homomorphism form, valid on all of the algebra rather than only on homogeneous
  elements.
* `DividedPowers.TateResolution.differential_signRingHom` — a differential anticommutes with
  the grading sign.
* `DividedPowers.TateResolution.oddShiftFst_dpow` and
  `DividedPowers.TateResolution.oddShiftAlgHom_dpow` — the two coordinate maps and the shift
  algebra map preserve divided powers.

## Implementation notes

For the prescribed-degree route the extension is not reconstructed: it enters through exactly
the data and the properties that the set-indexed construction of Tag 0F4I produces — a grading-
and divided-power-preserving coefficient map, variables homogeneous of their prescribed degrees,
the presentation of each element inside a finite-variable stage, and the universal mapping
property — so the result composes directly with `exists_setVariableDividedPowerExtension` and
does not depend on how that algebra was built.

Three of the four differential axioms, together with divided-power compatibility, are read off
from the universal map directly, and in a sign-homomorphism form that holds on all of the
algebra: the Leibniz rule comes from multiplicativity, the grading conditions from
grading-preservation, and `d (γₙ x) = d x · γₙ₋₁ x` from preservation of divided powers.  Only
square-zeroness, and the uniqueness half, need the presentation by finite stages: a stage is a
subring generated by the coefficients, the variables and the divided powers of the variables,
so the elements killed by `d ∘ d` — respectively the elements where two candidate
differentials agree — form a subring containing those generators, and therefore everything.

For the single-degree route square-zeroness is not proved by induction on the finite variable
stages, as the derivation itself is.  The square of a graded derivation satisfies the *unsigned*
Leibniz rule — the two cross terms `± d x · d y` cancel — so the elements it kills form a
subring once homogeneous components are taken into account, and it is enough to check the
generators of a finite variable stage: the coefficients, the variables, and the divided powers
of the variables.  The set `{x | ∀ m, D (D (xₘ)) = 0}` quantified over homogeneous components,
rather than `{x | D (D x) = 0}`, is what makes that a subring: closure under multiplication
needs both factors decomposed into homogeneous pieces, and a vanishing square on an element does
not by itself give a vanishing square on its components.

On a divided power of a variable the computation closes after two steps rather than by
recursion: `D (γₙ T) = D T · γₙ₋₁ T` and `D T = ι (ev j)` is homogeneous of the odd degree
`d - 1` whenever `T` has a nonzero divided power at all, so the only surviving term carries the
square of an odd homogeneous element, which vanishes.

We use the homological, nonnegative grading convention.

## References

* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

/-- A linear map sending the `p d`-th piece into the `q d`-th piece sends `⨆ d, 𝒜 (p d)` into
`⨆ d, 𝒞 (q d)`. -/
private theorem map_mem_iSup_of_forall_mem {R : Type u} {A : Type v} {C : Type z} [CommRing R]
    [Ring A] [Ring C] [Algebra R A] [Algebra R C] (𝒜 : ℕ → Submodule R A)
    (𝒞 : ℕ → Submodule R C) (f : A →ₗ[R] C) (p q : ℕ → ℕ)
    (hf : ∀ (d : ℕ) (a : A), a ∈ 𝒜 (p d) → f a ∈ 𝒞 (q d)) {a : A}
    (ha : a ∈ ⨆ d, 𝒜 (p d)) : f a ∈ ⨆ d, 𝒞 (q d) :=
  (iSup_le fun d _ hx => Submodule.mem_iSup_of_mem d (hf d _ hx) :
    (⨆ d, 𝒜 (p d)) ≤ (⨆ d, 𝒞 (q d)).comap f) ha

section Sign

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The grading sign, as an `R`-linear map. -/
public noncomputable def signLinearMap (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (q : ℕ) :
    A →ₗ[R] A where
  toFun := signRingHom 𝒜 q
  map_add' := map_add _
  map_smul' r x := by
    change signRingHom 𝒜 q (r • x) = r • signRingHom 𝒜 q x
    rw [Algebra.smul_def, map_mul,
      signRingHom_of_mem 𝒜 q 0 (SetLike.algebraMap_mem_graded 𝒜 r)]
    simp [Algebra.smul_def]

/-- The grading sign as a linear map agrees with the grading sign. -/
@[simp]
public theorem signLinearMap_apply (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (q : ℕ) (x : A) :
    signLinearMap 𝒜 q x = signRingHom 𝒜 q x := rfl

/-- Applying the grading sign twice is the identity. -/
@[simp]
public theorem signRingHom_signRingHom (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (q : ℕ)
    (x : A) : signRingHom 𝒜 q (signRingHom 𝒜 q x) = x :=
  signRingHom_involutive 𝒜 q x

/-- The grading sign preserves every homogeneous piece. -/
public theorem signRingHom_mem (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (q m : ℕ) {x : A}
    (hx : x ∈ 𝒜 m) : signRingHom 𝒜 q x ∈ 𝒜 m := by
  rw [signRingHom_of_mem 𝒜 q m hx]
  exact (𝒜 m).smul_mem _ hx

/-- The grading sign fixes the even part. -/
public theorem signRingHom_one_of_mem_evenPart (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {x : A} (hx : x ∈ evenPart 𝒜) : signRingHom 𝒜 1 x = x := by
  induction hx using Submodule.iSup_induction' with
  | mem d x hx =>
      rw [signRingHom_of_mem 𝒜 1 (2 * d) hx, one_mul, pow_mul]
      simp
  | zero => simp
  | add x y _ _ ih ih' => rw [map_add, ih, ih']

/-- The differential sends the positive even part into the odd part. -/
public theorem differential_mem_oddPart (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA] {x : A}
    (hx : x ∈ positiveEvenPart 𝒜) : dA x ∈ oddPart 𝒜 := by
  refine map_mem_iSup_of_forall_mem 𝒜 𝒜 dA (fun d => 2 * (d + 1)) (fun d => 2 * d + 1)
    (fun d x hx => ?_) hx
  exact IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (show x ∈ 𝒜 (2 * d + 1 + 1) from hx)

/-- The grading sign preserves the odd part. -/
public theorem signRingHom_mem_oddPart (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (q : ℕ) {x : A} (hx : x ∈ oddPart 𝒜) : signRingHom 𝒜 q x ∈ oddPart 𝒜 :=
  map_mem_iSup_of_forall_mem 𝒜 𝒜 (signLinearMap 𝒜 q) _ _
    (fun _ _ hx => signRingHom_mem 𝒜 q _ hx) hx

/-- The signed Leibniz rule, in the sign-homomorphism form valid on all of `A`. -/
public theorem differential_mul_signRingHom (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA] (x y : A) :
    dA (x * y) = dA x * y + signRingHom 𝒜 1 x * dA y := by
  classical
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i x =>
      induction y using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | @homogeneous j y =>
          rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) x.2 y.2,
            signRingHom_of_mem 𝒜 1 i x.2, one_mul, smul_mul_assoc]
      | add y y' ih ih' =>
          simp only [mul_add, map_add, ih, ih']
          abel
  | add x x' ih ih' =>
      simp only [add_mul, map_add, ih, ih']
      abel

/-- The grading sign anticommutes with any degree-lowering map.  Only the two grading axioms
of a differential are used, so this is available before square-zeroness is known. -/
public theorem signRingHom_comm_of_lowersDegree (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (hzero : ∀ {x : A}, x ∈ 𝒜 0 → dA x = 0)
    (hmem : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 (n + 1) → dA x ∈ 𝒜 n) (x : A) :
    dA (signRingHom 𝒜 1 x) = - signRingHom 𝒜 1 (dA x) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i x =>
      cases i with
      | zero =>
          rw [signRingHom_of_mem 𝒜 1 0 x.2, map_smul, hzero x.2]
          simp
      | succ i =>
          rw [signRingHom_of_mem 𝒜 1 (i + 1) x.2, map_smul,
            signRingHom_of_mem 𝒜 1 i (hmem x.2)]
          simp only [one_mul, pow_succ]
          module
  | add x x' ih ih' =>
      simp only [map_add, ih, ih']
      abel

/-- The grading sign anticommutes with the differential. -/
public theorem differential_signRingHom (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA] (x : A) :
    dA (signRingHom 𝒜 1 x) = - signRingHom 𝒜 1 (dA x) :=
  signRingHom_comm_of_lowersDegree 𝒜 dA IsDifferentialGradedAlgebra.d_grade_zero
    IsDifferentialGradedAlgebra.d_mem x

end Sign

section Shift

attribute [local implicit_reducible] TwistedModule

variable {R : Type u} {A : Type v} {C : Type z}
variable [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]

/-- A grading-preserving algebra map commutes with the grading sign. -/
public theorem algHom_signRingHom (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (𝒞 : ℕ → Submodule R C) [GradedAlgebra 𝒞] (ι : A →ₐ[R] C)
    (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m) (q : ℕ) (a : A) :
    ι (signRingHom 𝒜 q a) = signRingHom 𝒞 q (ι a) := by
  classical
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous m a =>
      rw [signRingHom_of_mem 𝒜 q m a.2, signRingHom_of_mem 𝒞 q m (hι m _ a.2), map_smul]
  | add a a' ih ih' => simp only [map_add, ih, ih']

/-- An algebra map preserving the grading maps the odd part into the odd part. -/
public theorem algHom_mem_oddPart (𝒜 : ℕ → Submodule R A) (𝒞 : ℕ → Submodule R C)
    (ι : A →ₐ[R] C) (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m) {a : A}
    (ha : a ∈ oddPart 𝒜) : ι a ∈ oddPart 𝒞 :=
  map_mem_iSup_of_forall_mem 𝒜 𝒞 ι.toLinearMap _ _ (fun _ a ha => hι _ a ha) ha

/-- An algebra map preserving the grading maps the even part into the even part. -/
public theorem algHom_mem_evenPart (𝒜 : ℕ → Submodule R A) (𝒞 : ℕ → Submodule R C)
    (ι : A →ₐ[R] C) (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m) {a : A}
    (ha : a ∈ evenPart 𝒜) : ι a ∈ evenPart 𝒞 :=
  map_mem_iSup_of_forall_mem 𝒜 𝒞 ι.toLinearMap _ _ (fun _ a ha => hι _ a ha) ha

/-- A coefficient times the adjoined variable is the second summand of the extension. -/
public theorem inl_mul_generator (𝒞 : ℕ → Submodule R C) [GradedAlgebra 𝒞] (q : ℕ) (c : C) :
    TrivSqZeroExt.inl c * OddVariableExtension.generator 𝒞 q =
      TrivSqZeroExt.inr (show TwistedModule 𝒞 q from c) := by
  rw [OddVariableExtension.generator, TrivSqZeroExt.inl_mul_inr]
  congr 1
  show c * (1 : C) = c
  rw [mul_one]

/-- The inclusion of the coefficient algebra is the first summand. -/
public theorem inclusion_eq_inl (𝒞 : ℕ → Submodule R C) [GradedAlgebra 𝒞] (q : ℕ) (c : C) :
    OddVariableExtension.inclusion 𝒞 q c = TrivSqZeroExt.inl c := rfl

variable (𝒞 : ℕ → Submodule R C) [GradedAlgebra 𝒞]

/-- The first-coordinate projection of the degree-one odd extension, as an algebra map. -/
public def oddShiftFst : OddVariableExtension 𝒞 1 →ₐ[R] C where
  toFun := TrivSqZeroExt.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' := TrivSqZeroExt.fst_mul
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' := TrivSqZeroExt.fst_add
  commutes' _ := rfl

/-- The second-coordinate projection of the degree-one odd extension, as an `R`-linear map.
Composed with an algebra map into the extension whose first coordinate is the identity, it is
the differential that the map encodes. -/
public def oddShiftSnd : OddVariableExtension 𝒞 1 →ₗ[R] C where
  toFun w := w.snd
  map_add' w w' := TrivSqZeroExt.snd_add w w'
  map_smul' r w := TrivSqZeroExt.snd_smul r w

/-- The first coordinate of `inl c + inr c'` is `c`. -/
@[simp]
public theorem oddShiftFst_inl_add_inr (c c' : C) :
    oddShiftFst 𝒞 (TrivSqZeroExt.inl c +
      TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from c')) = c := by
  show c + (0 : C) = c
  rw [add_zero]

/-- The second coordinate of `inl c + inr c'` is `c'`. -/
@[simp]
public theorem oddShiftSnd_inl_add_inr (c c' : C) :
    oddShiftSnd 𝒞 (TrivSqZeroExt.inl c +
      TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from c')) = c' := by
  show (0 : C) + c' = c'
  rw [zero_add]

/-- The first coordinate of a product is the product of the first coordinates. -/
@[simp]
public theorem oddShiftFst_mul (w w' : OddVariableExtension 𝒞 1) :
    oddShiftFst 𝒞 (w * w') = oddShiftFst 𝒞 w * oddShiftFst 𝒞 w' := rfl

/-- The second coordinate of `w * w'` is `w₁ w'₂ + w₂ ε(w'₁)`, where `ε` is the grading sign. -/
@[simp]
public theorem oddShiftSnd_mul (w w' : OddVariableExtension 𝒞 1) :
    oddShiftSnd 𝒞 (w * w') =
      oddShiftFst 𝒞 w * oddShiftSnd 𝒞 w' +
        oddShiftSnd 𝒞 w * signRingHom 𝒞 1 (oddShiftFst 𝒞 w') := rfl

/-- An element of the extension is recovered from its two coordinates. -/
public theorem inl_fst_add_inr_snd (w : OddVariableExtension 𝒞 1) :
    TrivSqZeroExt.inl (oddShiftFst 𝒞 w) +
      TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from oddShiftSnd 𝒞 w) = w :=
  TrivSqZeroExt.inl_fst_add_inr_snd_eq w

/-- The first coordinate of a homogeneous element has the same degree. -/
public theorem oddShiftFst_mem (m : ℕ) (w : OddVariableExtension 𝒞 1)
    (hw : w ∈ OddVariableExtension.grade 𝒞 1 m) : oddShiftFst 𝒞 w ∈ 𝒞 m :=
  ((OddVariableExtension.mem_grade_iff 𝒞 1 m w).1 hw).1

/-- The second coordinate of a homogeneous element of positive degree has degree one less. -/
public theorem oddShiftSnd_mem (m : ℕ) (hm : 1 ≤ m) (w : OddVariableExtension 𝒞 1)
    (hw : w ∈ OddVariableExtension.grade 𝒞 1 m) : oddShiftSnd 𝒞 w ∈ 𝒞 (m - 1) := by
  have h := ((OddVariableExtension.mem_grade_iff 𝒞 1 m w).1 hw).2
  simp only [hm, reduceIte] at h
  exact h

/-- The second coordinate of a homogeneous element of degree zero vanishes. -/
public theorem oddShiftSnd_eq_zero (w : OddVariableExtension 𝒞 1)
    (hw : w ∈ OddVariableExtension.grade 𝒞 1 0) : oddShiftSnd 𝒞 w = 0 := by
  have h := ((OddVariableExtension.mem_grade_iff 𝒞 1 0 w).1 hw).2
  have hnot : ¬ (1 : ℕ) ≤ 0 := by omega
  simp only [hnot, reduceIte, Submodule.mem_bot] at h
  exact h

variable [IsStrictlyGradedComm 𝒞]

omit [IsStrictlyGradedComm 𝒞] in
/-- The positive even part of the degree-one odd extension has positive even first coordinate
and odd second coordinate. -/
public theorem oddShift_mem_positiveEvenPart {w : OddVariableExtension 𝒞 1}
    (hw : w ∈ positiveEvenPart (OddVariableExtension.grade 𝒞 1)) :
    oddShiftFst 𝒞 w ∈ positiveEvenPart 𝒞 ∧ oddShiftSnd 𝒞 w ∈ oddPart 𝒞 := by
  induction hw using Submodule.iSup_induction' with
  | mem k w hw =>
      refine ⟨Submodule.mem_iSup_of_mem k (oddShiftFst_mem 𝒞 _ w hw),
        Submodule.mem_iSup_of_mem k ?_⟩
      have h := oddShiftSnd_mem 𝒞 (2 * (k + 1)) (by omega) w hw
      have hidx : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rwa [hidx] at h
  | zero => exact ⟨by simp, by simp⟩
  | add w w' _ _ ih ih' =>
      exact ⟨by rw [map_add]; exact Submodule.add_mem _ ih.1 ih'.1,
        by rw [map_add]; exact Submodule.add_mem _ ih.2 ih'.2⟩

/-- The first-coordinate projection preserves divided powers. -/
public theorem oddShiftFst_dpow (δ : DividedPowerStructure 𝒞) (n : ℕ)
    (w : OddVariableExtension 𝒞 1)
    (hw : w ∈ positiveEvenPart (OddVariableExtension.grade 𝒞 1)) :
    δ.dpow n (oddShiftFst 𝒞 w) =
      oddShiftFst 𝒞 ((oddVariableDividedPowerStructure 𝒞 δ 1 one_pos odd_one).dpow n w) := by
  obtain ⟨hfst, hsnd⟩ := oddShift_mem_positiveEvenPart 𝒞 hw
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [δ.dpow_zero hfst,
      (oddVariableDividedPowerStructure 𝒞 δ 1 one_pos odd_one).dpow_zero hw]
    simp
  · have hform := oddVariableDividedPowerStructure_dpow 𝒞 δ 1 one_pos odd_one n
      (by omega) (oddShiftFst 𝒞 w) (oddShiftSnd 𝒞 w) hfst hsnd
    simp only [inclusion_eq_inl, inl_mul_generator] at hform
    rw [← inl_fst_add_inr_snd 𝒞 w, hform]
    simp

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

variable (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]

/-- The algebra map `a ↦ ι a + ε(ι (dA a)) T` from a differential graded algebra into the
degree-one odd extension of a graded algebra receiving it. -/
public noncomputable def oddShiftAlgHom (ι : A →ₐ[R] C)
    (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m) :
    A →ₐ[R] OddVariableExtension 𝒞 1 where
  toFun a := TrivSqZeroExt.inl (ι a) +
    TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from signRingHom 𝒞 1 (ι (dA a)))
  map_one' := by
    have hz : dA (1 : A) = 0 :=
      IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (SetLike.one_mem_graded 𝒜)
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [hz]
      rfl
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · have hleib : dA (a * b) = dA a * b + signRingHom 𝒜 1 a * dA b :=
        differential_mul_signRingHom 𝒜 dA a b
      have hsign : ι (signRingHom 𝒜 1 a) = signRingHom 𝒞 1 (ι a) :=
        algHom_signRingHom 𝒜 𝒞 ι hι 1 a
      have hequiv : ∀ c : C, signRingEquiv 𝒞 1 c = signRingHom 𝒞 1 c := fun _ => rfl
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, zero_add,
        add_zero, TrivSqZeroExt.snd_mul, TwistedModule.op_smul, TwistedModule.smul_eq_mul,
        hleib, map_add, map_mul, hsign, hequiv, signRingHom_signRingHom]
      rw [add_comm]
      rfl
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
      rfl
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [add_add_add_comm]
      rfl
  commutes' r := by
    have hz : dA (algebraMap R A r) = 0 :=
      IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (SetLike.algebraMap_mem_graded 𝒜 r)
    have hr : (algebraMap R (OddVariableExtension 𝒞 1) r) =
        TrivSqZeroExt.inl (algebraMap R C r) := rfl
    rw [hr]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [hz]
      rfl

omit [IsStrictlyGradedComm 𝒞] [IsStrictlyGradedComm 𝒜] in
/-- The shift algebra map sends `a` to `ι a + ε(ι (dA a)) T`. -/
@[simp]
public theorem oddShiftAlgHom_apply (ι : A →ₐ[R] C)
    (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m) (a : A) :
    oddShiftAlgHom 𝒞 𝒜 dA ι hι a =
      TrivSqZeroExt.inl (ι a) +
        TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from signRingHom 𝒞 1 (ι (dA a))) := rfl

omit [IsStrictlyGradedComm 𝒞] [IsStrictlyGradedComm 𝒜] in
/-- The first coordinate of the shift algebra map is `ι`. -/
@[simp]
public theorem oddShiftFst_oddShiftAlgHom (ι : A →ₐ[R] C)
    (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m) (a : A) :
    oddShiftFst 𝒞 (oddShiftAlgHom 𝒞 𝒜 dA ι hι a) = ι a := by
  rw [oddShiftAlgHom_apply, oddShiftFst_inl_add_inr]

omit [IsStrictlyGradedComm 𝒞] [IsStrictlyGradedComm 𝒜] in
/-- The second coordinate of the shift algebra map is `a ↦ ε(ι (dA a))`. -/
@[simp]
public theorem oddShiftSnd_oddShiftAlgHom (ι : A →ₐ[R] C)
    (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m) (a : A) :
    oddShiftSnd 𝒞 (oddShiftAlgHom 𝒞 𝒜 dA ι hι a) = signRingHom 𝒞 1 (ι (dA a)) := by
  rw [oddShiftAlgHom_apply, oddShiftSnd_inl_add_inr]

omit [IsStrictlyGradedComm 𝒞] [IsStrictlyGradedComm 𝒜] in
/-- The shift algebra map preserves the grading. -/
public theorem oddShiftAlgHom_mem (ι : A →ₐ[R] C)
    (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m) (m : ℕ) (a : A) (ha : a ∈ 𝒜 m) :
    oddShiftAlgHom 𝒞 𝒜 dA ι hι a ∈ OddVariableExtension.grade 𝒞 1 m := by
  refine (OddVariableExtension.mem_grade_iff 𝒞 1 m _).2 ⟨?_, ?_⟩
  · simpa using hι m a ha
  · cases m with
    | zero =>
        have hz : dA a = 0 := IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) ha
        show (show C from (TrivSqZeroExt.inl (ι a) +
          TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from
            signRingHom 𝒞 1 (ι (dA a)))).snd) ∈ _
        simp [hz]
    | succ k =>
        show (show C from (TrivSqZeroExt.inl (ι a) +
          TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from
            signRingHom 𝒞 1 (ι (dA a)))).snd) ∈ _
        have hmem : signRingHom 𝒞 1 (ι (dA a)) ∈ 𝒞 k :=
          signRingHom_mem 𝒞 1 k (hι k _ (IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) ha))
        simpa using hmem

/-- The shift algebra map preserves divided powers. -/
public theorem oddShiftAlgHom_dpow (γ : DividedPowerStructure 𝒜)
    [IsCompatibleWithDifferential γ dA] (δ : DividedPowerStructure 𝒞) (ι : A →ₐ[R] C)
    (hι : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m)
    (hιdp : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 → δ.dpow n (ι a) = ι (γ.dpow n a))
    (n : ℕ) (a : A) (ha : a ∈ positiveEvenPart 𝒜) :
    (oddVariableDividedPowerStructure 𝒞 δ 1 one_pos odd_one).dpow n
        (oddShiftAlgHom 𝒞 𝒜 dA ι hι a) = oddShiftAlgHom 𝒞 𝒜 dA ι hι (γ.dpow n a) := by
  have hfa : oddShiftAlgHom 𝒞 𝒜 dA ι hι a ∈
      positiveEvenPart (OddVariableExtension.grade 𝒞 1) :=
    algHom_mem_positiveEvenPart 𝒜 (OddVariableExtension.grade 𝒞 1)
      (oddShiftAlgHom 𝒞 𝒜 dA ι hι) (oddShiftAlgHom_mem 𝒞 𝒜 dA ι hι) ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(oddVariableDividedPowerStructure 𝒞 δ 1 one_pos odd_one).dpow_zero hfa,
      γ.dpow_zero ha, map_one]
  · have hx : ι a ∈ positiveEvenPart 𝒞 := algHom_mem_positiveEvenPart 𝒜 𝒞 ι hι ha
    have hy : signRingHom 𝒞 1 (ι (dA a)) ∈ oddPart 𝒞 :=
      signRingHom_mem_oddPart 𝒞 1
        (algHom_mem_oddPart 𝒜 𝒞 ι hι (differential_mem_oddPart 𝒜 dA ha))
    have hform := oddVariableDividedPowerStructure_dpow 𝒞 δ 1 one_pos odd_one n
      (by omega) (ι a) (signRingHom 𝒞 1 (ι (dA a))) hx hy
    simp only [inclusion_eq_inl, inl_mul_generator] at hform
    rw [oddShiftAlgHom_apply, hform, oddShiftAlgHom_apply]
    have hcomp : dA (γ.dpow n a) = dA a * γ.dpow (n - 1) a :=
      IsCompatibleWithDifferential.d_dpow (by omega) ha
    have heven : ι (γ.dpow (n - 1) a) ∈ evenPart 𝒞 :=
      algHom_mem_evenPart 𝒜 𝒞 ι hι (dpow_mem_evenPart 𝒜 γ (n - 1) ha)
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      exact hιdp n a ha
    · show (show C from _) = (show C from _)
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add]
      rw [hιdp (n - 1) a ha, hcomp, map_mul, map_mul,
        signRingHom_one_of_mem_evenPart 𝒞 heven]
      exact DividedPowers.TateResolution.evenPart_mul_comm 𝒞 heven _

end Shift

section Square

variable {R : Type u} {C : Type v} [CommRing R] [Ring C] [Algebra R C]
  (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] (D : C →ₗ[R] C) [IsGradedDerivation Cᵢ D]

/-- **The square of a graded derivation is an unsigned derivation.** For homogeneous `x` and `y`
the two cross terms of the twice-applied Leibniz rule carry the signs `(-1) ^ (i - 1)` and
`(-1) ^ i`, which cancel, so no sign survives. This is what makes the elements killed by
`D ∘ D` closed under multiplication. -/
public theorem comp_self_mul_of_mem_grade {i k : ℕ} {x y : C}
    (hx : x ∈ Cᵢ i) (hy : y ∈ Cᵢ k) :
    D (D (x * y)) = D (D x) * y + x * D (D y) := by
  have hsign : ∀ m : ℕ, (-1 : R) ^ (m + 1) = -(-1 : R) ^ m := fun m => by
    rw [pow_succ, mul_neg_one]
  have hsq : ∀ m : ℕ, (-1 : R) ^ m * (-1 : R) ^ m = 1 := fun m => by
    rw [← mul_pow]; simp
  match i, k with
  | 0, 0 =>
      have hDx : D x = 0 := IsGradedDerivation.d_grade_zero (𝒜 := Cᵢ) (d := D) hx
      have hDy : D y = 0 := IsGradedDerivation.d_grade_zero (𝒜 := Cᵢ) (d := D) hy
      rw [IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hx hy, hDx, hDy]
      simp
  | 0, k + 1 =>
      have hDx : D x = 0 := IsGradedDerivation.d_grade_zero (𝒜 := Cᵢ) (d := D) hx
      have hDy : D y ∈ Cᵢ k := IsGradedDerivation.d_mem (𝒜 := Cᵢ) (d := D) hy
      rw [IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hx hy, hDx, zero_mul, zero_add,
        pow_zero, one_smul, IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hx hDy, hDx,
        zero_mul, zero_add, pow_zero, one_smul]
      simp
  | i + 1, 0 =>
      have hDx : D x ∈ Cᵢ i := IsGradedDerivation.d_mem (𝒜 := Cᵢ) (d := D) hx
      have hDy : D y = 0 := IsGradedDerivation.d_grade_zero (𝒜 := Cᵢ) (d := D) hy
      rw [IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hx hy, hDy, mul_zero, smul_zero,
        add_zero, IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hDx hy, hDy, mul_zero,
        smul_zero, add_zero]
      simp
  | i + 1, k + 1 =>
      have hDx : D x ∈ Cᵢ i := IsGradedDerivation.d_mem (𝒜 := Cᵢ) (d := D) hx
      have hDy : D y ∈ Cᵢ k := IsGradedDerivation.d_mem (𝒜 := Cᵢ) (d := D) hy
      rw [IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hx hy, map_add, map_smul,
        IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hDx hy,
        IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hx hDy, smul_add, smul_smul, hsq,
        one_smul, hsign i, neg_smul, add_assoc, add_neg_cancel_left]

/-- A graded derivation compatible with the divided powers squares to zero on every divided power
of `t` once `D t = ε` is a cycle: the only surviving term carries the square of the odd
homogeneous element `ε`. -/
private theorem comp_self_dpow_eq_zero [IsStrictlyGradedComm Cᵢ] (δ : DividedPowerStructure Cᵢ)
    [IsCompatibleWithDifferential δ D] {m : ℕ} {t ε : C} (ht : t ∈ Cᵢ m) (hε : ε ∈ Cᵢ (m - 1))
    (hDt : D t = ε) (hDε : D ε = 0) (n : ℕ) : D (D (δ.dpow n t)) = 0 := by
  have hone : D (1 : C) = 0 :=
    IsGradedDerivation.d_grade_zero (𝒜 := Cᵢ) (d := D) (SetLike.one_mem_graded Cᵢ)
  by_cases hpos : t ∈ positiveEvenPart Cᵢ
  · rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ ht hpos with hz | ⟨e, he⟩
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [δ.dpow_zero hpos, hone, map_zero]
      · rw [hz, δ.dpow_zero_eq_zero (by omega : n ≠ 0), map_zero, map_zero]
    · have hevC : ε ∈ Cᵢ (2 * e + 1) := by
        rwa [he, show 2 * (e + 1) - 1 = 2 * e + 1 by omega] at hε
      have hevsq : ε * ε = 0 := by
        have h := IsStrictlyGradedComm.odd_sq_zero (𝒜 := Cᵢ) (d := e) hevC
        rwa [pow_two] at h
      -- Every divided power of the variable is homogeneous.
      have hhom : ∀ k : ℕ, ∃ p : ℕ, δ.dpow k t ∈ Cᵢ p := by
        intro k
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          exact ⟨0, by rw [δ.dpow_zero hpos]; exact SetLike.one_mem_graded Cᵢ⟩
        · exact ⟨2 * k * (e + 1), δ.dpow_mem_grade (by omega : k ≠ 0) hpos (he ▸ ht)⟩
      -- The divided power formula, available for every positive index.
      have hform : ∀ k : ℕ, k ≠ 0 → D (δ.dpow k t) = ε * δ.dpow (k - 1) t := by
        intro k hk
        rw [IsCompatibleWithDifferential.d_dpow (γ := δ) (d := D) hk hpos, hDt]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [δ.dpow_zero hpos, hone, map_zero]
      · obtain ⟨p, hp⟩ := hhom (n - 1)
        rw [hform n (by omega), IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D) hevC hp, hDε,
          zero_mul, zero_add]
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · have hn1 : n - 1 = 0 := by omega
          rw [hn1, δ.dpow_zero hpos, hone, mul_zero, smul_zero]
        · rw [hform (n - 1) (by omega), ← mul_assoc, hevsq, zero_mul, smul_zero]
  · rw [δ.dpow_null hpos, map_zero, map_zero]

end Square

section MixedDegree

attribute [local implicit_reducible] TwistedModule

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
variable [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]

/-- A cycle of degree `deg j - 1` for each adjoined variable `j` determines the unique
divided-power-compatible differential on an extension by a set of variables of degrees `deg`.

The extension enters through the data and the properties that the set-indexed construction of
Tag 0F4I produces: a grading- and divided-power-preserving coefficient map `ι`, variables `T`
with `T j` homogeneous of degree `deg j`, the presentation of every element inside a
finite-variable stage, and the universal mapping property.  This is Tag 09PM for a whole set of
variables of arbitrary prescribed degrees at once, which is what an algebra with variables in
every positive degree needs; its single-variable forms are
`existsUnique_differential_oddVariableExtension` and
`existsUnique_differential_evenVariableAlgebra`, and its form for the variables of a single
degree, which needs no universal property, is
`existsUnique_differential_setVariableExtension`. -/
@[stacks 09PM "set of variables of prescribed degrees"]
public theorem existsUnique_differential_mixedDegreeSetVariableExtension
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsCompatibleWithDifferential γ dA]
    (𝒞 : ℕ → Submodule R C) [GradedAlgebra 𝒞] [IsStrictlyGradedComm 𝒞]
    (δ : DividedPowerStructure 𝒞) (ι : A →ₐ[R] C) (T : J → C) (deg : J → ℕ)
    (hdeg : ∀ j : J, 0 < deg j)
    (hι_grade : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ι a ∈ 𝒞 m)
    (hι_dpow : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 → δ.dpow n (ι a) = ι (γ.dpow n a))
    (hT : ∀ j : J, T j ∈ 𝒞 (deg j))
    (hgen : ∀ x : C, ∃ S : Finset J, x ∈ finiteVariableStage δ ι T S)
    (huniv : ∀ {D : Type z} [Ring D] [Algebra R D]
        (𝒟 : ℕ → Submodule R D) [GradedAlgebra 𝒟] [IsStrictlyGradedComm 𝒟]
        (ε : DividedPowerStructure 𝒟) (f : A →ₐ[R] D) (t : J → D),
        (∀ (m : ℕ) (a : A), a ∈ 𝒜 m → f a ∈ 𝒟 m) →
        (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 → ε.dpow n (f a) = f (γ.dpow n a)) →
        (∀ j : J, t j ∈ 𝒟 (deg j)) →
        ∃! g : C →ₐ[R] D,
          (∀ a : A, g (ι a) = f a) ∧ (∀ j : J, g (T j) = t j) ∧
            (∀ (m : ℕ) (x : C), x ∈ 𝒞 m → g x ∈ 𝒟 m) ∧
            (∀ (n : ℕ) (x : C), x ∈ positiveEvenPart 𝒞 → ε.dpow n (g x) = g (δ.dpow n x)))
    (e : J → A) (he_grade : ∀ j : J, e j ∈ 𝒜 (deg j - 1))
    (he_cycle : ∀ j : J, dA (e j) = 0) :
    ∃! dC : C →ₗ[R] C,
      IsDifferentialGradedAlgebra 𝒞 dC ∧ (∀ a : A, dC (ι a) = ι (dA a)) ∧
        (∀ j : J, dC (T j) = ι (e j)) ∧ IsCompatibleWithDifferential δ dC := by
  classical
  -- A subring containing the coefficients, the variables and their divided powers is everything.
  have hclosure : ∀ E : Subring C, (∀ a : A, ι a ∈ E) → (∀ j : J, T j ∈ E) →
      (∀ (n : ℕ) (j : J), δ.dpow n (T j) ∈ E) → ∀ x : C, x ∈ E := by
    intro E hιE hTE hdpE x
    obtain ⟨S, hS⟩ := hgen x
    refine (Subring.closure_le (t := E)).2 ?_ hS
    rintro y (⟨a, rfl⟩ | ⟨j, -, rfl | ⟨n, rfl⟩⟩)
    · exact hιE a
    · exact hTE j
    · exact hdpE n j
  have hd1 : ∀ j : J, 1 ≤ deg j := hdeg
  -- Algebra maps into the degree-one odd extension of `C` whose first coordinate is the
  -- identity are exactly the divided-power-compatible differentials; apply the universal
  -- property to that extension.
  have ht_grade : ∀ j : J,
      TrivSqZeroExt.inl (T j) +
        TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from signRingHom 𝒞 1 (ι (e j))) ∈
        OddVariableExtension.grade 𝒞 1 (deg j) := by
    intro j
    refine (OddVariableExtension.mem_grade_iff 𝒞 1 (deg j) _).2 ⟨?_, ?_⟩
    · simpa using hT j
    · have hmem : signRingHom 𝒞 1 (ι (e j)) ∈ 𝒞 (deg j - 1) :=
        signRingHom_mem 𝒞 1 (deg j - 1) (hι_grade (deg j - 1) _ (he_grade j))
      show (show C from (TrivSqZeroExt.inl (T j) +
        TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from
          signRingHom 𝒞 1 (ι (e j)))).snd) ∈ _
      simpa [hd1 j] using hmem
  obtain ⟨g, hg, -⟩ := huniv (OddVariableExtension.grade 𝒞 1)
    (oddVariableDividedPowerStructure 𝒞 δ 1 one_pos odd_one)
    (oddShiftAlgHom 𝒞 𝒜 dA ι hι_grade)
    (fun j => TrivSqZeroExt.inl (T j) +
      TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from signRingHom 𝒞 1 (ι (e j))))
    (oddShiftAlgHom_mem 𝒞 𝒜 dA ι hι_grade)
    (oddShiftAlgHom_dpow 𝒞 𝒜 dA γ δ ι hι_grade hι_dpow) ht_grade
  -- The first coordinate of `g` is the identity.
  have hfst : ∀ x : C, oddShiftFst 𝒞 (g x) = x := by
    obtain ⟨g₀, -, hg₀u⟩ := huniv 𝒞 δ ι T hι_grade hι_dpow hT
    have hcomp : (oddShiftFst 𝒞).comp g = g₀ := by
      refine hg₀u _ ⟨fun a => ?_, fun j => ?_, fun m x hx => ?_, fun n x hx => ?_⟩
      · simp only [AlgHom.comp_apply, hg.1 a, oddShiftFst_oddShiftAlgHom]
      · simp only [AlgHom.comp_apply, hg.2.1 j, oddShiftFst_inl_add_inr]
      · exact oddShiftFst_mem 𝒞 m _ (hg.2.2.1 m x hx)
      · have hgx : g x ∈ positiveEvenPart (OddVariableExtension.grade 𝒞 1) :=
          algHom_mem_positiveEvenPart 𝒞 (OddVariableExtension.grade 𝒞 1) g hg.2.2.1 hx
        simp only [AlgHom.comp_apply]
        rw [oddShiftFst_dpow 𝒞 δ n (g x) hgx, hg.2.2.2 n x hx]
    have hid : (AlgHom.id R C) = g₀ :=
      hg₀u _ ⟨fun _ => rfl, fun _ => rfl, fun _ _ hx => hx, fun _ _ _ => rfl⟩
    intro x
    have hx := congrArg (fun h : C →ₐ[R] C => h x) (hcomp.trans hid.symm)
    simpa using hx
  -- The differential, read off from the second coordinate.
  let dC : C →ₗ[R] C := (signLinearMap 𝒞 1).comp ((oddShiftSnd 𝒞).comp g.toLinearMap)
  have hdC : ∀ x : C, dC x = signRingHom 𝒞 1 (oddShiftSnd 𝒞 (g x)) := fun _ => rfl
  have hsnd : ∀ x : C, oddShiftSnd 𝒞 (g x) = signRingHom 𝒞 1 (dC x) := by
    intro x; rw [hdC, signRingHom_signRingHom]
  have hgeq : ∀ x : C, g x =
      TrivSqZeroExt.inl x +
        TrivSqZeroExt.inr (show TwistedModule 𝒞 1 from signRingHom 𝒞 1 (dC x)) := by
    intro x
    rw [← inl_fst_add_inr_snd 𝒞 (g x), hfst x, hsnd x]
  have hdC_ι : ∀ a : A, dC (ι a) = ι (dA a) := by
    intro a
    rw [hdC, hg.1 a, oddShiftSnd_oddShiftAlgHom, signRingHom_signRingHom]
  have hdC_T : ∀ j : J, dC (T j) = ι (e j) := by
    intro j
    rw [hdC, hg.2.1 j, oddShiftSnd_inl_add_inr, signRingHom_signRingHom]
  -- The two grading axioms.
  have hzero : ∀ {x : C}, x ∈ 𝒞 0 → dC x = 0 := by
    intro x hx
    rw [hdC, oddShiftSnd_eq_zero 𝒞 (g x) (hg.2.2.1 0 x hx), map_zero]
  have hmem : ∀ {n : ℕ} {x : C}, x ∈ 𝒞 (n + 1) → dC x ∈ 𝒞 n := by
    intro n x hx
    have h := oddShiftSnd_mem 𝒞 (n + 1) (by omega) (g x) (hg.2.2.1 (n + 1) x hx)
    rw [Nat.add_sub_cancel] at h
    rw [hdC]
    exact signRingHom_mem 𝒞 1 n h
  -- The sign-form Leibniz rule, valid on all of `C`.
  have hleib : ∀ x y : C, dC (x * y) = dC x * y + signRingHom 𝒞 1 x * dC y := by
    intro x y
    have h : oddShiftSnd 𝒞 (g (x * y)) =
        oddShiftFst 𝒞 (g x) * oddShiftSnd 𝒞 (g y) +
          oddShiftSnd 𝒞 (g x) * signRingHom 𝒞 1 (oddShiftFst 𝒞 (g y)) := by
      rw [map_mul g, oddShiftSnd_mul]
    rw [hsnd (x * y), hsnd x, hsnd y, hfst x, hfst y] at h
    have h' := congrArg (signRingHom 𝒞 1) h
    simp only [map_add, map_mul, signRingHom_signRingHom] at h'
    rw [h', add_comm]
  -- Compatibility with the divided powers.
  have hcompat : ∀ {n : ℕ} {x : C}, n ≠ 0 → x ∈ positiveEvenPart 𝒞 →
      dC (δ.dpow n x) = dC x * δ.dpow (n - 1) x := by
    intro n x hn hx
    have hgx : g x ∈ positiveEvenPart (OddVariableExtension.grade 𝒞 1) :=
      algHom_mem_positiveEvenPart 𝒞 (OddVariableExtension.grade 𝒞 1) g hg.2.2.1 hx
    obtain ⟨-, hsndodd⟩ := oddShift_mem_positiveEvenPart 𝒞 hgx
    rw [hsnd x] at hsndodd
    have hform := oddVariableDividedPowerStructure_dpow 𝒞 δ 1 one_pos odd_one n hn
      x (signRingHom 𝒞 1 (dC x)) hx hsndodd
    simp only [inclusion_eq_inl, inl_mul_generator] at hform
    have hval := hg.2.2.2 n x hx
    rw [hgeq x, hform] at hval
    have h := congrArg (oddShiftSnd 𝒞) hval
    rw [oddShiftSnd_inl_add_inr, hsnd (δ.dpow n x)] at h
    have heven : δ.dpow (n - 1) x ∈ evenPart 𝒞 := dpow_mem_evenPart 𝒞 δ (n - 1) hx
    have h' := congrArg (signRingHom 𝒞 1) h
    simp only [map_mul, signRingHom_signRingHom] at h'
    rw [signRingHom_one_of_mem_evenPart 𝒞 heven] at h'
    rw [← h']
    exact DividedPowers.TateResolution.evenPart_mul_comm 𝒞 heven _
  have hsign_dC : ∀ x : C, dC (signRingHom 𝒞 1 x) = - signRingHom 𝒞 1 (dC x) :=
    signRingHom_comm_of_lowersDegree 𝒞 dC hzero hmem
  have hone : dC 1 = 0 := hzero (SetLike.one_mem_graded 𝒞)
  have : IsGradedDerivation 𝒞 dC :=
    { d_grade_zero := hzero
      d_mem := hmem
      leibniz := fun {i _ x y} hx _ => by
        rw [hleib, signRingHom_of_mem 𝒞 1 i hx, one_mul, smul_mul_assoc] }
  have : IsCompatibleWithDifferential δ dC := ⟨fun hn hx => hcompat hn hx⟩
  -- Squaring to zero, by exhibiting the elements killed by `dC ∘ dC` as a subring.
  have hsq : ∀ x : C, dC (dC x) = 0 := by
    have hdpT : ∀ (n : ℕ) (j : J), dC (dC (δ.dpow n (T j))) = 0 := fun n j =>
      comp_self_dpow_eq_zero 𝒞 dC δ (hT j) (hι_grade _ _ (he_grade j)) (hdC_T j)
        (by rw [hdC_ι, he_cycle, map_zero]) n
    let E : Subring C :=
      { carrier := {x : C | dC (dC x) = 0}
        mul_mem' := by
          intro x y hx hy
          show dC (dC (x * y)) = 0
          replace hx : dC (dC x) = 0 := hx
          replace hy : dC (dC y) = 0 := hy
          rw [hleib, map_add, hleib, hleib, hx, hsign_dC, hy]
          simp
        one_mem' := by
          show dC (dC 1) = 0
          rw [hone, map_zero]
        add_mem' := by
          intro x y hx hy
          show dC (dC (x + y)) = 0
          replace hx : dC (dC x) = 0 := hx
          replace hy : dC (dC y) = 0 := hy
          rw [map_add, map_add, hx, hy, add_zero]
        zero_mem' := by
          show dC (dC 0) = 0
          simp
        neg_mem' := by
          intro x hx
          show dC (dC (-x)) = 0
          replace hx : dC (dC x) = 0 := hx
          rw [map_neg, map_neg, hx, neg_zero] }
    have hall : ∀ x : C, x ∈ E := by
      refine hclosure E (fun a => ?_) (fun j => ?_) (fun n j => ?_)
      · show dC (dC (ι a)) = 0
        rw [hdC_ι, hdC_ι, IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) a, map_zero]
      · show dC (dC (T j)) = 0
        rw [hdC_T, hdC_ι, he_cycle j, map_zero]
      · show dC (dC (δ.dpow n (T j))) = 0
        exact hdpT n j
    intro x
    exact hall x
  refine ⟨dC, ⟨IsGradedDerivation.of_d_sq_zero 𝒞 dC hsq, hdC_ι, hdC_T, inferInstance⟩, ?_⟩
  rintro dC' ⟨inst', hι', hT', compat'⟩
  have hleib' : ∀ x y : C, dC' (x * y) = dC' x * y + signRingHom 𝒞 1 x * dC' y :=
    differential_mul_signRingHom 𝒞 dC'
  have hone' : dC' 1 = 0 :=
    IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒞) (SetLike.one_mem_graded 𝒞)
  let F : Subring C :=
    { carrier := {x : C | dC x = dC' x}
      mul_mem' := by
        intro x y hx hy
        show dC (x * y) = dC' (x * y)
        replace hx : dC x = dC' x := hx
        replace hy : dC y = dC' y := hy
        rw [hleib, hleib', hx, hy]
      one_mem' := by
        show dC 1 = dC' 1
        rw [hone, hone']
      add_mem' := by
        intro x y hx hy
        show dC (x + y) = dC' (x + y)
        replace hx : dC x = dC' x := hx
        replace hy : dC y = dC' y := hy
        rw [map_add, map_add, hx, hy]
      zero_mem' := by
        show dC 0 = dC' 0
        simp
      neg_mem' := by
        intro x hx
        show dC (-x) = dC' (-x)
        replace hx : dC x = dC' x := hx
        rw [map_neg, map_neg, hx] }
  have hFall : ∀ x : C, x ∈ F := by
    refine hclosure F (fun a => ?_) (fun j => ?_) (fun n j => ?_)
    · show dC (ι a) = dC' (ι a)
      rw [hdC_ι, hι']
    · show dC (T j) = dC' (T j)
      rw [hdC_T, hT']
    · show dC (δ.dpow n (T j)) = dC' (δ.dpow n (T j))
      by_cases hpos : T j ∈ positiveEvenPart 𝒞
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [δ.dpow_zero hpos, hone, hone']
        · rw [hcompat (by omega) hpos, compat'.d_dpow (by omega) hpos, hdC_T, hT']
      · rw [δ.dpow_null hpos, map_zero, map_zero]
  exact (LinearMap.ext fun x => hFall x).symm

end MixedDegree

section SetVariable

open EvenVariableAlgebra OddVariableExtension

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  (γ : DividedPowerStructure Aᵢ)
  (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  (δ : DividedPowerStructure Cᵢ)
  (ι : A →ₐ[R] C) (T : J → C) (d : ℕ) (hd : 0 < d)

/-- **The extension of a differential along a family of cycles is square-zero.** The graded
derivation extending a differential `dA` to a set-variable divided power extension, with a cycle
of degree `d - 1` prescribed as the value on each adjoined variable, satisfies `D ∘ D = 0`.

This is the content missing from
`DividedPowers.TateResolution.existsUnique_gradedDerivation_setVariableExtension`, whose
prescribed values carry no cycle condition and whose conclusion is therefore only a graded
derivation. -/
public theorem IsSetVariableExtension.differential_sq_eq_zero
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd)
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra Aᵢ dA]
    (ev : J → A) (hev : ∀ j : J, ev j ∈ Aᵢ (d - 1)) (hcycle : ∀ j : J, dA (ev j) = 0)
    (D : C →ₗ[R] C) [IsGradedDerivation Cᵢ D] [IsCompatibleWithDifferential δ D]
    (hDι : ∀ a : A, D (ι a) = ι (dA a)) (hDT : ∀ j : J, D (T j) = ι (ev j))
    (x : C) : D (D x) = 0 := by
  classical
  -- The elements all of whose homogeneous components are killed by `D ∘ D`.
  let W : Subring C :=
    { carrier := {y : C | ∀ m : ℕ, D (D (gradedPart Cᵢ y m)) = 0}
      zero_mem' := fun m => by rw [gradedPart_zero, map_zero, map_zero]
      one_mem' := fun m => by
        rcases eq_or_ne m 0 with hm | hm
        · subst hm
          rw [gradedPart_of_mem_same Cᵢ (SetLike.one_mem_graded Cᵢ),
            IsGradedDerivation.d_grade_zero (𝒜 := Cᵢ) (d := D) (SetLike.one_mem_graded Cᵢ),
            map_zero]
        · rw [gradedPart_of_mem_ne Cᵢ (SetLike.one_mem_graded Cᵢ) (Ne.symm hm), map_zero,
            map_zero]
      add_mem' := fun {y z} hy hz m => by
        rw [gradedPart_add, map_add, map_add, hy m, hz m, add_zero]
      neg_mem' := fun {y} hy m => by rw [gradedPart_neg, map_neg, map_neg, hy m, neg_zero]
      mul_mem' := fun {y z} hy hz m => by
        obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ y
        obtain ⟨t, ht⟩ := exists_gradedPart_decomposition Cᵢ z
        rw [hs, ht, gradedPart_mul_sum, map_sum, map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_sum, map_sum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rcases eq_or_ne (i + k) m with hik | hik
        · rw [gradedPart_mul_homogeneous Cᵢ (gradedPart_mem Cᵢ y i) (gradedPart_mem Cᵢ z k) hik,
            comp_self_mul_of_mem_grade Cᵢ D (gradedPart_mem Cᵢ y i) (gradedPart_mem Cᵢ z k),
            hy i, hz k, zero_mul, mul_zero, add_zero]
        · rw [gradedPart_mul_homogeneous_of_ne Cᵢ (gradedPart_mem Cᵢ y i)
            (gradedPart_mem Cᵢ z k) hik, map_zero, map_zero] }
  -- The generators of a finite variable stage lie in `W`.
  have hstage : ∀ S : Finset J, finiteVariableStage δ ι T S ≤ W := by
    intro S
    refine Subring.closure_le.2 ?_
    rintro y (⟨a, rfl⟩ | ⟨i, -, rfl | ⟨n, rfl⟩⟩) m
    · rw [gradedPart_algHom Aᵢ Cᵢ ι hC.coefficient_grade a m, hDι, hDι,
        IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := Aᵢ) (d := dA), map_zero]
    · rcases eq_or_ne m d with hm | hm
      · subst hm
        rw [gradedPart_of_mem_same Cᵢ (hC.generator_mem i), hDT, hDι, hcycle]
        simp
      · rw [gradedPart_of_mem_ne Cᵢ (hC.generator_mem i) (Ne.symm hm), map_zero, map_zero]
    · obtain ⟨p, hp⟩ := hC.exists_mem_grade_dpow_generator i n
      rcases eq_or_ne p m with hpm | hpm
      · subst hpm
        rw [gradedPart_of_mem_same Cᵢ hp]
        exact comp_self_dpow_eq_zero Cᵢ D δ (hC.generator_mem i)
          (hC.coefficient_grade (d - 1) (ev i) (hev i)) (hDT i)
          (by rw [hDι, hcycle, map_zero]) n
      · rw [gradedPart_of_mem_ne Cᵢ hp hpm, map_zero, map_zero]
  -- An element lies in some finite variable stage, hence in `W`; decomposing it finishes.
  obtain ⟨S, hS⟩ := hC.finite_support x
  obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ x
  rw [hs, map_sum, map_sum]
  exact Finset.sum_eq_zero fun m _ => hstage S hS m

/-- **The differential of a set-variable divided power extension**, the set-indexed form of
Tag 09PM. A differential on the coefficient algebra, compatible with its divided powers,
together with a *cycle* of degree `d - 1` prescribed as the value on each adjoined variable of
degree `d`, determines the unique divided-power-compatible differential on the extension.

This is the inductive step of Tate's construction: at a stage whose cycles in degree `n` are to
be killed, the variables adjoined in degree `n + 1` are indexed by those cycles, and the cycle
condition is exactly what makes the extended operator square-zero.

The variant for variables of arbitrary prescribed degrees, which instead needs the universal
property of the extension, is
`existsUnique_differential_mixedDegreeSetVariableExtension`. -/
@[stacks 09PM "set of variables"]
public theorem existsUnique_differential_setVariableExtension
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd)
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra Aᵢ dA] [IsCompatibleWithDifferential γ dA]
    (ev : J → A) (hev : ∀ j : J, ev j ∈ Aᵢ (d - 1)) (hcycle : ∀ j : J, dA (ev j) = 0) :
    ∃! D : C →ₗ[R] C,
      IsDifferentialGradedAlgebra Cᵢ D ∧ (∀ a : A, D (ι a) = ι (dA a)) ∧
        (∀ j : J, D (T j) = ι (ev j)) ∧ IsCompatibleWithDifferential δ D := by
  obtain ⟨D, hD, hDuniq⟩ := existsUnique_gradedDerivation_setVariableExtension Aᵢ γ Cᵢ δ ι T
    d hd hC dA ev hev
  let : IsGradedDerivation Cᵢ D := hD.1
  let : IsCompatibleWithDifferential δ D := hD.2.2.2
  refine ⟨D, ⟨IsGradedDerivation.of_d_sq_zero Cᵢ D (IsSetVariableExtension.differential_sq_eq_zero
    Aᵢ γ Cᵢ δ ι T d hd hC dA ev hev hcycle D hD.2.1 hD.2.2.1), hD.2.1, hD.2.2.1, hD.2.2.2⟩, ?_⟩
  intro D' hD'
  let : IsDifferentialGradedAlgebra Cᵢ D' := hD'.1
  exact hDuniq D' ⟨inferInstance, hD'.2.1, hD'.2.2.1, hD'.2.2.2⟩

end SetVariable

end DividedPowers.TateResolution

end
