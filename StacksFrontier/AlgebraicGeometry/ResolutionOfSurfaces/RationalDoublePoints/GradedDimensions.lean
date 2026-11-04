module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseDichotomy
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalTwistDegree

/-!
# The graded dimensions of a rational surface singularity

Section 54.12 of the source opens by computing `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1` for a two-dimensional
Gorenstein rational surface singularity, which is what makes the embedding dimension three and
`dim_κ(𝔪²/𝔪³) = 5` smaller than the number six of products `xᵢxⱼ`, hence what produces the
quadratic form the rest of the section studies. The computation is Riemann–Roch on the exceptional
curve `E` of the blowup of the maximal ideal: `χ(E, 𝒪_E(n)) = n · deg 𝒪_E(1) + χ(E, 𝒪_E)`, with
`χ(E, 𝒪_E(n)) = dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹)` and `χ(E, 𝒪_E) = 1`.

This file proves that computation in the form

`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = n · (dim_κ(𝔪/𝔪²) − 1) + 1`,

unconditionally, for every member of the rational singularity situation of [Stacks, Tag 0B4W].
The source's `2n + 1` is the case `dim_κ(𝔪/𝔪²) = 3`, equivalently `deg 𝒪_E(1) = 2`, which the
source obtains from `ω_E = 𝒪_E(-1)` and which is not available in this file. It is available in
`RationalDoublePoints/EmbeddingDimensionGorenstein.lean`, as `AlgebraicGeometry.BlowUpDualizing`
`.finrank_cotangentSpace_eq_three_of_dualizingNormalization`, carrying one hypothesis: a
dualizing module on the blowup normalized in the sense of [Stacks, Remark 0B4R]. The three
results below whose hypothesis is that value are discharged by applying them to it; no
restatement of them is added there, the derivation being wholly in them already.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf`:
  **`deg 𝒪_E(n) = dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) − 1`** for every `n`, the computation of
  `AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_one` at every twist.
* `AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_eq_nsmul`:
  **`deg 𝒪_E(n) = n · deg 𝒪_E(1)`**, from the additivity of the degree in the tensor product
  ([Stacks, Tag 0AYX]) and `𝒪_E(1) ⊗ 𝒪_E(n) ≅ 𝒪_E(n + 1)`.
* `AlgebraicGeometry.BlowUpDualizing.finrank_gradedPiece_eq`: **the graded dimensions**,
  `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = n · (dim_κ(𝔪/𝔪²) − 1) + 1`.
* `AlgebraicGeometry.BlowUpDualizing.two_mul_add_one_le_finrank_gradedPiece`:
  **`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) ≥ 2n + 1`** for a singularity which is not regular, which needs no further
  input.
* `AlgebraicGeometry.BlowUpDualizing.finrank_gradedPiece_eq_two_mul_add_one`: **the source's
  `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1`**, from embedding dimension three.
* `AlgebraicGeometry.BlowUpDualizing.exists_generators_and_quadraticRelation_of_finrank`
  and `.exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear_of_finrank`: the quadratic relation
  and the case I / case II dichotomy of Section 54.12, with the dimension formula discharged and
  only the embedding dimension left as a hypothesis.

## The argument

The degree of an invertible module on the exceptional curve is `χ(L) − χ(𝒪_E)`, and both Euler
characteristics collapse to `h⁰ − h¹` because `E` is one-dimensional. For `L = 𝒪_E(n)` the four
dimensions are `h⁰(𝒪_E(n)) = dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹)` by clause (5) of [Stacks, Tag 0B63],
`h¹(𝒪_E(n)) = 0` by clause (4), `h⁰(𝒪_E) = 1` and `h¹(𝒪_E) = 0`; that is the first result, and at
`n = 1` it is the computation of clause (3). The second result is induction on `n`: the
degree of a tensor product of two invertible modules is the sum of the degrees, with no hypothesis
beyond properness and the dimension bound, and `𝒪_E(1) ⊗ 𝒪_E(n)` is `𝒪_E(n + 1)`. Eliminating the
degree between the two gives the graded dimensions.

## Implementation notes

What remains of Section 54.12's opening computation is `dim_κ(𝔪/𝔪²) = 3`. The source gets it from
`deg 𝒪_E(1) = 2`, which it gets from `ω_E = 𝒪_E(-1)` by Riemann–Roch on `E` over `κ`. Two steps
of that are in place. `ω_E ≅ (ω_X|_E)(-1)` is clause (1) of [Stacks, Tag 0B64], and `ω_X ≅ 𝒪_X`
— where the Gorenstein hypothesis on `A` enters — is
`AlgebraicGeometry.BlowUpDualizing.nonempty_iso_structureModule_of_iso_self` of
`ResolutionOfSurfaces/RationalSingularities/BlowUpDualizingGorenstein.lean`, which carries only
the global generation `G` that clause (3) of the same tag already carries; composing them gives
`ω_E ≅ 𝒪_E(-1)`, which is
`AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_curveTwistSheaf` of
`ResolutionOfSurfaces/RationalSingularities/BlowUpExceptionalDualizingGorenstein.lean`.

`deg 𝒪_E(1) = 2` does **not** follow from that, and a revision of this note which said it did was
wrong. Riemann–Roch gives the degree of `ω_E` only once `ω_E` is known to be the dualizing sheaf
of `E` as a proper curve over `κ` — `Stacks.Duality.dualizingSheafOverField` of the structure
morphism of `E` — and what is proved about `ω_E` is that it is *a* dualizing module on the scheme
`E` (`AlgebraicGeometry.BlowUpDualizing.isDualizingModule_exceptionalDualizingModule`), which by
[Stacks, Tag 0A7F] pins it down only up to shift and invertible twist. The module documentation
of `ResolutionOfSurfaces/RationalSingularities/BlowUpExceptionalDualizing.lean` records what
would pin it down, and names the two steps of that which are absent from the project.

So what is unconditional here remains `deg 𝒪_E(1) ≥ 2` for `A` not regular, i.e.
`dim_κ(𝔪/𝔪²) ≥ 3`; the results needing the exact value take it in a binder and are left
unregistered, and `finrank_gradedPiece_eq` itself carries nothing. The exact value is obtained
in `RationalDoublePoints/EmbeddingDimensionGorenstein.lean` without `deg 𝒪_E(1) = 2` being read
off `ω_E = 𝒪_E(-1)` at all: `ω_E` is identified with the dualizing sheaf of `E` over `κ` — which
is proved, see below — and the degree of `𝒪_E(-1)` is then bounded through the duality of
dimensions of [Stacks, Tag 0BS6] and a count of global sections of `ω_X|_E`, so that `ω_X ≅ 𝒪_X`
is never needed.

Everything of the computation on the near side of that one isomorphism is in
`RationalDoublePoints/EmbeddingDimension.lean`: the degree of the twist is additive over all of
`ℤ` there, not just over `ℕ` as in
`AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_eq_nsmul` below, so
`deg 𝒪_E(-1) = 1 − dim_κ(𝔪/𝔪²)`, and duality over `κ` at
`Stacks.Duality.dualizingSheafOverField` — which is proved with no hypothesis carried — turns the
isomorphism into `deg 𝒪_E(-1) = −2` and hence into `dim_κ(𝔪/𝔪²) = 3`. The three results below
whose hypothesis is that value have counterparts there taking the isomorphism instead; that
file also records why a shift-and-twist normalization argument from [Stacks, Tag 0A7F] does not
replace the two missing steps.

`IsProper` of the structure morphism of the exceptional curve is clause (1) of
[Stacks, Tag 0B63] but is not an instance outside the file that proves it, so it is taken as an
instance binder by the results whose statements mention the degree and discharged inside the
proofs of the results whose statements do not.

## References

* [Stacks Project, Tag 0BGB](https://stacks.math.columbia.edu/tag/0BGB)
* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalRing (CotangentSpace ResidueField maximalIdeal)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **The degree of a finite locally free module depends on the module only through its
identity.** Local freeness of a given rank is a proposition, so the two witnesses do not enter;
this is the companion of `AlgebraicGeometry.curveDegree_congr_hom`, which says the same of the
structure morphism. It is what lets the two constructions of the tensor product of sheaves of
modules be exchanged inside a degree, their equality
`Stacks.TensorSheafDedup.tensorSheaf_eq` being unavailable to the elaborator as a definitional
one across module boundaries. -/
public theorem curveDegree_congr_module {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (rank : ℕ)
    {E E' : X.Modules} (h : E = E')
    (iE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank)
    (iE' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' rank) :
    @curveDegree k _ X f _ hdim E rank iE = @curveDegree k _ X f _ hdim E' rank iE' := by
  subst h
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.BlowUpDualizing

/-- The exceptional curve of a rational singularity situation has topological dimension at most
one. -/
private theorem topologicalKrullDim_exceptionalCurve_le_one (S : RationalSingularitySituation.{u}) :
    topologicalKrullDim (exceptionalCurve S.A) ≤ 1 :=
  le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two)

variable (S : RationalSingularitySituation.{u})
  [IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))]

/-! ### The degree of every twist -/

/-- **`deg 𝒪_E(n) = dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) − 1`.** The degree is the alternating sum of the dimensions of
cohomology minus the same sum for the structure sheaf; both collapse to `h⁰ − h¹` because `E` is
one-dimensional, and the four remaining dimensions are `h⁰(𝒪_E(n)) = dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹)` by clause (5)
of [Stacks, Tag 0B63], `h¹(𝒪_E(n)) = 0` by clause (4), `h⁰(𝒪_E) = 1` and `h¹(𝒪_E) = 0`.

At `n = 1` this is
`AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_one`, the computation the
source performs in the proof of clause (3). -/
public theorem invertibleCurveDegree_curveTwistSheaf (n : ℕ) :
    invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A (n : ℤ)) =
      (Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) : ℤ) - 1 := by
  have hvan : ∀ (F : (exceptionalCurve S.A).Modules) (m : ℕ), 2 ≤ m →
      IsZero (cohomologyOverField (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) F m) := fun F m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) F (d := 1)
      (topologicalKrullDim_exceptionalCurve_le_one S)
      (by omega)
  rw [invertibleCurveDegree_eq_sub_of_isZero (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (topologicalKrullDim_exceptionalCurve_le_one S)
      (curveTwistSheaf S.A (n : ℤ)) (fun m hm => hvan _ m hm) (fun m hm => hvan _ m hm),
    finrank_cohomologyOverField_unit_zero S, finrank_cohomologyOverField_unit_one S,
    finrank_cohomologyOverField_curveTwistSheaf_zero S n (IsLocalRing.gradedPiece S.A n)
      (LinearEquiv.refl S.A _),
    finrank_cohomologyOverField_curveTwistSheaf_one S n]
  push_cast
  ring

/-! ### The degree is additive in the twist -/

/-- **`deg 𝒪_E(n) = n · deg 𝒪_E(1)`.** The degree of a tensor product of two invertible modules on
a proper scheme of dimension at most one is the sum of the degrees ([Stacks, Tag 0AYX], with no
hypothesis beyond that), and `𝒪_E(1) ⊗ 𝒪_E(n) ≅ 𝒪_E(n + 1)`; the base case is
`deg 𝒪_E(0) = 0`, because `𝒪_E(0) ≅ 𝒪_E`. -/
public theorem invertibleCurveDegree_curveTwistSheaf_eq_nsmul (n : ℕ) :
    invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A (n : ℤ)) =
      (n : ℤ) * invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A 1) := by
  induction n with
  | zero =>
      rw [Nat.cast_zero, zero_mul]
      exact invertibleCurveDegree_eq_zero_of_iso_unit (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (topologicalKrullDim_exceptionalCurve_le_one S)
        (curveTwistSheaf S.A ((0 : ℕ) : ℤ)) (curveTwistSheafZeroIso S.A)
  | succ n ih =>
      have hiso : Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
          (curveTwistSheaf S.A 1) (curveTwistSheaf S.A (n : ℤ)) ≅
            curveTwistSheaf S.A ((n + 1 : ℕ) : ℤ) :=
        curveTwistSheafAddIso S.A 1 (n : ℤ) ≪≫
          curveTwistSheafCongr S.A (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by push_cast; ring)
      have htens : (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(exceptionalCurve S.A).toRingedSpace.presheaf,
              (exceptionalCurve S.A).toRingedSpace.IsSheaf⟩).obj (curveTwistSheaf S.A 1)).obj
              (curveTwistSheaf S.A (n : ℤ)))
          = Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
              (curveTwistSheaf S.A 1) (curveTwistSheaf S.A (n : ℤ)) :=
        rfl
      have hraw := curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one
        (ResidueField S.A) (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (topologicalKrullDim_exceptionalCurve_le_one S)
        (curveTwistSheaf S.A 1) (curveTwistSheaf S.A (n : ℤ)) 1 1
      simp only [Nat.cast_one, one_mul] at hraw
      have : Stacks.Ample.IsInvertibleModule (exceptionalCurve S.A)
          (Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
            (curveTwistSheaf S.A 1) (curveTwistSheaf S.A (n : ℤ))) :=
        Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso hiso.symm
      have hadd : curveDegree (ResidueField S.A)
            (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
            (topologicalKrullDim_exceptionalCurve_le_one S)
            (Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
              (curveTwistSheaf S.A 1) (curveTwistSheaf S.A (n : ℤ))) 1 =
          curveDegree (ResidueField S.A)
              (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
              (topologicalKrullDim_exceptionalCurve_le_one S)
              (curveTwistSheaf S.A 1) 1 +
            curveDegree (ResidueField S.A)
              (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
              (topologicalKrullDim_exceptionalCurve_le_one S)
              (curveTwistSheaf S.A (n : ℤ)) 1 :=
        (curveDegree_congr_module (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
          (topologicalKrullDim_exceptionalCurve_le_one S)
          1 htens
          (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (exceptionalCurve S.A)
            (curveTwistSheaf S.A 1) (curveTwistSheaf S.A (n : ℤ)) 1 1)
          inferInstance).symm.trans hraw
      rw [← invertibleCurveDegree_eq_of_iso (ResidueField S.A)
            (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
            (topologicalKrullDim_exceptionalCurve_le_one S)
            hiso,
          invertibleCurveDegree_eq_curveDegree_one, hadd,
          ← invertibleCurveDegree_eq_curveDegree_one, ← invertibleCurveDegree_eq_curveDegree_one,
          ih]
      push_cast
      ring

/-! ### The graded dimensions -/

omit [IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))] in
/-- **The graded dimensions of a rational surface singularity:**

`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = n · (dim_κ(𝔪/𝔪²) − 1) + 1`.

Eliminate `deg 𝒪_E(n)` between
`AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf` and
`AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_eq_nsmul`, using that
`deg 𝒪_E(1) = dim_κ(𝔪/𝔪²) − 1`. This is the Riemann–Roch computation that opens Section 54.12 of
the source, with the value of `dim_κ(𝔪/𝔪²)` left open. -/
public theorem finrank_gradedPiece_eq (n : ℕ) :
    (Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) : ℤ) =
      (n : ℤ) * ((Module.finrank (ResidueField S.A) (CotangentSpace S.A) : ℤ) - 1) + 1 := by
  have : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
    isProper_exceptionalDivisorToCentre_residuePoint S.A
  have hn := invertibleCurveDegree_curveTwistSheaf S n
  have hmul := invertibleCurveDegree_curveTwistSheaf_eq_nsmul S n
  rw [invertibleCurveDegree_curveTwistSheaf_one S] at hmul
  rw [hmul] at hn
  linarith [hn]

omit [IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))] in
/-- **`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1`**, the computation that opens Section 54.12, for a singularity of
embedding dimension three.

Embedding dimension three is a hypothesis, not a conclusion: the source derives it from
`deg 𝒪_E(1) = 2`, which rests on `ω_E = 𝒪_E(-1)` and so on `ω_X ≅ 𝒪_X` for the blowup, which the
project does not prove. See the module docstring. -/
public theorem finrank_gradedPiece_eq_two_mul_add_one (n : ℕ)
    (h : Module.finrank (ResidueField S.A) (CotangentSpace S.A) = 3) :
    Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) = 2 * n + 1 := by
  have hz := finrank_gradedPiece_eq S n
  rw [h] at hz
  have : (Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) : ℤ)
      = ((2 * n + 1 : ℕ) : ℤ) := by push_cast at hz ⊢; linarith [hz]
  exact_mod_cast this

omit [IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))] in
/-- **`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) ≥ 2n + 1` for a singularity that is not regular.** Clause (3) of
[Stacks, Tag 0B63] gives `deg 𝒪_E(1) ≥ 2` there, that is `dim_κ(𝔪/𝔪²) ≥ 3`, and the graded
dimensions are increasing in that quantity. This is the half of the source's `2n + 1` which does
not need the Gorenstein hypothesis; equality is embedding dimension exactly three. -/
public theorem two_mul_add_one_le_finrank_gradedPiece (hreg : ¬ IsRegularLocalRing S.A) (n : ℕ) :
    2 * n + 1 ≤ Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) := by
  have hne : Module.finrank (ResidueField S.A) (CotangentSpace S.A) ≠ 2 := fun h =>
    hreg ((isRegularLocalRing_iff_finrank_cotangentSpace_eq_two S).mpr h)
  have h3 : 3 ≤ Module.finrank (ResidueField S.A) (CotangentSpace S.A) := by
    have h2 := two_le_finrank_cotangentSpace S
    omega
  have hz := finrank_gradedPiece_eq S n
  have hcast : ((2 * n + 1 : ℕ) : ℤ)
      ≤ (Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) : ℤ) := by
    have h3' : (3 : ℤ) ≤ (Module.finrank (ResidueField S.A) (CotangentSpace S.A) : ℤ) := by
      exact_mod_cast h3
    push_cast
    nlinarith [hz, h3', Nat.cast_nonneg (α := ℤ) n]
  exact_mod_cast hcast

/-! ### The quadratic form of Section 54.12 -/

omit [IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))] in
/-- **The quadratic relation of Section 54.12**, with the dimension formula discharged. For a
singularity of embedding dimension three the maximal ideal is generated by three elements whose
six products `xₚxᵩ`, `p ≤ q`, outnumber `dim_κ(𝔪²/𝔪³) = 5` and so satisfy a relation modulo `𝔪³`
with an upper triangular coefficient matrix one of whose entries on or above the diagonal is a
unit. -/
public theorem exists_generators_and_quadraticRelation_of_finrank
    (h : Module.finrank (ResidueField S.A) (CotangentSpace S.A) = 3) :
    ∃ (x : Fin 3 → S.A) (a : Fin 3 → Fin 3 → S.A) (b : Fin 3 → Fin 3 → Fin 3 → S.A),
      Ideal.span (Set.range x) = maximalIdeal S.A ∧ (∀ p q, q < p → a p q = 0) ∧
        (∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal S.A) ∧
        ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r) :=
  exists_generators_and_quadraticRelation
    (finrank_gradedPiece_eq_two_mul_add_one S 1 h)
    (finrank_gradedPiece_eq_two_mul_add_one S 2 h)

omit [IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))] in
/-- **The case I / case II dichotomy of Section 54.12**, with the dimension formula discharged.
Either the singularity admits generators of the maximal ideal in the case II normal form
`x₃² = Σ aₚᵩᵣ xₚxᵩxᵣ`, or it admits generators whose quadratic relation is in case I: upper
triangular with a unit entry, and the quadratic form not a scalar times the square of a linear
form. In case I the Claim of Section 54.12
(`AlgebraicGeometry.rank_le_one_of_not_isScalarSqLinear`) and the existence of a good coordinate
(`AlgebraicGeometry.isGoodCoordinateForm_of_upperTriangular_fin_three`) apply. -/
public theorem exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear_of_finrank
    (h : Module.finrank (ResidueField S.A) (CotangentSpace S.A) = 3) :
    (∃ (x : Fin 3 → S.A) (b : Fin 3 → Fin 3 → Fin 3 → S.A),
        Ideal.span (Set.range x) = maximalIdeal S.A ∧
          x 2 * x 2 = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r)) ∨
      ∃ (x : Fin 3 → S.A) (a : Fin 3 → Fin 3 → S.A) (b : Fin 3 → Fin 3 → Fin 3 → S.A),
        Ideal.span (Set.range x) = maximalIdeal S.A ∧ (∀ p q, q < p → a p q = 0) ∧
          (∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal S.A) ∧
          (∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r)) ∧
          ¬ IsScalarSqLinear fun p q => IsLocalRing.residue S.A (a p q) :=
  exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear
    (finrank_gradedPiece_eq_two_mul_add_one S 1 h)
    (finrank_gradedPiece_eq_two_mul_add_one S 2 h)

end AlgebraicGeometry.BlowUpDualizing

end
