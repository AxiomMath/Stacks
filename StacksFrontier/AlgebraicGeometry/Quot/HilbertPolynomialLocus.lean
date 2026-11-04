module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorTensorPowerReindex
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerLocus

/-!
# The loci of the Hilbert polynomials in a family of coherent sheaves

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `L` an invertible
`𝒪_X`-module and `(T, 𝓕)` an object of `Coh_{X/B}`.  For `P : ℤ → ℤ` the *locus of `P`* is the
set of points `t ∈ T` at which

`P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`  for every `n ∈ ℤ`.

The object lies in `Coh^{P, L}_{X/B}` exactly when its locus of `P` is all of `T`.  By Stacks 0DN4
the function `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is a numerical polynomial for every `t`, so the loci of
the numerical polynomials cover `T`; two different functions have disjoint loci.  This is the
decomposition `Coh_{X/B} = ∐_P Coh^P_{X/B}` of Stacks 0DNF read on a single object.

## Main definitions

* `AlgebraicGeometry.Space.CoherentObject.hilbertPolynomialLocus`: the locus of `P`.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.hasHilbertPolynomial_iff_hilbertPolynomialLocus_eq_univ`:
  the object has Hilbert polynomial `P` exactly when its locus of `P` is everything.
* `AlgebraicGeometry.Space.CoherentObject.mem_hilbertPolynomialLocus_twistedEuler`: every point
  lies in the locus of its own twisted Euler characteristic, which is a numerical polynomial.
* `AlgebraicGeometry.Space.CoherentObject.iUnion_hilbertPolynomialLocus`: the loci of the
  numerical polynomials cover `T`.
* `AlgebraicGeometry.Space.CoherentObject.pairwise_disjoint_hilbertPolynomialLocus`: the loci of
  different functions are disjoint.
* `AlgebraicGeometry.Space.CoherentHom.preimage_hilbertPolynomialLocus`: along a morphism of
  `Coh_{X/B}` the locus of `P` pulls back to the locus of `P`.
* `CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial_of_isLocallyConstant`:
  `Coh^{P, L}_{X/B} ⊆ Coh_{X/B}` is cut out by an open and closed condition, represented on each
  object by the locus of `P`, as soon as each `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant
  and the degrees of the polynomials `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` are locally bounded on `T`.

## Implementation notes

The last result is the reduction by which the source's infinitely many conditions
`P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`, one for each `n ∈ ℤ`, become finitely many near every point:
two polynomials of degree at most `d` agreeing at `0, …, d` are equal.  Its two inputs are
results, not data.  Local constancy is, for each `n`, the local constancy of the Euler
characteristic of the fibres of a flat family with proper support (Stacks 0D1Z applied to the
perfect complex of Stacks 0A1P, or the finite projective model of Stacks 0A1Q); the bound on the
degrees is the bound of Stacks 0DN4 by the dimension of the fibres of `X_T ⟶ T`, which is locally
bounded on `T`.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Space.CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]

/-- **The locus of a Hilbert polynomial.**  For an object `(T, 𝓕)` of `Coh_{X/B}` and
`P : ℤ → ℤ`, the set of points `t ∈ T` with `P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` for every `n`. -/
def hilbertPolynomialLocus (A : CoherentObject D) (P : ℤ → ℤ) : Set A.testScheme :=
  {t | ∀ n : ℤ, twistedEuler L A t n = P n}

/-- A point `t` lies in the locus of `P` exactly when `χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = P(n)` for every
`n`. -/
theorem mem_hilbertPolynomialLocus_iff (A : CoherentObject D) (P : ℤ → ℤ) (t : A.testScheme) :
    t ∈ hilbertPolynomialLocus L A P ↔ ∀ n : ℤ, twistedEuler L A t n = P n :=
  Iff.rfl

/-- An object of `Coh_{X/B}` has Hilbert polynomial `P` exactly when its locus of `P` is the
whole test scheme. -/
theorem hasHilbertPolynomial_iff_hilbertPolynomialLocus_eq_univ (A : CoherentObject D)
    (P : ℤ → ℤ) : HasHilbertPolynomial L P A ↔ hilbertPolynomialLocus L A P = Set.univ := by
  rw [hasHilbertPolynomial_iff, Set.eq_univ_iff_forall]
  exact forall_congr' fun t => forall_congr' fun n => eq_comm

/-- **Every point lies in the locus of a numerical polynomial** (Stacks 0DN4): the twisted Euler
characteristic `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` at `t` is the function of a rational polynomial, and
`t` lies in its locus. -/
theorem mem_hilbertPolynomialLocus_twistedEuler (A : CoherentObject D) (t : A.testScheme) :
    (∃ p : Polynomial ℚ, ∀ m : ℤ, p.eval (m : ℚ) = (twistedEuler L A t m : ℚ)) ∧
      t ∈ hilbertPolynomialLocus L A (twistedEuler L A t) :=
  ⟨exists_polynomial_eval_eq_twistedEuler L A t, fun _ => rfl⟩

/-- **The loci of the numerical polynomials cover the test scheme.** -/
theorem iUnion_hilbertPolynomialLocus (A : CoherentObject D) :
    ⋃ P : {P : ℤ → ℤ // ∃ p : Polynomial ℚ, ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)},
      hilbertPolynomialLocus L A P.1 = Set.univ :=
  Set.eq_univ_of_forall fun t => Set.mem_iUnion.2
    ⟨⟨_, (mem_hilbertPolynomialLocus_twistedEuler L A t).1⟩,
      (mem_hilbertPolynomialLocus_twistedEuler L A t).2⟩

/-- **The loci of different functions are disjoint.** -/
theorem pairwise_disjoint_hilbertPolynomialLocus (A : CoherentObject D) :
    Pairwise fun P Q : ℤ → ℤ => Disjoint (hilbertPolynomialLocus L A P)
      (hilbertPolynomialLocus L A Q) := by
  intro P Q hPQ
  refine Set.disjoint_left.2 fun t hP hQ => hPQ (funext fun n => ?_)
  rw [← hP n, ← hQ n]

/-- **Each point lies in the locus of exactly one function**, and that function is a numerical
polynomial: the twisted Euler characteristic at the point. -/
theorem existsUnique_mem_hilbertPolynomialLocus (A : CoherentObject D) (t : A.testScheme) :
    ∃! P : ℤ → ℤ, t ∈ hilbertPolynomialLocus L A P :=
  ⟨twistedEuler L A t, fun _ => rfl, fun _ hP => funext fun n => (hP n).symm⟩

end AlgebraicGeometry.Space.CoherentObject

open Topology

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]

/-- **The locus of a Hilbert polynomial pulls back along morphisms of `Coh_{X/B}`**: for a
morphism `A' ⟶ A` lying over `h : T' ⟶ T`, the locus of `P` in `T'` is the preimage under `h` of
the locus of `P` in `T`, the twisted Euler characteristics being constant along `h`
(`AlgebraicGeometry.Space.CoherentHom.twistedEuler_eq`). -/
theorem CoherentHom.preimage_hilbertPolynomialLocus {A' A : CoherentObject D}
    (φ : CoherentHom A' A) (P : ℤ → ℤ) :
    φ.baseScheme ⁻¹' CoherentObject.hilbertPolynomialLocus L A P =
      CoherentObject.hilbertPolynomialLocus L A' P := by
  ext t
  simp only [Set.mem_preimage, CoherentObject.mem_hilbertPolynomialLocus_iff,
    CoherentHom.twistedEuler_eq L φ t]

/-- **`Coh^{P, L}_{X/B}` is cut out by an open and closed condition, given local constancy and a
local degree bound.**  If for every object `(T, 𝓕)` of `Coh_{X/B}` and every `n` the function
`t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant on `T`, and near every point of `T` the
functions `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` are polynomials of bounded degree, then for every
`P : ℤ → ℤ` the condition of having Hilbert polynomial `P` with respect to `L` is an open and
closed condition on the objects of `Coh_{X/B}`, represented on each object by the locus of `P`. -/
theorem CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial_of_isLocallyConstant
    (hlc : ∀ (A : CoherentObject D) (n : ℤ),
      IsLocallyConstant fun t : A.testScheme => CoherentObject.twistedEuler L A t n)
    (hdeg : ∀ (A : CoherentObject D) (t : A.testScheme), ∃ U ∈ 𝓝 t, ∃ d : ℕ,
      ∀ t' ∈ U, IsPolynomialOfDegreeLE (CoherentObject.twistedEuler L A t') d)
    (P : ℤ → ℤ) :
    CoherentSituation.IsOpenAndClosedCondition D (CoherentObject.HasHilbertPolynomial L P) := by
  have h := CoherentSituation.isOpenAndClosedCondition_of_isClopen (D := D)
    (fun A n t => CoherentObject.twistedEuler L A t n) P
    (fun φ n t => CoherentHom.twistedEuler_eq L φ t n)
    (fun A => isClopen_setOf_forall_eq_of_locally_isPolynomialOfDegreeLE (hlc A) (hdeg A) P)
  have he : CoherentObject.HasHilbertPolynomial L P =
      fun A : CoherentObject D => ∀ (n : ℤ) (t : A.testScheme),
        CoherentObject.twistedEuler L A t n = P n := by
    funext A
    exact propext ⟨fun hA n t => (hA t n).symm, fun hA t n => (hA n t).symm⟩
  rwa [he]

end AlgebraicGeometry.Space

end
