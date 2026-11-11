module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute

/-!
# A family of curves whose total space is not a scheme

A family of curves (Stacks 0D4Z, `AlgebraicGeometry.CurveFamily`) is a flat, proper, finitely
presented morphism of relative dimension at most one from an *algebraic space* to a scheme. Over
the spectrum of a complete Noetherian local ring the total space of such a family is forced to be
a scheme; over the affine line it is not, and the source exhibits a counterexample.

The counterexample is built from the cubic surface

```
  T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t * T₀ * T₁ * T₂ = 0
```

in `P²` over `k[t]`, for `k` an uncountable algebraically closed field of characteristic
different from three: this is a smooth rational surface `Y` whose fibre `Y₀` over `t = 0` is the
smooth plane Fermat cubic, a curve of genus one. Because `Y` is rational its Picard group is
countable, while `Y₀(k)` is uncountable and `Y₀(k) → Pic(Y₀)` is injective, so one may choose a
point `y ∈ Y₀(k)` with `O(n y)` outside the image of `Pic(Y) → Pic(Y₀)` for every `n > 0`. That
choice makes `Y` satisfy the key property

* (2) every proper closed subscheme of `Y` dominating the affine line meets `Y₀` in a point
  other than `y`.

Blowing `Y` up at `y` gives `Z` with exceptional divisor `E` and strict transform `C` of `Y₀`,
and Artin's contraction theorem blows `C` down to a point `x` of an *algebraic space* `X`, which
is a family of curves over the affine line.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.not_exists_scheme_of_no_dominating_closed_avoiding`:
  the obstruction used in Stacks 0D5E. No *scheme* admits a proper morphism to an affine base with
  infinite fibres together with a point `x` such that no closed subset avoiding `x` surjects onto
  the base. This is why the total space `X` above is not a scheme.
* `Stacks.Examples.CurveFamilyNotScheme.exists_isClosed_notMem_surjective`: the engine of that
  obstruction. In a scheme proper over an affine base with infinite fibres, every point is
  avoided by a closed subset which surjects onto the base, namely the complement of any affine
  open neighbourhood of the point.
* `Stacks.Examples.CurveFamilyNotScheme.cubicEquation_map_eval_zero`: the surface the source
  starts from degenerates at `t = 0` to the Fermat cubic.

## Implementation notes

This file proves the obstruction: the geometry that the construction of Section 0D5D produces is
incompatible with being a scheme. The construction itself, and the complete statement of Stacks
0D5E, are in the files under `StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/`: the cubic
surface (`CubicSurface/`), the choice of `y` (`PointChoice.lean`), the blowup and the strict
transform (`Blowup/`), the formal contraction `W` of the formal neighbourhood of `C` and the proof
that `Z_{/C} ⟶ W` is a formal modification (the input the source takes from Artin's paper; files
`StacksDraft/AlgebraicGeometry/Surfaces/NegativeCurve*.lean`), Artin's contraction theorem
`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_isSeparated` (Stacks 0GIB), and
the final theorem `Stacks.Examples.CurveFamilyNotScheme.exists_curveFamily_total_not_scheme`
(`Main.lean`).

Concretely, if `X` were a scheme then `x` would have an affine open neighbourhood `U`, and
`T = X \ U` would be a closed subset avoiding `x` and surjecting onto the affine line — the
`exists_isClosed_notMem_surjective` step. Transporting `T` through the blow-down to a closed
subscheme of `Z` disjoint from `C`, and then down to `Y`, produces a proper closed subscheme of
`Y` dominating the affine line and meeting `Y₀` only at `y`, contradicting (2). It is exactly the
negation of the conclusion of `exists_isClosed_notMem_surjective` that the construction delivers,
and it is that negation which appears as the last hypothesis of
`not_exists_scheme_of_no_dominating_closed_avoiding`.

Three further points about the hypotheses. Relative dimension one enters only through the fibres
being infinite, which is weaker, so the statement is correspondingly stronger; flatness and
finite presentation are not needed at all. The base is asked to be affine, which the affine line
is, and which is what makes the fibre of an affine open over a point of the base affine. Finally,
properness is Mathlib's `AlgebraicGeometry.IsProper`, and only properness of the scheme `X` over
the base is used, not properness of the algebraic space.

The engine of `exists_isClosed_notMem_surjective` is the source's parenthetical "the fibres of
`X → A¹` are proper of dimension 1 and the fibres of `U → A¹` are affine hence different": a
fibre contained in an affine open `U` is itself affine, because the fibre inclusion is an affine
morphism and the fibre is then the preimage of `U` along it; being also proper over the residue
field it is finite, contradicting infinitude.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

/-! ### The surface the construction starts from -/

open MvPolynomial in
/-- The equation of the surface `Y` the source starts from: the cubic
`T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t * T₀ * T₁ * T₂` in the projective plane over `k[t]`, where `t` is
the coordinate on the affine line. -/
@[sga "7 XVIII 3.2.5" "partial"]
def cubicEquation (k : Type u) [Field k] : MvPolynomial (Fin 3) (Polynomial k) :=
  X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 - C Polynomial.X * (X 0 * X 1 * X 2)

open MvPolynomial in
/-- The fibre of the surface over `t = 0` is cut out by the Fermat cubic, which over a field of
characteristic different from three is a smooth plane curve of genus one. -/
theorem cubicEquation_map_eval_zero (k : Type u) [Field k] :
    map (Polynomial.evalRingHom (0 : k)) (cubicEquation k) = X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 := by
  simp [cubicEquation]

/-! ### The obstruction -/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A fibre of a proper morphism to an affine base which is contained in an affine open subset of
the source is finite.

The fibre inclusion is an affine morphism, being a base change of the affine morphism
`Spec κ(s) ⟶ S`; so the preimage of the affine open along it is affine, and that preimage is
everything. The fibre is therefore an affine scheme proper over `κ(s)`, hence finite over
`κ(s)`, hence finite. -/
theorem finite_preimage_of_subset_isAffineOpen [IsProper f] [IsAffine S] (s : S) {U : X.Opens}
    (hU : IsAffineOpen U) (hsub : f ⁻¹' {s} ⊆ U) : (f ⁻¹' {s}).Finite := by
  have hpb := IsPullback.of_hasPullback f (S.fromSpecResidueField s)
  have hfibreι : IsAffineHom (f.fiberι s) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hpre : IsAffineOpen ((f.fiberι s) ⁻¹ᵁ U) := hU.preimage (f.fiberι s)
  have htop : (f.fiberι s) ⁻¹ᵁ U = ⊤ := by
    refine TopologicalSpace.Opens.ext ?_
    rw [Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_top, Set.preimage_eq_univ_iff,
      Scheme.Hom.range_fiberι]
    exact hsub
  rw [htop] at hpre
  have : IsAffine ((⊤ : (f.fiber s).Opens) : Scheme.{u}) := hpre
  have : IsAffine (f.fiber s) := IsAffine.of_isIso (Scheme.topIso (f.fiber s)).inv
  have hproper : IsProper (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback (P := @IsProper) hpb ‹IsProper f›
  have : IsFinite (f.fiberToSpecResidueField s) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hproper, inferInstance⟩
  have hfin := (f.fiberToSpecResidueField s).finite_preimage_singleton
    (IsLocalRing.closedPoint (S.residueField s))
  have : Finite (f.fiber s) := by
    refine Set.finite_univ_iff.mp (hfin.subset fun x _ => ?_)
    simp only [Set.mem_preimage]
    exact Scheme.Hom.fiberToSpecResidueField_apply f s x
  have : Finite (f ⁻¹' {s}) := (f.fiberHomeo s).finite_iff.mp this
  exact Set.toFinite _

/-- An affine open subset of a scheme proper over an affine base does not contain a whole
infinite fibre. -/
theorem exists_notMem_of_infinite_preimage [IsProper f] [IsAffine S] (s : S)
    (hs : ¬ (f ⁻¹' {s}).Finite) {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ x : X, f x = s ∧ x ∉ U := by
  by_contra hcon
  refine hs (finite_preimage_of_subset_isAffineOpen f s hU fun x hx => ?_)
  by_contra hxU
  exact hcon ⟨x, hx, hxU⟩

/-- In a scheme proper over an affine base all of whose fibres are infinite, every point is
avoided by a closed subset which surjects onto the base: the complement of any affine open
neighbourhood of the point.

This is the step the source takes when it passes from an affine open neighbourhood `U` of `x` to
the closed subset `T = X \ U` dominating the affine line. -/
theorem exists_isClosed_notMem_surjective [IsProper f] [IsAffine S]
    (hfibres : ∀ s : S, ¬ (f ⁻¹' {s}).Finite) (x : X) :
    ∃ T : Set X, IsClosed T ∧ x ∉ T ∧ ∀ s : S, ∃ y ∈ T, f y = s := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  refine ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl, by simpa using hxU, fun s => ?_⟩
  obtain ⟨y, hys, hyU⟩ := exists_notMem_of_infinite_preimage f s (hfibres s) hU
  exact ⟨y, hyU, hys⟩

/-- **The obstruction in Stacks 0D5E**: no *scheme* carries the geometry that the construction
of Stacks, Section 0D5D produces. Explicitly, there is no scheme `X` with a proper morphism
`f : X ⟶ S` to an affine base whose fibres are all infinite, together with a point `x` of `X`
such that no closed subset of `X` avoiding `x` surjects onto `S`.

The total space of the source's family satisfies the three hypotheses with `S = A¹_k`: it is
proper over the affine line with one-dimensional, hence infinite, fibres, and the point `x` to
which the strict transform of the central fibre is contracted is avoided by no dominating closed
subset. The complete statement of Stacks 0D5E, with the family constructed by Artin's
contraction, is `Stacks.Examples.CurveFamilyNotScheme.exists_curveFamily_total_not_scheme`
(`StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/Main.lean`), whose proof uses this
obstruction in the space-level form
`Stacks.Examples.CurveFamilyNotScheme.not_exists_iso_yoneda_of_transport`. -/
theorem not_exists_scheme_of_no_dominating_closed_avoiding (S : Scheme.{u}) [IsAffine S] :
    ¬ ∃ (X : Scheme.{u}) (f : X ⟶ S) (_ : IsProper f) (x : X),
        (∀ s : S, ¬ (f ⁻¹' {s}).Finite) ∧
          ∀ T : Set X, IsClosed T → x ∉ T → ∃ s : S, ∀ y ∈ T, f y ≠ s := by
  rintro ⟨X, f, hf, x, hfibres, hx⟩
  obtain ⟨T, hTclosed, hxT, hTsurj⟩ := exists_isClosed_notMem_surjective f hfibres x
  obtain ⟨s, hs⟩ := hx T hTclosed hxT
  obtain ⟨y, hyT, hys⟩ := hTsurj s
  exact hs y hyT hys

end Stacks.Examples.CurveFamilyNotScheme

end
