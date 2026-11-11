module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDiagonal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassCupVanishing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimension
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalConormalClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupRelation
public import StacksCore.Tactic.StacksAttribute

/-!
# The identity `γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a`

The proof of Lemma 0FIJ, and through it Remark 0FIK, rests on the identity
`γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a` in `H^*(X × X)(d)` for `X` equidimensional of dimension `d`:
the classes `p₁^*a` and `p₂^*a` agree on `Δ`, so Lemma 0FII applies to their difference. This
file turns a vanishing `γ([Δ]) ∪ (p₁^*a - p₂^*a) = 0` into the form consumed by
`Stacks.WeilCohomology.FirstChernClassData.trace_unique_of_key`, and proves it in dimension `0`,
where `Δ` is open and closed (the diagonal of an étale morphism).

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.isOpenImmersion_diag_of_relativeDimension_zero`
* `Stacks.WeilCohomology.FirstChernClassData.key_of_cup_eq_zero`
* `perfectDuality_diagonalClass_and_existsUnique_trace` (Remark 0FIK), `trace_unique`,
  `bijective_diagonalContract`, `key_diagonalClass`,
  `key_of_relativeDimension_zero` (namespace
  `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace SmoothProjectiveScheme

/-- **The diagonal of `X` is an open immersion when `X` has dimension `0`**: `X ⟶ Spec k` is then
smooth of relative dimension `0`, that is étale, hence unramified. -/
theorem isOpenImmersion_diag_of_relativeDimension_zero
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (h : RelativeDimension X.obj.hom 0) : IsOpenImmersion (diag X).hom.left := by
  have : Smooth X.obj.hom := SmoothProjectiveScheme.smooth X
  have : SmoothOfRelativeDimension 0 X.obj.hom :=
    Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq X.obj.hom 0
      ((relativeDimension_iff_forall_topologicalKrullDimAt X.obj.hom 0).mp h)
  have : Etale X.obj.hom := (Etale.iff_smoothOfRelativeDimension_zero X.obj.hom).mpr inferInstance
  exact Unramified.isOpenImmersion_diagonal X.obj.hom

end SmoothProjectiveScheme

namespace FirstChernClassData

open SmoothProjectiveScheme

variable {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- An element of even degree `2d` commutes with every element. -/
theorem mul_comm_of_mem_grade_two_mul (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    {x : 𝔇.H X}
    (hx : x ∈ 𝔇.grade X (2 * (d : ℤ))) (y : 𝔇.H X) : x * y = y * x := by
  induction y using DirectSum.Decomposition.inductionOn (𝔇.grade X) with
  | zero => simp
  | @homogeneous j y =>
    rw [𝔇.graded_comm X _ _ x _ hx y.2]
    have : Int.negOnePow (2 * (d : ℤ) * j) = 1 := by
      rw [Int.negOnePow_eq_one_iff]
      exact ⟨(d : ℤ) * j, by ring⟩
    rw [this]
    simp
  | add y y' h h' => rw [mul_add, add_mul, h, h']

/-- A class in the image of `H^{2d}(X × X)(d)` has untwisted class of degree `2d`. -/
theorem untwistClass_mem_of_mem_range (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    {g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d}
    (hg : g ∈ LinearMap.range (tateTwistMap (L := 𝔇.tate)
      (𝔇.grade (prod X X) (2 * (d : ℤ))).subtype d)) :
    𝔇.untwistClass X d g ∈ 𝔇.grade (prod X X) (2 * (d : ℤ)) := by
  obtain ⟨y, rfl⟩ := hg
  rw [untwistClass, κ, tateTwistCoordinates_map]
  exact Submodule.coe_mem _

/-- `p₁^*a` and `p₂^*a` agree on the diagonal. -/
theorem pull_diag_sub_eq_zero (X : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X) :
    𝔇.pull (diag X) (𝔇.pull (fst X X) a - 𝔇.pull (snd X X) a) = 0 := by
  rw [map_sub, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← 𝔇.pull_comp, ← 𝔇.pull_comp, diag_fst,
    diag_snd, sub_self]

/-- **From `γ([Δ]) ∪ (p₁^*a - p₂^*a) = 0` to the identity of Lemma 0FIJ**, in the form
`η ∪ p₁^*a = η ∪ p₂^*a` for the untwisted class `η = κ(g)` of `g ∈ H^{2d}(X × X)(d)`. -/
theorem key_of_cup_eq_zero (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d)
    (hg : 𝔇.untwistClass X d g ∈ 𝔇.grade (prod X X) (2 * (d : ℤ)))
    (hvan : ∀ a : 𝔇.H X,
      tateCupLeft (𝔇.cup (prod X X)) d (𝔇.pull (fst X X) a - 𝔇.pull (snd X X) a) g = 0)
    (a : 𝔇.H X) :
    𝔇.untwistClass X d g * 𝔇.pull (fst X X) a = 𝔇.untwistClass X d g * 𝔇.pull (snd X X) a := by
  have h := congrArg (𝔇.κ (prod X X) d) (hvan a)
  rw [κ, tateTwistCoordinates_tateCupLeft, map_zero, LinearMap.mul_apply', sub_mul,
    sub_eq_zero] at h
  rw [𝔇.mul_comm_of_mem_grade_two_mul _ d hg, 𝔇.mul_comm_of_mem_grade_two_mul _ d hg]
  exact h

namespace IsCohomologicalChernCharacter

variable {𝔇} [CharZero F]
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch)

/-- The untwisted class of `γ([Δ])` has degree `2d`. -/
private theorem untwistClass_diagonalClass_mem (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) ∈
      𝔇.grade (prod X X) (2 * (d : ℤ)) :=
  𝔇.untwistClass_mem_of_mem_range X _ (h.codimensionCycleClass_mem hA1 hA3 _ _ _)

/-- **The identity `γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a` in dimension `0`**, where the diagonal is
open and closed, from (A1). -/
theorem key_of_relativeDimension_zero (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (hX : RelativeDimension X.obj.hom 0) (a : 𝔇.H X) :
    𝔇.untwistClass X 0 (h.codimensionCycleClass (prod X X) 0 (diagonalClass X 0)) *
        𝔇.pull (fst X X) a =
      𝔇.untwistClass X 0 (h.codimensionCycleClass (prod X X) 0 (diagonalClass X 0)) *
        𝔇.pull (snd X X) a := by
  have := isOpenImmersion_diag_of_relativeDimension_zero X hX
  refine 𝔇.key_of_cup_eq_zero X 0 _ ?_ (fun b ↦ ?_) a
  · exact h.untwistClass_diagonalClass_mem hA1 hA3 X 0
  · exact h.cup_codimensionCycleClass_eq_zero_of_isOpenImmersion hA1 (diag X) _
      (𝔇.pull_diag_sub_eq_zero X b)

/-- **The identity `γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a` in dimension `d = 1 + s`**, granted the
first relation `b^![Δ] = [E] · θ` of Lemma 0FIH for the blowing up of `X × X` in the diagonal:
Lemma 0FII for `Z = Δ`, the diagonal being nowhere dense. -/
theorem key_of_blowup_relation (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory)
        (d s : ℕ)
    (hd : d = 1 + s) (hX : RelativeDimension X.obj.hom d)
    (θ : codimensionChowGroup k (blowupObj (diag X)).obj.hom s)
    (hrel : codimensionGysin (blowupObj (diag X)).obj.hom (prod X X).obj.hom
        (SmoothProjectiveScheme.w (blowupHom (diag X))) (d : ℤ)
        (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left (d : ℤ)) ≍
      codimensionIntersectionProduct k (blowupObj (diag X)).obj.hom 1 s
        (closedSubschemeClass (blowupObj (diag X)).obj.hom (exceptionalHom (diag X)).hom.left 1) θ)
    (a : 𝔇.H X) :
    𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) *
        𝔇.pull (fst X X) a =
      𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) *
        𝔇.pull (snd X X) a := by
  refine 𝔇.key_of_cup_eq_zero X d _
    (h.untwistClass_diagonalClass_mem hA1 hA3 X _)
    (fun b ↦ ?_) a
  exact h.cup_codimensionCycleClass_eq_zero_of_blowup hA1 hA3 hA4 hA7 (diag X)
    (isNowhereDense_range_diag X hX (by omega)) d s hd θ hrel _ (𝔇.pull_diag_sub_eq_zero X b)

/-- **The identity `γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a`** of the proof of Lemma 0FIJ, for `X`
nonempty and equidimensional of dimension `d`, from (A1), (A3), (A4) and (A7). In dimension `0`
the diagonal is open and closed (`key_of_relativeDimension_zero`). In dimension `d ≥ 1` the
diagonal is nowhere dense of codimension `d` in `X × X`, its conormal sheaf `Ω_X` is the
restriction of `p₁^*Ω_X`, and Lemma 0FIH gives `b^![Δ] = [E] · θ` for the blowing up of `X × X`
in `Δ` (`codimensionGysin_closedSubschemeClass_heq_blowupTheta`), so Lemma 0FII applies to
`p₁^*a - p₂^*a`, which vanishes on `Δ`. -/
theorem key_diagonalClass (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory)
        (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (a : 𝔇.H X) :
    𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) *
        𝔇.pull (fst X X) a =
      𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) *
        𝔇.pull (snd X X) a := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact h.key_of_relativeDimension_zero hA1 hA3 X hX.relativeDimension a
  obtain ⟨α, hα⟩ := exists_pullback_diag_eq_classOf_centreConormal X
  have hrel := codimensionGysin_closedSubschemeClass_heq_blowupTheta (diag X)
    (isNonemptyEquidimensional_prod hX hX).relativeDimension hX.relativeDimension rfl hd α hα
  exact h.key_of_blowup_relation hA1 hA3 hA4 hA7 X d (d - 1) (by omega) hX.relativeDimension
    (blowupTheta (diag X) α d) hrel a

/-- **Uniqueness of the trace map**, the second assertion of Remark 0FIK
(`perfectDuality_diagonalClass_and_existsUnique_trace`). Let (D0), (D1), (D2') satisfy
(A1)–(A7), with `γ` the cycle class map of Tag 0FIF, and let `X` be a nonempty smooth projective
scheme over `k`, equidimensional of dimension `d`. Then a linear map `λ : H^{2d}(X)(d) ⟶ F` with
`(1 ⊗ λ)γ([Δ]) = 1` as in axiom (A6) is unique.

The axioms used are (A1), (A3), (A4), (A5) and (A7), through the identity
`γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a` (`key_diagonalClass`); (A2) enters through `γ` itself. -/
theorem trace_unique (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom) (hA7 : 𝔇.BlowupAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) (hX : IsNonemptyEquidimensional X d)
    (lam lam' : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam : 𝔇.traceContract hA5 X d lam
      (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) = 1)
    (hlam' : 𝔇.traceContract hA5 X d lam'
      (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) = 1) :
    lam = lam' :=
  𝔇.trace_unique_of_key hA5 X d _
    (h.untwistClass_diagonalClass_mem hA1 hA3 X _)
    (h.key_diagonalClass hA1 hA3 hA4 hA7 X d hX) lam lam' hlam hlam'

/-- **`γ([Δ])` defines a perfect duality**, the first assertion of Remark 0FIK
(`perfectDuality_diagonalClass_and_existsUnique_trace`), between `H^i(X)` and
`H^{2d-i}(X)(d)`. Let (D0), (D1), (D2') satisfy (A1)–(A7), with `γ` the cycle class map of Tag
0FIF, and let `X` be a nonempty smooth projective scheme over `k`, equidimensional of dimension
`d`. For `i + j = 2d`, contraction against the `(i, j)` Künneth component of `γ([Δ])`,
`μ ↦ (1 ⊗ μ)γ([Δ])_{i,j}`, is a bijection `(H^j(X)(d))^* ⟶ H^i(X)`. -/
theorem bijective_diagonalContract (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom)
    (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass) (hA7 : 𝔇.BlowupAxiom)
        (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) {i j : ℤ} (hij : i + j = 2 * (d : ℤ)) :
    Function.Bijective (𝔇.diagonalContract hA5 X d
      (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) i j) := by
  obtain ⟨lam, hlam⟩ := hA6 X d hX
  exact 𝔇.bijective_diagonalContract_of_key hA5 X d _
    (h.untwistClass_diagonalClass_mem hA1 hA3 X _)
    (h.key_diagonalClass hA1 hA3 hA4 hA7 X d hX) lam hlam hij

/-- **Stacks Project, Remark 0FIK: uniqueness of trace maps.** Let (D0), (D1), (D2') satisfy
(A1)–(A7), with `γ` the cycle class map of Tag 0FIF, and let `X` be a nonempty smooth projective
scheme over `k`, equidimensional of dimension `d`. Then:

* `γ([Δ]) ∈ ⨁_i H^i(X) ⊗ H^{2d-i}(X)(d)` defines a perfect duality between `H^i(X)` and
  `H^{2d-i}(X)(d)` for all `i`: both are finite dimensional, and contraction against the
  `(i, 2d-i)` Künneth component of `γ([Δ])`, `μ ↦ (1 ⊗ μ)γ([Δ])_{i,2d-i}`, is a bijection
  `(H^{2d-i}(X)(d))^* ⟶ H^i(X)`;
* the linear map `∫_X = λ : H^{2d}(X)(d) ⟶ F` of axiom (A6), normalised by
  `(1 ⊗ λ)γ([Δ]) = 1`, exists and is unique.

The proof is the remark's: the left-dual structure of Lemma 0FIJ, through the identity
`γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a` (`key_diagonalClass`), and the linear algebra of Tag 0FFV
(`...Concrete.DiagonalExpansion`). Axiom (A2) enters only through `γ`. -/
@[stacks 0FIK "for X nonempty smooth projective equidimensional of dimension d and data \
satisfying (A1)-(A7): γ([Δ]) defines a perfect duality between H^i(X) and H^{2d-i}(X)(d) for \
all i (both finite dimensional, contraction (H^{2d-i}(X)(d))^* → H^i(X) bijective), and the \
trace map λ of (A6) is unique"]
theorem perfectDuality_diagonalClass_and_existsUnique_trace (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom)
    (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass) (hA7 : 𝔇.BlowupAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    (∀ i j : ℤ, i + j = 2 * (d : ℤ) →
      FiniteDimensional F (𝔇.grade X i) ∧
        FiniteDimensional F (tateTwist F 𝔇.tate (𝔇.grade X j) d) ∧
        Function.Bijective (𝔇.diagonalContract hA5 X d
          (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) i j)) ∧
      ∃! lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F,
        𝔇.traceContract hA5 X d lam
          (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) = 1 := by
  obtain ⟨lam, hlam⟩ := hA6 X d hX
  obtain ⟨l, hD⟩ := 𝔇.exists_diagonalData hA5 X d _
    (h.untwistClass_diagonalClass_mem hA1 hA3 X _) lam hlam
    (h.key_diagonalClass hA1 hA3 hA4 hA7 X d hX)
  have : FiniteDimensional F (𝔇.H X) := DiagonalExpansion.finiteDimensional hD
  refine ⟨fun i j hij ↦ ⟨inferInstance, ?_,
    h.bijective_diagonalContract hA1 hA3 hA4 hA5 hA6 hA7 X d hX hij⟩,
    ⟨lam, hlam, fun lam' hlam' ↦ h.trace_unique hA1 hA3 hA4 hA5 hA7 X d hX lam' lam hlam' hlam⟩⟩
  exact LinearEquiv.finiteDimensional
    (tateTwistCoordinates (V := 𝔇.grade X j) 𝔇.coord (d : ℤ)).symm

end IsCohomologicalChernCharacter

end FirstChernClassData

end Stacks.WeilCohomology

end
