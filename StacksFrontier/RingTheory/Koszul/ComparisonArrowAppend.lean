module

public import StacksFrontier.RingTheory.Koszul.ComparisonArrowData

/-!
# The comparison data of a concatenated sequence

Let `g₁, …, g_p` and `h₁, …, h_s` be elements of a commutative ring `R` and let
`N ≥ n ≥ t ≥ 1`. Comparison data in the sense of `Koszul.KoszulArrowData` for the two sequences
assembles into comparison data for the concatenated sequence: the carrier is the tensor product
of the two carriers, and every structure map is the tensor product of the two structure maps,
read through the isomorphism
$$K_m(g_1, \ldots, g_p, h_1, \ldots, h_s) \cong K_m(g_1, \ldots, g_p) \otimes_R
  K_m(h_1, \ldots, h_s)$$
of Tag 0664. The homotopy retraction is the one of `Koszul.nonempty_koszulRetractData`, and the
identity `ε ∘ κ = τ_{N,t}` for the concatenation is exactly the statement that the append
isomorphism commutes with the transition homomorphisms,
`Koszul.powAppendFromTensor_powTensorTransition`.

The arrow `β` of the concatenation is obtained from the two arrows by the universal property of
the tensor product; the Koszul anticommutation hypothesis holds because the target
`K_n ⊗_R K_t` is graded commutative, both factors being exterior algebras.

## Main definitions

* `Koszul.appendBetaLeft` and `Koszul.appendBetaRight`: the two arms of `β`.
* `Koszul.appendBeta`, `Koszul.appendEps`, `Koszul.appendOddHom`, `Koszul.appendKappaOdd` and
  `Koszul.appendXiOdd`: the structure maps of the concatenation.
* `Koszul.KoszulArrowData.append`: the comparison data of the concatenated sequence.

## Main results

* `Koszul.powMul_comp_appendPairLeft` and `Koszul.powMul_comp_appendPairRight`: the
  multiplication map commutes with the two inclusions of pieces.
* `Koszul.appendEps_comp_appendKappa`, `Koszul.appendEps_comp_appendXi`,
  `Koszul.powMul_comp_appendBeta`, `Koszul.appendBeta_comp_appendKappa` and
  `Koszul.appendBeta_comp_appendXi`: the five identities of the comparison data, for the
  concatenation.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 0664](https://stacks.math.columbia.edu/tag/0664)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open scoped ExteriorAlgebra TensorProduct

open DifferentialGradedAlgebra DividedPowers.TateResolution

variable {R : Type u} [CommRing R] {p s n t N : ℕ}

section Multiplication

/-- The multiplication map commutes with a family of inclusions which commute with the
transition homomorphisms. -/
private theorem powMul_comp_tensorHomPair {q w : ℕ} {f : Fin q → R} {G : Fin w → R}
    (F : ∀ m, (powAlgebra f m).Hom (powAlgebra G m)) (ht : 1 ≤ t) (htn : t ≤ n)
    (hF : (powTransition G ht htn).toAlgebraHom.comp (F n).toAlgebraHom =
      (F t).toAlgebraHom.comp (powTransition f ht htn).toAlgebraHom) :
    (powMul G ht htn).toAlgebraHom.comp (tensorHomPair (F n) (F t)).toAlgebraHom =
      (F t).toAlgebraHom.comp (powMul f ht htn).toAlgebraHom := by
  refine GradedTensorProduct.algHom_ext (powAlgebra f n).grading (powAlgebra f t).grading ?_ ?_
  · refine AlgHom.ext fun a => ?_
    change (powMul G ht htn).toAlgebraHom
        ((tensorHomPair (F n) (F t)).toAlgebraHom
          (a ᵍ⊗ₜ[R] (1 : (powAlgebra f t).A) :
            (powAlgebra f n).grading ᵍ⊗[R] (powAlgebra f t).grading)) =
      (F t).toAlgebraHom ((powMul f ht htn).toAlgebraHom
        (a ᵍ⊗ₜ[R] (1 : (powAlgebra f t).A) :
          (powAlgebra f n).grading ᵍ⊗[R] (powAlgebra f t).grading))
    rw [tensorHomPair_tmul, map_one, powMul_tmul, powMul_tmul, mul_one, mul_one]
    exact AlgHom.congr_fun hF a
  · refine AlgHom.ext fun b => ?_
    change (powMul G ht htn).toAlgebraHom
        ((tensorHomPair (F n) (F t)).toAlgebraHom
          ((1 : (powAlgebra f n).A) ᵍ⊗ₜ[R] b :
            (powAlgebra f n).grading ᵍ⊗[R] (powAlgebra f t).grading)) =
      (F t).toAlgebraHom ((powMul f ht htn).toAlgebraHom
        ((1 : (powAlgebra f n).A) ᵍ⊗ₜ[R] b :
          (powAlgebra f n).grading ᵍ⊗[R] (powAlgebra f t).grading))
    rw [tensorHomPair_tmul, map_one, powMul_tmul, powMul_tmul, map_one, map_one, one_mul,
      one_mul]

/-- **The multiplication map commutes with the inclusion of the first piece.** -/
theorem powMul_comp_appendPairLeft (g : Fin p → R) (h : Fin s → R) (ht : 1 ≤ t) (htn : t ≤ n) :
    (powMul (Fin.append g h) ht htn).toAlgebraHom.comp
        (tensorHomPair (appendFromLeft g h n) (appendFromLeft g h t)).toAlgebraHom =
      (appendFromLeft g h t).toAlgebraHom.comp (powMul g ht htn).toAlgebraHom :=
  powMul_comp_tensorHomPair (appendFromLeft g h) ht htn
    (powTransition_comp_appendFromLeft g h ht htn)

/-- **The multiplication map commutes with the inclusion of the second piece.** -/
theorem powMul_comp_appendPairRight (g : Fin p → R) (h : Fin s → R) (ht : 1 ≤ t) (htn : t ≤ n) :
    (powMul (Fin.append g h) ht htn).toAlgebraHom.comp
        (tensorHomPair (appendFromRight g h n) (appendFromRight g h t)).toAlgebraHom =
      (appendFromRight g h t).toAlgebraHom.comp (powMul h ht htn).toAlgebraHom :=
  powMul_comp_tensorHomPair (appendFromRight g h) ht htn
    (powTransition_comp_appendFromRight g h ht htn)

end Multiplication

section Components

variable {ht : 1 ≤ t} {htn : t ≤ n} {hnN : n ≤ N}

/-- The left arm of the arrow `β` of a concatenated sequence. -/
def appendBetaLeft {g : Fin p → R} (h : Fin s → R)
    (D : KoszulArrowData g n t N ht htn hnN) :
    D.carrier.Hom
      (tensorProduct (powAlgebra (Fin.append g h) n) (powAlgebra (Fin.append g h) t)) :=
  (tensorHomPair (appendFromLeft g h n) (appendFromLeft g h t)).comp D.beta

/-- The right arm of the arrow `β` of a concatenated sequence. -/
def appendBetaRight (g : Fin p → R) {h : Fin s → R}
    (E : KoszulArrowData h n t N ht htn hnN) :
    E.carrier.Hom
      (tensorProduct (powAlgebra (Fin.append g h) n) (powAlgebra (Fin.append g h) t)) :=
  (tensorHomPair (appendFromRight g h n) (appendFromRight g h t)).comp E.beta

variable {g : Fin p → R} {h : Fin s → R} (D : KoszulArrowData g n t N ht htn hnN)
  (E : KoszulArrowData h n t N ht htn hnN)

/-- **The arrow `β` of a concatenated sequence.** -/
def appendBeta :
    (tensorProduct D.carrier E.carrier).Hom
      (tensorProduct (powAlgebra (Fin.append g h) n) (powAlgebra (Fin.append g h) t)) :=
  tensorLift (anticommutesAlong_of_isGradedCommutative
    (isGradedCommutative_powTensor (Fin.append g h) n t) (appendBetaLeft h D)
    (appendBetaRight g E))

/-- The arrow `β` of a concatenation restricts to its left arm. -/
theorem appendBeta_includeLeft (c : D.carrier.A) :
    (appendBeta D E).toAlgebraHom
        (GradedTensorProduct.includeLeft D.carrier.grading E.carrier.grading c) =
      (appendBetaLeft h D).toAlgebraHom c := by
  show tensorLiftAlgebraHom (anticommutesAlong_of_isGradedCommutative
    (isGradedCommutative_powTensor (Fin.append g h) n t) (appendBetaLeft h D)
    (appendBetaRight g E)) (c ᵍ⊗ₜ[R] (1 : E.carrier.A) :
      D.carrier.grading ᵍ⊗[R] E.carrier.grading) = _
  rw [tensorLiftAlgebraHom_tmul, map_one, mul_one]

/-- The arrow `β` of a concatenation restricts to its right arm. -/
theorem appendBeta_includeRight (e : E.carrier.A) :
    (appendBeta D E).toAlgebraHom
        (GradedTensorProduct.includeRight D.carrier.grading E.carrier.grading e) =
      (appendBetaRight g E).toAlgebraHom e := by
  show tensorLiftAlgebraHom (anticommutesAlong_of_isGradedCommutative
    (isGradedCommutative_powTensor (Fin.append g h) n t) (appendBetaLeft h D)
    (appendBetaRight g E)) ((1 : D.carrier.A) ᵍ⊗ₜ[R] e :
      D.carrier.grading ᵍ⊗[R] E.carrier.grading) = _
  rw [tensorLiftAlgebraHom_tmul, map_one, one_mul]

/-- The quasi-isomorphism `ε` of a concatenated sequence. -/
def appendEps :
    (tensorProduct D.carrier E.carrier).Hom (powAlgebra (Fin.append g h) t) :=
  (powAppendFromTensor g h t).comp (tensorHomPair D.eps E.eps)

/-- The inclusion of the odd part of a concatenated sequence. -/
def appendOddHom : (tensorProduct D.odd E.odd).Hom (tensorProduct D.carrier E.carrier) :=
  tensorHomPair D.oddHom E.oddHom

/-- The structure map `K_N → B` of a concatenated sequence, through the odd part. -/
def appendKappaOdd :
    (powAlgebra (Fin.append g h) N).Hom (tensorProduct D.odd E.odd) :=
  (tensorHomPair D.kappaOdd E.kappaOdd).comp (powAppendToTensor g h N)

/-- The section `K_t → B` of a concatenated sequence, through the odd part. -/
def appendXiOdd :
    (powAlgebra (Fin.append g h) t).Hom (tensorProduct D.odd E.odd) :=
  (tensorHomPair D.xiOdd E.xiOdd).comp (powAppendToTensor g h t)

end Components

section Identities

variable {ht : 1 ≤ t} {htn : t ≤ n} {hnN : n ≤ N} {g : Fin p → R} {h : Fin s → R}
  (D : KoszulArrowData g n t N ht htn hnN) (E : KoszulArrowData h n t N ht htn hnN)

/-- The comparison `ε` of a concatenation, after the odd part and a tensor product of maps out
of the exponent-`m` algebras, is the append isomorphism after the tensor product of the
composites. -/
private theorem appendEps_comp_apply_tensorHomPair (m : ℕ) (u : (powAlgebra g m).Hom D.odd)
    (v : (powAlgebra h m).Hom E.odd) (a : (powAlgebra (Fin.append g h) m).A) :
    (appendEps D E).toAlgebraHom ((appendOddHom D E).toAlgebraHom
        ((tensorHomPair u v).toAlgebraHom ((powAppendToTensor g h m).toAlgebraHom a))) =
      (powAppendFromTensor g h t).toAlgebraHom
        ((tensorHomPair (D.eps.comp (D.oddHom.comp u)) (E.eps.comp (E.oddHom.comp v))).toAlgebraHom
          ((powAppendToTensor g h m).toAlgebraHom a)) := by
  rw [← tensorHomPair_comp_tensorHomPair, ← tensorHomPair_comp_tensorHomPair]
  rfl

/-- **`ε ∘ κ` is the transition homomorphism, for a concatenated sequence.** This is the step
which needs the append isomorphism to commute with the transition homomorphisms. -/
theorem appendEps_comp_appendKappa :
    ((appendEps D E).comp ((appendOddHom D E).comp (appendKappaOdd D E))).toAlgebraHom =
      (powTransition (Fin.append g h) ht (htn.trans hnN)).toAlgebraHom :=
  AlgHom.ext fun a =>
    (appendEps_comp_apply_tensorHomPair D E N D.kappaOdd E.kappaOdd a).trans <| by
      rw [tensorHomPair_eq_of_eq D.eps_kappa E.eps_kappa]
      exact powAppendFromTensor_powTensorTransition_apply g h ht (htn.trans hnN) a

/-- **`ε ∘ ξ` is the identity, for a concatenated sequence.** -/
theorem appendEps_comp_appendXi :
    ((appendEps D E).comp ((appendOddHom D E).comp (appendXiOdd D E))).toAlgebraHom =
      AlgHom.id R (powAlgebra (Fin.append g h) t).A :=
  AlgHom.ext fun a =>
    (appendEps_comp_apply_tensorHomPair D E t D.xiOdd E.xiOdd a).trans <| by
      rw [tensorHomPair_eq_id D.eps_xi E.eps_xi]
      exact congrArg (fun φ => φ a) (powAppendFromTensor_powAppendToTensor g h t)

/-- The multiplication map after an arrow `β` and a pair of inclusions compatible with it. -/
private theorem powMul_apply_tensorHomPair_beta {q w : ℕ} {f : Fin q → R} {G : Fin w → R}
    (F : ∀ m, (powAlgebra f m).Hom (powAlgebra G m)) (ht : 1 ≤ t) (htn : t ≤ n)
    (hF : (powMul G ht htn).toAlgebraHom.comp (tensorHomPair (F n) (F t)).toAlgebraHom =
      (F t).toAlgebraHom.comp (powMul f ht htn).toAlgebraHom)
    {A : DifferentialGradedAlgebra R} (ε : A.Hom (powAlgebra f t))
    (β : A.Hom (tensorProduct (powAlgebra f n) (powAlgebra f t)))
    (hβ : ((powMul f ht htn).comp β).toAlgebraHom = ε.toAlgebraHom) (c : A.A) :
    (powMul G ht htn).toAlgebraHom ((tensorHomPair (F n) (F t)).toAlgebraHom (β.toAlgebraHom c)) =
      (F t).toAlgebraHom (ε.toAlgebraHom c) := by
  rw [← AlgHom.comp_apply, hF, AlgHom.comp_apply]
  exact congrArg (F t).toAlgebraHom (AlgHom.congr_fun hβ c)

/-- **`μ_n ∘ β` is `ε`, for a concatenated sequence.** -/
theorem powMul_comp_appendBeta :
    ((powMul (Fin.append g h) ht htn).comp (appendBeta D E)).toAlgebraHom =
      (appendEps D E).toAlgebraHom := by
  refine GradedTensorProduct.algHom_ext D.carrier.grading E.carrier.grading ?_ ?_
  · refine AlgHom.ext fun c => ?_
    have hleft : (powMul (Fin.append g h) ht htn).toAlgebraHom
        ((appendBeta D E).toAlgebraHom
          (GradedTensorProduct.includeLeft D.carrier.grading E.carrier.grading c)) =
        (appendFromLeft g h t).toAlgebraHom (D.eps.toAlgebraHom c) :=
      (congrArg _ (appendBeta_includeLeft D E c)).trans
        (powMul_apply_tensorHomPair_beta (appendFromLeft g h) ht htn
          (powMul_comp_appendPairLeft g h ht htn) D.eps D.beta D.mul_beta c)
    have hright : (appendEps D E).toAlgebraHom
        (GradedTensorProduct.includeLeft D.carrier.grading E.carrier.grading c) =
        (appendFromLeft g h t).toAlgebraHom (D.eps.toAlgebraHom c) := by
      show (powAppendFromTensor g h t).toAlgebraHom
        ((tensorHomPair D.eps E.eps).toAlgebraHom
          (c ᵍ⊗ₜ[R] (1 : E.carrier.A) : D.carrier.grading ᵍ⊗[R] E.carrier.grading)) = _
      rw [tensorHomPair_tmul, map_one, powAppendFromTensor_tmul, map_one, mul_one]
    simp only [AlgHom.comp_apply, Hom.comp_toAlgebraHom]
    rw [hleft, hright]
  · refine AlgHom.ext fun e => ?_
    have hleft : (powMul (Fin.append g h) ht htn).toAlgebraHom
        ((appendBeta D E).toAlgebraHom
          (GradedTensorProduct.includeRight D.carrier.grading E.carrier.grading e)) =
        (appendFromRight g h t).toAlgebraHom (E.eps.toAlgebraHom e) :=
      (congrArg _ (appendBeta_includeRight D E e)).trans
        (powMul_apply_tensorHomPair_beta (appendFromRight g h) ht htn
          (powMul_comp_appendPairRight g h ht htn) E.eps E.beta E.mul_beta e)
    have hright : (appendEps D E).toAlgebraHom
        (GradedTensorProduct.includeRight D.carrier.grading E.carrier.grading e) =
        (appendFromRight g h t).toAlgebraHom (E.eps.toAlgebraHom e) := by
      show (powAppendFromTensor g h t).toAlgebraHom
        ((tensorHomPair D.eps E.eps).toAlgebraHom
          ((1 : D.carrier.A) ᵍ⊗ₜ[R] e : D.carrier.grading ᵍ⊗[R] E.carrier.grading)) = _
      rw [tensorHomPair_tmul, map_one, powAppendFromTensor_tmul, map_one, one_mul]
    simp only [AlgHom.comp_apply, Hom.comp_toAlgebraHom]
    rw [hleft, hright]

end Identities

section Pieces

variable {ht : 1 ≤ t} {htn : t ≤ n} {hnN : n ≤ N} {g : Fin p → R} {h : Fin s → R}
  (D : KoszulArrowData g n t N ht htn hnN) (E : KoszulArrowData h n t N ht htn hnN)

/-- The inclusion of the odd part of a concatenation, on a sum of the two inclusions. -/
theorem appendOddHom_add_include (x : D.odd.A) (y : E.odd.A) :
    (appendOddHom D E).toAlgebraHom
        (GradedTensorProduct.includeLeft D.odd.grading E.odd.grading x +
          GradedTensorProduct.includeRight D.odd.grading E.odd.grading y) =
      GradedTensorProduct.includeLeft D.carrier.grading E.carrier.grading
          (D.oddHom.toAlgebraHom x) +
        GradedTensorProduct.includeRight D.carrier.grading E.carrier.grading
          (E.oddHom.toAlgebraHom y) := by
  show (tensorHomPair D.oddHom E.oddHom).toAlgebraHom
    (GradedTensorProduct.includeLeft D.odd.grading E.odd.grading x +
      GradedTensorProduct.includeRight D.odd.grading E.odd.grading y) = _
  rw [map_add, tensorHomPair_includeLeft, tensorHomPair_includeRight]

/-- The arrow `β` of a concatenation, on a sum of the two inclusions. -/
theorem appendBeta_add_include (c : D.carrier.A) (e : E.carrier.A) :
    (appendBeta D E).toAlgebraHom
        (GradedTensorProduct.includeLeft D.carrier.grading E.carrier.grading c +
          GradedTensorProduct.includeRight D.carrier.grading E.carrier.grading e) =
      (appendBetaLeft h D).toAlgebraHom c + (appendBetaRight g E).toAlgebraHom e := by
  rw [map_add, appendBeta_includeLeft, appendBeta_includeRight]

/-- A tensor product of two homomorphisms after the append isomorphism, on a generator. -/
private theorem tensorHomPair_powAppendToTensor_powVec {A B : DifferentialGradedAlgebra R}
    (g : Fin p → R) (h : Fin s → R) (m : ℕ) (u : (powAlgebra g m).Hom A)
    (v : (powAlgebra h m).Hom B) (x : Fin (p + s) → R) :
    (tensorHomPair u v).toAlgebraHom
        ((powAppendToTensor g h m).toAlgebraHom (powVec (Fin.append g h) m x)) =
      GradedTensorProduct.includeLeft A.grading B.grading
          (u.toAlgebraHom (powVec g m (coordLeft R p s x))) +
        GradedTensorProduct.includeRight A.grading B.grading
          (v.toAlgebraHom (powVec h m (coordRight R p s x))) := by
  rw [powAppendToTensor_powVec, map_add,
    show appendTensorLeft g h m x =
      GradedTensorProduct.includeLeft (powAlgebra g m).grading (powAlgebra h m).grading
        (powVec g m (coordLeft R p s x)) from rfl,
    show appendTensorRight g h m x =
      GradedTensorProduct.includeRight (powAlgebra g m).grading (powAlgebra h m).grading
        (powVec h m (coordRight R p s x)) from rfl,
    tensorHomPair_includeLeft, tensorHomPair_includeRight]

/-- The structure map `K_N → B` of a concatenation, on a generator. -/
theorem appendKappaOdd_powVec (v : Fin (p + s) → R) :
    (appendKappaOdd D E).toAlgebraHom (powVec (Fin.append g h) N v) =
      GradedTensorProduct.includeLeft D.odd.grading E.odd.grading
          (D.kappaOdd.toAlgebraHom (powVec g N (coordLeft R p s v))) +
        GradedTensorProduct.includeRight D.odd.grading E.odd.grading
          (E.kappaOdd.toAlgebraHom (powVec h N (coordRight R p s v))) :=
  tensorHomPair_powAppendToTensor_powVec g h N D.kappaOdd E.kappaOdd v

/-- The section `K_t → B` of a concatenation, on a generator. -/
theorem appendXiOdd_powVec (v : Fin (p + s) → R) :
    (appendXiOdd D E).toAlgebraHom (powVec (Fin.append g h) t v) =
      GradedTensorProduct.includeLeft D.odd.grading E.odd.grading
          (D.xiOdd.toAlgebraHom (powVec g t (coordLeft R p s v))) +
        GradedTensorProduct.includeRight D.odd.grading E.odd.grading
          (E.xiOdd.toAlgebraHom (powVec h t (coordRight R p s v))) :=
  tensorHomPair_powAppendToTensor_powVec g h t D.xiOdd E.xiOdd v

/-- The left arm of `β`, on the image of `K_N`. -/
theorem appendBetaLeft_kappa (x : (powAlgebra g N).A) :
    (appendBetaLeft h D).toAlgebraHom (D.oddHom.toAlgebraHom (D.kappaOdd.toAlgebraHom x)) =
      GradedTensorProduct.includeLeft (powAlgebra (Fin.append g h) n).grading
          (powAlgebra (Fin.append g h) t).grading
        ((appendFromLeft g h n).toAlgebraHom
          ((powTransition g (ht.trans htn) hnN).toAlgebraHom x)) :=
  (congrArg (tensorHomPair (appendFromLeft g h n) (appendFromLeft g h t)).toAlgebraHom
    (AlgHom.congr_fun D.beta_kappa x)).trans (tensorHomPair_includeLeft _ _ _)

/-- The right arm of `β`, on the image of `K_N`. -/
theorem appendBetaRight_kappa (y : (powAlgebra h N).A) :
    (appendBetaRight g E).toAlgebraHom (E.oddHom.toAlgebraHom (E.kappaOdd.toAlgebraHom y)) =
      GradedTensorProduct.includeLeft (powAlgebra (Fin.append g h) n).grading
          (powAlgebra (Fin.append g h) t).grading
        ((appendFromRight g h n).toAlgebraHom
          ((powTransition h (ht.trans htn) hnN).toAlgebraHom y)) :=
  (congrArg (tensorHomPair (appendFromRight g h n) (appendFromRight g h t)).toAlgebraHom
    (AlgHom.congr_fun E.beta_kappa y)).trans (tensorHomPair_includeLeft _ _ _)

/-- The left arm of `β`, on the image of `K_t`. -/
theorem appendBetaLeft_xi (x : (powAlgebra g t).A) :
    (appendBetaLeft h D).toAlgebraHom (D.oddHom.toAlgebraHom (D.xiOdd.toAlgebraHom x)) =
      GradedTensorProduct.includeRight (powAlgebra (Fin.append g h) n).grading
          (powAlgebra (Fin.append g h) t).grading
        ((appendFromLeft g h t).toAlgebraHom x) :=
  (congrArg (tensorHomPair (appendFromLeft g h n) (appendFromLeft g h t)).toAlgebraHom
    (AlgHom.congr_fun D.beta_xi x)).trans (tensorHomPair_includeRight _ _ _)

/-- The right arm of `β`, on the image of `K_t`. -/
theorem appendBetaRight_xi (y : (powAlgebra h t).A) :
    (appendBetaRight g E).toAlgebraHom (E.oddHom.toAlgebraHom (E.xiOdd.toAlgebraHom y)) =
      GradedTensorProduct.includeRight (powAlgebra (Fin.append g h) n).grading
          (powAlgebra (Fin.append g h) t).grading
        ((appendFromRight g h t).toAlgebraHom y) :=
  (congrArg (tensorHomPair (appendFromRight g h n) (appendFromRight g h t)).toAlgebraHom
    (AlgHom.congr_fun E.beta_xi y)).trans (tensorHomPair_includeRight _ _ _)

end Pieces

section Remaining

variable {ht : 1 ≤ t} {htn : t ≤ n} {hnN : n ≤ N} {g : Fin p → R} {h : Fin s → R}
  (D : KoszulArrowData g n t N ht htn hnN) (E : KoszulArrowData h n t N ht htn hnN)

/-- **`β ∘ κ` is the first inclusion after the transition homomorphism, for a concatenated
sequence.** -/
theorem appendBeta_comp_appendKappa :
    ((appendBeta D E).comp ((appendOddHom D E).comp (appendKappaOdd D E))).toAlgebraHom =
      (GradedTensorProduct.includeLeft (powAlgebra (Fin.append g h) n).grading
          (powAlgebra (Fin.append g h) t).grading).comp
        (powTransition (Fin.append g h) (ht.trans htn) hnN).toAlgebraHom := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  show (appendBeta D E).toAlgebraHom ((appendOddHom D E).toAlgebraHom
      ((appendKappaOdd D E).toAlgebraHom (powVec (Fin.append g h) N v))) =
    GradedTensorProduct.includeLeft (powAlgebra (Fin.append g h) n).grading
        (powAlgebra (Fin.append g h) t).grading
      ((powTransition (Fin.append g h) (ht.trans htn) hnN).toAlgebraHom
        (powVec (Fin.append g h) N v))
  rw [appendKappaOdd_powVec, appendOddHom_add_include, appendBeta_add_include,
    appendBetaLeft_kappa, appendBetaRight_kappa, ← map_add, powTransition_powVec,
    powTransition_powVec, powTransition_powVec, appendFromLeft_powVec,
    appendFromRight_powVec, ← map_add, append_zero_add_zero_append, append_mulLeft_pow]

/-- **`β ∘ ξ` is the second inclusion, for a concatenated sequence.** -/
theorem appendBeta_comp_appendXi :
    ((appendBeta D E).comp ((appendOddHom D E).comp (appendXiOdd D E))).toAlgebraHom =
      GradedTensorProduct.includeRight (powAlgebra (Fin.append g h) n).grading
        (powAlgebra (Fin.append g h) t).grading := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  show (appendBeta D E).toAlgebraHom ((appendOddHom D E).toAlgebraHom
      ((appendXiOdd D E).toAlgebraHom (powVec (Fin.append g h) t v))) =
    GradedTensorProduct.includeRight (powAlgebra (Fin.append g h) n).grading
        (powAlgebra (Fin.append g h) t).grading (powVec (Fin.append g h) t v)
  rw [appendXiOdd_powVec, appendOddHom_add_include, appendBeta_add_include,
    appendBetaLeft_xi, appendBetaRight_xi, ← map_add, appendFromLeft_powVec,
    appendFromRight_powVec, ← map_add, append_zero_add_zero_append,
    append_coordLeft_coordRight]

namespace KoszulArrowData

/-- **The comparison data of a concatenated sequence is the tensor product of the data of the
two pieces.** -/
def append : KoszulArrowData (Fin.append g h) n t N ht htn hnN where
  carrier := tensorProduct D.carrier E.carrier
  eps := appendEps D E
  retract := (powAppendRetract g h t).comp
    ((D.retract.tensorLeft (powAlgebra h t)).comp (E.retract.tensorRight D.carrier))
  odd := tensorProduct D.odd E.odd
  oddComm := isGradedCommutative_tensorProduct D.odd E.odd D.oddComm E.oddComm
  oddHom := appendOddHom D E
  kappaOdd := appendKappaOdd D E
  xiOdd := appendXiOdd D E
  beta := appendBeta D E
  eps_kappa := appendEps_comp_appendKappa D E
  eps_xi := appendEps_comp_appendXi D E
  mul_beta := powMul_comp_appendBeta D E
  beta_kappa := appendBeta_comp_appendKappa D E
  beta_xi := appendBeta_comp_appendXi D E

end KoszulArrowData

end Remaining

end Koszul
