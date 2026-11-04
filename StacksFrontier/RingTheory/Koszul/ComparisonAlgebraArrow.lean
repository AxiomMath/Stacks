module

public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraOverKoszul
public import StacksFrontier.RingTheory.Koszul.PowPairTensorIsomorphism

/-!
# The arrow from `R⟨x, z, u⟩` to the tensor product `K_n ⊗_R K_t`

Let `f` be an element of a commutative ring `R` and let `1 ≤ t ≤ n` with `n + t ≤ N`. The
algebra `B_{N,t} = R⟨x, z, u⟩` of `Koszul.comparisonAlgebra` maps to the Koszul algebra
`K_{n,t} = R⟨y, x⟩` of the pair `(f^n, f^t)` by `Koszul.comparisonToPowPair`, and `K_{n,t}` is
the tensor product `K_n ⊗_R K_t` of two one-variable Koszul algebras by
`Koszul.powPairToTensor`. Composing the two produces **the arrow `β` of Tag 0GZ7**
$$\beta : B_{N,t} \longrightarrow K_n \otimes_R K_t, \qquad
  x \longmapsto 1 \otimes \xi, \qquad z \longmapsto f^{N-n}\,(\xi \otimes 1),$$
recorded here as `Koszul.comparisonToTensor`.

The content of this file is the "pleasant computation" of Tag 0GZ7, namely that `β` is
compatible with the three structural maps already available:

* composed with the multiplication map `μ_n : K_n ⊗_R K_t → K_t` of `Koszul.powMul` it is the
  comparison homomorphism `ε : B_{N,t} → K_t` of `Koszul.comparisonToKoszul`;
* restricted along the homomorphism `κ : K_N → B_{N,t}` of `Koszul.koszulToComparison`, which
  sends the generator of `K_N` to `z`, it is the inclusion of the left tensor factor composed
  with the transition homomorphism `τ_{N,n} : K_N → K_n`;
* restricted along the homomorphism `ξ : K_t → B_{N,t}` sending the generator of `K_t` to `x`,
  it is the inclusion of the right tensor factor.

The `x`-side homomorphism `ξ : K_t → B_{N,t}` is built here, mirroring the `z`-side
homomorphism `κ` of `StacksFrontier/RingTheory/Koszul/ComparisonAlgebraOverKoszul.lean`: the
functional `x ↦ f^t`, `z ↦ f^N` of the odd part `R⟨x, z⟩` pulls back along the inclusion of the
first coordinate to the functional `x ↦ f^t` of `K_t`, so the induced map of exterior algebras
commutes with the differentials. The homomorphism `ξ` is a section of `ε`.

## Main definitions

* `Koszul.comparisonXInclusion`: the linear map `R → R²` onto the `x` coordinate.
* `Koszul.koszulToComparisonOddX`: the homomorphism `K_t → R⟨x, z⟩` sending the generator of
  `K_t` to `x`.
* `Koszul.koszulToComparisonX`: the homomorphism `ξ : K_t → B_{N,t}` sending the generator of
  `K_t` to the odd generator `x`.
* `Koszul.comparisonToTensor`: the arrow `β : B_{N,t} → K_n ⊗_R K_t` of Tag 0GZ7.

## Main results

* `Koszul.seqDual_comp_comparisonXInclusion`: the functional of `R⟨x, z⟩` pulls back along
  `comparisonXInclusion` to the functional of `K_t`.
* `Koszul.koszulToComparisonX_ι`: the value of `ξ` on a generator.
* `Koszul.comparisonToKoszul_comp_koszulToComparisonX`: the composite `ε ∘ ξ` is the identity of
  `K_t`, so `ξ` is a section of the comparison homomorphism.
* `Koszul.powMul_comp_powPairToTensor`: the composite `μ_n ∘ (K_{n,t} → K_n ⊗_R K_t)` is the
  multiplication homomorphism `K_{n,t} → K_t`.
* `Koszul.comparisonToTensor_comparisonInclusion`: the arrow `β` on the odd part of `B_{N,t}`.
* `Koszul.comparisonToTensor_x` and `Koszul.comparisonToTensor_z`: the values of `β` on the two
  odd generators.
* `Koszul.powMul_comp_comparisonToTensor`: the composite `μ_n ∘ β` is the comparison
  homomorphism `ε : B_{N,t} → K_t`.
* `Koszul.comparisonToTensor_comp_koszulToComparison`: the composite `β ∘ κ` is the inclusion of
  the left tensor factor composed with the transition homomorphism `τ_{N,n}`.
* `Koszul.comparisonToTensor_comp_koszulToComparisonX`: the composite `β ∘ ξ` is the inclusion
  of the right tensor factor.

## Implementation notes

Every element of `K_n`, of `K_t` and of their tensor product is named at the carrier type of the
differential graded algebra it belongs to, through `Koszul.powOneGen`, `Koszul.powTensorY` and
`Koszul.powTensorX`: the graded tensor product needs the graded-algebra instance of each factor,
and that instance is found only when the submodule family and the element live over the same
carrier.

Each of the four composites is checked on a single generator `ι v` of the exterior algebra it
starts from, with `ExteriorAlgebra.hom_ext`; the generator computations go through
`Koszul.ι_eq_smul_powOneGen`, which rewrites `ι v` as `v 0` times the standard generator, so
that the already-available values of the structural maps on the standard generators apply.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open scoped ExteriorAlgebra TensorProduct

open DifferentialGradedAlgebra DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

section KoszulToComparisonX

/-- The map of Koszul algebras `K_t = R⟨x⟩ → R⟨x, z⟩` sending the generator of `K_t` to `x`. -/
def koszulToComparisonOddX (f : R) (N t : ℕ) :
    (powAlgebra (fun _ : Fin 1 => f) t).Hom (comparisonOddAlgebra f N t) where
  toAlgebraHom := ExteriorAlgebra.map (comparisonXInclusion R)
  map_grading _ _ ha :=
    map_mem_cohomologicalExteriorGrade R (Fin 1 → R) (Fin 2 → R) (comparisonXInclusion R) ha
  map_d a := by
    change ExteriorAlgebra.map (comparisonXInclusion R)
        (contraction (seqDual fun _ : Fin 1 => f ^ t) a) =
      comparisonExteriorDifferential f N t (ExteriorAlgebra.map (comparisonXInclusion R) a)
    rw [comparisonExteriorDifferential, ← seqDual_comp_comparisonXInclusion f N t]
    exact (contractLeft_exteriorAlgebraMap (comparisonXInclusion R)
      (seqDual (comparisonSeq f N t)) a).symm

/-- The underlying algebra homomorphism of `K_t → R⟨x, z⟩` is the map of exterior algebras
induced by `comparisonXInclusion`. -/
@[simp]
theorem koszulToComparisonOddX_toAlgebraHom (f : R) (N t : ℕ) :
    (koszulToComparisonOddX f N t).toAlgebraHom =
      ExteriorAlgebra.map (comparisonXInclusion R) := rfl

/-- The homomorphism `ξ : K_t → B_{N,t}` of differential graded algebras sending the generator
of `K_t` to the odd generator `x` of `B_{N,t}`. -/
def koszulToComparisonX (f : R) {N t : ℕ} (h : t ≤ N) :
    (powAlgebra (fun _ : Fin 1 => f) t).Hom (comparisonAlgebra f h) :=
  (comparisonOddToAlgebra f h).comp (koszulToComparisonOddX f N t)

/-- The homomorphism `ξ : K_t → B_{N,t}` sends a generator `ι v` of `K_t` to the odd part
element `ι (v₀, 0)` of `B_{N,t}`. -/
theorem koszulToComparisonX_ι (f : R) {N t : ℕ} (h : t ≤ N) (v : Fin 1 → R) :
    (koszulToComparisonX f h).toAlgebraHom (ExteriorAlgebra.ι R v) =
      comparisonInclusion R (ExteriorAlgebra.ι R (Pi.single 0 (v 0))) := by
  show comparisonInclusion R
      (ExteriorAlgebra.map (comparisonXInclusion R) (ExteriorAlgebra.ι R v)) = _
  rw [ExteriorAlgebra.map_apply_ι, comparisonXInclusion_apply]

/-- The homomorphism `ξ : K_t → B_{N,t}` sends the generator of `K_t` to `x`. -/
theorem koszulToComparisonX_gen (f : R) {N t : ℕ} (h : t ≤ N) :
    (koszulToComparisonX f h).toAlgebraHom (ExteriorAlgebra.ι R fun _ => 1) =
      comparisonInclusion R (comparisonX R) := by
  rw [koszulToComparisonX_ι]
  rfl

/-- **The homomorphism `ξ` is a section of the comparison homomorphism `ε`.** The composite
`K_t → B_{N,t} → K_t` is the identity of `K_t`. -/
theorem comparisonToKoszul_comp_koszulToComparisonX (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonToKoszul f h).toAlgebraHom.comp (koszulToComparisonX f h).toAlgebraHom =
      AlgHom.id R (ExteriorAlgebra R (Fin 1 → R)) := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  have hcomp : (comparisonToKoszul f h).toAlgebraHom
      (comparisonInclusion R (ExteriorAlgebra.ι R (Pi.single 0 (v 0)))) =
      ExteriorAlgebra.ι R v := by
    show comparisonLift f N t
        (EvenVariableAlgebra.coeffEmbedding (ExteriorAlgebra.ι R (Pi.single 0 (v 0)))) = _
    rw [comparisonLift_coeffEmbedding, comparisonExteriorMap, ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rw [comparisonProj_apply, Pi.single_eq_same, Pi.single_eq_of_ne (by decide), mul_zero,
      add_zero, Subsingleton.elim i 0]
  show (comparisonToKoszul f h).toAlgebraHom
      ((koszulToComparisonX f h).toAlgebraHom (ExteriorAlgebra.ι R v)) = ExteriorAlgebra.ι R v
  rw [koszulToComparisonX_ι, hcomp]

end KoszulToComparisonX

section Multiplication

/-- The isomorphism `K_{n,t} → K_n ⊗_R K_t` sends a generator `ι v` to
`v₀ (ξ ⊗ 1) + v₁ (1 ⊗ ξ)`. -/
theorem powPairToTensor_ι (f : R) (n t : ℕ) (v : Fin 2 → R) :
    (powPairToTensor f n t).toAlgebraHom (ExteriorAlgebra.ι R v) =
      v 0 • powTensorY f n t + v 1 • powTensorX f n t :=
  powPairToTensorAlgHom_ι f n t v

/-- The multiplication homomorphism `K_{n,t} → K_t` sends a generator `ι v` to the image of `v`
under the linear map with matrix `(f^{n-t}, 1)`. -/
theorem powPairToKoszul_ι (f : R) {n t : ℕ} (ht : t ≤ n) (v : Fin 2 → R) :
    (powPairToKoszul f ht).toAlgebraHom (ExteriorAlgebra.ι R v) =
      ExteriorAlgebra.ι R (powPairProj f n t v) :=
  ExteriorAlgebra.map_apply_ι (powPairProj f n t) v

/-- The isomorphism `K_{n,t} → K_n ⊗_R K_t` sends a multiple of the generator `y` to that
multiple of the pure tensor `ξ ⊗ 1`. -/
theorem powPairToTensorAlgHom_single_zero (f : R) (n t : ℕ) (c : R) :
    powPairToTensorAlgHom f n t (ExteriorAlgebra.ι R (Pi.single (0 : Fin 2) c)) =
      c • powTensorY f n t := by
  rw [powPairToTensorAlgHom_ι,
    show (Pi.single (0 : Fin 2) c : Fin 2 → R) 0 = c from by simp,
    show (Pi.single (0 : Fin 2) c : Fin 2 → R) 1 = 0 from by simp, zero_smul, add_zero]

/-- The isomorphism `K_{n,t} → K_n ⊗_R K_t` sends a multiple of the generator `x` to that
multiple of the pure tensor `1 ⊗ ξ`. -/
theorem powPairToTensorAlgHom_single_one (f : R) (n t : ℕ) (c : R) :
    powPairToTensorAlgHom f n t (ExteriorAlgebra.ι R (Pi.single (1 : Fin 2) c)) =
      c • powTensorX f n t := by
  rw [powPairToTensorAlgHom_ι,
    show (Pi.single (1 : Fin 2) c : Fin 2 → R) 0 = 0 from by simp,
    show (Pi.single (1 : Fin 2) c : Fin 2 → R) 1 = c from by simp, zero_smul, zero_add]

/-- The transition homomorphism `K_m → K_n` of one-variable Koszul algebras scales a generator
`ι v` by `f^(m-n)`. -/
private theorem powTransition_ι_fin_one (f : R) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m)
    (v : Fin 1 → R) :
    (powTransition (fun _ : Fin 1 => f) hn hnm).toAlgebraHom (ExteriorAlgebra.ι R v) =
      ExteriorAlgebra.ι R (fun _ : Fin 1 => f ^ (m - n) * v 0) := by
  rw [powTransition_apply, ExteriorAlgebra.map_apply_ι]
  congr 1
  funext i
  rw [LinearMap.mulLeft_apply, Pi.mul_apply, Subsingleton.elim i 0]

/-- The multiplication map `μ_n : K_n ⊗_R K_t → K_t` sends the pure tensor `ξ ⊗ 1` to
`f^{n-t}` times the generator of `K_t`. -/
theorem powMul_powTensorY (f : R) {n t : ℕ} (ht1 : 1 ≤ t) (htn : t ≤ n) :
    (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom (powTensorY f n t) =
      ExteriorAlgebra.ι R (fun _ : Fin 1 => f ^ (n - t)) := by
  have h : (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom (powTensorY f n t) =
      (powTransition (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom
          (ExteriorAlgebra.ι R (Pi.single 0 1)) * (1 : (powOne f t).A) :=
    powMul_tmul (fun _ : Fin 1 => f) ht1 htn (powOneGen f n) (1 : (powOne f t).A)
  rw [h, mul_one, powTransition_ι_fin_one, Pi.single_eq_same, mul_one]

/-- The multiplication map `μ_n : K_n ⊗_R K_t → K_t` sends the pure tensor `1 ⊗ ξ` to the
generator of `K_t`. -/
theorem powMul_powTensorX (f : R) {n t : ℕ} (ht1 : 1 ≤ t) (htn : t ≤ n) :
    (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom (powTensorX f n t) =
      ExteriorAlgebra.ι R (fun _ : Fin 1 => (1 : R)) := by
  have h : (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom (powTensorX f n t) =
      (powTransition (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom (1 : (powOne f n).A) *
        powOneGen f t :=
    powMul_tmul (fun _ : Fin 1 => f) ht1 htn (1 : (powOne f n).A) (powOneGen f t)
  have h1 : (ExteriorAlgebra.ι R (Pi.single (0 : Fin 1) (1 : R)) :
      ExteriorAlgebra R (Fin 1 → R)) =
      ExteriorAlgebra.ι R (fun _ : Fin 1 => (1 : R)) := by
    congr 1
    funext i
    rw [Subsingleton.elim i 0, Pi.single_eq_same]
  rw [h, map_one, one_mul]
  exact h1

/-- The multiplication map `μ_n` of the tensor product, read on a generator of `K_{n,t}`: it
agrees there with the multiplication map `K_{n,t} → K_t`. -/
theorem powMul_powPairToTensor_ι (f : R) {n t : ℕ} (ht1 : 1 ≤ t) (htn : t ≤ n)
    (v : Fin 2 → R) :
    (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom
        ((powPairToTensor f n t).toAlgebraHom (ExteriorAlgebra.ι R v)) =
      (powPairToKoszul f htn).toAlgebraHom (ExteriorAlgebra.ι R v) := by
  have hsum : (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom
      ((powPairToTensor f n t).toAlgebraHom (ExteriorAlgebra.ι R v)) =
      v 0 • (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom (powTensorY f n t) +
        v 1 • (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom (powTensorX f n t) := by
    rw [powPairToTensor_ι, map_add, _root_.map_smul, _root_.map_smul]
  have hfin : ((v 0 • ExteriorAlgebra.ι R (fun _ : Fin 1 => f ^ (n - t)) +
      v 1 • ExteriorAlgebra.ι R (fun _ : Fin 1 => (1 : R)) :
        ExteriorAlgebra R (Fin 1 → R))) =
      ExteriorAlgebra.ι R (powPairProj f n t v) := by
    rw [← _root_.map_smul, ← _root_.map_smul, ← map_add]
    congr 1
    funext i
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_one,
      powPairProj_apply, mul_comm (v 0) (f ^ (n - t))]
  rw [hsum, powMul_powTensorY, powMul_powTensorX]
  exact hfin.trans (powPairToKoszul_ι f htn v).symm

/-- **The multiplication map of the tensor product computes the multiplication map of the
Koszul algebra of a pair.** The composite `K_{n,t} → K_n ⊗_R K_t → K_t` of the isomorphism
`Koszul.powPairToTensor` with `μ_n` is the homomorphism `K_{n,t} → K_t` of
`Koszul.powPairToKoszul`, which sends `y` to `f^{n-t} x` and `x` to `x`. -/
theorem powMul_comp_powPairToTensor (f : R) {n t : ℕ} (ht1 : 1 ≤ t) (htn : t ≤ n) :
    (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom.comp
        (powPairToTensor f n t).toAlgebraHom =
      (powPairToKoszul f htn).toAlgebraHom := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  exact powMul_powPairToTensor_ι f ht1 htn v

end Multiplication

section Arrow

/-- **The arrow `β` of Tag 0GZ7.** For `1 ≤ t`, `t ≤ n` and `n + t ≤ N` the homomorphism
`B_{N,t} → K_n ⊗_R K_t` of differential graded algebras sending `x` to `1 ⊗ ξ` and `z` to
`f^{N-n} (ξ ⊗ 1)`: the arrow into the Koszul algebra of the pair `(f^n, f^t)` read through the
identification of that algebra with the tensor product `K_n ⊗_R K_t`. -/
def comparisonToTensor (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N) :
    (comparisonAlgebra f h).Hom (powTensorAlgebra f n t) :=
  (powPairToTensor f n t).comp (comparisonToPowPair f h hN)

/-- **The arrow `β` on the odd part of `B_{N,t}`.** On the image of an element `a` of the odd
part `R⟨x, z⟩` it is the image of `a` in `K_{n,t}` read in `K_n ⊗_R K_t`. -/
theorem comparisonToTensor_comparisonInclusion (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N)
    (a : comparisonExterior R) :
    (comparisonToTensor f h hN).toAlgebraHom (comparisonInclusion R a) =
      powPairToTensorAlgHom f n t (comparisonPairExteriorMap f N n a) := by
  show powPairToTensorAlgHom f n t
      (comparisonPairLift f N n t (EvenVariableAlgebra.coeffEmbedding a)) = _
  rw [comparisonPairLift_coeffEmbedding]

/-- The arrow `β` sends the odd generator `x` to the pure tensor `1 ⊗ ξ`. -/
theorem comparisonToTensor_x (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N) :
    (comparisonToTensor f h hN).toAlgebraHom (comparisonInclusion R (comparisonX R)) =
      powTensorX f n t := by
  rw [comparisonToTensor_comparisonInclusion, comparisonPairExteriorMap_x, powPairX,
    powPairToTensorAlgHom_single_one, one_smul]

/-- The arrow `β` sends the odd generator `z` to `f^{N-n}` times the pure tensor `ξ ⊗ 1`. -/
theorem comparisonToTensor_z (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N) :
    (comparisonToTensor f h hN).toAlgebraHom (comparisonInclusion R (comparisonZ R)) =
      f ^ (N - n) • powTensorY f n t := by
  rw [comparisonToTensor_comparisonInclusion, comparisonPairExteriorMap_z, _root_.map_smul,
    powPairY, powPairToTensorAlgHom_single_zero, one_smul]

/-- **The pleasant computation of Tag 0GZ7.** Composing the arrow `β : B_{N,t} → K_n ⊗_R K_t`
with the multiplication map `μ_n : K_n ⊗_R K_t → K_t` returns the comparison homomorphism
`ε : B_{N,t} → K_t`. -/
theorem powMul_comp_comparisonToTensor (f : R) {N n t : ℕ} (h : t ≤ N) (ht1 : 1 ≤ t)
    (htn : t ≤ n) (hN : n + t ≤ N) :
    (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom.comp
        (comparisonToTensor f h hN).toAlgebraHom =
      (comparisonToKoszul f h).toAlgebraHom := by
  have hassoc : (powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom.comp
      (comparisonToTensor f h hN).toAlgebraHom =
      ((powMul (fun _ : Fin 1 => f) ht1 htn).toAlgebraHom.comp
          (powPairToTensor f n t).toAlgebraHom).comp
        (comparisonToPowPair f h hN).toAlgebraHom := rfl
  rw [hassoc, powMul_comp_powPairToTensor]
  exact powPairToKoszul_comp_comparisonToPowPair f h htn hN

end Arrow

section Restrictions

/-- **The arrow `β` restricted along `κ : K_N → B_{N,t}` is the left tensor factor.** The
composite `K_N → B_{N,t} → K_n ⊗_R K_t` is the inclusion of the left factor composed with the
transition homomorphism `τ_{N,n} : K_N → K_n`. -/
theorem comparisonToTensor_comp_koszulToComparison (f : R) {N n t : ℕ} (h : t ≤ N) (hn1 : 1 ≤ n)
    (hnN : n ≤ N) (hN : n + t ≤ N) :
    (comparisonToTensor f h hN).toAlgebraHom.comp (koszulToComparison f h).toAlgebraHom =
      (GradedTensorProduct.includeLeft (powOne f n).grading (powOne f t).grading).comp
        (powTransition (fun _ : Fin 1 => f) hn1 hnN).toAlgebraHom := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  have hproj : comparisonPairProj f N n (Pi.single 1 (v 0)) =
      Pi.single (0 : Fin 2) (f ^ (N - n) * v 0) := by
    funext j
    fin_cases j <;> simp
  have hleft : (koszulToComparison f h).toAlgebraHom (ExteriorAlgebra.ι R v) =
      comparisonInclusion R (ExteriorAlgebra.ι R (Pi.single 1 (v 0))) := by
    show comparisonInclusion R
        (ExteriorAlgebra.map (zInclusion R) (ExteriorAlgebra.ι R v)) = _
    rw [ExteriorAlgebra.map_apply_ι, zInclusion_apply]
  have hlhs : (comparisonToTensor f h hN).toAlgebraHom
      ((koszulToComparison f h).toAlgebraHom (ExteriorAlgebra.ι R v)) =
      (f ^ (N - n) * v 0) • powTensorY f n t := by
    rw [hleft, comparisonToTensor_comparisonInclusion, comparisonPairExteriorMap,
      ExteriorAlgebra.map_apply_ι, hproj, powPairToTensorAlgHom_single_zero]
  have htrans : ((powTransition (fun _ : Fin 1 => f) hn1 hnN).toAlgebraHom
      (ExteriorAlgebra.ι R v) : (powOne f n).A) =
      (f ^ (N - n) * v 0) • powOneGen f n := by
    exact (powTransition_ι_fin_one f hn1 hnN v).trans
      (ι_eq_smul_powOneGen f n (fun _ : Fin 1 => f ^ (N - n) * v 0))
  have hrhs : GradedTensorProduct.includeLeft (powOne f n).grading (powOne f t).grading
      ((powTransition (fun _ : Fin 1 => f) hn1 hnN).toAlgebraHom (ExteriorAlgebra.ι R v)) =
      (f ^ (N - n) * v 0) • powTensorY f n t := by
    rw [htrans, _root_.map_smul]
    rfl
  exact hlhs.trans hrhs.symm

/-- **The arrow `β` restricted along `ξ : K_t → B_{N,t}` is the right tensor factor.** The
composite `K_t → B_{N,t} → K_n ⊗_R K_t` is the inclusion of the right factor. -/
theorem comparisonToTensor_comp_koszulToComparisonX (f : R) {N n t : ℕ} (h : t ≤ N)
    (hN : n + t ≤ N) :
    (comparisonToTensor f h hN).toAlgebraHom.comp (koszulToComparisonX f h).toAlgebraHom =
      GradedTensorProduct.includeRight (powOne f n).grading (powOne f t).grading := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  have hproj : comparisonPairProj f N n (Pi.single 0 (v 0)) =
      Pi.single (1 : Fin 2) (v 0) := by
    funext j
    fin_cases j <;> simp
  have hlhs : (comparisonToTensor f h hN).toAlgebraHom
      ((koszulToComparisonX f h).toAlgebraHom (ExteriorAlgebra.ι R v)) =
      v 0 • powTensorX f n t := by
    rw [koszulToComparisonX_ι, comparisonToTensor_comparisonInclusion,
      comparisonPairExteriorMap, ExteriorAlgebra.map_apply_ι, hproj,
      powPairToTensorAlgHom_single_one]
  have hrhs : GradedTensorProduct.includeRight (powOne f n).grading (powOne f t).grading
      (ExteriorAlgebra.ι R v) = v 0 • powTensorX f n t := by
    rw [ι_eq_smul_powOneGen f t v, _root_.map_smul]
    rfl
  exact hlhs.trans hrhs.symm

end Restrictions

end Koszul
