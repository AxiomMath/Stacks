module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorFreeDividedPowers
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulCompatibility
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableDifferential
public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraMap
public import StacksFrontier.RingTheory.Koszul.PowAlgebraMultiplication

/-!
# The comparison map from `R⟨x, z, u⟩` to the Koszul algebra of a pair of powers

Let `f` be an element of a commutative ring `R`. For `n, t ≥ 1` write
`K_{n,t} = R⟨y, x⟩` for the Koszul algebra of the pair `(f ^ n, f ^ t)`, that is, the exterior
algebra on `R²` with two generators of cohomological degree `-1` and
$$\mathrm{d}(y) = f^n, \qquad \mathrm{d}(x) = f^t.$$
It is the Koszul algebra of the concatenated sequence, and it receives both `K_n` and `K_t`,
hence also their tensor product: the homomorphism `K_n ⊗_R K_t → K_{n,t}` sends `a ⊗ b` to the
product of the images of `a` and `b`.

Whenever `N ≥ n + t`, the algebra `B_{N,t} = R⟨x, z, u⟩` of `Koszul.comparisonAlgebra` maps to
`K_{n,t}` by
$$x \longmapsto x, \qquad z \longmapsto f^{N-n} y, \qquad u \longmapsto -f^{N-n-t}\, y x ,$$
which is the arrow of Tag 0GZ7 read in `K_{n,t}` instead of in `K_n ⊗_R K_t`. The value on `u`
is legitimate because `d(-f^{N-n-t} y x) = f^{N-n} y - f^{N-t} x` is exactly the image of the
cycle `z - f^{N-t} x` killed by `u`. Composing with the multiplication map `K_{n,t} → K_t`,
which sends `y` to `f^{n-t} x` and `x` to `x`, returns the comparison homomorphism
`B_{N,t} → K_t` of `Koszul.comparisonToKoszul`.

## Main definitions

* `Koszul.powPairSeq` and `Koszul.powPairAlgebra`: the pair `(f ^ n, f ^ t)` and its Koszul
  algebra `K_{n,t}`.
* `Koszul.powPairY` and `Koszul.powPairX`: the two generators of `K_{n,t}`.
* `Koszul.powPairU`: the degree `-2` element `-f^{N-n-t} y x` of `K_{n,t}` that the even
  generator `u` of `B_{N,t}` maps to.
* `Koszul.comparisonToPowPair`: the homomorphism `B_{N,t} → K_{n,t}` of differential graded
  algebras, for `N ≥ n + t`.
* `Koszul.powPairToKoszul`: the homomorphism `K_{n,t} → K_t` sending `y` to `f^{n-t} x` and `x`
  to `x`, for `t ≤ n`.
* `Koszul.powPairFromTensor`: the homomorphism `K_n ⊗_R K_t → K_{n,t}`.

## Main results

* `Koszul.powPairAlgebra_d_powPairU`: the differential of `K_{n,t}` sends `-f^{N-n-t} y x` to
  `f^{N-n} y - f^{N-t} x`, the image of the cycle `z - f^{N-t} x`.
* `Koszul.comparisonToPowPair_x`, `Koszul.comparisonToPowPair_z` and
  `Koszul.comparisonToPowPair_u`: the values of `B_{N,t} → K_{n,t}` on the three generators.
* `Koszul.powPairToKoszul_comp_comparisonToPowPair`: the composite
  `B_{N,t} → K_{n,t} → K_t` is the comparison homomorphism `B_{N,t} → K_t`.
* `Koszul.powPairFromTensor_comp_includeLeft` and
  `Koszul.powPairFromTensor_comp_includeRight`: the homomorphism `K_n ⊗_R K_t → K_{n,t}`
  restricts on the two factors to the maps sending the generators to `y` and to `x`.

## Implementation notes

The homomorphism out of `B_{N,t}` is produced by the universal property of the even-variable
divided power extension (Tag 09PI) applied with the adjoined variable sent to `-f^{N-n-t} y x`,
whose divided powers in the target are those of
`DividedPowers.TateResolution.exteriorDividedPowerStructure`. Compatibility with the
differentials is checked on the divided power monomials `a u⁽ᵏ⁾`; for `k ≥ 1` it uses the
compatibility of the exterior divided powers with every Koszul differential
(`DividedPowers.TateResolution.isCompatibleWithDifferential_exteriorDividedPowerStructure`),
the Leibniz rule in the sign-homomorphism form
(`DividedPowers.TateResolution.differential_mul_signRingHom`) and that a graded algebra
homomorphism commutes with the grading sign
(`DividedPowers.TateResolution.algHom_signRingHom`). No case distinction on how large `k` is is
needed: the identity `d(γ_k τ) = d(τ) γ_{k-1}(τ)` holds for every `k ≥ 1`.

That the composite `B_{N,t} → K_{n,t} → K_t` is the comparison homomorphism is checked on the
divided power monomials as well, using that a degree-preserving algebra homomorphism out of the
exterior algebra of a finite free module automatically preserves the exterior divided powers
(`DividedPowers.TateResolution.algHom_map_dpow_exteriorDividedPowerStructure`) together with the
fact that `-f^{N-n-t} y x` maps to zero in `K_t`.

Every statement about the differential of `K_{n,t}` is proved for
`Koszul.contraction (Koszul.seqDual (Koszul.powPairSeq f n t))` and then restated for
`(Koszul.powPairAlgebra f n t).d`, which is the same map by definition. Rewriting the bundled
differential into the unbundled one inside a proof produces a term that is not type-correct at
reducible transparency — the surrounding instance arguments still mention
`(Koszul.powPairAlgebra f n t).ring` — after which no further rewrite fires.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
-/


@[expose] public section

namespace Koszul

universe u

open scoped ExteriorAlgebra TensorProduct

open DifferentialGradedAlgebra DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

section PowPair

/-- The pair `(f ^ n, f ^ t)` of values taken by the differential of `K_{n,t}` on its two
generators `y` and `x`. -/
def powPairSeq (f : R) (n t : ℕ) : Fin 2 → R
  | 0 => f ^ n
  | 1 => f ^ t

/-- The first entry of the pair `(f ^ n, f ^ t)` is `f ^ n`. -/
@[simp] theorem powPairSeq_zero (f : R) (n t : ℕ) : powPairSeq f n t 0 = f ^ n := rfl

/-- The second entry of the pair `(f ^ n, f ^ t)` is `f ^ t`. -/
@[simp] theorem powPairSeq_one (f : R) (n t : ℕ) : powPairSeq f n t 1 = f ^ t := rfl

/-- The Koszul algebra `K_{n,t} = R⟨y, x⟩` of the pair `(f ^ n, f ^ t)`: the exterior algebra on
`R²` with the two generators in cohomological degree `-1` and with `d y = f ^ n`,
`d x = f ^ t`. -/
noncomputable def powPairAlgebra (f : R) (n t : ℕ) : DifferentialGradedAlgebra.{u, u} R :=
  cohomologicalDifferentialGradedAlgebra R (Fin 2 → R) (seqDual (powPairSeq f n t))

/-- The underlying algebra of `K_{n,t}` is the exterior algebra on `R²`. -/
theorem powPairAlgebra_A (f : R) (n t : ℕ) :
    (powPairAlgebra f n t).A = ExteriorAlgebra R (Fin 2 → R) := rfl

/-- The grading of `K_{n,t}` is the cohomological grading of the exterior algebra on `R²`. -/
theorem powPairAlgebra_grading (f : R) (n t : ℕ) :
    (powPairAlgebra f n t).grading = cohomologicalExteriorGrade R (Fin 2 → R) := rfl

/-- The differential of `K_{n,t}` is contraction by the functional `R² → R` given by the pair
`(f ^ n, f ^ t)`. -/
theorem powPairAlgebra_d (f : R) (n t : ℕ) :
    (powPairAlgebra f n t).d = contraction (seqDual (powPairSeq f n t)) := rfl

/-- The first generator `y` of `K_{n,t}`, with `d y = f ^ n`. -/
noncomputable def powPairY (R : Type u) [CommRing R] : ExteriorAlgebra R (Fin 2 → R) :=
  ExteriorAlgebra.ι R (Pi.single 0 1)

/-- The second generator `x` of `K_{n,t}`, with `d x = f ^ t`. -/
noncomputable def powPairX (R : Type u) [CommRing R] : ExteriorAlgebra R (Fin 2 → R) :=
  ExteriorAlgebra.ι R (Pi.single 1 1)

/-- The generator `y` lies in the first exterior power of `R²`. -/
theorem powPairY_mem (R : Type u) [CommRing R] :
    powPairY R ∈ exteriorGrade R (Fin 2 → R) 1 :=
  ι_mem_one _

/-- The generator `x` lies in the first exterior power of `R²`. -/
theorem powPairX_mem (R : Type u) [CommRing R] :
    powPairX R ∈ exteriorGrade R (Fin 2 → R) 1 :=
  ι_mem_one _

/-- An element of the first exterior power of `R²` has cohomological degree `-1` in `K_{n,t}`. -/
private theorem mem_powPairAlgebra_grading_neg_one {f : R} {n t : ℕ}
    {a : ExteriorAlgebra R (Fin 2 → R)} (ha : a ∈ exteriorGrade R (Fin 2 → R) 1) :
    a ∈ (powPairAlgebra f n t).grading (-1) := by
  rw [powPairAlgebra_grading, show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num,
    cohomologicalExteriorGrade_neg_natCast]
  exact ha

/-- The generator `y` has cohomological degree `-1`. -/
theorem powPairY_mem_grading (f : R) (n t : ℕ) :
    powPairY R ∈ (powPairAlgebra f n t).grading (-1) :=
  mem_powPairAlgebra_grading_neg_one (powPairY_mem R)

/-- The generator `x` has cohomological degree `-1`. -/
theorem powPairX_mem_grading (f : R) (n t : ℕ) :
    powPairX R ∈ (powPairAlgebra f n t).grading (-1) :=
  mem_powPairAlgebra_grading_neg_one (powPairX_mem R)

/-- The differential of `K_{n,t}` sends the `i`-th generator to the `i`-th entry of the pair. -/
private theorem powPairAlgebra_d_ι_single (f : R) (n t : ℕ) (i : Fin 2) :
    (powPairAlgebra f n t).d (ExteriorAlgebra.ι R (Pi.single i 1)) =
      algebraMap R (ExteriorAlgebra R (Fin 2 → R)) (powPairSeq f n t i) :=
  (CliffordAlgebra.contractLeft_ι (0 : QuadraticForm R (Fin 2 → R)) _ _).trans
    (by rw [seqDual_single])

/-- The differential of `K_{n,t}` sends the generator `y` to `f ^ n`. -/
theorem powPairAlgebra_d_y (f : R) (n t : ℕ) :
    (powPairAlgebra f n t).d (powPairY R) =
      algebraMap R (ExteriorAlgebra R (Fin 2 → R)) (f ^ n) :=
  powPairAlgebra_d_ι_single f n t 0

/-- The differential of `K_{n,t}` sends the generator `x` to `f ^ t`. -/
theorem powPairAlgebra_d_x (f : R) (n t : ℕ) :
    (powPairAlgebra f n t).d (powPairX R) =
      algebraMap R (ExteriorAlgebra R (Fin 2 → R)) (f ^ t) :=
  powPairAlgebra_d_ι_single f n t 1

/-- The element `-f^{N-n-t} y x` of `K_{n,t}`, of cohomological degree `-2`: the image of the
even generator `u` of `B_{N,t}`. -/
noncomputable def powPairU (f : R) (N n t : ℕ) : ExteriorAlgebra R (Fin 2 → R) :=
  -(f ^ (N - n - t) • (powPairY R * powPairX R))

/-- The element `-f^{N-n-t} y x` lies in the second exterior power of `R²`. -/
theorem powPairU_mem (f : R) (N n t : ℕ) :
    powPairU f N n t ∈ exteriorGrade R (Fin 2 → R) 2 := by
  have h : powPairY R * powPairX R ∈ exteriorGrade R (Fin 2 → R) 2 := by
    simpa using SetLike.mul_mem_graded (powPairY_mem R) (powPairX_mem R)
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ h)

/-- The element `-f^{N-n-t} y x` lies in the positive even part of the exterior algebra on
`R²`. -/
theorem powPairU_mem_positiveEvenPart (f : R) (N n t : ℕ) :
    powPairU f N n t ∈ positiveEvenPart (exteriorGrade R (Fin 2 → R)) :=
  mem_positiveEvenPart_of_even (exteriorGrade R (Fin 2 → R)) 2 (by norm_num) even_two
    (powPairU_mem f N n t)

/-- Contraction by the functional of `K_{n,t}` sends `-f^{N-n-t} y x` to
`f^{N-n} y - f^{N-t} x`. -/
theorem contraction_powPairU (f : R) {N n t : ℕ} (hN : n + t ≤ N) :
    contraction (seqDual (powPairSeq f n t)) (powPairU f N n t) =
      f ^ (N - n) • powPairY R - f ^ (N - t) • powPairX R := by
  have hc1 : f ^ (N - n - t) * f ^ n = f ^ (N - t) := by
    rw [← pow_add]; congr 1; omega
  have hc2 : f ^ (N - n - t) * f ^ t = f ^ (N - n) := by
    rw [← pow_add]; congr 1; omega
  have hleib := contractLeft_mul_of_mem (seqDual (powPairSeq f n t)) 1 (powPairY_mem R)
    (powPairX R)
  have hy : contraction (seqDual (powPairSeq f n t)) (powPairY R) =
      algebraMap R (ExteriorAlgebra R (Fin 2 → R)) (f ^ n) := powPairAlgebra_d_y f n t
  have hx : contraction (seqDual (powPairSeq f n t)) (powPairX R) =
      algebraMap R (ExteriorAlgebra R (Fin 2 → R)) (f ^ t) := powPairAlgebra_d_x f n t
  have hmul1 : algebraMap R (ExteriorAlgebra R (Fin 2 → R)) (f ^ n) * powPairX R =
      f ^ n • powPairX R := (Algebra.smul_def _ _).symm
  have hmul2 : powPairY R * algebraMap R (ExteriorAlgebra R (Fin 2 → R)) (f ^ t) =
      f ^ t • powPairY R := by
    rw [← Algebra.commutes, ← Algebra.smul_def]
  have hd : contraction (seqDual (powPairSeq f n t)) (powPairY R * powPairX R) =
      f ^ n • powPairX R - f ^ t • powPairY R := by
    rw [hleib, hy, hx, hmul1, hmul2]
    simp only [pow_one, neg_one_smul]
    abel
  rw [powPairU]
  simp only [map_neg, map_smul, hd, smul_sub, smul_smul, hc1, hc2, neg_sub]

/-- The differential of `K_{n,t}` sends `-f^{N-n-t} y x` to `f^{N-n} y - f^{N-t} x`, which is
the image of the cycle `z - f^{N-t} x` of `B_{N,t}`. -/
theorem powPairAlgebra_d_powPairU (f : R) {N n t : ℕ} (hN : n + t ≤ N) :
    (powPairAlgebra f n t).d (powPairU f N n t) =
      f ^ (N - n) • powPairY R - f ^ (N - t) • powPairX R :=
  contraction_powPairU f hN

end PowPair

section TensorFactors

/-- The linear map `R → R²` onto the `i`-th coordinate, which sends the generator of a
one-variable Koszul algebra to the `i`-th generator of `K_{n,t}`. -/
def powPairCoord (R : Type u) [CommRing R] (i : Fin 2) : (Fin 1 → R) →ₗ[R] (Fin 2 → R) :=
  (LinearMap.single R (fun _ : Fin 2 => R) i).comp (LinearMap.proj 0)

/-- The map `powPairCoord R i` sends `v` to the vector with `v 0` in the `i`-th coordinate and
zero elsewhere. -/
@[simp] theorem powPairCoord_apply (i : Fin 2) (v : Fin 1 → R) :
    powPairCoord R i v = Pi.single i (v 0) := rfl

/-- The functional of `K_{n,t}` restricted along the `i`-th coordinate is the functional of the
one-variable Koszul algebra on the `i`-th entry of the pair. -/
private theorem seqDual_comp_powPairCoord (f : R) (n t : ℕ) (i : Fin 2) :
    seqDual (powPairSeq f n t) ∘ₗ powPairCoord R i =
      seqDual fun _ : Fin 1 => powPairSeq f n t i := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, powPairCoord_apply, seqDual_apply_single, seqDual_apply,
    Fin.sum_univ_one]

/-- The functional of `K_{n,t}` restricted along the first coordinate is the functional of
`K_n`. -/
theorem seqDual_comp_powPairCoord_zero (f : R) (n t : ℕ) :
    seqDual (powPairSeq f n t) ∘ₗ powPairCoord R 0 = seqDual fun _ : Fin 1 => f ^ n :=
  seqDual_comp_powPairCoord f n t 0

/-- The functional of `K_{n,t}` restricted along the second coordinate is the functional of
`K_t`. -/
theorem seqDual_comp_powPairCoord_one (f : R) (n t : ℕ) :
    seqDual (powPairSeq f n t) ∘ₗ powPairCoord R 1 = seqDual fun _ : Fin 1 => f ^ t :=
  seqDual_comp_powPairCoord f n t 1

/-- The homomorphism `K_n → K_{n,t}` sending the generator of `K_n` to `y`. -/
noncomputable def koszulToPowPairLeft (f : R) (n t : ℕ) :
    (powAlgebra (fun _ : Fin 1 => f) n).Hom (powPairAlgebra f n t) where
  toAlgebraHom := ExteriorAlgebra.map (powPairCoord R 0)
  map_grading _ _ ha :=
    map_mem_cohomologicalExteriorGrade R (Fin 1 → R) (Fin 2 → R) (powPairCoord R 0) ha
  map_d a := by
    change ExteriorAlgebra.map (powPairCoord R 0)
        (contraction (seqDual fun _ : Fin 1 => f ^ n) a) =
      contraction (seqDual (powPairSeq f n t)) (ExteriorAlgebra.map (powPairCoord R 0) a)
    rw [← seqDual_comp_powPairCoord_zero f n t]
    exact (contractLeft_exteriorAlgebraMap (powPairCoord R 0)
      (seqDual (powPairSeq f n t)) a).symm

/-- The homomorphism `K_t → K_{n,t}` sending the generator of `K_t` to `x`. -/
noncomputable def koszulToPowPairRight (f : R) (n t : ℕ) :
    (powAlgebra (fun _ : Fin 1 => f) t).Hom (powPairAlgebra f n t) where
  toAlgebraHom := ExteriorAlgebra.map (powPairCoord R 1)
  map_grading _ _ ha :=
    map_mem_cohomologicalExteriorGrade R (Fin 1 → R) (Fin 2 → R) (powPairCoord R 1) ha
  map_d a := by
    change ExteriorAlgebra.map (powPairCoord R 1)
        (contraction (seqDual fun _ : Fin 1 => f ^ t) a) =
      contraction (seqDual (powPairSeq f n t)) (ExteriorAlgebra.map (powPairCoord R 1) a)
    rw [← seqDual_comp_powPairCoord_one f n t]
    exact (contractLeft_exteriorAlgebraMap (powPairCoord R 1)
      (seqDual (powPairSeq f n t)) a).symm

/-- **The Koszul algebra of a pair of powers receives the tensor product.** The homomorphism
`K_n ⊗_R K_t → K_{n,t}` sends `a ⊗ b` to the product of the image of `a` under `K_n → K_{n,t}`
and the image of `b` under `K_t → K_{n,t}`. -/
noncomputable def powPairFromTensor (f : R) (n t : ℕ) :
    (tensorProduct (powAlgebra (fun _ : Fin 1 => f) n)
        (powAlgebra (fun _ : Fin 1 => f) t)).Hom (powPairAlgebra f n t) :=
  tensorLift
    (anticommutesAlong_cohomological (koszulToPowPairLeft f n t) (koszulToPowPairRight f n t))

end TensorFactors

section PowPairToKoszul

/-- The linear map `R² → R` with matrix `(f^{n-t}, 1)`: it sends the generator `y` of `K_{n,t}`
to `f^{n-t} x` and the generator `x` to `x`. -/
def powPairProj (f : R) (n t : ℕ) : (Fin 2 → R) →ₗ[R] (Fin 1 → R) where
  toFun v := fun _ => f ^ (n - t) * v 0 + v 1
  map_add' v w := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The map `powPairProj f n t` sends `v` to `f^{n-t} v₀ + v₁`. -/
@[simp] theorem powPairProj_apply (f : R) (n t : ℕ) (v : Fin 2 → R) (i : Fin 1) :
    powPairProj f n t v i = f ^ (n - t) * v 0 + v 1 := rfl

/-- For `t ≤ n`, the functional of `K_t` composed with `powPairProj f n t` is the functional of
`K_{n,t}`. -/
theorem seqDual_comp_powPairProj (f : R) {n t : ℕ} (ht : t ≤ n) :
    (seqDual fun _ : Fin 1 => f ^ t) ∘ₗ powPairProj f n t = seqDual (powPairSeq f n t) := by
  have hf : f ^ (n - t) * f ^ t = f ^ n := by rw [← pow_add]; congr 1; omega
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, seqDual_apply, seqDual_apply, Fin.sum_univ_one, Fin.sum_univ_two,
    powPairProj_apply, powPairSeq_zero, powPairSeq_one, ← hf]
  ring

/-- **The multiplication homomorphism `K_{n,t} → K_t`** for `t ≤ n`: it sends the generator `y`
to `f^{n-t} x` and the generator `x` to `x`. -/
noncomputable def powPairToKoszul (f : R) {n t : ℕ} (ht : t ≤ n) :
    (powPairAlgebra f n t).Hom (powAlgebra (fun _ : Fin 1 => f) t) where
  toAlgebraHom := ExteriorAlgebra.map (powPairProj f n t)
  map_grading _ _ ha :=
    map_mem_cohomologicalExteriorGrade R (Fin 2 → R) (Fin 1 → R) (powPairProj f n t) ha
  map_d a := by
    change ExteriorAlgebra.map (powPairProj f n t)
        (contraction (seqDual (powPairSeq f n t)) a) =
      contraction (seqDual fun _ : Fin 1 => f ^ t)
        (ExteriorAlgebra.map (powPairProj f n t) a)
    rw [← seqDual_comp_powPairProj f ht]
    exact (contractLeft_exteriorAlgebraMap (powPairProj f n t)
      (seqDual fun _ : Fin 1 => f ^ t) a).symm

/-- The algebra homomorphism underlying `K_{n,t} → K_t` is the map of exterior algebras induced
by `powPairProj f n t`. -/
@[simp]
theorem powPairToKoszul_toAlgebraHom (f : R) {n t : ℕ} (ht : t ≤ n) :
    (powPairToKoszul f ht).toAlgebraHom = ExteriorAlgebra.map (powPairProj f n t) := rfl

/-- The map `powPairProj f n t` restricted along the first coordinate is multiplication by
`f^{n-t}`. -/
theorem powPairProj_comp_powPairCoord_zero (f : R) (n t : ℕ) :
    powPairProj f n t ∘ₗ powPairCoord R 0 = LinearMap.mulLeft R fun _ : Fin 1 => f ^ (n - t) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [LinearMap.comp_apply, powPairCoord_apply, powPairProj_apply, LinearMap.mulLeft_apply,
    Pi.mul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (by decide), add_zero,
    Subsingleton.elim i 0]

/-- The map `powPairProj f n t` restricted along the second coordinate is the identity. -/
theorem powPairProj_comp_powPairCoord_one (f : R) (n t : ℕ) :
    powPairProj f n t ∘ₗ powPairCoord R 1 = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [LinearMap.comp_apply, powPairCoord_apply, powPairProj_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide), mul_zero, zero_add, LinearMap.id_apply,
    Subsingleton.elim i 0]

/-- The map of exterior algebras induced by `powPairProj f n t` sends `y` to `f^{n-t}` times the
generator of the exterior algebra on `R`. -/
theorem map_powPairProj_powPairY (f : R) (n t : ℕ) :
    ExteriorAlgebra.map (powPairProj f n t) (powPairY R) =
      f ^ (n - t) • ExteriorAlgebra.ι R (fun _ => 1) := by
  rw [powPairY, ExteriorAlgebra.map_apply_ι, ← map_smul]
  congr 1
  funext i
  rw [Pi.smul_apply, smul_eq_mul, powPairProj_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide), add_zero, mul_one]

/-- The map of exterior algebras induced by `powPairProj f n t` sends `x` to the generator of
the exterior algebra on `R`. -/
theorem map_powPairProj_powPairX (f : R) (n t : ℕ) :
    ExteriorAlgebra.map (powPairProj f n t) (powPairX R) =
      ExteriorAlgebra.ι R (fun _ : Fin 1 => (1 : R)) := by
  rw [powPairX, ExteriorAlgebra.map_apply_ι]
  congr 1
  funext i
  rw [powPairProj_apply, Pi.single_eq_same, Pi.single_eq_of_ne (by decide), mul_zero, zero_add]

/-- The homomorphism `K_{n,t} → K_t` sends the generator `y` to `f^{n-t}` times the generator
of `K_t`. -/
theorem powPairToKoszul_y (f : R) {n t : ℕ} (ht : t ≤ n) :
    (powPairToKoszul f ht).toAlgebraHom (powPairY R) =
      f ^ (n - t) • ExteriorAlgebra.ι R (fun _ => 1) :=
  map_powPairProj_powPairY f n t

/-- The homomorphism `K_{n,t} → K_t` sends the generator `x` to the generator of `K_t`. -/
theorem powPairToKoszul_x (f : R) {n t : ℕ} (ht : t ≤ n) :
    (powPairToKoszul f ht).toAlgebraHom (powPairX R) =
      ExteriorAlgebra.ι R (fun _ : Fin 1 => (1 : R)) :=
  map_powPairProj_powPairX f n t

/-- The homomorphism `K_n ⊗_R K_t → K_{n,t}` restricts on the left factor to the map sending
the generator of `K_n` to `y`. -/
theorem powPairFromTensor_comp_includeLeft (f : R) (n t : ℕ) :
    (powPairFromTensor f n t).toAlgebraHom.comp
        (GradedTensorProduct.includeLeft (powAlgebra (fun _ : Fin 1 => f) n).grading
          (powAlgebra (fun _ : Fin 1 => f) t).grading) =
      ExteriorAlgebra.map (powPairCoord R 0) :=
  tensorLiftAlgebraHom_comp_includeLeft
    (anticommutesAlong_cohomological (koszulToPowPairLeft f n t) (koszulToPowPairRight f n t))

/-- The homomorphism `K_n ⊗_R K_t → K_{n,t}` restricts on the right factor to the map sending
the generator of `K_t` to `x`. -/
theorem powPairFromTensor_comp_includeRight (f : R) (n t : ℕ) :
    (powPairFromTensor f n t).toAlgebraHom.comp
        (GradedTensorProduct.includeRight (powAlgebra (fun _ : Fin 1 => f) n).grading
          (powAlgebra (fun _ : Fin 1 => f) t).grading) =
      ExteriorAlgebra.map (powPairCoord R 1) :=
  tensorLiftAlgebraHom_comp_includeRight
    (anticommutesAlong_cohomological (koszulToPowPairLeft f n t) (koszulToPowPairRight f n t))

end PowPairToKoszul

section ComparisonToPowPair

/-- The linear map `R² → R²` sending the `x` coordinate of `B_{N,t}` to the `x` coordinate of
`K_{n,t}` and the `z` coordinate to `f^{N-n}` times the `y` coordinate. -/
def comparisonPairProj (f : R) (N n : ℕ) : (Fin 2 → R) →ₗ[R] (Fin 2 → R) where
  toFun v := fun j => if j = 0 then f ^ (N - n) * v 1 else v 0
  map_add' v w := by
    funext j
    simp only [Pi.add_apply]
    split_ifs with hj
    · ring
    · rfl
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs with hj
    · ring
    · rfl

/-- The map `comparisonPairProj f N n` sends `v` to `(f^{N-n} v₁, v₀)`. -/
theorem comparisonPairProj_apply (f : R) (N n : ℕ) (v : Fin 2 → R) (j : Fin 2) :
    comparisonPairProj f N n v j = if j = 0 then f ^ (N - n) * v 1 else v 0 := rfl

/-- The first coordinate of `comparisonPairProj f N n v` is `f^{N-n} v₁`. -/
@[simp] theorem comparisonPairProj_apply_zero (f : R) (N n : ℕ) (v : Fin 2 → R) :
    comparisonPairProj f N n v 0 = f ^ (N - n) * v 1 := rfl

/-- The second coordinate of `comparisonPairProj f N n v` is `v₀`. -/
@[simp] theorem comparisonPairProj_apply_one (f : R) (N n : ℕ) (v : Fin 2 → R) :
    comparisonPairProj f N n v 1 = v 0 := rfl

/-- The map `comparisonPairProj f N n` sends the first basis vector to the second. -/
theorem comparisonPairProj_single_zero (f : R) (N n : ℕ) :
    comparisonPairProj f N n (Pi.single 0 1) = Pi.single 1 (1 : R) := by
  funext j
  fin_cases j <;> simp

/-- The map `comparisonPairProj f N n` sends the second basis vector to `f^{N-n}` times the
first. -/
theorem comparisonPairProj_single_one (f : R) (N n : ℕ) :
    comparisonPairProj f N n (Pi.single 1 1) = Pi.single 0 (f ^ (N - n)) := by
  funext j
  fin_cases j <;> simp

/-- For `n ≤ N`, the functional of `K_{n,t}` composed with `comparisonPairProj f N n` is the
functional `comparisonSeq f N t` of `R⟨x, z⟩`. -/
theorem seqDual_comp_comparisonPairProj (f : R) {N n t : ℕ} (hn : n ≤ N) :
    seqDual (powPairSeq f n t) ∘ₗ comparisonPairProj f N n = seqDual (comparisonSeq f N t) := by
  have hf : f ^ (N - n) * f ^ n = f ^ N := by rw [← pow_add]; congr 1; omega
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, seqDual_apply, seqDual_apply, Fin.sum_univ_two, Fin.sum_univ_two,
    comparisonPairProj_apply_zero, comparisonPairProj_apply_one, powPairSeq_zero, powPairSeq_one,
    comparisonSeq_zero, comparisonSeq_one, ← hf]
  ring

/-- The map `R⟨x, z⟩ → R⟨y, x⟩` of exterior algebras induced by `comparisonPairProj`. -/
noncomputable def comparisonPairExteriorMap (f : R) (N n : ℕ) :
    comparisonExterior R →ₐ[R] ExteriorAlgebra R (Fin 2 → R) :=
  ExteriorAlgebra.map (comparisonPairProj f N n)

/-- The map `R⟨x, z⟩ → R⟨y, x⟩` sends `x` to `x`. -/
theorem comparisonPairExteriorMap_x (f : R) (N n : ℕ) :
    comparisonPairExteriorMap f N n (comparisonX R) = powPairX R := by
  rw [comparisonPairExteriorMap, comparisonX, ExteriorAlgebra.map_apply_ι,
    comparisonPairProj_single_zero, powPairX]

/-- The map `R⟨x, z⟩ → R⟨y, x⟩` sends `z` to `f^{N-n} y`. -/
theorem comparisonPairExteriorMap_z (f : R) (N n : ℕ) :
    comparisonPairExteriorMap f N n (comparisonZ R) = f ^ (N - n) • powPairY R := by
  have hsingle : Pi.single (0 : Fin 2) (f ^ (N - n)) =
      f ^ (N - n) • Pi.single (0 : Fin 2) (1 : R) := by
    funext j
    by_cases hj : j = 0
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [comparisonPairExteriorMap, comparisonZ, ExteriorAlgebra.map_apply_ι,
    comparisonPairProj_single_one, hsingle, _root_.map_smul, powPairY]

/-- The map `R⟨x, z⟩ → R⟨y, x⟩` preserves the exterior degree. -/
theorem comparisonPairExteriorMap_mem (f : R) (N n m : ℕ) {a : comparisonExterior R}
    (ha : a ∈ exteriorGrade R (Fin 2 → R) m) :
    comparisonPairExteriorMap f N n a ∈ exteriorGrade R (Fin 2 → R) m :=
  ExteriorAlgebra.map_mem_exteriorPower (comparisonPairProj f N n) ha

/-- The cycle `z - f^{N-t} x` of `B_{N,t}` maps to the differential of `-f^{N-n-t} y x`. -/
theorem comparisonPairExteriorMap_comparisonCycle (f : R) (N n t : ℕ) :
    comparisonPairExteriorMap f N n (comparisonCycle f N t) =
      f ^ (N - n) • powPairY R - f ^ (N - t) • powPairX R := by
  rw [comparisonCycle, map_sub, map_smul, comparisonPairExteriorMap_x,
    comparisonPairExteriorMap_z]

/-- For `n ≤ N`, the map `R⟨x, z⟩ → R⟨y, x⟩` intertwines the differential of `R⟨x, z⟩` with
the differential of `K_{n,t}`. -/
theorem comparisonPairExteriorMap_comp_differential (f : R) {N n t : ℕ} (hn : n ≤ N)
    (a : comparisonExterior R) :
    comparisonPairExteriorMap f N n (comparisonExteriorDifferential f N t a) =
      contraction (seqDual (powPairSeq f n t)) (comparisonPairExteriorMap f N n a) := by
  rw [comparisonExteriorDifferential, comparisonPairExteriorMap,
    ← seqDual_comp_comparisonPairProj (t := t) f hn]
  exact (contractLeft_exteriorAlgebraMap (comparisonPairProj f N n)
    (seqDual (powPairSeq f n t)) a).symm

/-- The ring homomorphism `B_{N,t} → K_{n,t}` sending the even generator `u` to
`-f^{N-n-t} y x`: on `a u⁽ᵏ⁾` it is the image of `a` times the `k`-th divided power of
`-f^{N-n-t} y x`. -/
noncomputable def comparisonPairLift (f : R) (N n t : ℕ) :
    EvenVariableAlgebra (comparisonExterior R) →+* ExteriorAlgebra R (Fin 2 → R) :=
  evenLift (exteriorGrade R (Fin 2 → R)) (exteriorGrade R (Fin 2 → R)) 2 (by norm_num) even_two
    (comparisonPairExteriorMap f N n).toRingHom
    (fun m _ ha => comparisonPairExteriorMap_mem f N n m ha)
    (exteriorDividedPowerStructure R 2) (powPairU f N n t) (powPairU_mem f N n t)

/-- The map `B_{N,t} → K_{n,t}` sends `a u⁽ᵏ⁾` to the image of `a` times the `k`-th divided power
of `-f^{N-n-t} y x`. -/
theorem comparisonPairLift_monomial (f : R) (N n t k : ℕ) (a : comparisonExterior R) :
    comparisonPairLift f N n t (EvenVariableAlgebra.monomial k a) =
      comparisonPairExteriorMap f N n a *
        (exteriorDividedPowerStructure R 2).dpow k (powPairU f N n t) :=
  evenLift_monomial (exteriorGrade R (Fin 2 → R)) (exteriorGrade R (Fin 2 → R)) 2 (by norm_num)
    even_two _ _ _ (powPairU f N n t) (powPairU_mem f N n t) k a

/-- The map `B_{N,t} → K_{n,t}` sends `a u⁽⁰⁾` to the image of `a` in `R⟨y, x⟩`. -/
theorem comparisonPairLift_monomial_zero (f : R) (N n t : ℕ) (a : comparisonExterior R) :
    comparisonPairLift f N n t (EvenVariableAlgebra.monomial 0 a) =
      comparisonPairExteriorMap f N n a := by
  rw [comparisonPairLift_monomial,
    (exteriorDividedPowerStructure R 2).dpow_zero (powPairU_mem_positiveEvenPart f N n t), mul_one]

/-- On the coefficient algebra `R⟨x, z⟩`, the map `B_{N,t} → K_{n,t}` is
`comparisonPairExteriorMap`. -/
theorem comparisonPairLift_coeffEmbedding (f : R) (N n t : ℕ) (a : comparisonExterior R) :
    comparisonPairLift f N n t (EvenVariableAlgebra.coeffEmbedding a) =
      comparisonPairExteriorMap f N n a := by
  rw [EvenVariableAlgebra.coeffEmbedding_apply, comparisonPairLift_monomial_zero]

/-- The map `B_{N,t} → K_{n,t}` sends elements of total degree `m` of `B_{N,t}`, with `u` in
degree `2`, into the `m`-th exterior power of `R²`. -/
theorem comparisonPairLift_mem (f : R) (N n t m : ℕ)
    {x : EvenVariableAlgebra (comparisonExterior R)}
    (hx : x ∈ EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2 m) :
    comparisonPairLift f N n t x ∈ exteriorGrade R (Fin 2 → R) m :=
  evenLift_mem_grade (exteriorGrade R (Fin 2 → R)) (exteriorGrade R (Fin 2 → R)) 2 (by norm_num)
    even_two _ _ _ (powPairU f N n t) (powPairU_mem f N n t) m x hx

/-- The map `B_{N,t} → K_{n,t}` preserves the cohomological grading. -/
theorem comparisonPairLift_mem_grading (f : R) (N n t : ℕ) (m : ℤ)
    {x : EvenVariableAlgebra (comparisonExterior R)}
    (hx : x ∈ cohomologicalGrade (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) m) :
    comparisonPairLift f N n t x ∈ cohomologicalExteriorGrade R (Fin 2 → R) m := by
  by_cases hm : m ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
    rw [cohomologicalGrade_neg_natCast] at hx
    rw [cohomologicalExteriorGrade_neg_natCast]
    exact comparisonPairLift_mem f N n t k hx
  · have h0 : x = 0 := eq_zero_of_mem_cohomologicalGrade_of_pos _ (by omega) hx
    rw [h0, _root_.map_zero]
    exact Submodule.zero_mem _

/-- The ring homomorphism `B_{N,t} → K_{n,t}` is a homomorphism of `R`-algebras. -/
noncomputable def comparisonPairAlgHom (f : R) (N n t : ℕ) :
    EvenVariableAlgebra (comparisonExterior R) →ₐ[R] ExteriorAlgebra R (Fin 2 → R) :=
  { comparisonPairLift f N n t with
    commutes' := fun r => by
      have h : algebraMap R (EvenVariableAlgebra (comparisonExterior R)) r =
          EvenVariableAlgebra.coeffEmbedding (algebraMap R (comparisonExterior R) r) := rfl
      change comparisonPairLift f N n t (algebraMap R _ r) = _
      rw [h, comparisonPairLift_coeffEmbedding]
      exact (comparisonPairExteriorMap f N n).commutes r }

/-- The `R`-algebra homomorphism `B_{N,t} → K_{n,t}` agrees with the ring homomorphism
`comparisonPairLift f N n t`. -/
theorem comparisonPairAlgHom_apply (f : R) (N n t : ℕ)
    (x : EvenVariableAlgebra (comparisonExterior R)) :
    comparisonPairAlgHom f N n t x = comparisonPairLift f N n t x := rfl

/-- The map `B_{N,t} → K_{n,t}` commutes with the differentials. -/
theorem comparisonPairAlgHom_comp_differential (f : R) {N n t : ℕ} (hN : n + t ≤ N)
    (x : EvenVariableAlgebra (comparisonExterior R)) :
    comparisonPairAlgHom f N n t (comparisonDifferential f N t x) =
      contraction (seqDual (powPairSeq f n t)) (comparisonPairAlgHom f N n t x) := by
  have hdga : IsDifferentialGradedAlgebra (exteriorGrade R (Fin 2 → R))
      (contraction (seqDual (powPairSeq f n t))) :=
    isDifferentialGradedAlgebra_contraction _
  have hcomp : IsCompatibleWithDifferential (exteriorDividedPowerStructure R 2)
      (contraction (seqDual (powPairSeq f n t))) :=
    isCompatibleWithDifferential_exteriorDividedPowerStructure R 2 _
  have hcycle : contraction (seqDual (powPairSeq f n t)) (powPairU f N n t) =
      comparisonPairExteriorMap f N n (comparisonCycle f N t) := by
    rw [comparisonPairExteriorMap_comparisonCycle]
    exact powPairAlgebra_d_powPairU f hN
  have hsign : ∀ a : comparisonExterior R,
      comparisonPairExteriorMap f N n (signRingHom (exteriorGrade R (Fin 2 → R)) 1 a) =
        signRingHom (exteriorGrade R (Fin 2 → R)) 1 (comparisonPairExteriorMap f N n a) :=
    fun a => algHom_signRingHom (exteriorGrade R (Fin 2 → R)) (exteriorGrade R (Fin 2 → R))
      (comparisonPairExteriorMap f N n)
      (fun m _ ha => comparisonPairExteriorMap_mem f N n m ha) 1 a
  have hmon : ∀ (k : ℕ) (a : comparisonExterior R),
      comparisonPairAlgHom f N n t
          (comparisonDifferential f N t (EvenVariableAlgebra.monomial k a)) =
        contraction (seqDual (powPairSeq f n t))
          (comparisonPairAlgHom f N n t (EvenVariableAlgebra.monomial k a)) := by
    intro k a
    rw [comparisonPairAlgHom_apply, comparisonPairAlgHom_apply, comparisonPairLift_monomial,
      comparisonDifferential, evenPolynomialDifferential_monomial]
    split_ifs with hk
    · subst hk
      rw [add_zero, comparisonPairLift_monomial_zero,
        (exteriorDividedPowerStructure R 2).dpow_zero (powPairU_mem_positiveEvenPart f N n t),
        mul_one]
      exact comparisonPairExteriorMap_comp_differential f (by omega) a
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
      rw [_root_.map_add, comparisonPairLift_monomial, comparisonPairLift_monomial,
        differential_mul_signRingHom (exteriorGrade R (Fin 2 → R))
          (contraction (seqDual (powPairSeq f n t))) (comparisonPairExteriorMap f N n a)
          ((exteriorDividedPowerStructure R 2).dpow (m + 1) (powPairU f N n t)),
        IsCompatibleWithDifferential.d_dpow
          (γ := exteriorDividedPowerStructure R 2) (n := m + 1) (by omega)
          (powPairU_mem_positiveEvenPart f N n t),
        hcycle, comparisonPairExteriorMap_comp_differential f (by omega) a, _root_.map_mul,
        hsign a, mul_assoc]
  induction x using EvenVariableAlgebra.induction_on with
  | zero => simp
  | add k a y hy =>
    rw [_root_.map_add, _root_.map_add, _root_.map_add, _root_.map_add, hy, hmon k a]

/-- **The arrow of Tag 0GZ7, read in the Koszul algebra of the pair `(f^n, f^t)`.** For
`N ≥ n + t` the homomorphism `B_{N,t} → K_{n,t}` of differential graded algebras sends `x` to
`x`, `z` to `f^{N-n} y` and `u` to `-f^{N-n-t} y x`. -/
noncomputable def comparisonToPowPair (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N) :
    (comparisonAlgebra f h).Hom (powPairAlgebra f n t) where
  toAlgebraHom := comparisonPairAlgHom f N n t
  map_grading := by
    intro m a ha
    rw [comparisonAlgebra_grading] at ha
    exact comparisonPairLift_mem_grading f N n t m ha
  map_d := fun a => comparisonPairAlgHom_comp_differential f hN a

/-- The homomorphism `B_{N,t} → K_{n,t}` restricts on the coefficient algebra `R⟨x, z⟩` to
`comparisonPairExteriorMap`. -/
private theorem comparisonToPowPair_inclusion (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N)
    (a : comparisonExterior R) :
    (comparisonToPowPair f h hN).toAlgebraHom (comparisonInclusion R a) =
      comparisonPairExteriorMap f N n a :=
  comparisonPairLift_coeffEmbedding f N n t a

/-- The homomorphism `B_{N,t} → K_{n,t}` sends the odd generator `x` to `x`. -/
theorem comparisonToPowPair_x (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N) :
    (comparisonToPowPair f h hN).toAlgebraHom (comparisonInclusion R (comparisonX R)) =
      powPairX R :=
  (comparisonToPowPair_inclusion f h hN _).trans (comparisonPairExteriorMap_x f N n)

/-- The homomorphism `B_{N,t} → K_{n,t}` sends the odd generator `z` to `f^{N-n} y`. -/
theorem comparisonToPowPair_z (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N) :
    (comparisonToPowPair f h hN).toAlgebraHom (comparisonInclusion R (comparisonZ R)) =
      f ^ (N - n) • powPairY R :=
  (comparisonToPowPair_inclusion f h hN _).trans (comparisonPairExteriorMap_z f N n)

/-- The homomorphism `B_{N,t} → K_{n,t}` sends the even generator `u` to `-f^{N-n-t} y x`. -/
theorem comparisonToPowPair_u (f : R) {N n t : ℕ} (h : t ≤ N) (hN : n + t ≤ N) :
    (comparisonToPowPair f h hN).toAlgebraHom (comparisonU R) = powPairU f N n t := by
  change comparisonPairLift f N n t (EvenVariableAlgebra.monomial 1 1) = _
  rw [comparisonPairLift_monomial, map_one, one_mul,
    (exteriorDividedPowerStructure R 2).dpow_one (powPairU_mem_positiveEvenPart f N n t)]

end ComparisonToPowPair

section Composite

/-- For `t ≤ n ≤ N`, the composite of `comparisonPairProj f N n` and `powPairProj f n t` is
`comparisonProj f N t`. -/
theorem powPairProj_comp_comparisonPairProj (f : R) {N n t : ℕ} (ht : t ≤ n) (hn : n ≤ N) :
    powPairProj f n t ∘ₗ comparisonPairProj f N n = comparisonProj f N t := by
  have hf : f ^ (n - t) * f ^ (N - n) = f ^ (N - t) := by rw [← pow_add]; congr 1; omega
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [LinearMap.comp_apply, powPairProj_apply, comparisonPairProj_apply_zero,
    comparisonPairProj_apply_one, comparisonProj_apply, ← hf]
  ring

/-- For `t ≤ n ≤ N`, the composite of the maps of exterior algebras `R⟨x, z⟩ → R⟨y, x⟩` and
`R⟨y, x⟩ → R⟨x⟩` is `comparisonExteriorMap f N t`. -/
theorem powPairToKoszul_comp_comparisonPairExteriorMap (f : R) {N n t : ℕ} (ht : t ≤ n)
    (hn : n ≤ N) (a : comparisonExterior R) :
    ExteriorAlgebra.map (powPairProj f n t) (comparisonPairExteriorMap f N n a) =
      comparisonExteriorMap f N t a := by
  rw [comparisonPairExteriorMap, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    powPairProj_comp_comparisonPairProj f ht hn, comparisonExteriorMap]

/-- The element `-f^{N-n-t} y x` of `K_{n,t}` maps to zero in `K_t`, because the generator of
`K_t` squares to zero. -/
theorem powPairToKoszul_powPairU (f : R) (N n t : ℕ) :
    ExteriorAlgebra.map (powPairProj f n t) (powPairU f N n t) = 0 := by
  rw [powPairU, map_neg, map_smul, map_mul, map_powPairProj_powPairY,
    map_powPairProj_powPairX, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero, smul_zero,
    neg_zero]

/-- The composite of the algebra homomorphisms underlying `B_{N,t} → K_{n,t}` and
`K_{n,t} → K_t` is the one underlying the comparison homomorphism `B_{N,t} → K_t`. -/
theorem powPairProjMap_comp_comparisonPairAlgHom (f : R) {N n t : ℕ} (ht : t ≤ n) (hn : n ≤ N) :
    (ExteriorAlgebra.map (powPairProj f n t)).comp (comparisonPairAlgHom f N n t) =
      comparisonAlgHom f N t := by
  have hdpow : ∀ (k : ℕ) (x : ExteriorAlgebra R (Fin 2 → R)),
      x ∈ positiveEvenPart (exteriorGrade R (Fin 2 → R)) →
      ExteriorAlgebra.map (powPairProj f n t) ((exteriorDividedPowerStructure R 2).dpow k x) =
        (exteriorDividedPowerStructure R 1).dpow k
          (ExteriorAlgebra.map (powPairProj f n t) x) := fun k x hx =>
    (algHom_map_dpow_exteriorDividedPowerStructure R 2 (exteriorGrade R (Fin 1 → R))
      (exteriorDividedPowerStructure R 1) (ExteriorAlgebra.map (powPairProj f n t))
      (fun _ _ hz => ExteriorAlgebra.map_mem_exteriorPower _ hz) k hx).symm
  have hmon : ∀ (k : ℕ) (a : comparisonExterior R),
      ExteriorAlgebra.map (powPairProj f n t)
          (comparisonPairLift f N n t (EvenVariableAlgebra.monomial k a)) =
        comparisonLift f N t (EvenVariableAlgebra.monomial k a) := by
    intro k a
    rw [comparisonPairLift_monomial, comparisonLift_monomial, _root_.map_mul,
      powPairToKoszul_comp_comparisonPairExteriorMap f ht hn a,
      hdpow k _ (powPairU_mem_positiveEvenPart f N n t), powPairToKoszul_powPairU]
  refine AlgHom.ext fun x => ?_
  change ExteriorAlgebra.map (powPairProj f n t) (comparisonPairLift f N n t x) =
    comparisonLift f N t x
  induction x using EvenVariableAlgebra.induction_on with
  | zero => simp
  | add k a y hy =>
    rw [_root_.map_add, _root_.map_add, _root_.map_add, hy, hmon k a]

/-- **The composite `B_{N,t} → K_{n,t} → K_t` is the comparison homomorphism `B_{N,t} → K_t`.**
This is the "pleasant computation" of Tag 0GZ7: composing the arrow into `K_{n,t}` with the
multiplication map recovers the homomorphism `B_{N,t} → K_t`. -/
theorem powPairToKoszul_comp_comparisonToPowPair (f : R) {N n t : ℕ} (h : t ≤ N) (ht : t ≤ n)
    (hN : n + t ≤ N) :
    ((powPairToKoszul f ht).comp (comparisonToPowPair f h hN)).toAlgebraHom =
      (comparisonToKoszul f h).toAlgebraHom :=
  powPairProjMap_comp_comparisonPairAlgHom f ht (by omega)

end Composite

end Koszul
