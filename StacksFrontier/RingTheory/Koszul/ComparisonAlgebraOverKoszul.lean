module

public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraMap
public import StacksFrontier.RingTheory.Koszul.PowAlgebraMultiplication

/-!
# `R⟨x, z, u⟩` as a differential graded algebra over the Koszul algebra `K_N`

Let `f` be an element of a commutative ring `R` and let `N ≥ t ≥ 1`. The algebra
`B_{N,t} = R⟨x, z, u⟩` of `Koszul.comparisonAlgebra` receives the one-variable Koszul algebra
`K_N = R⟨z⟩` of `f ^ N` by sending the generator of `K_N` to the odd generator `z`, which is
legitimate because `d z = f ^ N`. Through this homomorphism `B_{N,t}` becomes a differential
graded `K_N`-algebra, and the comparison homomorphism `B_{N,t} → K_t` of
`Koszul.comparisonToKoszul` becomes a homomorphism of differential graded `K_N`-algebras: the
triangle
$$K_N \longrightarrow B_{N,t} \longrightarrow K_t$$
commutes with the transition homomorphism `τ_{N,t} : K_N → K_t`, which scales the generator by
`f^{N-t}`.

## Main definitions

* `Koszul.comparisonOddAlgebra`: the odd part `R⟨x, z⟩` of `B_{N,t}`, as an object of
  `DifferentialGradedAlgebra`.
* `Koszul.comparisonOddToAlgebra`: the inclusion `R⟨x, z⟩ → B_{N,t}` of the odd part, as a
  homomorphism of differential graded algebras.
* `Koszul.zInclusion`: the linear map `R → R²` onto the `z` coordinate.
* `Koszul.koszulToComparison`: the homomorphism `K_N → B_{N,t}` sending the generator of `K_N`
  to `z`.
* `Koszul.comparisonRestrictedModule` and `Koszul.comparisonRestrictedObject`: `B_{N,t}` as a
  left differential graded `K_N`-module, and as an object of the derived category
  `D(K_Nᵒᵖᵖ, d)`.

## Main results

* `Koszul.seqDual_comp_zInclusion`: the functional `x ↦ f^t`, `z ↦ f^N` of `R⟨x, z⟩` pulls back
  along `zInclusion` to the functional `z ↦ f^N` of `K_N`.
* `Koszul.koszulToComparison_ι`: the homomorphism `K_N → B_{N,t}` sends the generator of `K_N`
  to `z`.
* `Koszul.comparisonToKoszul_comp_koszulToComparison`: the composite
  `K_N → B_{N,t} → K_t` is the transition homomorphism `τ_{N,t}`, so `B_{N,t} → K_t` is a
  homomorphism of differential graded `K_N`-algebras.

## Implementation notes

The homomorphism `K_N → B_{N,t}` is assembled in two steps, because `B_{N,t}` is built as an
even-variable divided power extension of its odd part. The first step is the map of Koszul
algebras `R⟨z⟩ → R⟨x, z⟩` induced by the linear map `R → R²` onto the second coordinate, which
pulls the functional of `R⟨x, z⟩` back to the functional of `K_N`; the second is the inclusion
of the coefficients of the even-variable extension, which commutes with the differentials by
`Koszul.comparisonDifferential_inclusion`. The commuting triangle is then checked on the single
generator of `K_N` with `ExteriorAlgebra.hom_ext`.

A left differential graded module is recorded as a right module over the graded opposite
algebra, so the derived category in which `B_{N,t}` is viewed is `D(K_Nᵒᵖᵖ, d)`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/


@[expose] public section

namespace Koszul

universe u

open scoped ExteriorAlgebra

open DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

section OddPart

/-- The odd part `R⟨x, z⟩` of `B_{N,t}`, as an object of `DifferentialGradedAlgebra`: the
exterior algebra on `R²` with the two generators in cohomological degree `-1` and with
`d x = f ^ t`, `d z = f ^ N`. -/
noncomputable def comparisonOddAlgebra (f : R) (N t : ℕ) : DifferentialGradedAlgebra.{u, u} R :=
  cohomologicalDifferentialGradedAlgebra R (Fin 2 → R) (seqDual (comparisonSeq f N t))

/-- The underlying algebra of `comparisonOddAlgebra f N t` is the exterior algebra on `R²`. -/
theorem comparisonOddAlgebra_A (f : R) (N t : ℕ) :
    (comparisonOddAlgebra f N t).A = comparisonExterior R := rfl

/-- The grading of `comparisonOddAlgebra f N t` is the cohomological grading of the exterior
algebra on `R²`. -/
theorem comparisonOddAlgebra_grading (f : R) (N t : ℕ) :
    (comparisonOddAlgebra f N t).grading = cohomologicalExteriorGrade R (Fin 2 → R) := rfl

/-- The differential of `comparisonOddAlgebra f N t` is `comparisonExteriorDifferential f N t`. -/
theorem comparisonOddAlgebra_d (f : R) (N t : ℕ) :
    (comparisonOddAlgebra f N t).d = comparisonExteriorDifferential f N t := rfl

/-- The inclusion of the odd part into `B_{N,t}` preserves the cohomological grading. -/
theorem comparisonInclusion_mem_cohomologicalGrade (n : ℤ) {a : comparisonExterior R}
    (ha : a ∈ cohomologicalExteriorGrade R (Fin 2 → R) n) :
    comparisonInclusion R a ∈
      cohomologicalGrade (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) n := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [cohomologicalExteriorGrade_neg_natCast] at ha
    rw [cohomologicalGrade_neg_natCast]
    exact (EvenVariableAlgebra.coeffEmbedding_mem_grade_iff _ 2 k a).2 ha
  · rw [eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R (Fin 2 → R) (by omega) ha,
      _root_.map_zero]
    exact Submodule.zero_mem _

/-- The inclusion of the odd part `R⟨x, z⟩` into `B_{N,t}`, as a homomorphism of differential
graded algebras. -/
noncomputable def comparisonOddToAlgebra (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonOddAlgebra f N t).Hom (comparisonAlgebra f h) where
  toAlgebraHom := comparisonInclusion R
  map_grading n _ ha := comparisonInclusion_mem_cohomologicalGrade n ha
  map_d a := (comparisonDifferential_inclusion f N t a).symm

/-- The underlying algebra homomorphism of `comparisonOddToAlgebra f h` is
`comparisonInclusion R`. -/
@[simp]
theorem comparisonOddToAlgebra_toAlgebraHom (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonOddToAlgebra f h).toAlgebraHom = comparisonInclusion R := rfl

end OddPart

section KoszulToComparison

/-- The linear map `R → R²` onto the second coordinate, which sends the generator of `K_N` to
the odd generator `z` of `B_{N,t}`. -/
def zInclusion (R : Type u) [CommRing R] : (Fin 1 → R) →ₗ[R] (Fin 2 → R) :=
  (LinearMap.single R (fun _ : Fin 2 => R) 1).comp (LinearMap.proj 0)

/-- `zInclusion R` sends `v` to `v 0` placed in the second coordinate. -/
@[simp] theorem zInclusion_apply (v : Fin 1 → R) :
    zInclusion R v = Pi.single 1 (v 0) := rfl

/-- The functional `x ↦ f^t`, `z ↦ f^N` of `R⟨x, z⟩` pulls back along `zInclusion` to the
functional `z ↦ f^N` whose contraction is the differential of `K_N`. -/
theorem seqDual_comp_zInclusion (f : R) (N t : ℕ) :
    seqDual (comparisonSeq f N t) ∘ₗ zInclusion R = seqDual fun _ : Fin 1 => f ^ N := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, zInclusion_apply, seqDual_apply_single, comparisonSeq_one,
    seqDual_apply, Fin.sum_univ_one]

/-- The map of Koszul algebras `K_N = R⟨z⟩ → R⟨x, z⟩` sending the generator of `K_N` to `z`. -/
noncomputable def koszulToComparisonOdd (f : R) (N t : ℕ) :
    (powAlgebra (fun _ : Fin 1 => f) N).Hom (comparisonOddAlgebra f N t) where
  toAlgebraHom := ExteriorAlgebra.map (zInclusion R)
  map_grading _ _ ha :=
    map_mem_cohomologicalExteriorGrade R (Fin 1 → R) (Fin 2 → R) (zInclusion R) ha
  map_d a := by
    change ExteriorAlgebra.map (zInclusion R)
        (contraction (seqDual fun _ : Fin 1 => f ^ N) a) =
      comparisonExteriorDifferential f N t (ExteriorAlgebra.map (zInclusion R) a)
    rw [comparisonExteriorDifferential, ← seqDual_comp_zInclusion f N t]
    exact (contractLeft_exteriorAlgebraMap (zInclusion R) (seqDual (comparisonSeq f N t)) a).symm

/-- The underlying algebra homomorphism of `koszulToComparisonOdd f N t` is the map of exterior
algebras induced by `zInclusion R`. -/
@[simp]
theorem koszulToComparisonOdd_toAlgebraHom (f : R) (N t : ℕ) :
    (koszulToComparisonOdd f N t).toAlgebraHom = ExteriorAlgebra.map (zInclusion R) := rfl

/-- The homomorphism `K_N → B_{N,t}` of differential graded algebras sending the generator of
`K_N` to the odd generator `z` of `B_{N,t}`. It exhibits `B_{N,t}` as a differential graded
algebra over `K_N`. -/
noncomputable def koszulToComparison (f : R) {N t : ℕ} (h : t ≤ N) :
    (powAlgebra (fun _ : Fin 1 => f) N).Hom (comparisonAlgebra f h) :=
  (comparisonOddToAlgebra f h).comp (koszulToComparisonOdd f N t)

/-- The homomorphism `K_N → B_{N,t}` sends the generator of `K_N` to `z`. -/
theorem koszulToComparison_ι (f : R) {N t : ℕ} (h : t ≤ N) :
    (koszulToComparison f h).toAlgebraHom (ExteriorAlgebra.ι R fun _ => 1) =
      comparisonInclusion R (comparisonZ R) := by
  change comparisonInclusion R
      (ExteriorAlgebra.map (zInclusion R) (ExteriorAlgebra.ι R fun _ => 1)) = _
  rw [ExteriorAlgebra.map_apply_ι, comparisonZ]
  congr 1

/-- The differential of `B_{N,t}` on the image of the generator of `K_N` is `f ^ N`, as it must
be for `K_N → B_{N,t}` to be a homomorphism of differential graded algebras. -/
theorem comparisonAlgebra_d_koszulToComparison_ι (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonAlgebra f h).d
        ((koszulToComparison f h).toAlgebraHom (ExteriorAlgebra.ι R fun _ => 1)) =
      algebraMap R (EvenVariableAlgebra (comparisonExterior R)) (f ^ N) := by
  rw [koszulToComparison_ι, comparisonAlgebra_d_z]

end KoszulToComparison

section Triangle

/-- **The comparison homomorphism `B_{N,t} → K_t` is a homomorphism of differential graded
`K_N`-algebras.** The composite `K_N → B_{N,t} → K_t` is the transition homomorphism
`τ_{N,t} : K_N → K_t`, which scales the generator by `f^{N-t}`. -/
theorem comparisonToKoszul_comp_koszulToComparison (f : R) {N t : ℕ} (ht : 1 ≤ t) (h : t ≤ N) :
    (comparisonToKoszul f h).toAlgebraHom.comp (koszulToComparison f h).toAlgebraHom =
      (powTransition (fun _ : Fin 1 => f) ht h).toAlgebraHom := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  have hleft : (koszulToComparison f h).toAlgebraHom (ExteriorAlgebra.ι R v) =
      comparisonInclusion R (ExteriorAlgebra.ι R (Pi.single 1 (v 0))) := by
    change comparisonInclusion R
        (ExteriorAlgebra.map (zInclusion R) (ExteriorAlgebra.ι R v)) = _
    rw [ExteriorAlgebra.map_apply_ι, zInclusion_apply]
  have hcomp : (comparisonToKoszul f h).toAlgebraHom
      (comparisonInclusion R (ExteriorAlgebra.ι R (Pi.single 1 (v 0)))) =
      ExteriorAlgebra.ι R fun _ => f ^ (N - t) * v 0 := by
    change comparisonLift f N t
        (EvenVariableAlgebra.coeffEmbedding (ExteriorAlgebra.ι R (Pi.single 1 (v 0)))) = _
    rw [comparisonLift_coeffEmbedding, comparisonExteriorMap, ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rw [comparisonProj_apply]
    simp
  have hright : (powTransition (fun _ : Fin 1 => f) ht h).toAlgebraHom (ExteriorAlgebra.ι R v) =
      ExteriorAlgebra.ι R fun _ => f ^ (N - t) * v 0 := by
    rw [powTransition_apply, ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rw [LinearMap.mulLeft_apply, Pi.mul_apply, Subsingleton.elim i 0]
  change (comparisonToKoszul f h).toAlgebraHom
      ((koszulToComparison f h).toAlgebraHom (ExteriorAlgebra.ι R v)) =
    (powTransition (fun _ : Fin 1 => f) ht h).toAlgebraHom (ExteriorAlgebra.ι R v)
  rw [hleft, hcomp, hright]

end Triangle

section RestrictedModule

open CategoryTheory DifferentialGradedAlgebra DifferentialGradedModule DifferentialGraded.Bimodule

/-- The homomorphism `K_N → B_{N,t}`, read on the graded opposite algebras. -/
noncomputable def oppKoszulToComparison (f : R) {N t : ℕ} (h : t ≤ N) :
    (oppAlgebra (powAlgebra (fun _ : Fin 1 => f) N)).Hom (oppAlgebra (comparisonAlgebra f h)) :=
  oppositeHom (DifferentialGradedAlgebra.opposite R (powAlgebra (fun _ : Fin 1 => f) N))
    (DifferentialGradedAlgebra.opposite R (comparisonAlgebra f h)) (koszulToComparison f h)

/-- `B_{N,t}` as a left differential graded `K_N`-module, with `K_N` acting through the
homomorphism `K_N → B_{N,t}`. Left modules are recorded as right modules over the graded
opposite algebra. -/
noncomputable def comparisonRestrictedModule (f : R) {N t : ℕ} (h : t ≤ N) :
    DifferentialGradedModule (oppAlgebra (powAlgebra (fun _ : Fin 1 => f) N)) :=
  restrictScalars (oppKoszulToComparison f h)
    (regularModule (oppAlgebra (comparisonAlgebra f h)))

/-- The underlying module of `B_{N,t}` as a left differential graded `K_N`-module is the graded
opposite of `B_{N,t}`. -/
theorem comparisonRestrictedModule_M (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonRestrictedModule f h).M = (oppAlgebra (comparisonAlgebra f h)).A := rfl

/-- The grading of `B_{N,t}` as a left differential graded `K_N`-module is the grading of the
graded opposite of `B_{N,t}`. -/
theorem comparisonRestrictedModule_grading (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonRestrictedModule f h).grading = (oppAlgebra (comparisonAlgebra f h)).grading := rfl

/-- The differential of `B_{N,t}` as a left differential graded `K_N`-module is the differential
of the graded opposite of `B_{N,t}`. -/
theorem comparisonRestrictedModule_d (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonRestrictedModule f h).d = (oppAlgebra (comparisonAlgebra f h)).d := rfl

/-- `B_{N,t}` as an object of the derived category `D(K_Nᵒᵖᵖ, d)` of left differential graded
`K_N`-modules. -/
noncomputable def comparisonRestrictedObject (f : R) {N t : ℕ} (h : t ≤ N) :
    derivedCategory' (oppAlgebra (powAlgebra (fun _ : Fin 1 => f) N)) :=
  (toHomotopyCategory (oppAlgebra (powAlgebra (fun _ : Fin 1 => f) N)) ⋙
      (quasiIsomorphisms' (oppAlgebra (powAlgebra (fun _ : Fin 1 => f) N))).Q).obj
    (comparisonRestrictedModule f h)

end RestrictedModule

end Koszul
