module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZeroGrading
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulTransition
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedProduct
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableDerivation

/-! # The exterior algebra is free on its degree-one generators, as a divided power algebra

Stacks Tag 09PH exhibits `⋀[R] (Fin r → R)` as the graded divided power algebra obtained from `R`
by adjoining `r` odd variables of degree one, and
`StacksFrontier/RingTheory/DividedPowers/TateResolution/ExteriorDividedPowers.lean` carries out that
construction. Tag 0GZ4 needs the *mapping property* that goes with it: a map of differential
graded divided power algebras **out of** the Koszul algebra, prescribed on the generators. This
file proves it, in two halves.

The first half is that no divided-power hypothesis is needed at all: **every** degree-preserving
`R`-algebra homomorphism out of `⋀[R] (Fin r → R)` automatically preserves the divided powers of
`DividedPowers.TateResolution.exteriorDividedPowerStructure`. The reason is a degeneracy: the
divided powers are determined by their values on the coefficients and on the variables
(`DividedPowers.TateResolution.ringHom_dpow_of_finiteVariableStage`), and both of those meet the
positive even part only in zero — the coefficients sit in degree `0` and the variables in the odd
degree `1`, while the positive even part is concentrated in degrees `2, 4, …`. So the two
generator-wise compatibility hypotheses are about divided powers of `0`, where every ring
homomorphism is compatible. What has to be checked instead is that the whole exterior algebra
*is* the finite variable stage on the `r` generators, which it is because `⋀[R] M` is generated
as an `R`-algebra by the image of `ExteriorAlgebra.ι`.

The second half constructs the homomorphism. A linear map `Rʳ → D` whose values square to zero
extends to `⋀[R] (Fin r → R)` by `ExteriorAlgebra.lift`; values in degree one square to zero
because a homogeneous element of odd degree does. Degrees are preserved because the `m`-th
exterior power is spanned by wedges of `m` vectors, and the differentials agree because the
difference of the two composites is additive, kills the coefficients and obeys the signed Leibniz
rule — which is checked on `ExteriorAlgebra.ι R p · y` by
`DividedPowers.TateResolution.leibniz_of_mem_grade_left`, the prescribed boundary of a generator
being exactly what makes the generator term cancel.

## Main definitions

* `DividedPowers.TateResolution.exteriorGen` — the `i`-th wedge generator
  `ExteriorAlgebra.ι R (Pi.single i 1)` of `⋀[R] (Fin r → R)`.

## Main results

* `DividedPowers.TateResolution.mem_finiteVariableStage_exteriorGen` — the exterior algebra is
  the finite variable stage on its `r` degree-one generators.
* `DividedPowers.TateResolution.algHom_map_dpow_exteriorDividedPowerStructure` — a
  degree-preserving algebra homomorphism out of `⋀[R] (Fin r → R)` preserves divided powers.
* `DividedPowers.TateResolution.exists_algHom_exterior_of_mem_grade_one` — the mapping property:
  degree-one elements with prescribed boundaries determine a morphism of differential graded
  divided power algebras out of the Koszul algebra.

## References

* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped ExteriorAlgebra

universe u z

section Generators

variable (R : Type u) [CommRing R] (r : ℕ)

/-- The `i`-th wedge generator of `⋀[R] (Fin r → R)`. -/
public noncomputable def exteriorGen (i : Fin r) : ExteriorAlgebra R (Fin r → R) :=
  ExteriorAlgebra.ι R (Pi.single i 1)

/-- The generator spelled out, so that a statement about `exteriorGen` is literally a statement
about `ExteriorAlgebra.ι R (Pi.single i 1)`. -/
public theorem exteriorGen_eq (i : Fin r) :
    exteriorGen R r i = ExteriorAlgebra.ι R (Pi.single i 1) := rfl

/-- Each generator is homogeneous of exterior degree one. -/
public theorem exteriorGen_mem (i : Fin r) : exteriorGen R r i ∈ ⋀[R]^1 (Fin r → R) :=
  ExteriorAlgebra.ι_mem_exteriorPower_one _

/-- Every vector of `Rʳ` is an `R`-combination of the generators. -/
public theorem ι_eq_sum_exteriorGen (p : Fin r → R) :
    ExteriorAlgebra.ι R p =
      ∑ i, algebraMap R (ExteriorAlgebra R (Fin r → R)) (p i) * exteriorGen R r i := by
  have h : ∑ i, algebraMap R (ExteriorAlgebra R (Fin r → R)) (p i) * exteriorGen R r i =
      ExteriorAlgebra.ι R (∑ i, p i • (Pi.single i 1 : Fin r → R)) := by
    rw [_root_.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.map_smul, Algebra.smul_def]
    rfl
  rw [h]
  congr 1
  funext j
  rw [Finset.sum_apply]
  simp [Pi.single_apply]

/-- **The exterior algebra is the finite variable stage on its `r` degree-one generators.**
The stage is the subring generated by the image of `R`, the generators, and all their divided
powers; the exterior algebra is already generated as an `R`-algebra by the image of
`ExteriorAlgebra.ι`, and every vector is an `R`-combination of the generators. -/
public theorem mem_finiteVariableStage_exteriorGen (x : ExteriorAlgebra R (Fin r → R)) :
    x ∈ finiteVariableStage (exteriorDividedPowerStructure R r)
      (Algebra.ofId R (ExteriorAlgebra R (Fin r → R))) (exteriorGen R r) Finset.univ := by
  set St := finiteVariableStage (exteriorDividedPowerStructure R r)
    (Algebra.ofId R (ExteriorAlgebra R (Fin r → R))) (exteriorGen R r) Finset.univ with hSt
  have halg : ∀ c : R, algebraMap R (ExteriorAlgebra R (Fin r → R)) c ∈ St :=
    fun c => Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  have hgen : ∀ i, exteriorGen R r i ∈ St :=
    fun i => Subring.subset_closure (Or.inr ⟨i, Finset.mem_univ i, Or.inl rfl⟩)
  have hι : ∀ p : Fin r → R, ExteriorAlgebra.ι R p ∈ St := by
    intro p
    rw [ι_eq_sum_exteriorGen]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (halg _) (hgen i)
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => exact halg c
  | add a b ha hb => exact Subring.add_mem _ ha hb
  | ι_mul a p ha => exact Subring.mul_mem _ (hι p) ha

end Generators

section MapDpow

variable (R : Type u) [CommRing R] (r : ℕ) {D : Type z} [Ring D] [Algebra R D]

/-- **A degree-preserving algebra homomorphism out of `⋀[R] (Fin r → R)` preserves divided
powers.** No compatibility hypothesis is needed. The divided powers of the exterior algebra are
determined by their values on the coefficients and on the degree-one generators, and both of
those meet the positive even part only in zero, where every ring homomorphism is compatible. -/
public theorem algHom_map_dpow_exteriorDividedPowerStructure
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (ε : DividedPowerStructure Dᵢ) (G : ExteriorAlgebra R (Fin r → R) →ₐ[R] D)
    (hG : ∀ (m : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
      x ∈ exteriorGrade R (Fin r → R) m → G x ∈ Dᵢ m)
    (n : ℕ) {x : ExteriorAlgebra R (Fin r → R)}
    (hx : x ∈ positiveEvenPart (exteriorGrade R (Fin r → R))) :
    ε.dpow n (G x) = G ((exteriorDividedPowerStructure R r).dpow n x) := by
  set δ := exteriorDividedPowerStructure R r with hδ
  set ι := Algebra.ofId R (ExteriorAlgebra R (Fin r → R)) with hι
  have hzero : ∀ {z : ExteriorAlgebra R (Fin r → R)} {d : ℕ}, z ∈ exteriorGrade R (Fin r → R) d →
      d < 2 → z ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) → z = 0 := by
    intro z d hz hd hpos
    rcases positiveEven_homogeneous_eq_zero_or_grade _ hz hpos with hz0 | ⟨k, hk⟩
    · exact hz0
    · omega
  have hzeroι : ∀ a : R, ι a ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) → ι a = 0 :=
    fun a => hzero (SetLike.algebraMap_mem_graded (exteriorGrade R (Fin r → R)) a) two_pos
  have hdpow0 : ∀ k : ℕ, ε.dpow k (G 0) = G (δ.dpow k 0) := by
    intro k
    rw [_root_.map_zero]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [δ.dpow_zero (Submodule.zero_mem _), ε.dpow_zero (Submodule.zero_mem _),
        _root_.map_one]
    · rw [δ.dpow_apply_zero hk.ne', ε.dpow_apply_zero hk.ne', _root_.map_zero]
  refine ringHom_dpow_of_finiteVariableStage (degreeZeroGrade R R)
    (exteriorGrade R (Fin r → R)) Dᵢ δ ε ι (exteriorGen R r) Finset.univ 1
    ?_ (fun i => exteriorGen_mem R r i) ?_ G.toRingHom hG (fun c => G.commutes c) ?_ ?_
    (mem_finiteVariableStage_exteriorGen R r x) hx n
  · intro m a ha
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact SetLike.algebraMap_mem_graded (exteriorGrade R (Fin r → R)) a
    · rw [eq_zero_of_mem_degreeZeroGrade R R hm.ne' ha, _root_.map_zero]
      exact Submodule.zero_mem _
  · intro k a ha
    rw [hzeroι a ha]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, by rw [δ.dpow_zero (Submodule.zero_mem _), _root_.map_one]⟩
    · exact ⟨0, by rw [δ.dpow_apply_zero hk.ne', _root_.map_zero]⟩
  · intro k a ha
    rw [hzeroι a ha]
    exact hdpow0 k
  · intro k i hi
    rw [hzero (exteriorGen_mem R r i) one_lt_two hi]
    exact hdpow0 k

end MapDpow

section Lift

variable (R : Type u) [CommRing R] (r : ℕ) {D : Type z} [Ring D] [Algebra R D]

/-- **The mapping property of the Koszul algebra as a differential graded divided power
algebra.** Let `D` be a strictly graded-commutative algebra with divided powers and a
differential, and suppose given, for each `i`, an element `t i` of `D` homogeneous of degree one
whose boundary is the image of `fᵢ`. Then there is an `R`-algebra homomorphism
`⋀[R] (Fin r → R) → D` sending the `i`-th wedge generator to `t i` which preserves exterior
degrees, intertwines the Koszul differential of `f` with the differential of `D`, and preserves
divided powers.

This is Tag 0GZ4's map `α` out of the Koszul algebra, and the three conclusions after the first
are exactly the three clauses of its `IsDividedPowerDGAHom` condition. Note that no divided-power
hypothesis on the data is needed: compatibility with divided powers is automatic by
`DividedPowers.TateResolution.algHom_map_dpow_exteriorDividedPowerStructure`. -/
public theorem exists_algHom_exterior_of_mem_grade_one
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (ε : DividedPowerStructure Dᵢ) (dD : D →ₗ[R] D)
    (hdga : IsDifferentialGradedAlgebra Dᵢ dD)
    (f : Fin r → R) (t : Fin r → D) (ht : ∀ i, t i ∈ Dᵢ 1)
    (hdt : ∀ i, dD (t i) = algebraMap R D (f i)) :
    ∃ α : ExteriorAlgebra R (Fin r → R) →ₐ[R] D,
      (∀ i, α (ExteriorAlgebra.ι R (Pi.single i 1)) = t i) ∧
      (∀ (m : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ exteriorGrade R (Fin r → R) m → α x ∈ Dᵢ m) ∧
      (∀ x, α (Koszul.contraction (Koszul.seqDual f) x) = dD (α x)) ∧
      (∀ (n : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) →
          α ((exteriorDividedPowerStructure R r).dpow n x) = ε.dpow n (α x)) := by
  classical
  set g : (Fin r → R) →ₗ[R] D := Fintype.linearCombination R t with hg
  have hgmem : ∀ p : Fin r → R, g p ∈ Dᵢ 1 := by
    intro p
    rw [hg, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ht i)
  have hgsq : ∀ p : Fin r → R, g p * g p = 0 := by
    intro p
    have h := IsStrictlyGradedComm.odd_sq_zero (𝒜 := Dᵢ) (d := 0)
      (show g p ∈ Dᵢ (2 * 0 + 1) from by simpa using hgmem p)
    rwa [pow_two] at h
  set α : ExteriorAlgebra R (Fin r → R) →ₐ[R] D := ExteriorAlgebra.lift R ⟨g, hgsq⟩ with hα
  have hαι : ∀ p : Fin r → R, α (ExteriorAlgebra.ι R p) = g p := by
    intro p
    rw [hα]
    exact ExteriorAlgebra.lift_ι_apply (R := R) g hgsq p
  have hgsingle : ∀ i : Fin r, g (Pi.single i 1 : Fin r → R) = t i := by
    intro i
    rw [hg, Fintype.linearCombination_apply,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun j _ hj => by simp [hj])]
    simp
  have hgd : ∀ p : Fin r → R, dD (g p) = algebraMap R D (Koszul.seqDual f p) := by
    intro p
    rw [hg, Fintype.linearCombination_apply, _root_.map_sum, Koszul.seqDual_apply,
      _root_.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.map_smul, hdt i, Algebra.smul_def, ← _root_.map_mul]
  have hmulti : ∀ (m : ℕ) (v : Fin m → (Fin r → R)),
      α (ExteriorAlgebra.ιMulti R m v) ∈ Dᵢ m := by
    intro m
    induction m with
    | zero =>
      intro v
      rw [show ExteriorAlgebra.ιMulti R 0 v = 1 from by simp [ExteriorAlgebra.ιMulti],
        _root_.map_one]
      exact SetLike.one_mem_graded Dᵢ
    | succ k ih =>
      intro v
      rw [Koszul.ιMulti_succ_apply, _root_.map_mul, hαι (v 0)]
      have h := SetLike.mul_mem_graded (hgmem (v 0)) (ih (Fin.tail v))
      rwa [Nat.add_comm 1 k] at h
  have hgrade : ∀ (m : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
      x ∈ exteriorGrade R (Fin r → R) m → α x ∈ Dᵢ m := by
    intro m x hx
    rw [← (Submodule.ext_iff.mp (ExteriorAlgebra.ιMulti_span_fixedDegree R m))] at hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨v, rfl⟩ := hz; exact hmulti m v
    | zero => rw [_root_.map_zero]; exact Submodule.zero_mem _
    | add a b _ _ iha ihb => rw [_root_.map_add]; exact Submodule.add_mem _ iha ihb
    | smul c a _ iha => rw [_root_.map_smul]; exact Submodule.smul_mem _ c iha
  have hdiff : ∀ x, α (Koszul.contraction (Koszul.seqDual f) x) = dD (α x) := by
    intro x
    induction x using CliffordAlgebra.left_induction with
    | algebraMap c =>
      rw [AlgHom.commutes, Koszul.contraction, CliffordAlgebra.contractLeft_algebraMap,
        _root_.map_zero, hdga.d_grade_zero (SetLike.algebraMap_mem_graded Dᵢ c)]
    | add a b ha hb =>
      simp only [_root_.map_add]
      rw [ha, hb]
    | ι_mul y p hy =>
      have hleib : dD (g p * α y) =
          dD (g p) * α y + (-1 : R) ^ 1 • (g p * dD (α y)) :=
        leibniz_of_mem_grade_left Dᵢ dD.toAddMonoidHom
          (fun i j x y hx hy => hdga.leibniz hx hy) (hgmem p) (α y)
      rw [Koszul.contraction, CliffordAlgebra.contractLeft_ι_mul, _root_.map_sub,
        _root_.map_smul, _root_.map_mul, hαι p, _root_.map_mul, hαι p, hleib, hgd p, hy,
        pow_one, neg_one_smul, Algebra.smul_def, sub_eq_add_neg]
  exact ⟨α, fun i => (hαι _).trans (hgsingle i), hgrade, hdiff, fun n x hx =>
    (algHom_map_dpow_exteriorDividedPowerStructure R r Dᵢ ε α hgrade n hx).symm⟩

end Lift

end DividedPowers.TateResolution

end
