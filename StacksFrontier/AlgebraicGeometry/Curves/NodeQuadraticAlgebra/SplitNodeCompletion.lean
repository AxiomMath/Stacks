module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Conductor
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SplitNode
public import StacksFrontier.RingTheory.Branches.Completion
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra

/-!
# The completion of a split node

Let `A` be a nodal local algebra over a field `k`, with residue field `κ`. The node is split
exactly when its completion is the node ring `κ[[x, y]]/(x y)` as a `k`-algebra, that is, exactly
when any one of the conditions of `Stacks.Curves.isSplitNode_tfae` holds.

## Main results

* `Stacks.Curves.nonempty_algEquiv_adicCompletion_quotient_X_mul_X_iff_numberOfBranches_eq_two`:
  the completion of a node is `κ[[x, y]]/(x y)` exactly when the node has two branches.
* `Stacks.Curves.isReduced_adicCompletion_of_isNodalAlgebra`: the completion of a node is
  reduced.
* `Stacks.Curves.isNodalAlgebra_adicCompletion_of_isNodalAlgebra_of_isNoetherianRing`: the
  completion of a node is a node, with no Nagata hypothesis.
* `Stacks.Curves.numberOfBranchesOfLocalRing_adicCompletion_maximalIdeal`: completion preserves
  the number of branches of a one-dimensional Noetherian local ring.
* `Stacks.Curves.exists_nodalQuadraticRelation_adicCompletion_of_algEquiv_quotient`: a
  power-series presentation of the completion exhibits its quadratic relation with the
  coefficient triple of the presentation.

## References

* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C2D](https://stacks.math.columbia.edu/tag/0C2D)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-! ### The completion of a node is a node -/

/-- A nodal algebra has a nodal completion. -/
private theorem hasNodalCompletion_of_isNodalAlgebra (k : Type u) (A : Type v) [Field k]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] (hA : IsNodalAlgebra k A) :
    HasNodalCompletion k A :=
  (show Algebra.IsSeparableExtension k (ResidueField A) ∧ HasNodalCompletion k A from
    ((isNodalAlgebra_tfae k A).out 1 3).mp hA).2

/-- **The completion of a node is reduced.** -/
theorem isReduced_adicCompletion_of_isNodalAlgebra (k : Type u) (A : Type v) [Field k]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] (hA : IsNodalAlgebra k A) :
    IsReduced (AdicCompletion (maximalIdeal A) A) := by
  obtain ⟨a, b, c, hdet, ⟨f⟩⟩ := hasNodalCompletion_of_isNodalAlgebra k A hA
  have : IsReduced (MvPowerSeries (Fin 2) (ResidueField A) ⧸
      Ideal.span {nodalBinaryQuadratic a b c}) :=
    isReduced_nodalBinaryQuadratic_quotient a b c hdet
  exact isReduced_of_injective f.toRingHom f.injective

/-- **The completion of a node is a node.** -/
theorem isNodalAlgebra_adicCompletion_of_isNodalAlgebra_of_isNoetherianRing
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    IsNodalAlgebra k (AdicCompletion (maximalIdeal A) A) :=
  ⟨isSeparableExtension_of_algEquiv (residueFieldAlgEquiv_adicCompletion k A) hA.1,
    isReduced_adicCompletion_of_isNodalAlgebra k A hA,
    hasNodalQuadraticRelation_adicCompletion A hA.2.2⟩

/-- **Completion preserves the number of branches of a one-dimensional Noetherian local ring.** -/
theorem numberOfBranchesOfLocalRing_adicCompletion_maximalIdeal (A : Type v) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hdim : ringKrullDim A = 1) :
    numberOfBranchesOfLocalRing (AdicCompletion (maximalIdeal A) A) =
      numberOfBranchesOfLocalRing A :=
  (numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion_of_dimension_one
    A (henselizationData A).carrier
    (henselizationData (AdicCompletion (maximalIdeal A) A)).carrier
    (strictHenselizationData A).carrier
    (strictHenselizationData (AdicCompletion (maximalIdeal A) A)).carrier
    (SeparableClosure (ResidueField A))
    (SeparableClosure (ResidueField (AdicCompletion (maximalIdeal A) A))) hdim).1.symm

/-! ### The quadratic relation read off from a presentation of the completion -/

/-- **A power-series presentation of the completion of a node exhibits the quadratic relation of
the completion with the coefficient triple of the presentation.** The images of the two variables
lift a basis of the cotangent space, and the images of the constants `a`, `b`, `c` are
coefficients of a relation between them; the constants of the power-series ring reach the residue
field of the completion bijectively, by the isomorphism `τ` of the statement. -/
theorem exists_nodalQuadraticRelation_adicCompletion_of_algEquiv_quotient
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) (a b c : ResidueField A)
    (f : AdicCompletion (maximalIdeal A) A ≃ₐ[k]
      (MvPowerSeries (Fin 2) (ResidueField A) ⧸ Ideal.span {nodalBinaryQuadratic a b c})) :
    ∃ (τ : ResidueField A ≃+* ResidueField (AdicCompletion (maximalIdeal A) A))
      (x y : maximalIdeal (AdicCompletion (maximalIdeal A) A))
      (e : Module.Basis (BinaryIndex (ResidueField (AdicCompletion (maximalIdeal A) A)))
        (ResidueField (AdicCompletion (maximalIdeal A) A))
        (CotangentSpace (AdicCompletion (maximalIdeal A) A)))
      (α β γ : AdicCompletion (maximalIdeal A) A),
      e ⟨0⟩ = (maximalIdeal (AdicCompletion (maximalIdeal A) A)).toCotangent x ∧
        e ⟨1⟩ = (maximalIdeal (AdicCompletion (maximalIdeal A) A)).toCotangent y ∧
        residue (AdicCompletion (maximalIdeal A) A) α = τ a ∧
        residue (AdicCompletion (maximalIdeal A) A) β = τ b ∧
        residue (AdicCompletion (maximalIdeal A) A) γ = τ c ∧
        α * (x : AdicCompletion (maximalIdeal A) A) ^ 2 +
            β * (x : AdicCompletion (maximalIdeal A) A) *
              (y : AdicCompletion (maximalIdeal A) A) +
            γ * (y : AdicCompletion (maximalIdeal A) A) ^ 2 ∈
          maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ 3 := by
  classical
  let K := ResidueField A
  let P := MvPowerSeries (Fin 2) K
  let I : Ideal P := Ideal.span {nodalBinaryQuadratic a b c}
  let B := AdicCompletion (maximalIdeal A) A
  let hPB : P →+* B := f.symm.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk I)
  have hsurjPB : Function.Surjective hPB := by
    intro w
    obtain ⟨q, rfl⟩ := f.symm.toRingEquiv.surjective w
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) q
    exact ⟨p, rfl⟩
  have hmaxB : Ideal.map hPB (maximalIdeal P) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective hPB hsurjPB
  have hmaxP : maximalIdeal P = Ideal.span {(MvPowerSeries.X 0 : P), MvPowerSeries.X 1} := by
    rw [maximalIdeal_mvPowerSeries_eq_span_X K 2]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  let x : B := hPB (MvPowerSeries.X 0)
  let y : B := hPB (MvPowerSeries.X 1)
  let α : B := hPB (MvPowerSeries.C a)
  let β : B := hPB (MvPowerSeries.C b)
  let γ : B := hPB (MvPowerSeries.C c)
  have hspan : Ideal.span ({x, y} : Set B) = maximalIdeal B := by
    rw [← hmaxB, hmaxP, Ideal.map_span, Set.image_pair]
  have hx : x ∈ maximalIdeal B := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hy : y ∈ maximalIdeal B := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  let σ : K →+* ResidueField B := (residue B).comp (hPB.comp MvPowerSeries.C)
  have hinjσ : Function.Injective σ := σ.injective
  have hsurjσ : Function.Surjective σ := by
    intro z
    obtain ⟨w, rfl⟩ := residue_surjective (R := B) z
    obtain ⟨p, rfl⟩ := hsurjPB w
    refine ⟨MvPowerSeries.constantCoeff p, ?_⟩
    have hcc : MvPowerSeries.constantCoeff
        (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p)) = 0 := by
      simp
    have hmemP : p - MvPowerSeries.C (MvPowerSeries.constantCoeff p) ∈ maximalIdeal P := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map (MvPowerSeries.constantCoeff (σ := Fin 2) (R := K))
      rw [hcc] at hu'
      exact not_isUnit_zero hu'
    have hmem : hPB (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p)) ∈ maximalIdeal B :=
      hmaxB ▸ Ideal.mem_map_of_mem hPB hmemP
    have hzero := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sub, map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  let τ : K ≃+* ResidueField B := RingEquiv.ofBijective σ ⟨hinjσ, hsurjσ⟩
  have hrel : α * x ^ 2 + β * x * y + γ * y ^ 2 ∈ maximalIdeal B ^ 3 := by
    have hq : hPB (nodalBinaryQuadratic a b c) = 0 := by
      have : (Ideal.Quotient.mk I) (nodalBinaryQuadratic a b c) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      change f.symm.toRingEquiv ((Ideal.Quotient.mk I) (nodalBinaryQuadratic a b c)) = 0
      rw [this, map_zero]
    have heq : α * x ^ 2 + β * x * y + γ * y ^ 2 = hPB (nodalBinaryQuadratic a b c) := by
      simp only [nodalBinaryQuadratic, map_add, map_mul, map_pow, α, β, γ, x, y]
    rw [heq, hq]
    exact Submodule.zero_mem _
  have hfin : Module.finrank (ResidueField B) (CotangentSpace B) = 2 :=
    finrank_cotangentSpace_eq_two_of_hasNodalQuadraticRelation
      (hasNodalQuadraticRelation_adicCompletion A hA.2.2)
  obtain ⟨e, he₀, he₁⟩ :=
    exists_cotangent_basis_of_pair_generators_and_finrank_two B ⟨x, hx⟩ ⟨y, hy⟩ hspan hfin
  exact ⟨τ, ⟨x, hx⟩, ⟨y, hy⟩, e, α, β, γ, he₀, he₁, rfl, rfl, rfl, hrel⟩

/-! ### The completion condition -/

/-- **A node whose completion is `κ[[x, y]]/(x y)` has two branches.** -/
theorem numberOfBranches_eq_two_of_nonempty_algEquiv_adicCompletion_quotient_X_mul_X
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A)
    (f : AdicCompletion (maximalIdeal A) A ≃ₐ[k]
      (MvPowerSeries (Fin 2) (ResidueField A) ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (ResidueField A)) *
                      MvPowerSeries.X 1})) :
    numberOfBranchesOfLocalRing A = 2 := by
  let B := AdicCompletion (maximalIdeal A) A
  have hB : IsNodalAlgebra k B :=
    isNodalAlgebra_adicCompletion_of_isNodalAlgebra_of_isNoetherianRing k A hA
  have hspanq : Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (ResidueField A)) *
                              MvPowerSeries.X 1} =
      Ideal.span {nodalBinaryQuadratic (0 : ResidueField A) 1 0} := by
    rw [nodalBinaryQuadratic_zero_one_zero]
  let f' := f.trans (Ideal.quotientEquivAlgOfEq k hspanq)
  obtain ⟨τ, x, y, e, α, β, γ, he₀, he₁, hα, hβ, hγ, hrel⟩ :=
    exists_nodalQuadraticRelation_adicCompletion_of_algEquiv_quotient k A hA 0 1 0 f'
  have hcube : ∀ (z w : B), z ∈ maximalIdeal B → w ∈ maximalIdeal B →
      z * w ^ 2 ∈ maximalIdeal B ^ 3 := fun z w hz hw ↦ by
    rw [show maximalIdeal B ^ 3 = maximalIdeal B * maximalIdeal B ^ 2 by ring]
    exact Ideal.mul_mem_mul hz (Ideal.pow_mem_pow hw 2)
  have hαx : α * (x : B) ^ 2 ∈ maximalIdeal B ^ 3 :=
    hcube _ _ ((residue_eq_zero_iff _).mp (by rw [hα, map_zero])) x.2
  have hγy : γ * (y : B) ^ 2 ∈ maximalIdeal B ^ 3 :=
    hcube _ _ ((residue_eq_zero_iff _).mp (by rw [hγ, map_zero])) y.2
  have hβu : IsUnit β := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_
    rw [hβ, map_one]
    exact one_ne_zero
  have hβxy : β * ((x : B) * (y : B)) ∈ maximalIdeal B ^ 3 := by
    have h : β * ((x : B) * (y : B)) =
        (α * (x : B) ^ 2 + β * (x : B) * (y : B) + γ * (y : B) ^ 2) -
          α * (x : B) ^ 2 - γ * (y : B) ^ 2 := by ring
    rw [h]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hrel hαx) hγy
  have hxy : (x : B) * (y : B) ∈ maximalIdeal B ^ 3 :=
    (Ideal.unit_mul_mem_iff_mem _ hβu).mp hβxy
  have hsplit := nonempty_quadraticAlgebra_algEquiv_prod_of_cotangent_coordinates k B hB x y e
    he₀ he₁ hxy
  have hbrB : numberOfBranchesOfLocalRing B = 2 :=
    (nonempty_quadraticAlgebra_algEquiv_prod_iff_numberOfBranches_eq_two k B hB).mp hsplit
  rwa [← numberOfBranchesOfLocalRing_adicCompletion_maximalIdeal A
    (ringKrullDim_eq_one_of_isNodalAlgebra k A hA)]

/-- **The completion of a node with two branches is `κ[[x, y]]/(x y)`.** -/
theorem nonempty_algEquiv_adicCompletion_quotient_X_mul_X_of_numberOfBranches_eq_two
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) (hbr : numberOfBranchesOfLocalRing A = 2) :
    Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k]
      (MvPowerSeries (Fin 2) (ResidueField A) ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (ResidueField A)) *
                      MvPowerSeries.X 1})) := by
  let B := AdicCompletion (maximalIdeal A) A
  have hB : IsNodalAlgebra k B :=
    isNodalAlgebra_adicCompletion_of_isNodalAlgebra_of_isNoetherianRing k A hA
  obtain ⟨a, b, c, hdet, ⟨f⟩⟩ := hasNodalCompletion_of_isNodalAlgebra k A hA
  have hbrB : numberOfBranchesOfLocalRing B = 2 := by
    rwa [numberOfBranchesOfLocalRing_adicCompletion_maximalIdeal A
      (ringKrullDim_eq_one_of_isNodalAlgebra k A hA)]
  have hsplitB := (nonempty_quadraticAlgebra_algEquiv_prod_iff_numberOfBranches_eq_two k B hB).mpr
    hbrB
  obtain ⟨τ, x, y, e, α, β, γ, he₀, he₁, hα, hβ, hγ, hrel⟩ :=
    exists_nodalQuadraticRelation_adicCompletion_of_algEquiv_quotient k A hA a b c f
  have hdiscB : residue B (4 * α * γ - β ^ 2) ≠ 0 := by
    have heq : residue B (4 * α * γ - β ^ 2) = τ (4 * a * c - b ^ 2) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_ofNat, hα, hβ, hγ, map_sub, map_mul, map_mul,
        map_pow, map_ofNat]
    rw [heq]
    exact fun h ↦ hdet ((map_eq_zero_iff τ τ.injective).mp h)
  obtain ⟨u, v, huv, hzero⟩ := exists_isotropic_of_nonempty_quadraticAlgebra_algEquiv_prod k B hB
    x y e he₀ he₁ α β γ hdiscB hrel hsplitB
  obtain ⟨u', rfl⟩ := τ.surjective u
  obtain ⟨v', rfl⟩ := τ.surjective v
  have hiso : ∃ u v : ResidueField A, (u ≠ 0 ∨ v ≠ 0) ∧
      a * u ^ 2 + b * u * v + c * v ^ 2 = 0 := by
    refine ⟨u', v', ?_, ?_⟩
    · rcases huv with h | h
      · exact Or.inl fun h0 ↦ h (by rw [h0, map_zero])
      · exact Or.inr fun h0 ↦ h (by rw [h0, map_zero])
    · refine (map_eq_zero_iff τ τ.injective).mp ?_
      simp only [map_add, map_mul, map_pow]
      rwa [hα, hβ, hγ] at hzero
  obtain ⟨w⟩ := nonempty_quotient_nodalBinaryQuadratic_algEquiv_of_isotropic a b c hdet hiso
  exact ⟨f.trans (w.restrictScalars k)⟩

/-- **The completion condition for a split node.** Let `A` be a nodal local algebra over a field
`k`, with residue field `κ`. Then the completion of `A` at its maximal ideal is `κ[[x, y]]/(x y)`
as a `k`-algebra if and only if `A` has two branches — hence if and only if any one of the four
conditions of `Stacks.Curves.isSplitNode_tfae` holds. -/
@[stacks 0CBU "condition (5), the completion condition"]
public theorem nonempty_algEquiv_adicCompletion_quotient_X_mul_X_iff_numberOfBranches_eq_two
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k]
        (MvPowerSeries (Fin 2) (ResidueField A) ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (ResidueField A)) *
                        MvPowerSeries.X 1})) ↔
      numberOfBranchesOfLocalRing A = 2 :=
  ⟨fun ⟨f⟩ ↦
    numberOfBranches_eq_two_of_nonempty_algEquiv_adicCompletion_quotient_X_mul_X k A hA f,
    nonempty_algEquiv_adicCompletion_quotient_X_mul_X_of_numberOfBranches_eq_two k A hA⟩

end Stacks.Curves

end
