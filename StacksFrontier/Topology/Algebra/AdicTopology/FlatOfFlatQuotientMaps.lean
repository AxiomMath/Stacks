module

public import StacksFrontier.RingTheory.AdicCompletion.DvrValuedPoints
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Flatness of a taut homomorphism of Noetherian adic rings from its quotients

Let `φ : A → C` be a continuous homomorphism of Noetherian adic topological rings which is taut
(Stacks 0AMX). For a weak ideal of definition `I` of `A`, write `J(I)` for the closure of
`φ(I)C`. This file proves that `φ` is flat as soon as every induced map `A ⧸ I → C ⧸ J(I)` is
flat. This is the last step of the proof of Stacks 0GCG, where the source cites Stacks 0912.

## Main results

* `RingHom.flat_of_isTaut_of_flat_quotientMap_closure`: the statement above.

## Implementation notes

A taut continuous homomorphism from a ring with a finitely generated ideal of definition to a
complete separated ring is adic (Stacks 0GBS): there is an ideal of definition `I` of `A` with
`φ(I)C` an ideal of definition of `C`. Then `C` is `φ(I)C`-adically complete, its powers
`φ(I)ⁿC = φ(Iⁿ)C` are open, hence closed, so `J(Iⁿ) = φ(Iⁿ)C`, and the hypothesis says that
every `C ⧸ Iⁿ C` is flat over `A ⧸ Iⁿ`. Flatness of `C` over `A` is then
`Module.Flat.of_flat_adic_reductions`, the inverse-limit argument of Stacks 0912 for an
adically complete algebra.

## References

* [Stacks Project, Tag 0912](https://stacks.math.columbia.edu/tag/0912)
* [Stacks Project, Tag 0AMX](https://stacks.math.columbia.edu/tag/0AMX)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
* [Stacks Project, Tag 0GCG](https://stacks.math.columbia.edu/tag/0GCG)
-/

@[expose] public section

namespace RingHom

variable {A C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace C]
  [IsTopologicalRing C] [IsLinearTopology C C] in
/-- Flatness of the ring map induced by `φ` between quotients depends on the ideal of the target
only, not on the proof that it contains the extension of the ideal of the source. -/
private theorem flat_quotientMap_of_eq (φ : A →+* C) {I : Ideal A} {K₁ K₂ : Ideal C}
    (h : K₁ = K₂) (h₁ : I ≤ K₁.comap φ) (h₂ : I ≤ K₂.comap φ)
    (hflat : (Ideal.quotientMap K₁ φ h₁).Flat) : (Ideal.quotientMap K₂ φ h₂).Flat := by
  subst h
  exact hflat

/-- **The last step of Stacks 0GCG**, Stacks 0912 for a taut homomorphism. Let `φ : A → C` be a
taut continuous homomorphism of Noetherian adic topological rings. If for every weak ideal of
definition `I` of `A` the induced map `A ⧸ I → C ⧸ J(I)` is flat, where `J(I)` is the closure of
`φ(I)C`, then `φ` is flat. -/
theorem flat_of_isTaut_of_flat_quotientMap_closure [IsNoetherianRing A] [IsNoetherianRing C]
    (φ : A →+* C) (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (hφ : Continuous φ) (htaut : RingHom.IsTaut φ)
    (hflat : ∀ I : Ideal A, TopologicalRing.IsWeakIdealOfDefinition I →
      (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp subset_closure)).Flat) :
    φ.Flat := by
  obtain ⟨⟨I₀, -, hI₀⟩, -⟩ := hA
  obtain ⟨-, hT2, hcomplete⟩ := hC
  have : @CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C) := hcomplete
  obtain ⟨I, hI, hJ⟩ := RingHom.isAdic_of_isTaut φ hφ htaut
    ⟨I₀, Ideal.fg_of_isNoetherianRing I₀, hI₀⟩
  let : Algebra A C := φ.toAlgebra
  have hcompl : IsAdicComplete (I.map (algebraMap A C)) C := by
    let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
    have _ : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
    exact (IsAdic.isAdicComplete_iff hJ).2 ⟨hcomplete, hT2⟩
  refine RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_flat_adic_reductions I fun n ↦ ?_)
  cases n with
  | zero =>
    have : Subsingleton (C ⧸ (I ^ 0).map (algebraMap A C)) := by
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    infer_instance
  | succ n =>
    have hopen : IsOpen (((I ^ (n + 1)).map φ : Ideal C) : Set C) := by
      rw [Ideal.map_pow]
      exact (isAdic_iff.mp hJ).1 (n + 1)
    have hclosure : Ideal.closure ((I ^ (n + 1)).map φ) = (I ^ (n + 1)).map φ :=
      Ideal.closure_eq_of_isClosed _
        (((I ^ (n + 1)).map φ).toAddSubgroup.isClosed_of_isOpen hopen)
    have h := flat_quotientMap_of_eq φ hclosure _ Ideal.le_comap_map
      (hflat _ (TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hI n))
    exact RingHom.flat_algebraMap_iff.mp h

end RingHom

end
