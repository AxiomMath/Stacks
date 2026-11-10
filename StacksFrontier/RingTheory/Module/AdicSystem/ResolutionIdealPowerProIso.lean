module

public import StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor
import all StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor

/-!
# Ideal powers of a finite free resolution as a pro-object

Let `I` be an ideal of a Noetherian ring `A` and let `M` be a bounded complex of finite
`A`-modules.  Choose a bounded-above resolution `p : P → M` by finite free modules, as produced
by `Stacks.AdicSystem.DerivedReductionProIso.derivedReduction_proIsomorphic_adicReduction`.
This file shows that the termwise tensor products `P ⊗ Iⁿ⁺¹`, regarded in the derived category
`D(A)`, form an inverse system pro-isomorphic to the system of termwise ideal-power complexes
`Iⁿ⁺¹ M`, via scalar multiplication `P ⊗ Iⁿ⁺¹ → P → M` factored through its image.

The comparison is the composite of two maps of inverse systems.  The first,
`P ⊗ Iⁿ⁺¹ → Iⁿ⁺¹ P`, is a levelwise isomorphism of complexes because each `P^i` is flat, so
scalar multiplication `P^i ⊗ Iⁿ⁺¹ → P^i` is injective.  The second, `Iⁿ⁺¹ P → Iⁿ⁺¹ M`, is a
pro-isomorphism by comparing the short exact sequences `0 → Iⁿ⁺¹ X → X → X / Iⁿ⁺¹ X → 0` for
`X = P, M`: the middle terms are quasi-isomorphic and the right-hand terms are pro-isomorphic by
Stacks tag 0G9M.  No derived tensor product appears in the statement.

## Main results

* `Stacks.AdicSystem.IdealPowerTensorComparison.exists_finiteFree_tensorIdealPower_proIso`:
  the resolution `P`, together with the pro-isomorphism from the system `P ⊗ Iⁿ⁺¹` to the system
  `Iⁿ⁺¹ M` in `D(A)`.

## Implementation notes

Positive powers are indexed by `n : ℕ` with exponent `n + 1`.  Since Mathlib has no category of
pro-objects, a pro-isomorphism is expressed by a natural comparison whose components acquire
two-sided inverses after passing to a later level, as in tag 0G3D.

## References

* [Stacks Project, Tag 0G9M](https://stacks.math.columbia.edu/tag/0G9M)
* [Stacks Project, Tag 0G4U](https://stacks.math.columbia.edu/tag/0G4U)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.AdicSystem.IdealPowerTensorComparison

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- Factoring scalar multiplication through its image commutes with the transitions. -/
private lemma tensorIdealPowerTransition_factorThruImage
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    tensorIdealPowerTransition M I n ≫ factorThruImage (idealPowerMultiplication M I n) =
      factorThruImage (idealPowerMultiplication M I (n + 1)) ≫
        idealPowerComplexTransition M I n := by
  apply (cancel_mono (image.ι (idealPowerMultiplication M I n))).1
  calc
    _ = tensorIdealPowerTransition M I n ≫ idealPowerMultiplication M I n :=
          (Category.assoc _ _ _).trans (congrArg _ (image.fac _))
    _ = factorThruImage (idealPowerMultiplication M I (n + 1)) ≫
          image.ι (idealPowerMultiplication M I (n + 1)) :=
          (tensorIdealPowerTransition_multiplication M I n).trans (image.fac _).symm
    _ = _ :=
          (congrArg _ (idealPowerComplexTransition_comp M I n).symm).trans
            (Category.assoc _ _ _).symm

/-- The map of inverse systems `M ⊗ Iⁿ⁺¹ → Iⁿ⁺¹ M` in `D(A)`. -/
private def tensorToIdealPowerNatTrans (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) :
    Functor.ofOpSequence (tensorIdealPowerTransition M I) ⋙ DerivedCategory.Q ⟶
      idealPowerSystem M I (idealPowerComplexTransition M I) :=
  NatTrans.ofOpSequence
    (fun n => DerivedCategory.Q.map (factorThruImage (idealPowerMultiplication M I n)))
    (fun n => by
      simp only [Functor.comp_map, idealPowerSystem, Functor.ofOpSequence_map_homOfLE_succ]
      exact ((Functor.map_comp _ _ _).symm.trans
        (congrArg _ (tensorIdealPowerTransition_factorThruImage M I n))).trans
          (Functor.map_comp _ _ _))

/-- For a complex of flat modules, `M ⊗ Iⁿ⁺¹ → Iⁿ⁺¹ M` is an isomorphism of complexes. -/
private lemma isIso_factorThruImage_idealPowerMultiplication
    (M : CochainComplex (ModuleCat.{u} A) ℤ) [∀ i : ℤ, Module.Flat A (M.X i)]
    (I : Ideal A) (n : ℕ) :
    IsIso (factorThruImage (idealPowerMultiplication M I n)) := by
  have : Mono (idealPowerMultiplication M I n) := mono_idealPowerMultiplication M I n
  have : Mono (factorThruImage (idealPowerMultiplication M I n)) :=
    mono_of_mono_fac (image.fac _)
  exact isIso_of_mono_of_epi _

/-- Let `I` be an ideal of a Noetherian ring `A` and `M` a bounded complex of finite
`A`-modules.  Then `M` has a bounded-above resolution `p : P → M` by finite free modules such
that the maps `P ⊗ Iⁿ⁺¹ → Iⁿ⁺¹ M`, obtained by tensoring `p` with `Iⁿ⁺¹` and factoring scalar
multiplication through its image, form an isomorphism of pro-objects in `D(A)`: each level
acquires a two-sided inverse after passing to a later level. -/
public theorem exists_finiteFree_tensorIdealPower_proIso
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (p : P ⟶ M),
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) ∧
      QuasiIso p ∧
      ∃ (t : ∀ n, idealPowerComplex M I (n + 1) ⟶ idealPowerComplex M I n)
        (_ht : ∀ n, t n ≫ image.ι (idealPowerMultiplication M I n) =
          image.ι (idealPowerMultiplication M I (n + 1)))
        (α : Functor.ofOpSequence (tensorIdealPowerTransition P I) ⋙ DerivedCategory.Q ⟶
          idealPowerSystem M I t),
        (∀ n, α.app (op n) = DerivedCategory.Q.map
          ((((MonoidalCategory.tensoringRight (ModuleCat.{u} A)).obj
              (idealPowerModule I n)).mapHomologicalComplex (ComplexShape.up ℤ)).map p ≫
            factorThruImage (idealPowerMultiplication M I n))) ∧
        ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
          (s : (idealPowerSystem M I t).obj (op m) ⟶
            (Functor.ofOpSequence (tensorIdealPowerTransition P I) ⋙
              DerivedCategory.Q).obj (op n)),
          α.app (op m) ≫ s =
              (Functor.ofOpSequence (tensorIdealPowerTransition P I) ⋙ DerivedCategory.Q).map
                (homOfLE h).op ∧
            s ≫ α.app (op n) = (idealPowerSystem M I t).map (homOfLE h).op := by
  obtain ⟨P, p, hPbounded, hPfinite, hp, _, hpred⟩ :=
    Stacks.AdicSystem.DerivedReductionProIso.derivedReduction_proIsomorphic_adicReduction I M
      hMbounded hMfinite
  have := hp
  have (i : ℤ) : Module.Flat A (P.X i) := by
    have : Module.Free A (P.X i) := (hPfinite i).2
    infer_instance
  refine ⟨P, p, hPbounded, hPfinite, (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).1 hp,
    idealPowerComplexTransition M I, idealPowerComplexTransition_comp M I,
    tensorToIdealPowerNatTrans P I ≫ idealPowerSystemMap p I, fun n => ?_, ?_⟩
  · rw [NatTrans.comp_app, idealPowerSystemMap_app]
    change DerivedCategory.Q.map (factorThruImage (idealPowerMultiplication P I n)) ≫ _ = _
    exact (Functor.map_comp _ _ _).symm.trans
      (congrArg _ (factorThruImage_idealPowerComplexMap p I n))
  · apply proInverse_comp
    · apply proInverse_of_isIso_app
      intro n
      have := isIso_factorThruImage_idealPowerMultiplication P I n
      change IsIso (DerivedCategory.Q.map (factorThruImage (idealPowerMultiplication P I n)))
      infer_instance
    · exact proInverse_idealPowerSystemMap_of_reduction p I hpred

end Stacks.AdicSystem.IdealPowerTensorComparison

end
