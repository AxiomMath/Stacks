module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimension
import StacksCore.Tactic.StacksAttribute

/-!
# The Cohen--Macaulay assertion of clause (2) of Tag 0BS2

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism with `X` of topological Krull dimension
at most one, and let

  `ω_X = H^{-1}(f^×(𝒪_{Spec k}))`

be the dualizing sheaf of [Stacks, Tag 0BS2]. Clause (2) of that lemma says that `ω_X` is a
*coherent Cohen--Macaulay* module *whose support is the irreducible components of dimension one*.
This file proves that no nonzero coherent submodule of `ω_X` has zero-dimensional support; for a
coherent module on a scheme of dimension at most one this is Cohen--Macaulayness together with the
absence of zero-dimensional irreducible components from the support. It also proves that `ω_X` is
nonzero in Situation [Stacks, Tag 0B5D].

## Main results

* `Stacks.Duality.subsingleton_hom_dualizingSheafOverField_of_supp_dim_le_zero`: there is no
  nonzero map to `ω_X` out of a coherent module whose support has dimension at most zero.
* `Stacks.Duality.isZero_of_mono_dualizingSheafOverField_of_supp_dim_le_zero`: **the
  Cohen--Macaulay assertion of clause (2)**: such a module cannot be a submodule of `ω_X` unless
  it is zero.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.not_isZero_dualizingSheafOverField`: in
  Situation [Stacks, Tag 0B5D] the sheaf `ω_X` is nonzero, which is the assertion of clause (2)
  that its support is *nonempty*.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0B5F](https://stacks.math.columbia.edu/tag/0B5F)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0B3J](https://stacks.math.columbia.edu/tag/0B3J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **A coherent module whose support has dimension at most zero admits no nonzero map to the
dualizing sheaf `ω_X`.** -/
theorem subsingleton_hom_dualizingSheafOverField_of_supp_dim_le_zero
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (M : X.Modules) (hM : M.IsCoherent)
    (hsupp : topologicalKrullDim (_root_.SheafOfModules.supp M) ≤ 0) :
    Subsingleton (M ⟶ dualizingSheafOverField f) :=
  have := hM
  have hMq : M.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  have hz := ModuleCat.subsingleton_of_isZero
    (isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k f M hsupp 1 Nat.one_pos)
  have hlin : Subsingleton (cohomologyOverField k f M 1 →ₗ[k] k) :=
    ⟨fun a b => LinearMap.ext fun z => by rw [Subsingleton.elim z 0, map_zero, map_zero]⟩
  (clauseFiveAddEquiv f hdim M hMq).injective.subsingleton

/-- **Stacks Project, Tag 0BS2, clause (2): the Cohen--Macaulay assertion.** On a proper `X` of
dimension at most one over a field, a coherent submodule of the dualizing sheaf
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` whose support has dimension at most zero is zero.

For a coherent module on a scheme of dimension at most one this is Cohen--Macaulayness together
with the absence of a zero-dimensional irreducible component from the support. -/
theorem isZero_of_mono_dualizingSheafOverField_of_supp_dim_le_zero
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (M : X.Modules)
    (u : M ⟶ dualizingSheafOverField f) (hu : Mono u) (hM : M.IsCoherent)
    (hsupp : topologicalKrullDim (_root_.SheafOfModules.supp M) ≤ 0) : IsZero M :=
  have hsub := subsingleton_hom_dualizingSheafOverField_of_supp_dim_le_zero f hdim M hM hsupp
  (IsZero.iff_id_eq_zero M).mpr
    (hu.right_cancellation (𝟙 M) 0 (@Subsingleton.elim _ hsub _ _))

end Stacks.Duality

namespace AlgebraicGeometry.CohenMacaulayCurveSituation

/-- **The dualizing sheaf of Situation [Stacks, Tag 0B5D] is nonzero**: the support of `ω_X` is
nonempty, as clause (2) of [Stacks, Tag 0BS2] asserts. -/
theorem not_isZero_dualizingSheafOverField (S : CohenMacaulayCurveSituation.{u}) :
    ¬ IsZero (Stacks.Duality.dualizingSheafOverField S.f) := by
  intro hz
  refine not_subsingleton_cohomologyOverField_one_dualizingSheaf S
    (subsingleton_of_subsingleton_dual S ?_)
  refine (Equiv.subsingleton_congr
    ((firstCohomologyDuality_dualizingSheafOverField S).dual
      (Stacks.Duality.dualizingSheafOverField S.f)
      (Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f)).toEquiv).mp ?_
  exact ⟨fun a b => hz.eq_of_tgt a b⟩

end AlgebraicGeometry.CohenMacaulayCurveSituation

end
