module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwistQuasicoherent

/-!
# The higher cohomology of the twists of a coherent sheaf on `ℙⁿ_k` eventually vanishes

Let `k` be a field, `n ≥ 0` and `ℱ` a coherent sheaf on `ℙⁿ_k`. There is a degree `d₀` beyond
which `Hⁱ(ℙⁿ_k, ℱ(d))` vanishes for every `i > 0` at once.

## Main results

* `AlgebraicGeometry.exists_isZero_Hgroup_projectiveTwist`: the vanishing in the abelian-group
  spelling `Hgroup`, with the bound uniform in the positive degree.
* `AlgebraicGeometry.exists_isZero_cohomologyOverField_projectiveTwist`: the same for the
  `k`-module-valued `AlgebraicGeometry.cohomologyOverField`.

## References

* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (tensorPowModuleProjectiveTwistIso)
open Stacks.RelativeVeryAmple (tensorModulesMapIso)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- For a coherent sheaf `ℱ` on projective `n`-space over a field there is a degree `d₀` such
that `Hⁱ(ℙⁿ_k, ℱ(d)) = 0` for every `d ≥ d₀` and every `i > 0`. -/
theorem exists_isZero_Hgroup_projectiveTwist (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent] :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p →
      IsZero (Hgroup (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf ⊤ p
        (projectiveTwist n F d)) := by
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist
      (projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) F
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n
        (Spec (CommRingCat.of k)))
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n
        (Spec (CommRingCat.of k)))
  refine ⟨(d₀ : ℤ), fun d hd p hp => (hd₀ d.toNat p (by omega) hp).of_iso
    ((Hfunctor (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf ⊤ p).mapIso ?_)⟩
  exact eqToIso (congrArg (projectiveTwist n F) (by omega : d = ((d.toNat : ℕ) : ℤ))) ≪≫
    tensorModulesMapIso (projectiveSpaceOverRing n (CommRingCat.of k)) (Iso.refl F)
      (tensorPowModuleProjectiveTwistIso n (Spec (CommRingCat.of k))
        ((d.toNat : ℕ) : ℤ)).symm

/-- For a coherent sheaf `ℱ` on `ℙⁿ_k` there is a degree `d₀` beyond which `Hⁱ(ℙⁿ_k, ℱ(d))`
vanishes as a `k`-module for every `i > 0`. -/
theorem exists_isZero_cohomologyOverField_projectiveTwist (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent] :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p →
      IsZero (cohomologyOverField k
        (projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
        (projectiveTwist n F d) p) := by
  obtain ⟨d₀, hd₀⟩ := exists_isZero_Hgroup_projectiveTwist k n F
  exact ⟨d₀, fun d hd p hp ↦
    (isZero_cohomologyOverField_iff_isZero_hgroup k _ _ p).2 (hd₀ d hd p hp)⟩

end AlgebraicGeometry

end
