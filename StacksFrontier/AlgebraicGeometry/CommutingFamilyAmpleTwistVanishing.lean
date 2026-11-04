module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.CommutingFamilyNoetherian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProperMapping

/-!
# Uniform Serre vanishing for commuting families on a proper scheme

Let `f : Z ⟶ Spec R` be proper with `R` Noetherian, `ℒ` an ample invertible `𝒪_Z`-module, and
`G` a commuting family (`Stacks.CommutingFamily`) of coherent `𝒪_Z`-modules generated in bounded
degree — the shape of a coherent graded module over `𝒪_Z[T₀, …, T_r]` with its variables in
degree one.  Then one `d₀` makes

`Hᵖ(Z, Gₙ ⊗ ℒ^{⊗ d}) = 0`  for every `d ≥ d₀`, every `n` and every `p > 0`.

This is the uniformity in `n` that [Stacks, Tag 0897] part (2) produces and that the proof of
[Stacks, Tag 0D39] uses on the fibre `X_y` for the graded pieces `𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ`.

## Main results

* `Stacks.CommutingFamily.exists_isZero_Hgroup_tensorPowTwist_of_isGenerated`: the uniform
  vanishing.

## The argument

It is `Stacks.CommutingFamily.exists_forall_isZero_of_isGenerated` for the class of
quasi-coherent coherent modules: the two halves of the long exact cohomology sequence are
`Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃` and `isZero_rightDerived_X₂`, the
twists are exact because `ℒ^{⊗ d}` is invertible, a single coherent module has eventually
vanishing higher cohomology by Serre's theorem ([Stacks, Tag 0B5T],
`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`), and the
Noetherian input is `Stacks.CommutingFamily.isGenerated_kernelFamily_of_isNoetherian`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (tensorRightModules)

universe u

namespace Stacks.CommutingFamily

/-- **Uniform Serre vanishing for a generated commuting family of coherent modules.**  Let
`f : Z ⟶ Spec R` be proper with `R` Noetherian and `ℒ` an ample invertible `𝒪_Z`-module.  For a
commuting family `G` of quasi-coherent coherent `𝒪_Z`-modules generated in bounded degree there
is one `d₀` with `Hᵖ(Z, Gₙ ⊗ ℒ^{⊗ d}) = 0` for all `d ≥ d₀`, all `n` and all `p > 0`. -/
theorem exists_isZero_Hgroup_tensorPowTwist_of_isGenerated {Z : Scheme.{u}} {R : Type u}
    [CommRing R] [IsNoetherianRing R] (f : Z ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (L : Z.Modules) [IsInvertibleModule Z L] (hL : IsAmple Z L) {r : ℕ}
    (G : CommutingFamily Z.Modules r) (hqc : ∀ n, (G.obj n).IsQuasicoherent)
    (hcoh : ∀ n, _root_.SheafOfModules.IsCoherent (G.obj n)) (hG : G.IsGenerated) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ n p, 0 < p →
      IsZero (Hgroup Z.ringCatSheaf ⊤ p (tensorModules Z (G.obj n) (tensorPowModule Z L d))) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  have : IsLocallyNoetherian Z := AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Z := by
    have : CompactSpace (Spec (CommRingCat.of R)) := inferInstance
    exact (QuasiCompact.compactSpace_of_compactSpace f)
  have : AlgebraicGeometry.IsNoetherian Z := {}
  -- The twists, as endofunctors of the category of sheaves of modules that `Hgroup` is defined
  -- on; they are equivalences, which is all that is used about them.
  let Φ : ℕ → SheafOfModules Z.ringCatSheaf ⥤ SheafOfModules Z.ringCatSheaf :=
    fun d => tensorRightModules Z (tensorPowModule Z L (d : ℤ))
  have hΦeq : ∀ d, (Φ d).IsEquivalence := fun d =>
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule Z _
  refine exists_forall_isZero_of_isGenerated (𝒜 := SheafOfModules Z.ringCatSheaf)
    (H := fun p => Hfunctor Z.ringCatSheaf ⊤ p)
    (fun p A hA => Functor.map_isZero _ hA)
    (fun S hS p _ h₂ h₁ =>
      Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hS _ p h₂ h₁)
    (fun S hS p _ h₁ h₃ =>
      Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂ hS _ p h₁ h₃)
    Φ (fun d A hA => Functor.map_isZero _ hA)
    (fun d S hS => ⟨_, hS.map_of_exact (Φ d), rfl, rfl, rfl⟩)
    (fun M => M.IsQuasicoherent ∧ _root_.SheafOfModules.IsCoherent M)
    (fun A B φ hA hB => by
      have := hA.1; have := hB.1
      exact ⟨Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel φ,
        Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules hA.2 hB.2 φ⟩)
    (fun A B φ hA hB => by
      have := hA.1; have := hB.1
      exact ⟨Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel φ,
        Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel_modules hA.2 hB.2 φ⟩)
    (fun A hA => by
      have := hA.2
      obtain ⟨d₀, hd₀⟩ :=
        Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f A L
          hL
      exact ⟨d₀, fun d hd p hp => hd₀ d p hd hp⟩)
    (fun r G hP hG => by
      have := fun n => (hP n).1
      have : ∀ n, (G.obj n).IsFiniteType := fun n => (hP n).2.isFiniteType
      exact isGenerated_kernelFamily_of_isNoetherian G hG)
    r G (fun n => ⟨hqc n, hcoh n⟩) hG

end Stacks.CommutingFamily

end
