module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.Descent
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional

/-!
# The zero section formula

For every finite locally free `𝒪_X`-module `ℰ` of rank `e` on a scheme `X` locally of finite type
over the base of chapter 42, the zero section `o : X ⟶ E = 𝐕(ℰ^∨)` satisfies

  `o_* α = p^*(c_e(ℰ) ∩ α)`  for every  `α ∈ A_k(X)`.

The proof is by induction on `e`, following the splitting principle. In rank zero `p` is an
isomorphism. In rank one, `ℰ` is an extension of `ℰ` by the zero module and the case of an
invertible quotient applies. In rank `e + 2`, on the projective bundle `π : 𝐏(ℰ) ⟶ X` the
tautological sequence `0 ⟶ ℰ' ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` has `ℰ'` of rank `e + 1`, so the formula for
`ℰ'` (induction) gives the one for `π^*ℰ`, which descends to `X`.

## Main results

* `Stacks.Chow.zeroSectionFormula` — the zero section formula in every rank.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-- A zero module of a scheme is finite locally free of rank zero: it is isomorphic to the free
module on the empty set. -/
theorem isFiniteLocallyFreeOfRank_zero_of_isZero {X : Scheme.{u}} (M : X.Modules)
    (hM : IsZero M) : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 0 := by
  have hZ : IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}) :=
    (IsZero.iff_id_eq_zero _).2 <|
      (SheafOfModules.freeHomEquiv _).injective (funext fun i => i.elim)
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}) 0 := by
    refine ⟨⟨(SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf) PEmpty.{u + 1}).localGeneratorsData, inferInstance, fun _ => ?_⟩⟩
    change Nonempty (PEmpty.{u + 1} ≃ Fin 0)
    exact ⟨Equiv.equivOfIsEmpty _ _⟩
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hZ.iso hM) hF

/-- **The zero section formula in rank one.** -/
theorem zeroSectionFormula_of_rank_one {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1] :
    ZeroSectionFormula C sX E (0 + 1) := by
  have := isFiniteLocallyFreeOfRank_zero_of_isZero (kernel (𝟙 E)) (isZero_kernel_of_mono _)
  have := GenuineChern.isFiniteLocallyFree_of_rank (kernel (𝟙 E)) 0
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (0 + 1) := ‹_›
  exact zeroSectionFormula_of_shortExact_of_rank_one C sX (kernel (𝟙 E)) E E 0 (kernel.ι _)
    (𝟙 E) (kernel.condition _) { exact := ShortComplex.exact_kernel (𝟙 E) }
    (zeroSectionFormula_of_rank_zero C sX _)

/-- The kernel `ℰ'` of the tautological surjection `π^*ℰ ⟶ 𝒪(1)`. -/
abbrev bundleTautologicalKernel {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] : (bundle E).Modules :=
  kernel (bundleTautological E)

/-- If `ℰ` is finite locally free of rank `m + 2`, then the kernel `ℰ'` of the tautological
surjection `π^*ℰ ⟶ 𝒪(1)` is finite locally free of rank `m + 1`. -/
theorem isFiniteLocallyFreeOfRank_bundleTautologicalKernel {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 2)] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (bundleTautologicalKernel E) (m + 1) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible _
    inferInstance (isInvertible_bundleTwist E) m inferInstance

/-- **The zero section formula**, in every rank. -/
theorem zeroSectionFormula (e : ℕ) : ∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e],
    ZeroSectionFormula C sX E e := by
  induction e with
  | zero =>
    intro X sX _ E _ _
    exact zeroSectionFormula_of_rank_zero C sX E
  | succ e ih =>
    intro X sX _ E _ _
    cases e with
    | zero => exact zeroSectionFormula_of_rank_one C sX E
    | succ m =>
      refine zeroSectionFormula_of_bundle C sX E (m + 1) ?_
      have := flat_bundleProj E (m + 1)
      have := locallyOfFiniteType_bundleProj E (m + 1)
      have := isFiniteLocallyFreeOfRank_bundleTautologicalKernel E m
      have := GenuineChern.isFiniteLocallyFree_of_rank (bundleTautologicalKernel E) (m + 1)
      have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (bundleTwist E) 1 :=
        GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible _
      have := GenuineChern.isFiniteLocallyFree_of_rank (bundleTwist E) 1
      exact zeroSectionFormula_of_shortExact_of_rank_one C (bundleProj E ≫ sX)
        (bundleTautologicalKernel E) ((Scheme.Modules.pullback (bundleProj E)).obj E)
        (bundleTwist E) (m + 1) (kernel.ι _) (bundleTautological E) (kernel.condition _)
        { exact := ShortComplex.exact_kernel _ }
        (ih (bundleProj E ≫ sX) (bundleTautologicalKernel E))

end Stacks.Chow

end
