module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreConditionSpecialCases
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange

/-!
# The completion of a finite locally free module is a finite locally free object

Let `X` be a locally Noetherian scheme and `I` a quasi-coherent ideal sheaf. An object `(𝓕_n)` of
`Coh(X, I)` is finite locally free when each `𝓕_n` is the direct image of a finite locally free
module on the closed subscheme cut out by `I ^ (n + 1)`
(`Stacks.Algebraization.IsFiniteLocallyFreeAdic`). The completion of a finite locally free
coherent `𝒪_X`-module `𝓕` is such an object: its `n`-th term `𝓕 / I ^ (n + 1) 𝓕` is the direct
image of the restriction of `𝓕` to that closed subscheme, by [Stacks, Tag 0EL1], and restriction
preserves finite local freeness.

## Main results

* `Stacks.Algebraization.isFiniteLocallyFreeAdic_completion` — completion carries finite locally
  free coherent modules to finite locally free objects of `Coh(X, I)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Algebraization

/-- **The completion of a finite locally free coherent module is a finite locally free object
of `Coh(X, I)`.** The `n`-th term is the direct image of the restriction of the module to the
closed subscheme cut out by `I ^ (n + 1)`. -/
public theorem isFiniteLocallyFreeAdic_completion (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F.obj) :
    IsFiniteLocallyFreeAdic I ((completionFunctor X I).obj F) := by
  intro n
  have : F.obj.IsCoherent := F.property
  have : F.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F.obj).1
  refine ⟨(Scheme.Modules.pullback (I ^ (n + 1)).subschemeι).obj F.obj,
    (Scheme.Modules.isFiniteLocallyFree_iff _).2
      (Stacks.Chow.isFiniteLocallyFree_pullback (I ^ (n + 1)).subschemeι F.obj hF), ⟨?_⟩⟩
  exact (idealQuotientPushforwardIso I (n + 1) F.obj (I ^ (n + 1)).subschemeι
    (Scheme.IdealSheafData.ker_subschemeι _)).symm ≪≫
      eqToIso (completionFunctor_obj X I F n).symm

end Stacks.Algebraization

end
