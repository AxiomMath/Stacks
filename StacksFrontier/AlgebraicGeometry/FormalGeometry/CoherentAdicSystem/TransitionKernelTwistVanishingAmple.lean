module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionKernelTwistVanishingPos
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic

/-!
# Stacks 0884 under the source's hypotheses

**Stacks 0884.** Let `A` be a Noetherian ring and `I ⊆ A` an ideal, let `f : X ⟶ Spec A` be
proper, let `L` be an `f`-ample invertible sheaf and put `𝓘 = I · 𝒪_X`. Let `(F_n)` be an object
of `Coh(X, 𝓘)`. Then there is an integer `d₀` with

  `H¹(X, Ker(F_{n+1} ⟶ F_n) ⊗ L ^⊗ d) = 0`  for all `n ≥ 0` and all `d ≥ d₀`.

The statement is spelled exactly as
`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule` of
`TransitionKernelTwistVanishing.lean` — the same `Stacks.Coherent.transitionKernel`, the same twist
and the same `H¹` — and has exactly the source's hypotheses.

## The proof

The source's proof is Stacks 087Z (the graded module `⨁ Ker(F_{n+1} ⟶ F_n)` over
`⨁ 𝓘ⁿ/𝓘ⁿ⁺¹` is quasi-coherent of finite type) followed by Stacks 0897 part (2). Both are carried
out in `Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_pos`, which
proves the vanishing in every positive degree, asking only that the restriction of `L` to the
closed subscheme `V(𝓘)` be ample. What remains here is to derive that from the source's
`f`-ampleness: over the affine base `Spec A` relative ampleness is ampleness on `X`
([Stacks, Tag 01VK], `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`), and ampleness
pulls back along the closed immersion `V(𝓘) ⟶ X`, which is affine ([Stacks, Tag 0892] part (2),
`Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`). The source's statement is then the
degree-one case.

## Main results

* `Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_isRelativelyAmple` —
  **Stacks 0884**.

## References

* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace Stacks.Coherent

/-- **Stacks 0884.** Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a proper
morphism and `L` an invertible `𝒪_X`-module ample relative to `f`. Let `𝓕` be an object of
`Coh(X, 𝓘)` for `𝓘 = I · 𝒪_X`. Then there is an integer `d₀` such that

  `H¹(X, Ker(𝓕_{n+1} ⟶ 𝓕_n) ⊗ L ^⊗ d) = 0`

for every `n ≥ 0` and every `d ≥ d₀` — one `d₀` for the whole system.

The hypotheses are exactly the source's. The proof is the degree-one case of
`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_pos` (Stacks 087Z and
Stacks 0897 part (2)), whose ampleness hypothesis on `V(𝓘)` follows from `f`-ampleness by
Stacks 01VK over the affine base and Stacks 0892 part (2) along the closed immersion
`V(𝓘) ⟶ X`. -/
@[stacks 0884]
public theorem exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_isRelativelyAmple
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)) :
    ∃ d₀ : ℤ, ∀ (n : ℕ) (d : ℤ), d₀ ≤ d →
      IsZero (Hgroup X.ringCatSheaf ⊤ 1
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
                ((isSheaf_structureRingPresheaf X))⟩).obj (transitionKernel 𝓕 n)).obj
          (Stacks.Ample.tensorPowModule X L d)))) :=
  let ⟨d₀, hd₀⟩ :=
    exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_pos A I f L
      (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom
        (baseIdealSheaf A I f).subschemeι L
        ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp hL)) 𝓕
  ⟨d₀, fun n d hd => hd₀ n d hd 1 Nat.one_pos⟩

end Stacks.Coherent

end
