module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FaithfullyFlatEffective
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.TensorEqualizer

/-!
# The descended module of a module descent datum is its module of invariants

Let `R → A` be a ring map and let `D = (N, φ)` be a descent datum on modules along it.  Its
module of invariants is `H⁰(s(N_•)) = {n ∈ N | φ(n ⊗ 1) = 1 ⊗ n}`, available as
`ModuleCat.invariantSubmodule`.  This file shows that for a universally injective — in
particular for a faithfully flat — ring map the canonical `A`-linear map
`A ⊗[R] H⁰(s(N_•)) → N`, `a ⊗ m ↦ a • m`, is an isomorphism, and that it is an isomorphism of
descent data.  This is the concrete form of Stacks 039W in the direction that matters, and it is
the objectwise half of part (3) of Stacks 023N;
`StacksFrontier/AlgebraicGeometry/Descent/Modules/InvariantsInverseFunctor.lean` makes it the
counit of an equivalence whose inverse functor is `(N, φ) ↦ H⁰(s(N_•))`, which is what part (3)
asserts.

## Main definitions

* `Stacks.Descent.invariantsForkIso` compares the two equalizer presentations of a module
  descent datum: the split equalizer of Stacks 08WZ and the base-changed equalizer of
  Stacks 08X7.
* `Stacks.Descent.invariantsTensorEquiv` is the resulting `A`-linear isomorphism
  `A ⊗[R] H⁰(s(N_•)) ≃ₗ[A] N`.

## Main results

* `Stacks.Descent.invariantsTensorEquiv_tmul`: the isomorphism sends `a ⊗ m` to `a • m`.
* `Stacks.Descent.transition_smul_tmul`: on an invariant section the transition isomorphism
  sends `(a • m) ⊗ b` to `a ⊗ (b • m)`.  This is the statement that the isomorphism is one of
  descent data.
* `Stacks.Descent.isEffective_of_faithfullyFlat`: every module descent datum along a faithfully
  flat ring map is effective, with the descended module exhibited as the invariants.

## Implementation notes

The two fork presentations are already available publicly:
`ModuleCat.DescentData.isSplitEqualizer_descentComparison` (Stacks 08WZ) and
`ModuleCat.tensorPushforward_isEqualizer` (Stacks 08X7).  They are forks of the *same* parallel
pair, so `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso` compares their cone points
directly, and `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp` says the
comparison commutes with the two inclusions.  The formula on pure tensors is then forced,
because the inclusion of the split equalizer is a monomorphism and
`ModuleCat.tensorPushforwardComparison_tmul` computes the other inclusion on `a ⊗ m`.

`Stacks.Descent.invariantsForkIso` has to be public rather than private, because it appears in
the body of `Stacks.Descent.invariantsTensorEquiv`, which `@[expose]` publishes.

`StacksFrontier/AlgebraicGeometry/Descent/Modules/EffectiveDescent.lean` carries `private`
counterparts of `invariantsForkIso` and `invariantsTensorEquiv` (`descentComparisonLinearIso`,
`descentCounitLinearEquiv` and `descentCounitLinearEquiv_tmul`), used there only to prove the
equivalence of effective descent with universal injectivity.  Being `private` they cannot be
cited, and their names are mangled, so there is no constant-name collision; promoting them and
deleting the declarations here is a dedup candidate.

The final statement needs no compatibility lemma beyond `transition_smul_tmul`, which is one
application of `A ⊗[R] A`-linearity of the transition to `(a ⊗ b) • (m ⊗ 1)`.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 039W](https://stacks.math.columbia.edu/tag/039W)
* [Stacks Project, Tag 08WZ](https://stacks.math.columbia.edu/tag/08WZ)
* [Stacks Project, Tag 08X7](https://stacks.math.columbia.edu/tag/08X7)
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory TensorProduct ModuleCat

namespace Stacks.Descent

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The comparison of the two equalizer presentations of a module descent datum: the split
equalizer of Stacks 08WZ, with cone point the datum's module, and the base-changed equalizer of
Stacks 08X7, with cone point the base extension of the invariants. -/
noncomputable def invariantsForkIso
    (h : Algebra.UniversallyInjective R A) (D : ModuleCat.DescentData.{u, u, w} R A) :
    ModuleCat.of A (A ⊗[R] ModuleCat.invariantSubmodule R A D) ≅
      ModuleCat.of A (ULift.{u} D.module) :=
  (tensorPushforward_isEqualizer R A h D).conePointUniqueUpToIso
    (Classical.choice
      (ModuleCat.DescentData.isSplitEqualizer_descentComparison R A D)).isEqualizer

/-- For a universally injective ring map, the canonical `A`-linear map from the base extension
of the invariants of a module descent datum to its module is an isomorphism. -/
noncomputable def invariantsTensorEquiv
    (h : Algebra.UniversallyInjective R A) (D : ModuleCat.DescentData.{u, u, w} R A) :
    (A ⊗[R] ModuleCat.invariantSubmodule R A D) ≃ₗ[A] D.module :=
  have he : Function.Bijective (invariantsForkIso R A h D).hom.hom := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  (LinearEquiv.ofBijective (invariantsForkIso R A h D).hom.hom he).trans
    (ULift.moduleEquiv.{u, w, u} (R := A) (M := D.module))

/-- The comparison isomorphism commutes with the two equalizer inclusions. -/
private theorem invariantsForkIso_spec
    (h : Algebra.UniversallyInjective R A) (D : ModuleCat.DescentData.{u, u, w} R A)
    (x : A ⊗[R] ModuleCat.invariantSubmodule R A D) :
    ModuleCat.DescentData.descentComparisonHom R A D
        ((invariantsForkIso R A h D).hom.hom x) =
      tensorPushforwardComparison R A D x := by
  have he : (invariantsForkIso R A h D).hom ≫
      ModuleCat.ofHom (ModuleCat.DescentData.descentComparisonHom R A D) =
      ModuleCat.ofHom (tensorPushforwardComparison R A D) :=
    ModuleCat.hom_ext (congrArg ModuleCat.Hom.hom
      (Limits.IsLimit.conePointUniqueUpToIso_hom_comp _ _ Limits.WalkingParallelPair.zero))
  simpa using congrArg (fun f : ModuleCat.of A (A ⊗[R] ModuleCat.invariantSubmodule R A D) ⟶
    ModuleCat.of A (A ⊗[R] ModuleCat.restrictModule R A D.module) => f.hom x) he

/-- The canonical isomorphism sends `a ⊗ m` to `a • m`. -/
theorem invariantsTensorEquiv_tmul
    (h : Algebra.UniversallyInjective R A) (D : ModuleCat.DescentData.{u, u, w} R A)
    (a : A) (m : ModuleCat.invariantSubmodule R A D) :
    invariantsTensorEquiv R A h D (a ⊗ₜ[R] m) = a • (m.1 : D.module) := by
  have hcmp₁ : ModuleCat.DescentData.descentComparisonHom R A D
      (ULift.up (invariantsTensorEquiv R A h D (a ⊗ₜ[R] m))) =
      a ⊗ₜ[R] (m.1 : ModuleCat.restrictModule R A D.module) := by
    simpa [invariantsTensorEquiv, tensorPushforwardComparison, LinearMap.lTensor_tmul] using
      invariantsForkIso_spec R A h D (a ⊗ₜ[R] m)
  have hmul : D.transitionRestrictScalars R A
      (((a • (m.1 : D.module) : D.module) : ModuleCat.restrictModule R A D.module) ⊗ₜ[R]
        (1 : A)) = a ⊗ₜ[R] (m.1 : ModuleCat.restrictModule R A D.module) := by
    have hcmp := (tensorPushforwardComparison_tmul R A D a m).symm
    change D.transitionRestrictScalars R A
      ((a • (m.1 : ModuleCat.restrictModule R A D.module)) ⊗ₜ[R] (1 : A)) =
        a ⊗ₜ[R] (m.1 : ModuleCat.restrictModule R A D.module) at hcmp
    convert hcmp using 1
  have hcmp₂ : ModuleCat.DescentData.descentComparisonHom R A D
      (ULift.up (a • (m.1 : D.module))) =
      a ⊗ₜ[R] (m.1 : ModuleCat.restrictModule R A D.module) := by
    rw [ModuleCat.DescentData.descentComparisonHom_apply R A D (a • (m.1 : D.module))]
    exact hmul
  exact congrArg ULift.down
    (ModuleCat.DescentData.descentComparisonHom_injective R A D (hcmp₁.trans hcmp₂.symm))

/-- On an invariant section the transition isomorphism is determined by the two scalars: it
sends `(a • m) ⊗ b` to `a ⊗ (b • m)`. -/
theorem transition_smul_tmul (D : ModuleCat.DescentData.{u, u, w} R A)
    (a b : A) (m : ModuleCat.invariantSubmodule R A D) :
    D.transition
        (((a • (m.1 : D.module) : D.module) : ModuleCat.restrictModule R A D.module) ⊗ₜ[R] b) =
      a ⊗ₜ[R] ((b • (m.1 : D.module) : D.module) : ModuleCat.restrictModule R A D.module) := by
  have hinv : D.transition (m.1 ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] m.1 := m.2
  have h := D.transition.map_smul (a ⊗ₜ[R] b) (m.1 ⊗ₜ[R] (1 : A))
  rwa [ModuleCat.sourceTensor_smul_tmul, hinv, ModuleCat.targetTensor_smul_tmul,
    mul_one, mul_one] at h

/-- **Effective descent of modules along a faithfully flat ring map, with the descended module
exhibited as the invariants.**  Every module descent datum along a faithfully flat `R → A` is
isomorphic, as a descent datum, to the base extension of its submodule of invariant sections. -/
theorem isEffective_of_faithfullyFlat [Module.FaithfullyFlat R A]
    (D : ModuleCat.DescentData.{u, u, w} R A) :
    ModuleCat.DescentData.IsEffective R A D := by
  refine ⟨ModuleCat.of R (ModuleCat.invariantSubmodule R A D),
    invariantsTensorEquiv R A (.of_faithfullyFlat R A) D, fun a b m ↦ ?_⟩
  rw [invariantsTensorEquiv_tmul, invariantsTensorEquiv_tmul]
  exact transition_smul_tmul R A D a b m

end Stacks.Descent

end
