module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.TensorPowerInvariant
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic

/-!
# Multiplication by a section of the twist, with an `n`-independent nonvanishing hypothesis

`Stacks.SectionProduct.mono_mulRight_of_associatedPoints` already needs only nonvanishing near the
associated points of its *domain*: at the `n`-th step of the induction underlying
`HasHilbertInductionStep` (clause 2, [Stacks, Tag 0F27]), that domain is
`T.F ⊗ L^{⊗ n}`, so the hypothesis it is applied with is nonvanishing near
`Ass(T.F ⊗ L^{⊗ n})` — a condition that, read literally, depends on `n`.

This file removes that dependence. `Stacks.Divisors.associatedPoints_tensorObj_tensorPowScheme_eq`
gives `Ass(F ⊗ L^{⊗ n}) = Ass(F)`, every integer `n`, when `L` is invertible — but it is stated for
`AlgebraicGeometry.Scheme.Modules.tensorObj`, Mathlib's sheafification-of-the-objectwise-tensor
spelling of the tensor product of sheaves of modules, while `mulRight` and
`mono_mulRight_of_associatedPoints` are stated for the *monoidal* `⊗` (the one localised along
sheafification, active here as `Stacks.SheafInternalHom.schemeMonoidalCategory`). The two are only
*isomorphic*, by `Stacks.SheafOfModules.tensorObjIso`, not equal, so closing the gap needs that
isomorphism transported across `Ass` by `Stacks.Divisors.associatedPoints_congr`
(an isomorphism-invariance lemma for associated points already on hand) before
`associatedPoints_tensorObj_tensorPowScheme_eq` applies. No new monoidal-category machinery is
built here: this is `mono_mulRight_of_associatedPoints`, composed with that associated-points
identity transported across the one bridging isomorphism the two tensor-product spellings need.

## Main results

* `Stacks.SectionProduct.mono_mulRight_tensorPowScheme_of_associatedPoints`: multiplication by a
  section nonvanishing near every associated point of `F` is a monomorphism on
  `F ⊗ L^{⊗ n} ⟶ (F ⊗ L^{⊗ n}) ⊗ L`, for every integer `n`, with the hypothesis stated once, about
  `Ass(F)`, independently of `n`.
* `Stacks.SectionProduct.mono_mulRight_tensorPowScheme_comp_of_associatedPoints`: the same after
  composing with an isomorphism identifying the target, the shape a caller gluing twists into
  `T.F ⊗ L^{⊗ (n+1)}` needs.

## What is not done

**This file stays at the `mulRight` level.** The induction step of `HasHilbertInductionStep` is
stated through `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` and
`whiskerLeft_mulSectionPowScheme`
(`StacksFrontier/AlgebraicGeometry/Algebraization/CoherentTripleTwistSuccessor.lean:183-201`), whose
section is `σ : Stacks.Ample.unitModule X ⟶ L` rather than `f : 𝟙_ X.Modules ⟶ L`, and whose twist
is spelled through `Stacks.RelativeVeryAmple.tensorModules`'s bifunctor `.map`
(`tensorModulesMap`) rather than through the monoidal `◁`. `Stacks.Ample.unitModule X` is only
*isomorphic* to `𝟙_ X.Modules`
(`Stacks.Ample.unitModuleIsoTensorUnit`,
`StacksFrontier/AlgebraicGeometry/AmpleWire/Basic.lean:315`),
not equal to it, and `tensorModules` is "deliberately" a second bifunctor-spelling from the
monoidal product
(`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPower.lean`,
docstring of `tensorModules`).
Transporting the lemmas below across both gaps at once is exactly the kind of elaboration that
exhausts the heartbeat budget elsewhere in the library, and is not done here; what is proved is the
`mulRight`/monoidal-unit-section form, with the `n`-dependence resolved, which is as far as Gap B
goes on its own.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

namespace Stacks.SectionProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open Stacks.TensorSectionNonvanishing

/-- The bridging fact doing all the work in this file: `Ass(F ⊗ L^{⊗ n}) = Ass(F)` for the
*monoidal* tensor product, `L` invertible, every integer `n`. Transports
`associatedPoints_tensorObj_tensorPowScheme_eq` (stated for
`AlgebraicGeometry.Scheme.Modules.tensorObj`) across `Stacks.SheafOfModules.tensorObjIso`
(the isomorphism identifying that spelling with the monoidal `⊗`), using
`Stacks.Divisors.associatedPoints_congr`. -/
theorem associatedPoints_tensorObj_monoidal_tensorPowScheme_eq {X : Scheme.{u}}
    (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) :
    Stacks.Divisors.associatedPoints (F ⊗ Stacks.Algebraization.tensorPowScheme X L n)
      = Stacks.Divisors.associatedPoints F :=
  (Stacks.Divisors.associatedPoints_congr
      (Stacks.SheafOfModules.tensorObjIso X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F
        (Stacks.Algebraization.tensorPowScheme X L n))).trans
    (Stacks.Divisors.associatedPoints_tensorObj_tensorPowScheme_eq F L n)

/-- **Multiplication by a global section of `L`, nonvanishing near every associated point of `F`,
is a monomorphism on the `n`-th twist**, for every integer `n`. The hypothesis is stated once,
about `Ass(F)`, with no reference to `n`: `Ass(F ⊗ L^{⊗ n}) = Ass(F)` since `L^{⊗ n}` is invertible
(`associatedPoints_tensorObj_monoidal_tensorPowScheme_eq` above), so
`mono_mulRight_of_associatedPoints` applies at the domain `F ⊗ L^{⊗ n}` with that hypothesis
rewritten. The quasi-coherence side conditions needed by `mono_mulRight_of_associatedPoints` at
that domain are taken as explicit hypotheses, following the precedent of
`mono_twistSectionMulNegOne_of_nonvanishing`
(`StacksFrontier/AlgebraicGeometry/Constructions/ProjectiveSpaceHyperplaneSection.lean:252`), rather
than derived: deriving them needs quasicoherence of the *monoidal* tensor product of two
quasicoherent modules, which is available only through a general-site instance
(`Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorObj`) whose site-level sheafification
hypotheses are not shown here to specialise to a scheme's Zariski site; taking the two facts as
hypotheses sidesteps that without weakening the statement, since a caller instantiating `n` always
has both twists already quasicoherent in practice. -/
theorem mono_mulRight_tensorPowScheme_of_associatedPoints {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) {N : X.Modules}
    [(F ⊗ Stacks.Algebraization.tensorPowScheme X L n).IsQuasicoherent]
    [((F ⊗ Stacks.Algebraization.tensorPowScheme X L n) ⊗ L).IsQuasicoherent]
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (f : 𝟙_ X.Modules ⟶ L)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints F, ∃ W : X.Opens, x ∈ W ∧ ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L
        (monoidalUnitHomEquiv L f)) :
    Mono (mulRight (F ⊗ Stacks.Algebraization.tensorPowScheme X L n) f) := by
  have hW' : ∀ x ∈ Stacks.Divisors.associatedPoints
      (F ⊗ Stacks.Algebraization.tensorPowScheme X L n),
      ∃ W : X.Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L
          (monoidalUnitHomEquiv L f) := by
    rw [associatedPoints_tensorObj_monoidal_tensorPowScheme_eq F L n]
    exact hW
  exact mono_mulRight_of_associatedPoints _ ψ f hW'

/-- **The same conclusion after identifying the target**, the shape a caller assembling the twists
of `HasHilbertInductionStep` into `T.F ⊗ L^{⊗ (n+1)}` needs: a monomorphism followed by an
isomorphism is a monomorphism. -/
theorem mono_mulRight_tensorPowScheme_comp_of_associatedPoints {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) {N G : X.Modules}
    [(F ⊗ Stacks.Algebraization.tensorPowScheme X L n).IsQuasicoherent]
    [((F ⊗ Stacks.Algebraization.tensorPowScheme X L n) ⊗ L).IsQuasicoherent]
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (f : 𝟙_ X.Modules ⟶ L)
    (e : ((F ⊗ Stacks.Algebraization.tensorPowScheme X L n) ⊗ L) ≅ G)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints F, ∃ W : X.Opens, x ∈ W ∧ ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L
        (monoidalUnitHomEquiv L f)) :
    Mono (mulRight (F ⊗ Stacks.Algebraization.tensorPowScheme X L n) f ≫ e.hom) :=
  have :=
    mono_mulRight_tensorPowScheme_of_associatedPoints F L n ψ f hW
  mono_comp _ _

end Stacks.SectionProduct

end
