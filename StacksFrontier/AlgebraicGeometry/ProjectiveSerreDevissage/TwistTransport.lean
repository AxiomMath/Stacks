module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSerreDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.TwistTransport
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Twist

/-!
# Serre vanishing for the twisting sheaves of `ℙⁿ_R`, from the transport of `𝒪(d)`

`Stacks.AlgebraicGeometry.ProjectiveSerreDevissage.HasEventuallyAcyclicProjectiveTwists` asserts,
for each `k`, the vanishing of `Hᵐ(ℙⁿ_R, 𝒪(k)(d))` in every positive degree `m` once `d` is large.
Its counterpart on the homogeneous spectrum of `R[T₀, …, Tₙ]` is
`Stacks.ProjectiveSpace.SerreVanishing.hasEventuallyAcyclicTwists_polyGrading`, over an arbitrary
commutative ring and with no Noetherian hypothesis.

This file carries that vanishing across the comparison of the two models of projective space,
given `Stacks.ProjectiveCohomology.HasPolyTwistTransport`, the identification of the two models'
twisting sheaves, which is clause (3) of [Stacks, Tag 01N2] at the polynomial grading.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSerreDevissage.tensorTwistingSheafPullbackIso`: the tensor
  product of two twisting sheaves of `ℙⁿ_R` is the inverse image, along the comparison of
  models, of the tensor product of the two `Proj`-model twisting sheaves.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSerreDevissage`
  `.hasEventuallyAcyclicProjectiveTwists_of_hasPolyTwistTransport`: Serre vanishing for the
  twisting sheaves of `ℙⁿ_R`, given the transport of `𝒪(d)`, with no Noetherian hypothesis on
  `R`.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveSerreDevissage

variable (S : Type u) [CommRing S] (n : ℕ)

/-- Given identifications `ek` and `ed` of the twisting sheaves `𝒪(k)` and `𝒪(d)` of `ℙⁿ_R` with
the inverse images of the `Proj`-model twisting sheaves, the tensor product of the two twisting
sheaves of `ℙⁿ_R` is the inverse image, along the comparison of the two models
`Stacks.ProjectiveCohomology.projModelIso`, of the tensor product of the two `Proj`-model
twisting sheaves. -/
def tensorTwistingSheafPullbackIso (k d : ℤ)
    (ek : (Scheme.Modules.pullback (projModelIso S n).inv).obj
        (twistingSheaf (polyGrading S n) k) ≅ projectiveTwistingSheaf (R := S) n k)
    (ed : (Scheme.Modules.pullback (projModelIso S n).inv).obj
        (twistingSheaf (polyGrading S n) d) ≅ projectiveTwistingSheaf (R := S) n d) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((AlgebraicGeometry.projectiveSpaceOverRing n
            (CommRingCat.of S)).toSheafedSpace)).presheaf,
          (((AlgebraicGeometry.projectiveSpaceOverRing n
            (CommRingCat.of S)).toSheafedSpace)).IsSheaf⟩))).obj
      (projectiveTwistingSheaf (R := S) n k, projectiveTwistingSheaf (R := S) n d) ≅
      (Scheme.Modules.pullback (projModelIso S n).inv).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(((AlgebraicGeometry.Proj (polyGrading S n)).toSheafedSpace)).presheaf,
              (((AlgebraicGeometry.Proj (polyGrading S n)).toSheafedSpace)).IsSheaf⟩))).obj
          (twistingSheaf (polyGrading S n) k, twistingSheaf (polyGrading S n) d)) :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of S)).toSheafedSpace)).presheaf,
        (((AlgebraicGeometry.projectiveSpaceOverRing n
          (CommRingCat.of S)).toSheafedSpace)).IsSheaf⟩))).mapIso
      (Iso.prod ek.symm ed.symm) ≪≫
    ((Stacks.RingedSpace.comparisonBifunctorIso
        (projModelIso S n).inv.toLRSHom.toShHom).app
      (twistingSheaf (polyGrading S n) k, twistingSheaf (polyGrading S n) d)).symm

/-- **Serre vanishing for the twisting sheaves of `ℙⁿ_R`, given the transport of `𝒪(d)` between
the two models of projective space.** For an arbitrary commutative ring `S` and each `k`, the
positive-degree cohomology of `𝒪(k)(d)` on `AlgebraicGeometry.projectiveSpaceOverRing n S`
vanishes once `d` is large. -/
theorem hasEventuallyAcyclicProjectiveTwists_of_hasPolyTwistTransport
    (h : HasPolyTwistTransport S n) :
    HasEventuallyAcyclicProjectiveTwists (R := S) n ⊤ := by
  intro k
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.ProjectiveSpace.SerreVanishing.hasEventuallyAcyclicTwists_polyGrading S n k
  refine ⟨d₀, fun d hd m hm => ?_⟩
  obtain ⟨ek⟩ := nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv S n k (h k)
  obtain ⟨ed⟩ := nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv S n d (h d)
  exact ((Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff (projModelIso S n).symm
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((AlgebraicGeometry.Proj (polyGrading S n)).toSheafedSpace)).presheaf,
          (((AlgebraicGeometry.Proj (polyGrading S n)).toSheafedSpace)).IsSheaf⟩))).obj
      (twistingSheaf (polyGrading S n) k, twistingSheaf (polyGrading S n) d)) m).2
      (hd₀ d hd m hm)).of_iso
    ((Hfunctor (AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of S)).ringCatSheaf
      ⊤ m).mapIso (tensorTwistingSheafPullbackIso S n k d ek.symm ed.symm))

end Stacks.AlgebraicGeometry.ProjectiveSerreDevissage

end
