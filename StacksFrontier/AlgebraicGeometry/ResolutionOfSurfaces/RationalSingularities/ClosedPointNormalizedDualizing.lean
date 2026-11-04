module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ClosedPointTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SituationCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.NormalizedResidueFieldLocallySmall

/-!
# `j^!(ω_A[-dim A]) ≅ 𝒪_{Spec κ}` at the closed point

Let `(A, 𝔪, κ)` be a Cohen–Macaulay Noetherian local ring, `j : Spec(κ) ⟶ Spec(A)` the closed
point and `ω_A` a dualizing module for `A` in the sense of
`Stacks.Duality.IsDualizingRingModule`. The twisted inverse image of [Stacks, Tag 0A9E] along `j`,
applied to `ω_A` placed in degree `-dim(A)`, is the structure sheaf of `Spec(κ)` in degree zero.

## Main results

* `AlgebraicGeometry.nonempty_twistedInverseImage_residuePoint_derivedTilde_iso_single`: the
  isomorphism `j^!(ω_A[-dim A]-tilde) ≅ κ[0]-tilde`.
* `RationalSingularitySituation.nonempty_twistedInverseImage_residuePoint_iso_single`: the same
  in Situation [Stacks, Tag 0B4W].

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open Stacks.Duality (isQuasicoherent_homology_derivedPushforward_of_qcqs)
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **`j^!(ω_A[-dim A]) ≅ 𝒪_{Spec κ}` at the closed point of `Spec(A)`.** For `(A, 𝔪, κ)` a
Cohen–Macaulay Noetherian local ring, `j : Spec(κ) ⟶ Spec(A)` the closed point and `ω_A` a
dualizing module for `A`, the twisted inverse image of [Stacks, Tag 0A9E] along `j` carries `ω_A`
placed in degree `-dim(A)` to `κ` placed in degree zero.

Here `ω_A` is a dualizing module in the sense that `ω_A` placed in some degree `n` is a dualizing
complex for `A`. -/
theorem nonempty_twistedInverseImage_residuePoint_derivedTilde_iso_single (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (hA : IsCohenMacaulayLocalRing A)
    (ω : ModuleCat.{u} A) (n : ℤ)
    (hn : @Dualizing.IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A))
      ((@DerivedCategory.singleFunctor (ModuleCat.{u} A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} A)) n).obj ω)) :
    letI : (Stacks.Duality.quasiCoherentDerivedPushforward (Stacks.Blowup.residuePoint A)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))).IsLeftAdjoint :=
      isLeftAdjoint_quasiCoherentDerivedPushforward_spec
        (CommRingCat.ofHom (IsLocalRing.residue A))
    Nonempty ((Stacks.Duality.twistedInverseImage (Stacks.Blowup.residuePoint A)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))).obj
        ((derivedTilde (CommRingCat.of A)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A)
            (-(Dualizing.localRingDimension A : ℤ))).obj ω)) ≅
      (derivedTilde (CommRingCat.of (IsLocalRing.ResidueField A))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (IsLocalRing.ResidueField A)) 0).obj
          ((ModuleCat.uliftFunctor.{0} (IsLocalRing.ResidueField A)).obj
            (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A))))) := by
  obtain ⟨e⟩ := twistedInverseImage_residuePoint_isoDerivedHom A
  obtain ⟨d⟩ := Dualizing.nonempty_derivedHom_residueField_iso_single_of_cohenMacaulay hA ω n hn
  exact ⟨e.app _ ≪≫ (derivedTilde (CommRingCat.of (IsLocalRing.ResidueField A))).mapIso d⟩

/-- **`j^!(ω_A[-dim A]) ≅ 𝒪_{Spec κ}` in Situation [Stacks, Tag 0B4W].** For `A` the base ring of
the situation, `j : Spec(κ) ⟶ Spec(A)` the closed point and `ω_A` a module which, placed in some
degree `n`, is a dualizing complex for `A`, the twisted inverse image of [Stacks, Tag 0A9E] along
`j` carries `ω_A` placed in degree `-dim(A)` to `κ` placed in degree zero. -/
theorem RationalSingularitySituation.nonempty_twistedInverseImage_residuePoint_iso_single
    (S : RationalSingularitySituation.{u}) (ω : ModuleCat.{u} S.A) (n : ℤ)
    (hn : @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A))
      ((@DerivedCategory.singleFunctor (ModuleCat.{u} S.A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} S.A)) n).obj ω)) :
    letI : (Stacks.Duality.quasiCoherentDerivedPushforward (Stacks.Blowup.residuePoint S.A)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S.A))))).IsLeftAdjoint :=
      isLeftAdjoint_quasiCoherentDerivedPushforward_spec
        (CommRingCat.ofHom (IsLocalRing.residue S.A))
    Nonempty ((Stacks.Duality.twistedInverseImage (Stacks.Blowup.residuePoint S.A)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S.A))))).obj
        ((derivedTilde (CommRingCat.of S.A)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A)
            (-(Dualizing.localRingDimension S.A : ℤ))).obj ω)) ≅
      (derivedTilde (CommRingCat.of (IsLocalRing.ResidueField S.A))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (IsLocalRing.ResidueField S.A)) 0).obj
          ((ModuleCat.uliftFunctor.{0} (IsLocalRing.ResidueField S.A)).obj
            (ModuleCat.of (IsLocalRing.ResidueField S.A)
              (IsLocalRing.ResidueField S.A))))) :=
  AlgebraicGeometry.nonempty_twistedInverseImage_residuePoint_derivedTilde_iso_single S.A
    S.isCohenMacaulayLocalRing ω n hn

end AlgebraicGeometry

end
