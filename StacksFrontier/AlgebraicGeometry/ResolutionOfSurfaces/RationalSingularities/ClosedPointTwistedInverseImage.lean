module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineRightAdjointDerivedHom
import StacksCore.Tactic.StacksAttribute

/-!
# The twisted inverse image at the closed point of the spectrum of a local ring

Let `(A, 𝔪, κ)` be a local ring and `j : Spec(κ) ⟶ Spec(A)` the closed point. The twisted inverse
image `j^×` of [Stacks, Tag 0A9E] corresponds to `RHom_A(κ, -)` under derived sheafification. More
generally, for a ring map `φ : R ⟶ S` the twisted inverse image along `Spec(φ)` corresponds to
`RHom_R(S, -)`; this is [Stacks, Tag 0A9F] at the twisted inverse image.

## Main results

* `AlgebraicGeometry.twistedInverseImage_spec_isoDerivedHom`: for a ring map `φ : R ⟶ S`, the
  twisted inverse image along `Spec(φ)` corresponds to `RHom_R(S, -)` under derived
  sheafification.
* `AlgebraicGeometry.twistedInverseImage_residuePoint_isoDerivedHom`: the same at the closed
  point `j : Spec(κ) ⟶ Spec(A)` of a local ring.

## References

* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
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

/-- For a ring map `φ : R ⟶ S`, the derived direct image along `Spec(φ)` on the derived categories
with quasi-coherent cohomology has a right adjoint ([Stacks, Tag 0A9E]). -/
instance isLeftAdjoint_quasiCoherentDerivedPushforward_spec {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (Stacks.Duality.quasiCoherentDerivedPushforward (Spec.map φ)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map φ))).IsLeftAdjoint :=
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (Spec.map φ)

/-- **[Stacks, Tag 0A9F] at the twisted inverse image.** For a homomorphism `φ : R ⟶ S` of
commutative rings, the twisted inverse image `Spec(φ)^×` of [Stacks, Tag 0A9E] corresponds to
`RHom_R(S, -)` under derived sheafification: `Spec(φ)^×(M~) ≅ RHom_R(S, M)~`, naturally in
`M ∈ D(R)`. -/
theorem twistedInverseImage_spec_isoDerivedHom {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Nonempty (derivedTilde R ⋙ Stacks.Duality.twistedInverseImage (Spec.map φ)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map φ)) ≅
        Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom ⋙ derivedTilde S) :=
  derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom φ
    (Stacks.Duality.twistedInverseImageAdjunction (Spec.map φ)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map φ)))

/-- **The twisted inverse image at the closed point of `Spec(A)` is `RHom_A(κ, -)`.** For
`(A, 𝔪, κ)` a local ring and `j = Spec(A → κ)` the closed immersion of the closed point
(`Stacks.Blowup.residuePoint`), `j^×(M~) ≅ RHom_A(κ, M)~`, naturally in `M ∈ D(A)`. -/
theorem twistedInverseImage_residuePoint_isoDerivedHom (A : Type u) [CommRing A] [IsLocalRing A] :
    letI : (Stacks.Duality.quasiCoherentDerivedPushforward (Stacks.Blowup.residuePoint A)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))).IsLeftAdjoint :=
      isLeftAdjoint_quasiCoherentDerivedPushforward_spec
        (CommRingCat.ofHom (IsLocalRing.residue A))
    Nonempty (derivedTilde (CommRingCat.of A) ⋙
          Stacks.Duality.twistedInverseImage (Stacks.Blowup.residuePoint A)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs
              (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) ≅
        Dualizing.AnyModel.derivedHom.{u, u, u, u, u} (IsLocalRing.residue A) ⋙
          derivedTilde (CommRingCat.of (IsLocalRing.ResidueField A))) :=
  twistedInverseImage_spec_isoDerivedHom (CommRingCat.ofHom (IsLocalRing.residue A))

end AlgebraicGeometry

end
