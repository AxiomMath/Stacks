module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ClosedPointTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineRightAdjointDerivedHom
import StacksCore.Tactic.StacksAttribute

/-!
# Further results on `ClosedPointTwistedInverseImage`

For a ring map `φ : R ⟶ S`, the derived pushforward along `Spec.map φ` sends quasi-coherent
complexes on `Spec S` to complexes on `Spec R` with quasi-coherent cohomology sheaves.

## Main definitions

* `AlgebraicGeometry.isQuasicoherentPushforwardSpec`: The cohomology sheaves of the derived
  pushforward along `Spec.map φ` of a quasi-coherent complex are quasi-coherent.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- For a ring map `φ : R ⟶ S` and a quasi-coherent complex `K` on `Spec S`, every cohomology
sheaf of the derived pushforward of `K` along `Spec.map φ` is quasi-coherent
([Stacks, Tag 08D5], part (1)). -/
abbrev isQuasicoherentPushforwardSpec {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec S)) (i : ℤ),
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
        ((Stacks.Duality.derivedPushforward (Spec.map φ)).obj K.obj)).IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map φ)

end AlgebraicGeometry

end
