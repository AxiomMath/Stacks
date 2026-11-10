module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.ComparisonIso
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme

/-!
# The twisted inverse image of `ω_A` along a closed subscheme of `ℙⁿ_A`

Let `f : X ⟶ Spec A` factor as a closed immersion `i : X ⟶ ℙⁿ_A` followed by the structure
morphism `p : ℙⁿ_A ⟶ Spec A`, and let `a` be a right adjoint of `Rf_*` on `D_QCoh`. Then
`Rf_* ≅ Rp_* ∘ Ri_*`, so `a ≅ i^× ∘ p^×`, and
`a(ω~_A) ≅ i^×((𝒪(-n-1) ⊗ p^*ω~_A)[n])` by duality on `ℙⁿ_A` with coefficients
(`Stacks.Duality.ProjCoeff.twistedInverseImageIso`).

* `Stacks.Duality.ProjCoeff.twistedInverseImageFactorIso`: `a ≅ p^× ⋙ i^×`.
* `Stacks.Duality.ProjCoeff.isDualizingComplex_of_closedImmersion_projSpace_of`: `a(ω~_A)` is a
  dualizing complex, given that `(𝒪(-n-1) ⊗ p^*ω~_A)[n]` is one on `ℙⁿ_A` and that the right
  adjoint of `Ri_*` carries dualizing complexes to dualizing complexes.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

variable {A : Type u} [CommRing A] (n : ℕ)

section Factor

variable {X : Scheme.{u}} (i : X ⟶ P A n) [IsClosedImmersion i]
  (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (j : ℤ),
    ((DerivedCategory.homologyFunctor (Spec (.of A)).Modules j).obj
      ((Stacks.Duality.derivedPushforward (i ≫ projToSpecCoeff A n)).obj K.obj)).IsQuasicoherent)

/-- `Ri_* : D_QCoh(X) ⥤ D_QCoh(ℙⁿ_A)` has a right adjoint, a closed immersion being qcqs. -/
instance isLeftAdjoint_affineHomQuasiCoherentDerivedPushforward :
    (Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward i).IsLeftAdjoint :=
  AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward i

/-- `i^×`, the right adjoint of `Ri_* : D_QCoh(X) ⥤ D_QCoh(ℙⁿ_A)`. -/
abbrev closedTwistedInverseImage :
    Stacks.Duality.quasiCoherentDerivedCategory (P A n) ⥤
      Stacks.Duality.quasiCoherentDerivedCategory X :=
  (Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward i).rightAdjoint

/-- The adjunction `Ri_* ⊣ i^×`. -/
abbrev closedTwistedInverseImageAdjunction :
    Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⊣
      closedTwistedInverseImage n i :=
  Adjunction.ofIsLeftAdjoint _

/-- `Ri_* ⋙ Rp_* ≅ R(i ≫ p)_*` on `D_QCoh`. -/
def pushforwardFactorIso :
    Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⋙ Rpq A n ≅
      Stacks.Duality.quasiCoherentDerivedPushforward (i ≫ projToSpecCoeff A n) hpush :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      ((Stacks.Duality.derivedPushforwardCompIso i (projToSpecCoeff A n)).app K.obj))
    (fun e => ObjectProperty.hom_ext _
      ((Stacks.Duality.derivedPushforwardCompIso i (projToSpecCoeff A n)).hom.naturality e.hom))

/-- **`a ≅ p^× ⋙ i^×`** for any right adjoint `a` of `R(i ≫ p)_*`. -/
def twistedInverseImageFactorIso
    (a : Stacks.Duality.quasiCoherentDerivedCategory (Spec (.of A)) ⥤
      Stacks.Duality.quasiCoherentDerivedCategory X)
    (adj : Stacks.Duality.quasiCoherentDerivedPushforward (i ≫ projToSpecCoeff A n) hpush ⊣ a) :
    a ≅ Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec A n ⋙
      closedTwistedInverseImage n i :=
  Adjunction.rightAdjointUniq adj
    (((closedTwistedInverseImageAdjunction n i).comp (adjq A n)).ofNatIsoLeft
      (pushforwardFactorIso n i hpush))

end Factor

/-- **`a(ω~_A)` is a dualizing complex on a closed subscheme of `ℙⁿ_A`**, given that
`(𝒪(-n-1) ⊗ p^*ω~_A)[n]` is a dualizing complex on `ℙⁿ_A` (`hGqc`) and that `i^×` carries
dualizing complexes to dualizing complexes (`hcl`). -/
theorem isDualizingComplex_of_closedImmersion_projSpace_of (ωA : ModuleCat.{u} A)
    [IsLocallyNoetherian (P A n)] (hGqc : Stacks.Duality.IsDualizingComplex (Gqc A n ωA).obj)
    {X : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Spec (.of A)) (i : X ⟶ P A n)
    [IsClosedImmersion i] (hfac : i ≫ projToSpecCoeff A n = f)
    (hcl : ∀ (a : Stacks.Duality.quasiCoherentDerivedCategory (P A n) ⥤
        Stacks.Duality.quasiCoherentDerivedCategory X)
      (_ : Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⊣ a)
      (K : Stacks.Duality.quasiCoherentDerivedCategory (P A n)),
      Stacks.Duality.IsDualizingComplex K.obj → Stacks.Duality.IsDualizingComplex (a.obj K).obj)
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (j : ℤ),
      ((DerivedCategory.homologyFunctor (Spec (.of A)).Modules j).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (a : Stacks.Duality.quasiCoherentDerivedCategory (Spec (.of A)) ⥤
      Stacks.Duality.quasiCoherentDerivedCategory X)
    (adj : Stacks.Duality.quasiCoherentDerivedPushforward f hpush ⊣ a) :
    Stacks.Duality.IsDualizingComplex (a.obj (Mqc A ωA)).obj := by
  subst hfac
  let e := (twistedInverseImageFactorIso n i hpush a adj).app (Mqc A ωA) ≪≫
    (closedTwistedInverseImage n i).mapIso (twistedInverseImageIso A n ωA)
  exact Stacks.Duality.isDualizingComplex_of_iso ((ObjectProperty.ι _).mapIso e).symm
    (hcl _ (closedTwistedInverseImageAdjunction n i) _ hGqc)

end Stacks.Duality.ProjCoeff
