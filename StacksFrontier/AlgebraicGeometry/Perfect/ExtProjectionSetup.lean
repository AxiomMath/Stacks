module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionFormula
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic

/-!
# The situation of [Stacks, Tag 0DJQ], read for the projection formula

Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of finite type, `E` a perfect
object of `D(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules flat over `S` whose
support is contained in a closed subset `Z` proper over `S`.  This file records the three facts
about `N = E ⊗^𝐋_{𝒪_X} 𝒢` that the projection formula of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportedProjectionFormula.lean` consumes:

* `N` has quasi-coherent (indeed coherent) cohomology sheaves;
* the cohomology sheaves of `N` are supported on `Z`;
* `Z` lies in a quasi-compact open `U ⊆ X` such that `U ⟶ X` and `U ⟶ X ⟶ S` are quasi-compact
  and quasi-separated.

## Main results

* `Stacks.Cohomology.ExtProjectionSetup.hasQuasicoherentCohomology_derivedTensorG`
* `Stacks.Cohomology.ExtProjectionSetup.cohomologySupportedOn_derivedTensorG`
* `Stacks.Cohomology.ExtProjectionSetup.exists_supportOpen`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect
open Stacks.Cohomology.SupportedProjectionFormula (DX HasQuasicoherentCohomology)

universe u

namespace Stacks.Cohomology.ExtProjectionSetup

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
  (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)

/-- **`E ⊗^𝐋 𝒢` has quasi-coherent cohomology sheaves**: they are coherent
(`Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor`) on the locally
Noetherian scheme `X`. -/
theorem hasQuasicoherentCohomology_derivedTensorG [IsNoetherian S] [LocallyOfFiniteType f]
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : PerfectPushforward.FlatProperSupportComplex f G) :
    HasQuasicoherentCohomology
      (Stacks.Cohomology.ExtProjectionFormula.derivedTensorG E G : DX X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro j
  have hc := PerfectPushforward.isCoherent_homology_derivedTensor f
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.toRingedSpace.sheaf)
    E G hE hG j
  have := hc
  exact (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj
      (Stacks.Cohomology.ExtProjectionFormula.derivedTensorG E G))).1

/-- **The cohomology sheaves of `E ⊗^𝐋 𝒢` are supported on any closed set containing the supports
of the terms of `𝒢`**, in the stalkwise form of [Stacks, Tag 08DF]. -/
theorem cohomologySupportedOn_derivedTensorG
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (Z : Set X)
    (hZ : ∀ q : ℤ, SheafOfModules.supp (G.X q) ⊆ Z) :
    Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
      (structureSheafRing X.toRingedSpace) Z
      (Stacks.Cohomology.ExtProjectionFormula.derivedTensorG E G : DX X) := by
  intro i x hx
  have hsub := PerfectPushforward.supp_homology_derivedTensor_subset X
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.toRingedSpace.sheaf)
    E G hE Z hZ i
  have hnot : x ∉ SheafOfModules.supp ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} X.toRingedSpace) i).obj
        (Stacks.Cohomology.ExtProjectionFormula.derivedTensorG E G)) :=
    fun hm => hx (hsub hm)
  have hs := (SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).not.1 hnot
  rw [not_nontrivial_iff_subsingleton] at hs
  exact AddCommGrpCat.isZero_iff_subsingleton.2 hs

/-- **A quasi-compact open neighbourhood of the support.**  For `S` Noetherian and `f` locally of
finite type, a closed subset `Z ⊆ X` proper over `S` lies in an open `U` such that `U ⟶ X` and
`U ⟶ X ⟶ S` are quasi-compact and quasi-separated: `U` is the union of finitely many affine
opens, hence a Noetherian scheme, and `X` is locally Noetherian, hence quasi-separated. -/
theorem exists_supportOpen [IsNoetherian S] [LocallyOfFiniteType f] (Z : Closeds X)
    (hZ : IsProperOver f Z) :
    ∃ U : X.Opens, (Z : Set X) ⊆ U ∧ QuasiCompact U.ι ∧ QuasiSeparated U.ι ∧
      QuasiCompact (U.ι ≫ f) ∧ QuasiSeparated (U.ι ≫ f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨U, hU, hZU⟩ := exists_isCompact_opens_superset_of_isProperOver f Z hZ
  have : IsNoetherian U.toScheme := isNoetherian_of_isCompact_opens U hU
  exact ⟨U, hZU, inferInstance, inferInstance, inferInstance, inferInstance⟩

end Stacks.Cohomology.ExtProjectionSetup

end
