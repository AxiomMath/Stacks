module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChangeExceptionalDivisor
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.RegularSurfaceCentre
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.PullbackSections.SpecStalkSections

/-!
# `b_*𝒪_{W'}(E) = 𝒪_W` at a closed point of a global regular surface

Let `W` be a scheme, let `w ∈ W` be a closed point whose local ring is regular of dimension two
and let `b : W' ⟶ W` be the blowing up of `W` in the reduced point `{w}`, with exceptional
divisor `E`. Then the comparison map

`α : 𝒪_W ⟶ b_*𝒪_{W'}(E)`

adjoint to multiplication by the canonical section of `𝒪_{W'}(E)` is invertible. This is part (4)
of [Stacks, Tag 0AGS] at `n = -1`, at a closed point of an arbitrary scheme.

## Main definitions

* `Stacks.BlowupTwistUnit.specSectionsLinearEquivOfIso`: an isomorphism of sheaves of modules on
  `Spec R`, read on global sections as an `R`-linear equivalence.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `nonempty_sectionsLinearEquiv_exceptionalTwistPushforward_comap`: `Γ(E', 𝒪(E')) ≅ 𝒪_{W,w}` for
  the blowing up of `Spec 𝒪_{W,w}` in the inverse image of the centre.
* `nonempty_stalkLinearEquiv_exceptionalTwistPushforward`: the stalk of `b_*𝒪_{W'}(E)` at `w` is
  free of rank one over `𝒪_{W,w}`.
* `isIso_exceptionalTwistComparison_pointIdeal`: `𝒪_W ⟶ b_*𝒪_{W'}(E)` is invertible at a closed
  point of an arbitrary scheme whose local ring is regular of dimension two.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ModuleStalkSpecialization

universe u

namespace Stacks.BlowupTwistUnit

attribute [local instance] Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule

/-! ### Global sections over the spectrum of a ring -/

/-- The `R`-linear equivalence of global sections induced by an isomorphism of sheaves of modules
on `Spec R`, where `R` acts on global sections through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
def specSectionsLinearEquivOfIso {R : CommRingCat.{u}} {G₁ G₂ : (Spec R).Modules} (κ : G₁ ≅ G₂) :
    letI : Module R Γ(G₁, (⊤ : (Spec R).Opens)) :=
      Module.compHom _ (Scheme.ΓSpecIso R).inv.hom
    letI : Module R Γ(G₂, (⊤ : (Spec R).Opens)) :=
      Module.compHom _ (Scheme.ΓSpecIso R).inv.hom
    Γ(G₁, (⊤ : (Spec R).Opens)) ≃ₗ[R] Γ(G₂, (⊤ : (Spec R).Opens)) :=
  ((ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).mapIso
    ((_root_.SheafOfModules.evaluation (Spec R).ringCatSheaf (op ⊤)).mapIso κ)).toLinearEquiv

/-! ### The sections upstairs -/

variable {W : Scheme.{u}}

/-- If the local ring of `W` at a closed point `w` is regular of dimension two, the global
sections of the exceptional twist of the blowing up of `Spec 𝒪_{W,w}` in the inverse image of
`{w}` are free of rank one over `𝒪_{W,w}`. -/
theorem nonempty_sectionsLinearEquiv_exceptionalTwistPushforward_comap (w : W)
    (hw : IsClosed ({w} : Set W)) [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) :
    letI : Module (W.presheaf.stalk w)
        Γ(exceptionalTwistPushforward
            ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap
              (W.fromSpecStalk w)),
          (⊤ : (Spec (W.presheaf.stalk w)).Opens)) :=
      Module.compHom _ (Scheme.ΓSpecIso (W.presheaf.stalk w)).inv.hom
    Nonempty (Γ(exceptionalTwistPushforward
        ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap
          (W.fromSpecStalk w)),
        (⊤ : (Spec (W.presheaf.stalk w)).Opens)) ≃ₗ[W.presheaf.stalk w] W.presheaf.stalk w) := by
  rw [Stacks.Blowup.vanishingIdeal_comap_fromSpecStalk_eq_specIdealSheaf w hw]
  exact ⟨exceptionalSectionsEquivOfRegular _ hstalkdim⟩

/-- The exceptional twist pushforward along a quasi-compact quasi-separated blowing up is
quasi-coherent. -/
private theorem isQuasicoherent_exceptionalTwistPushforward (M : Scheme.IdealSheafData W)
    [QuasiCompact (AlgebraicGeometry.blowUpToBase M)]
    [QuasiSeparated (AlgebraicGeometry.blowUpToBase M)] :
    (exceptionalTwistPushforward M).IsQuasicoherent :=
  AlgebraicGeometry.pushforward_isQuasicoherent (AlgebraicGeometry.blowUpToBase M)
    (show (AlgebraicGeometry.blowUp M).Modules from
      Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal M))

/-! ### The stalk at the closed point -/

/-- For the blowing up `b : W' ⟶ W` of a scheme in a reduced closed point `w` whose local ring is
regular of dimension two, the stalk of `b_*𝒪_{W'}(E)` at `w` is free of rank one over
`𝒪_{W,w}`. -/
theorem nonempty_stalkLinearEquiv_exceptionalTwistPushforward (w : W)
    (hw : IsClosed ({w} : Set W)) [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2)
    [QuasiCompact (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))]
    [QuasiSeparated (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))] :
    letI := stalkModule (exceptionalTwistPushforward
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) w
    Nonempty ((exceptionalTwistPushforward
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).presheaf.stalk w
      ≃ₗ[W.presheaf.stalk w] W.presheaf.stalk w) := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) with hM
  let := stalkModule (exceptionalTwistPushforward M) w
  have hflat : Flat (W.fromSpecStalk w) := flat_fromSpecStalk W w
  have hEC : Stacks.Divisors.IsEffectiveCartierDivisor (AlgebraicGeometry.exceptionalIdeal M) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M
  have hEC' := hEC
  have : (exceptionalTwistPushforward M).IsQuasicoherent :=
    isQuasicoherent_exceptionalTwistPushforward M
  obtain ⟨h, hsq⟩ :=
    AlgebraicGeometry.exists_isPullback_blowUpToBase_comap (W.fromSpecStalk w) M
  have : Flat h := MorphismProperty.of_isPullback hsq hflat
  have : Stacks.Divisors.IsPullbackDefined h (AlgebraicGeometry.exceptionalIdeal M) :=
    Stacks.Divisors.isPullbackDefined_of_flat h _ hEC
  obtain ⟨κ⟩ : Nonempty ((Scheme.Modules.pullback h).obj
      (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal M)) ≅
    Stacks.Divisors.invertibleSheaf'
      (AlgebraicGeometry.exceptionalIdeal (M.comap (W.fromSpecStalk w)))) := by
    rw [← AlgebraicGeometry.comap_exceptionalIdeal_of_isPullback M (W.fromSpecStalk w) hsq]
    exact ⟨Stacks.Divisors.invertibleSheafPullbackIso h _⟩
  have := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    hsq.flip (show (AlgebraicGeometry.blowUp M).Modules from
      Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal M))
  let ι : (Scheme.Modules.pullback (W.fromSpecStalk w)).obj (exceptionalTwistPushforward M) ≅
      exceptionalTwistPushforward (M.comap (W.fromSpecStalk w)) :=
    asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.flip.w).app
        (show (AlgebraicGeometry.blowUp M).Modules from
          Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal M))) ≪≫
      (Scheme.Modules.pushforward
        (AlgebraicGeometry.blowUpToBase (M.comap (W.fromSpecStalk w)))).mapIso κ
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  obtain ⟨e₁, -⟩ := AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv
    (exceptionalTwistPushforward M) w hU hwU
  obtain ⟨e₂⟩ := nonempty_sectionsLinearEquiv_exceptionalTwistPushforward_comap w hw hstalkdim
  exact ⟨e₁.symm.trans ((specSectionsLinearEquivOfIso ι).trans e₂)⟩

/-! ### The globalization -/

/-- For the blowing up `b : W' ⟶ W` of a scheme in a reduced closed point whose local ring is
regular of dimension two, the comparison map `𝒪_W ⟶ b_*𝒪_{W'}(E)` is invertible. -/
theorem isIso_exceptionalTwistComparison_pointIdeal (w : W) (hw : IsClosed ({w} : Set W))
    [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2)
    [QuasiCompact (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))]
    [QuasiSeparated (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))] :
    IsIso (exceptionalTwistComparison
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) with hM
  have : Stacks.Divisors.IsEffectiveCartierDivisor (AlgebraicGeometry.exceptionalIdeal M) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M
  have : (Stacks.Ample.unitModule W).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W
  have : (exceptionalTwistPushforward M).IsQuasicoherent :=
    isQuasicoherent_exceptionalTwistPushforward M
  have hdisj : Disjoint (((M.support.compl : W.Opens) : Set W)) ((M.support : Set W)) := by
    rw [show (((M.support.compl : W.Opens)) : Set W) = ((M.support : Set W))ᶜ from rfl]
    exact disjoint_compl_left
  have hVw : ∀ y : W, y ≠ w → y ∈ (M.support.compl : W.Opens) := by
    intro y hy
    have hmem : y ∉ ((M.support : Set W)) := by
      rw [hM, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hy
    exact hmem
  have hdim : 2 ≤ ringKrullDim (W.presheaf.stalk w) := by rw [hstalkdim]
  obtain ⟨e⟩ := nonempty_stalkLinearEquiv_exceptionalTwistPushforward w hw hstalkdim
  exact isIso_of_isIso_restrict_of_stalk_free (exceptionalTwistComparison M) w
    (M.support.compl : W.Opens)
    (isIso_restrictFunctor_exceptionalTwistComparison M (M.support.compl : W.Opens) hdisj)
    hVw hdim (Stacks.Ample.unitStalkEquiv W w) e

end Stacks.BlowupTwistUnit

end
