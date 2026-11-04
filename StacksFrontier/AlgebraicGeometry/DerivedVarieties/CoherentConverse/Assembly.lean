module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.ChowGraphDatum
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.ProjectiveSpacePerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.BoundedCoherentLocal
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.ClosedImmersionBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.QuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper

/-!
# The implication (2) ⇒ (1) of [Stacks, Tag 0FYD], from the Fourier–Mukai step

Let `X` be proper over a field `k` and `K ∈ D_QCoh(𝒪_X)`. This file proves that `K` lies in
`D^b_Coh(𝒪_X)` as soon as, for every `m` and every perfect `E'` on `T = X ×_k ℙᵐ_k`, the
Fourier–Mukai transform `M = Rq_*(Lp^*K ⊗^𝐋 E')` on `ℙᵐ_k` has finite total `Hom` from each
member of the exceptional sequence `𝒪(-m), …, 𝒪` — the hypothesis `hC`, which is what
condition (2) of [Stacks, Tag 0FYD] gives by adjunction.

The proof is the source's. By locality (`derivedCategoryBBounded_of_forall_restrict`) it suffices
to work near a point `x`. [Stacks, Tag 0CSJ] (`exists_chowGraphDatum`) gives `U ∋ x`, `m`, an open
`V ⊆ ℙᵐ_k` and a closed immersion `U ⟶ V`. [Stacks, Tag 09IQ] with [Stacks, Tag 068D] and
[Stacks, Tag 0G2E] (`exists_isPerfect_retract_chowDatum`) give a perfect `E'` on `T` whose
restriction to `q⁻¹V` contains `Ri_*𝒪_W`. The Fourier–Mukai transform `M` of `K` with kernel
`E'` lies in `D^b_Coh(ℙᵐ_k)` by `ProjectiveSpacePerfect`, hence so does `M|_V`, and
`R(U ⟶ V)_*(K|_U)` is a retract of `M|_V` (`nonempty_retract_chowDatum`, [Stacks, Tag 0CSK]).
Direct image along a closed immersion reflects `D^b_Coh`, so `K|_U ∈ D^b_Coh`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.CoherentConverse

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra

open DerivedChow Stacks.AlgebraicGeometry.ProjPolyChart
  Stacks.AlgebraicGeometry.ProjectiveSpacePerfect

variable {k : Type u} [Field k]

attribute [local instance] AlgebraicGeometry.modulesLinear

/-- The polynomial model of projective space is proper and smooth over `k`, by its comparison with
the library's model. -/
theorem isProper_projToSpecCoeff (m : ℕ) : IsProper (projToSpecCoeff k m) := by
  rw [← projModelIso_hom_comp_over]; infer_instance

/-- The polynomial model of projective space is smooth over `k`. -/
theorem smooth_projToSpecCoeff (m : ℕ) : Smooth (projToSpecCoeff k m) := by
  rw [← projModelIso_hom_comp_over]; infer_instance

/-- **[Stacks, Tag 0FYD], (2) ⇒ (1), granted the Fourier–Mukai step `hC`.** -/
theorem derivedCategoryBBounded_of_fourierMukai (X : Over (Spec (CommRingCat.of k)))
    [IsProper X.hom] (K : DerivedCategory X.left.Modules)
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) K)
    (hC : ∀ (m : ℕ) (E' : DerivedCategory (pullback X.hom (projToSpecCoeff k m)).Modules),
      Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := (pullback X.hom (projToSpecCoeff k m)).toRingedSpace) E' →
      ∀ a : Fin (m + 1), Pretriangulated.HasFiniteTotalHom k (seqE k m a)
        ((fourierMukai X.hom (projToSpecCoeff k m) E').obj K)) :
    DerivedCategoryB.derivedCategoryBBounded (fun M : X.left.Modules => M.IsCoherent) K := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType_over_field X.hom
  refine Stacks.AlgebraicGeometry.BoundedCoherentLocal.derivedCategoryBBounded_of_forall_restrict
    K fun x => ?_
  obtain ⟨U, m, V, Z, iZ, hxU, hiZ, hb, hV, hW⟩ := exists_chowGraphDatum X.hom x
  refine ⟨U, hxU, ?_⟩
  have := isProper_projToSpecCoeff (k := k) m
  have := smooth_projToSpecCoeff (k := k) m
  let p := pullback.fst X.hom (projToSpecCoeff k m)
  let q := pullback.snd X.hom (projToSpecCoeff k m)
  have : IsNoetherian (pullback X.hom (projToSpecCoeff k m)) :=
    isNoetherian_of_locallyOfFiniteType_over_field (p ≫ X.hom)
  have : IsLocallyNoetherian (Proj (polyGrading k m)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff k m)
  obtain ⟨E', hE', ⟨ρ⟩⟩ := exists_isPerfect_retract_chowDatum p q iZ U V hb hW
    (NoetherianSpace.isCompact _)
  have hKq : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.left.toRingedSpace) K :=
    hK
  obtain ⟨σ⟩ := nonempty_retract_chowDatum p q iZ U V hb hW K E' ρ hKq
  let M := (fourierMukai X.hom (projToSpecCoeff k m) E').obj K
  have hMq : DerivedCategoryB.derivedCategoryB (A := PMods k m)
      (SheafOfModules.isQuasicoherent
        (Stacks.AlgebraicGeometry.TwistEndomorphisms.projOver k m).left.ringCatSheaf) M :=
    isQuasicoherent_homology_fourierMukai X.hom (projToSpecCoeff k m) E'
      (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ E' hE') K hK
  have hMb : DerivedCategoryB.derivedCategoryBBounded (fun F : PMods k m => F.IsCoherent) M :=
    derivedCategoryBBounded_of_hasFiniteTotalHom k m M hMq (hC m E' hE')
  have := isClosedImmersion_chowDatumMorphism p q iZ U V hb hV hW
  have hRet := fun S : Scheme.{u} =>
    DerivedCategoryB.derivedCategoryBBounded_isStableUnderRetracts
      (fun F : S.Modules => F.IsCoherent)
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre S)
  have hc := (hRet _).of_retract (σ.trans (Retract.ofIso
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback V.ι).app M).symm))
    (Stacks.AlgebraicGeometry.BoundedCoherentLocal.derivedCategoryBBounded_restrict V M hMb)
  open Stacks.AlgebraicGeometry.ClosedImmersionBoundedCoherent in
  have hKU := derivedCategoryBBounded_of_derivedPushforward
    (chowDatumMorphism p q iZ U V hb hW) ((derivedPullback (ofScheme U.ι)).obj K)
    (Stacks.Cohomology.ProjectionFormulaQCohLocalization.isDQCoh_derivedPullback _ _ hKq) hc
  exact (hRet _).of_retract (Retract.ofIso
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback U.ι).app K)) hKU

end AlgebraicGeometry.CoherentConverse

end
