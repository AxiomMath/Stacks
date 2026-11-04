module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LipmanLocalStepTransport
public import StacksFrontier.AlgebraicGeometry.Duality.BlowUpNormalizedDualizingExists
public import StacksFrontier.RingTheory.Dualizing.CanonicalIdealExtension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingTrace
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowup
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUp
public import StacksFrontier.AlgebraicGeometry.Duality.CanonicalIdealStalk
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionDualizing

/-!
# The local step of [Stacks, Tag 0BBV]: a canonical ideal extends along one blowup

Let `B` be a two-dimensional Noetherian local normal Nagata domain defining a rational
singularity and `J ⊆ B` an ideal which is a dualizing module of `B`. Let `Y ⟶ Spec B` be the
normalized blowup of the closed point. Then at every point `y ∈ Y` the extended ideal
`J·𝒪_{Y,y}` is a dualizing module of `𝒪_{Y,y}`.

The normalized blowup is the blowup (normal by [Stacks, Tag 0B4Z]). If `B` is regular so are the
local rings of the blowup ([Stacks, Tag 0AGR]) and `J ≅ B` is principal. Otherwise let `ω_X` be
the dualizing module of the blowup normalized relative to `ω_A = J`
(`AlgebraicGeometry.BlowUpDualizing.exists_dualizingNormalization_blowUp_of`); the canonical map
`f^*J~ ⟶ ω_X` of [Stacks, Tag 0BBU] is surjective by clause (3) of [Stacks, Tag 0B64], so
`𝒪_{X,x} ⊗_B J ⟶ ω_{X,x}` is a surjection onto a torsion-free module of rank one, and
`J·𝒪_{X,x} ≅ ω_{X,x}`.

`AlgebraicGeometry.isDualizingRingModule_map_stalk_normalizedBlowUp_of` takes three inputs as
hypotheses: that `i^×` preserves dualizing complexes along a closed immersion (`hcl`), clause (3)
of [Stacks, Tag 0B64] (`hepi`), and the stalk argument (`hinj`, `hstalk`).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open BlowUpDualizing

/-- **The local step of [Stacks, Tag 0BBV]**, over the inputs `hcl`, `hepi`, `hinj`, `hstalk`. -/
theorem isDualizingRingModule_map_stalk_normalizedBlowUp_of
    (hcl : ∀ {Z W : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Z] (i : Z ⟶ W)
      [IsClosedImmersion i]
      (a : Stacks.Duality.quasiCoherentDerivedCategory W ⥤
        Stacks.Duality.quasiCoherentDerivedCategory Z)
      (_ : Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⊣ a)
      (K : Stacks.Duality.quasiCoherentDerivedCategory W),
      Stacks.Duality.IsDualizingComplex K.obj → Stacks.Duality.IsDualizingComplex (a.obj K).obj)
    (hepi : ∀ (S : RationalSingularitySituation.{u}) (_ : ¬ IsRegularLocalRing S.A)
      (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
      (ωX : (blowUpScheme S.A).Modules)
      (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
          isLocallyNoetherian_blowUpScheme S.A
        (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX),
      letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      Epi ((rationalSingularitySituationBlowUp S).normalizedPullbackMap hωA N.normalizedIso))
    (hinj : ∀ {B : Type u} [CommRing B] [IsDomain B] {X : Scheme.{u}} [IsIntegral X]
      (f : X ⟶ Spec (.of B)) [IsDominant f] (x : X), Function.Injective (baseToStalk f x))
    (hstalk : ∀ {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B] {X : Scheme.{u}}
      [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Spec (.of B)) [IsDominant f]
      (J : Ideal B) (_ : J ≠ ⊥) (ω : X.Modules) (_ : Stacks.Duality.IsDualizingModule ω)
      (π : (Scheme.Modules.pullback f).obj ((tilde.functor (.of B)).obj (ModuleCat.of B J)) ⟶ ω)
      (_ : Epi π) (x : X), ∃ _ : IsNoetherianRing (X.presheaf.stalk x),
        Stacks.Duality.IsDualizingRingModule (X.presheaf.stalk x) (J.map (baseToStalk f x))) :
    ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNormalDomain B] (hN : IsNagataRing B),
      ringKrullDim B = 2 → DefinesRationalSingularity B →
      ∀ (J : Ideal B), (letI := hN.1; Stacks.Duality.IsDualizingRingModule B J) →
      ∀ (hW : ∀ U : (Spec (.of B)).Opens, IsCompact (U : Set (Spec (.of B))) →
          (irreducibleComponents U).Finite)
        (hc : IsClosed ({IsLocalRing.closedPoint B} : Set (Spec (.of B))))
        (x : Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW (IsLocalRing.closedPoint B) hc),
        ∃ _ : IsNoetherianRing ((Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
            (IsLocalRing.closedPoint B) hc).presheaf.stalk x),
          Stacks.Duality.IsDualizingRingModule ((Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B))
              hW (IsLocalRing.closedPoint B) hc).presheaf.stalk x)
            (J.map ((Scheme.ΓSpecIso (.of B)).inv ≫
            (Stacks.Blowup.normalizedBlowUp (Spec (.of B)) hW (IsLocalRing.closedPoint B)
              hc).appTop ≫
            (Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
              (IsLocalRing.closedPoint B) hc).presheaf.germ ⊤ x trivial).hom) := by
  intro B _ _ _ hN hdim hrat J hJ hW hc x
  let : IsNoetherianRing B := hN.1
  have : IsNormal (Spec (.of B)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed B)
  let S := rationalSingularitySituationOfModification B hN hdim hrat (𝟙 (Spec (.of B)))
    (isModification_id _)
  let S' := rationalSingularitySituationBlowUp S
  have : IsLocallyNoetherian (blowUp (Stacks.Blowup.residuePoint B).ker) :=
    isLocallyNoetherian_blowUpScheme B
  have : IsNormal (blowUp (Stacks.Blowup.residuePoint B).ker) := S'.normalSource
  have : IsIntegral (blowUp (Stacks.Blowup.residuePoint B).ker) :=
    S'.modification.source_isIntegral
  have : IsDominant (blowUpToBase (Stacks.Blowup.residuePoint B).ker) :=
    S'.modification.isBirational.isDominant
  -- the local step on the blowup itself
  have hX0 : ∀ y : blowUp (Stacks.Blowup.residuePoint B).ker,
      ∃ _ : IsNoetherianRing ((blowUp (Stacks.Blowup.residuePoint B).ker).presheaf.stalk y),
        Stacks.Duality.IsDualizingRingModule
          ((blowUp (Stacks.Blowup.residuePoint B).ker).presheaf.stalk y)
          (J.map (baseToStalk (blowUpToBase (Stacks.Blowup.residuePoint B).ker) y)) := by
    intro y
    by_cases hreg : IsRegularLocalRing B
    · have hXreg : IsRegular (blowUp (Stacks.Blowup.residuePoint B).ker) := by
        rw [ker_residuePoint_eq_ofIdealTop_map]
        exact isRegular_blowUp_maximalIdeal B hdim
      have := hXreg.isRegularLocalRing_stalk y
      let := (baseToStalk (blowUpToBase (Stacks.Blowup.residuePoint B).ker) y).toAlgebra
      exact ⟨inferInstance, Stacks.Duality.isDualizingRingModule_map_of_isRegularLocalRing
        (hinj _ y) J hJ⟩
    · obtain ⟨ωX, ⟨N⟩⟩ := exists_dualizingNormalization_blowUp_of S (ModuleCat.of B J) hJ hcl
      have hJne : J ≠ ⊥ := by
        intro h
        subst h
        have := Stacks.Duality.IsDualizingRingModule.nontrivial
          (M := ModuleCat.of B (⊥ : Ideal B)) hJ
        obtain ⟨a, b, hab⟩ := exists_pair_ne (⊥ : Ideal B)
        exact hab (Subtype.ext ((Ideal.mem_bot.1 a.2).trans (Ideal.mem_bot.1 b.2).symm))
      exact hstalk (blowUpToBase (Stacks.Blowup.residuePoint B).ker) J hJne ωX N.isDualizing
        (S'.normalizedPullbackMap hJ N.normalizedIso) (hepi S hreg (ModuleCat.of B J) hJ ωX N) y
  -- transport along the normalization, an isomorphism
  have key : ∀ (I : (Spec (.of B)).IdealSheafData) (_ : I = (Stacks.Blowup.residuePoint B).ker)
      (hfin : ∀ U : (blowUp I).Opens, IsCompact (U : Set (blowUp I)) →
        (irreducibleComponents U).Finite)
      (x : Scheme.normalizationScheme (blowUp I) hfin),
      ∃ _ : IsNoetherianRing ((Scheme.normalizationScheme (blowUp I) hfin).presheaf.stalk x),
        Stacks.Duality.IsDualizingRingModule
          ((Scheme.normalizationScheme (blowUp I) hfin).presheaf.stalk x)
          (J.map (baseToStalk (Scheme.normalization (blowUp I) hfin ≫ blowUpToBase I) x)) := by
    intro I hI hfin x
    subst hI
    have := Scheme.isIso_normalization_of_isNormal (blowUp (Stacks.Blowup.residuePoint B).ker)
      hfin
    exact isDualizingRingModule_map_germ_of_iso _ _ J x (hX0 _)
  exact key _ (vanishingIdeal_closedPoint_eq_ker_residuePoint B hc) _ x

/-- **The local step of [Stacks, Tag 0BBV]**, over clause (3) of [Stacks, Tag 0B64] (`hepi`). -/
theorem isDualizingRingModule_map_stalk_normalizedBlowUp_of_epi
    (hepi : ∀ (S : RationalSingularitySituation.{u}) (_ : ¬ IsRegularLocalRing S.A)
      (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
      (ωX : (blowUpScheme S.A).Modules)
      (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
          isLocallyNoetherian_blowUpScheme S.A
        (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX),
      letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      Epi ((rationalSingularitySituationBlowUp S).normalizedPullbackMap hωA N.normalizedIso)) :
    ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNormalDomain B] (hN : IsNagataRing B),
      ringKrullDim B = 2 → DefinesRationalSingularity B →
      ∀ (J : Ideal B), (letI := hN.1; Stacks.Duality.IsDualizingRingModule B J) →
      ∀ (hW : ∀ U : (Spec (.of B)).Opens, IsCompact (U : Set (Spec (.of B))) →
          (irreducibleComponents U).Finite)
        (hc : IsClosed ({IsLocalRing.closedPoint B} : Set (Spec (.of B))))
        (x : Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW (IsLocalRing.closedPoint B) hc),
        ∃ _ : IsNoetherianRing ((Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
            (IsLocalRing.closedPoint B) hc).presheaf.stalk x),
          Stacks.Duality.IsDualizingRingModule ((Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B))
              hW (IsLocalRing.closedPoint B) hc).presheaf.stalk x)
            (J.map ((Scheme.ΓSpecIso (.of B)).inv ≫
            (Stacks.Blowup.normalizedBlowUp (Spec (.of B)) hW (IsLocalRing.closedPoint B)
              hc).appTop ≫
            (Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
              (IsLocalRing.closedPoint B) hc).presheaf.germ ⊤ x trivial).hom) :=
  isDualizingRingModule_map_stalk_normalizedBlowUp_of
    (fun i _ a adj K hK =>
      Stacks.Duality.LocallySmall.isDualizingComplex_of_closedImmersion i a adj K hK)
    hepi (fun f _ x => injective_germ_comp_appTop f x)
    (fun f _ J hJ ω hω π hπ x => by
      have := hπ
      exact isDualizingRingModule_stalk_of_epi f J hJ ω hω π x)

end AlgebraicGeometry
