module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitAuxAdic
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitAlgebraClosure
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat

/-!
# Adicness of the ring map of an adic formal component

Let `V` be an affine Noetherian object of the site, `I ⊆ A = Γ(V, 𝒪)` an ideal with
`V(I) = Z`, and `x₀ : V_{/Z} ⟶ W₀ ≅ Spf B` a morphism to a Noetherian adic affine formal
algebraic space with an étale chart `ω : W₀ ⟶ W`. If `x₀ ≫ ω` is adic, then so is the continuous
ring map `φ : B → A^∧` of `x₀`: some ideal of definition `J` of `B` has `I^N A^∧ ⊆ J A^∧`
(Stacks 0AN5 and 0GBS). In the proof of Stacks 0GI5 this is the adicness of the formal component
`x̂` over the limit, from which the adicness of `x̂_k` at a stage is deduced.

## Main results

* `AlgebraicGeometry.Artin.FormalDictionary.exists_pow_le_map_of_isAdicMorphism`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.FormalDictionary

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {Z : Set (Space.points B S hS (yoneda.obj V))}
  (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : FormalSpace.QuotientSystem B S hS Bt}

include hZI in
/-- **The ring map of an adic morphism `V_{/Z} ⟶ Spf B` is adic**, with an explicit power: an
ideal of definition `J` of `B` has `(I A^∧)^N ⊆ J A^∧`. -/
theorem exists_pow_le_map_of_isAdicMorphism [IsNoetherianRing Bt]
    (hBadic : TopologicalRing.IsAdic Bt)
    {W₀ W : FormalSpace.FppfSheaf B S hS} (e : W₀ ≅ FormalSpace.formalSpectrum DB)
    (hW₀ : IsAffineFormalAlgebraicSpace B S hS W₀) (ω : W₀ ⟶ W)
    (x₀ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W₀)
    (hadic : FormalSpace.IsAdicMorphism B S hS (x₀ ≫ ω)) :
    ∃ (J : Ideal Bt) (N : ℕ), _root_.IsAdic J ∧
      (I.map (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) ^ N ≤
        J.map ((continuousHomEquiv hZI hB).symm (x₀ ≫ e.hom)).toRingHom := by
  obtain ⟨hTR, hLT, hIadic, hAadic, hAw⟩ :=
    FormalSpace.adicCompletion_isAdic_of_fg I I.fg_of_isNoetherianRing
  set φ := (continuousHomEquiv hZI hB).symm (x₀ ≫ e.hom)
  -- `x₀` is adic: cancel the étale chart `ω`
  have hx₀ : FormalSpace.IsAdicMorphism B S hS x₀ :=
    FormalSpace.IsAdicMorphism.of_comp_eq B S hS
      (FormalSpace.isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hW₀)
      (FormalSpace.isRepresentableEtale_of_isIso B S hS (𝟙 _)) hadic (Category.id_comp _)
  -- hence so is `Spf φ`
  have hφe : continuousHomEquiv hZI hB φ = x₀ ≫ e.hom := Equiv.apply_symm_apply _ _
  have hspf : FormalSpace.formalSpectrumMap hB φ =
      (completionIsoFormalSpectrum hZI).inv ≫ x₀ ≫ e.hom := by
    rw [← hφe, continuousHomEquiv_apply, Iso.inv_hom_id_assoc]
  have hrep : FormalSpace.IsAdicMorphism B S hS (FormalSpace.formalSpectrumMap hB φ) := by
    rw [hspf]
    exact FormalSpace.IsAdicMorphism.comp B S hS _ _
      (FormalSpace.isAdicMorphism_of_isIso B S hS _)
      (FormalSpace.IsAdicMorphism.comp B S hS _ _ hx₀
        (FormalSpace.isAdicMorphism_of_isIso B S hS _))
  -- the two formal spectra are affine formal algebraic spaces
  have hDaff : IsAffineFormalAlgebraicSpace B S hS (FormalSpace.formalSpectrum DB) :=
    FormalSpace.isAffineFormalAlgebraicSpace_of_iso B S hS e hW₀
  have hEaff : IsAffineFormalAlgebraicSpace B S hS
      (FormalSpace.formalSpectrum (completionQuotientSystem V I)) :=
    FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum hAw _
      (FormalSpace.hasLargeSite_of_mk_lt_cutoff (completionQuotientSystem V I)
        (FormalSpace.mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hAadic
          (completionQuotientSystem V I)))
  have htaut : RingHom.IsTaut φ.toRingHom :=
    FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine
      B S hS hB hAw DB _ hDaff hEaff φ hrep
  -- taut is adic (Stacks 0GBS)
  obtain ⟨J₀, hJ₀def, hJ₀adic, -⟩ := FormalSpace.exists_idealOfDefinition_isAdicComplete hBadic
  let : UniformSpace (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :=
    IsTopologicalAddGroup.rightUniformSpace _
  obtain ⟨-, hT2, hcompl⟩ := hAadic
  have : T2Space (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) := hT2
  have : CompleteSpace (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) := hcompl
  obtain ⟨J, hJ, hJmap⟩ := RingHom.isAdic_of_isTaut φ.toRingHom htaut
    ⟨J₀, (IsNoetherian.noetherian J₀), hJ₀adic⟩
  -- `J A^∧` is open, so it contains a power of `I A^∧`
  have hopen : IsOpen ((J.map φ.toRingHom : Ideal _) : Set (AdicCompletion I
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) := by
    simpa using (isAdic_iff.mp hJmap).1 1
  obtain ⟨N, hN⟩ := (isAdic_iff.mp hIadic).2 _ (hopen.mem_nhds (J.map φ.toRingHom).zero_mem)
  exact ⟨J, N, hJ, fun x hx => hN hx⟩

end AlgebraicGeometry.Artin.FormalDictionary

end
