module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumHomEquiv
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperValuativeLifting
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeaklyAdmissibleCompleteLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartValuativeExtension
import all StacksFrontier.AlgebraicGeometry.Spaces.Valuative.PushDownSolution

/-!
# Proper finite-type modifications and formal modifications (Stacks 0ARX)

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be a closed subset and `U ⊆ X` its open complement. Stacks 0ARX
says that a finite-type modification `f : X' ⟶ X` of `X` outside `U`, corresponding under the
completion functor of Stacks 0AR5 (Theorem 0ARB) to a rig-étale `g : W ⟶ X_{/T}` with `W` a
locally Noetherian formal algebraic space, is proper exactly when `g` is a formal modification
(Definition 0GDK).

## Main results

* `AlgebraicGeometry.FormalSpace.isProper_iff_isFormalModification_of_iso`: a finite-type
  modification `f` of `X` outside `U` is proper exactly when the corresponding `g` is a formal
  modification.
* `AlgebraicGeometry.FormalSpace.isProper_of_isProper_completionSheafMap`: `f` is proper when its
  completion `f_{/T}` is proper, rig-surjective and has rig-surjective relative diagonal.
* `AlgebraicGeometry.FormalSpace.exists_lift_of_isRigSurjective_completionSheafMap`: a point
  `Spec R ⟶ Y` of an algebraic space, `R` a complete discrete valuation ring, whose fibre over
  `T` is the closed point, lifts after an extension of `R` through any morphism whose completion
  along `T` is rig-surjective.
* `AlgebraicGeometry.FormalSpace.adicModuleTopology_adicCompletion_eq`: on the completion of a
  Noetherian local ring, the maximal-adic module topology is the adic topology of its maximal
  ideal.

## References

* [Stacks Project, Tag 0ARX](https://stacks.math.columbia.edu/tag/0ARX)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
* [Stacks Project, Tag 0ARL](https://stacks.math.columbia.edu/tag/0ARL)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

/-- On the completion `A^∧` of a Noetherian local ring at its maximal ideal `𝔪`, the
`𝔪`-adic module topology is the adic topology of the maximal ideal `𝔪 A^∧` of `A^∧`. -/
theorem adicModuleTopology_adicCompletion_eq {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A).adicModuleTopology
        (AdicCompletion (IsLocalRing.maximalIdeal A) A) =
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)).adicTopology := by
  let I := IsLocalRing.maximalIdeal A
  let R₀ := AdicCompletion I A
  let : TopologicalSpace A := I.adicTopology
  let b : ModuleFilterBasis A R₀ :=
    I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis R₀)
  have hset : ∀ n : ℕ, ((I ^ n • (⊤ : Submodule A R₀) : Submodule A R₀) : Set R₀) =
      ((IsLocalRing.maximalIdeal R₀ ^ n : Ideal R₀) : Set R₀) := by
    intro n
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    ext x
    show x ∈ I ^ n • (⊤ : Submodule A R₀) ↔ x ∈ Ideal.map (algebraMap A R₀) (I ^ n)
    rw [Ideal.smul_top_eq_map]
    rfl
  refine IsTopologicalAddGroup.ext (b.toAddGroupFilterBasis.isTopologicalAddGroup)
    (@IsTopologicalRing.to_topologicalAddGroup _ _ (IsLocalRing.maximalIdeal R₀).adicTopology
      (Ideal.ringFilterBasis _).isTopologicalRing) ?_
  apply le_antisymm
  · rw [((IsLocalRing.maximalIdeal R₀).hasBasis_nhds_zero_adic).ge_iff]
    intro n _
    refine b.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mpr ⟨_, ⟨n, rfl⟩, ?_⟩
    exact (hset n).subset
  · rw [b.toAddGroupFilterBasis.nhds_zero_hasBasis.ge_iff]
    rintro V ⟨n, rfl⟩
    exact ((IsLocalRing.maximalIdeal R₀).hasBasis_nhds_zero_adic).mem_iff.mpr
      ⟨n, trivial, (hset n).superset⟩

section Comparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : Type u} [CommRing A]
  (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S) (I : Ideal A)

local instance : TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

/-- Transporting a completion along an equality of sets of points commutes with the
inclusion into the ambient algebraic space. -/
theorem eqToHom_comp_completionToUpliftedSheaf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {T₁ T₂ : Set (Space.points B S hS X)} (e : T₁ = T₂) :
    eqToHom (congrArg (Space.completionSheaf B S hS X) e) ≫ completionToUpliftedSheaf X hX T₂ =
      completionToUpliftedSheaf X hX T₁ := by
  subst e
  simp

/-- The comparison of Stacks 0GBA (2), followed by the inclusion of the completion into
`Spec A`, is the canonical morphism `Spf (A^∧) ⟶ Spec (A^∧) ⟶ Spec A`. -/
theorem completionComparison_comp_completionToUpliftedSheaf
    (D : AdicQuotientSystem B S hS I) (hD : QuotientSystemCompatible B S hS f I D)
    (hA' : B.Contains (Spec (.of (AdicCompletion I A))))
    (hq : ∀ J : { K : Ideal (AdicCompletion I A) //
        TopologicalRing.IsWeakIdealOfDefinition K },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫ f) = D.overS J) :
    completionComparison B S hS hA f I D hD ≫
        completionToUpliftedSheaf (yoneda.obj (affineOver B S hS hA f))
          (isAlgebraicSpace_yoneda B S hS _) (zeroLocusPoints B S hS hA f I) =
      formalSpectrumToSpec D hA' _ hq ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (Space.specSiteObjectMap (algebraMap A (AdicCompletion I A)) hA hA' f) ≫
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm (ULift.up (𝟙 _)) := by
  refine formalSpectrum_hom_ext D _ fun J ↦ ?_
  have hL := congrArg (· ≫ completionToUpliftedSheaf (yoneda.obj (affineOver B S hS hA f))
    (isAlgebraicSpace_yoneda B S hS _) (zeroLocusPoints B S hS hA f I))
    (completionComparison_stage B S hS hA f I D hD J)
  have hR := congrArg (· ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      (Space.specSiteObjectMap (algebraMap A (AdicCompletion I A)) hA hA' f) ≫
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          (F := upliftedSheaf (yoneda.obj (affineOver B S hS hA f))
            (isAlgebraicSpace_yoneda B S hS _))).symm (ULift.up (𝟙 _)))
    (formalSpectrumToSpec_spec D hA' _ hq J)
  simp only at hL hR
  refine ((Category.assoc _ _ _).symm.trans hL).trans
    (Eq.trans ?_ ((Category.assoc _ _ _).trans hR).symm)
  rw [quotientStageToCompletion]
  refine (Sheaf.sectionEquiv_symm_comp (BigFppfOver.topology B S hS) _ _).symm.trans ?_
  refine Eq.trans ?_ (congrArg (_ ≫ ·)
    (Sheaf.sectionEquiv_symm_map (BigFppfOver.topology B S hS) _ _))
  refine Eq.trans ?_ (Sheaf.sectionEquiv_symm_map (BigFppfOver.topology B S hS) _ _)
  refine congrArg _ ?_
  have key := congrArg (fun φ ↦ φ.app
      (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
      ⟨⟨quotientStageToAffine B S hS hA f I D hD J⟩,
        quotientStage_hasImageIn B S hS hA f I D hD J⟩)
    (Space.toSheafify_comp_completionSheafToAmbient B S hS (yoneda.obj (affineOver B S hS hA f))
      (upliftedSheaf (yoneda.obj (affineOver B S hS hA f))
        (isAlgebraicSpace_yoneda B S hS _)).property (zeroLocusPoints B S hS hA f I))
  refine key.trans ?_
  show ULift.up (quotientStageToAffine B S hS hA f I D hD J) =
    ULift.up ((BigAffineFppf.inclusion B S hS).map (stageToSpec D hA' _ J (hq J)) ≫
      Space.specSiteObjectMap (algebraMap A (AdicCompletion I A)) hA hA' f ≫ 𝟙 _)
  congr 1
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫ 𝟙 _
  rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end Comparison

section Lift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- The inclusion of the completion into an algebraic space is natural. -/
theorem completionSheafMap_comp_completionToUpliftedSheaf
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (h : Y ⟶ Z) (T : Set (Space.points B S hS Z)) :
    Space.completionSheafMap B S hS h T ≫ completionToUpliftedSheaf Z hZ T =
      completionToUpliftedSheaf Y hY (Space.pointsMap B S hS Y h ⁻¹' T) ≫
        (ObjectProperty.homMk (Functor.whiskerRight h uliftFunctor.{u + 1}) :
          upliftedSheaf Y hY ⟶ upliftedSheaf Z hZ) := by
  have : Mono (ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS Z hZ.isSheaf).hom :
      upliftedSheaf Z hZ ⟶ Space.sheafifiedULift B S hS Z) :=
    Sheaf.Hom.mono_of_presheaf_mono _ _ (h := (inferInstance :
      Mono (Space.sheafifiedULiftIso B S hS Z hZ.isSheaf).hom))
  rw [← cancel_mono (ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS Z hZ.isSheaf).hom :
    upliftedSheaf Z hZ ⟶ Space.sheafifiedULift B S hS Z)]
  rw [Category.assoc, ← completionSheafInclusion_eq_comp hZ,
    ← (Space.isPullback_completionSheafMap B S hS h T).w, completionSheafInclusion_eq_comp hY,
    Category.assoc, Category.assoc]
  congr 1
  apply ObjectProperty.hom_ext
  exact (Space.whiskerRight_comp_sheafifiedULiftIso_hom B S hS hY.isSheaf hZ.isSheaf h).symm

/-- For a continuous ring map out of a ring with an adic topology, every weak ideal of definition
of the target pulls back to a weak ideal of definition of the source containing it. -/
private theorem exists_weakIdealOfDefinition_le_comap {R R' : Type u} [CommRing R] [CommRing R']
    [TopologicalSpace R] [TopologicalSpace R'] {I : Ideal R} (hadic : _root_.IsAdic I)
    {φ : R →+* R'} (hφ : Continuous φ)
    (K : { K : Ideal R' // TopologicalRing.IsWeakIdealOfDefinition K }) :
    ∃ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K },
      J.1 ≤ Ideal.comap φ K.1 := by
  obtain ⟨n, hn⟩ := exists_pow_le_of_isOpen hadic (J := Ideal.comap φ K.1) (K.2.1.preimage hφ)
  exact ⟨⟨I ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hadic (Nat.succ_ne_zero n)⟩,
    (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩

/-- The stagewise comparison of two maps `Spf R' ⟶ Spec A`. -/
theorem formalSpectrumMap_comp_formalSpectrumToSpec_comp
    {A R₀ R' : Type u} [CommRing A] [CommRing R₀] [CommRing R'] [TopologicalSpace R₀]
    [IsTopologicalRing R₀] [IsLinearTopology R₀ R₀] [TopologicalSpace R']
    {I₀ : Ideal R₀} (hadic : _root_.IsAdic I₀) (hw : TopologicalRing.IsWeaklyAdmissible R₀)
    (hA : B.Contains (Spec (.of A))) (a : Spec (.of A) ⟶ S) (φ : A →+* R₀)
    (hR₀S : B.Contains (Spec (.of R₀))) (hR'S : B.Contains (Spec (.of R')))
    {D₀ : QuotientSystem B S hS R₀} {D' : QuotientSystem B S hS R'} (e : ContinuousHom D₀ D')
    (hD₀ : ∀ J : { K : Ideal R₀ // TopologicalRing.IsWeakIdealOfDefinition K },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
        (Spec.map (CommRingCat.ofHom φ) ≫ a) = D₀.overS J)
    (hD' : ∀ K : { K : Ideal R' // TopologicalRing.IsWeakIdealOfDefinition K },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫
        (Spec.map (CommRingCat.ofHom (e.toRingHom.comp φ)) ≫ a) = D'.overS K) :
    formalSpectrumMap hw e ≫ formalSpectrumToSpec D₀ hR₀S _ hD₀ ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (Space.specSiteObjectMap φ hA hR₀S a) =
      formalSpectrumToSpec D' hR'S _ hD' ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (Space.specSiteObjectMap (e.toRingHom.comp φ) hA hR'S a) := by
  refine formalSpectrum_hom_ext D' _ fun K ↦ ?_
  obtain ⟨J, hJ⟩ := exists_weakIdealOfDefinition_le_comap hadic e.continuous K
  have h1 := formalSpectrumMap_spec hw e J K hJ
  have h2 := formalSpectrumToSpec_spec D₀ hR₀S _ hD₀ J
  have h3 := formalSpectrumToSpec_spec D' hR'S _ hD' K
  have hsite : (BigAffineFppf.inclusion B S hS).map (e.stageMap J K hJ) ≫
      (BigAffineFppf.inclusion B S hS).map (stageToSpec D₀ hR₀S _ J (hD₀ J)) ≫
      Space.specSiteObjectMap φ hA hR₀S a =
      (BigAffineFppf.inclusion B S hS).map (stageToSpec D' hR'S _ K (hD' K)) ≫
        Space.specSiteObjectMap (e.toRingHom.comp φ) hA hR'S a := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 e.toRingHom hJ)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
          Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫
        Spec.map (CommRingCat.ofHom (e.toRingHom.comp φ))
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have s1 : formalSpectrumInclusion D' (OrderDual.toDual K) ≫
        (formalSpectrumMap hw e ≫ formalSpectrumToSpec D₀ hR₀S _ hD₀) ≫
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
              (Space.specSiteObjectMap φ hA hR₀S a) =
      ((formalSpectrumInclusion D' (OrderDual.toDual K) ≫ formalSpectrumMap hw e) ≫
          formalSpectrumToSpec D₀ hR₀S _ hD₀) ≫
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
                (Space.specSiteObjectMap φ hA hR₀S a) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Category.assoc _ _ _).symm)
  have s2 := congrArg (fun t ↦ (t ≫ formalSpectrumToSpec D₀ hR₀S _ hD₀) ≫
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (Space.specSiteObjectMap φ hA hR₀S a)) h1
  have s3 : (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (e.stageMap J K hJ)) ≫
          formalSpectrumInclusion D₀ (OrderDual.toDual J)) ≫
          formalSpectrumToSpec D₀ hR₀S _ hD₀) ≫
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
                (Space.specSiteObjectMap φ hA hR₀S a) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (e.stageMap J K hJ)) ≫
          (formalSpectrumInclusion D₀ (OrderDual.toDual J) ≫ formalSpectrumToSpec D₀ hR₀S _ hD₀) ≫
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
                (Space.specSiteObjectMap φ hA hR₀S a) :=
    (congrArg (· ≫ _) (Category.assoc _ _ _)).trans (Category.assoc _ _ _)
  have s4 := congrArg (fun t ↦ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (e.stageMap J K hJ)) ≫ t ≫
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (Space.specSiteObjectMap φ hA hR₀S a)) h2
  have s5 : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (e.stageMap J K hJ)) ≫
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
              ((BigAffineFppf.inclusion B S hS).map (stageToSpec D₀ hR₀S _ J (hD₀ J))) ≫
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
                (Space.specSiteObjectMap φ hA hR₀S a) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (stageToSpec D' hR'S _ K (hD' K))) ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (Space.specSiteObjectMap
            (e.toRingHom.comp φ) hA hR'S a) := by
    exact (congrArg (_ ≫ ·)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _).symm).trans
      (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _).symm.trans
        ((congrArg (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map hsite).trans
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _)))
  have s6 : formalSpectrumInclusion D' (OrderDual.toDual K) ≫ formalSpectrumToSpec D' hR'S _ hD' ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (Space.specSiteObjectMap
            (e.toRingHom.comp φ) hA hR'S a) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (stageToSpec D' hR'S _ K (hD' K))) ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (Space.specSiteObjectMap
            (e.toRingHom.comp φ) hA hR'S a) := by
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h3)
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6.symm))))

/-- Let `φ : Z ⟶ Y` be a morphism of algebraic spaces whose completion `Z_{/T'} ⟶ Y_{/T}` along
a set `T` of points of `Y` is rig-surjective, let `R` be a complete discrete valuation ring and
let `h : Spec R ⟶ Y` be a morphism whose fibre over `T` is the closed point. Then, after an
extension `R ⊂ R'` of complete discrete valuation rings, `h` lifts to `Z`. -/
theorem exists_lift_of_isRigSurjective_completionSheafMap
    {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hY : IsAlgebraicSpace B S hS Y) (φ : Z ⟶ Y) (T : Set (Space.points B S hS Y))
    (hrs : IsRigSurjective B S hS (Space.completionSheafMap B S hS φ T))
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (_hc : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (hRS : B.Contains (Spec (.of R))) (a : Spec (.of R) ⟶ S)
    (h : yoneda.obj (siteObject B S hS hRS a) ⟶ Y)
    (hpre : ∀ x, Space.pointsMap B S hS _ h x ∈ T ↔
      Space.pointsToScheme B S hS (siteObject B S hS hRS a) x = IsLocalRing.closedPoint R) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (ψ : R →+* R'), IsLocalHom ψ ∧ Function.Injective ψ ∧
        IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧
      ∃ (hR'S : B.Contains (Spec (.of R')))
        (y : yoneda.obj (siteObject B S hS hR'S (Spec.map (CommRingCat.ofHom ψ) ≫ a)) ⟶ Z),
        y ≫ φ = yoneda.map (Space.specSiteObjectMap ψ hRS hR'S a) ≫ h := by
  classical
  let I := IsLocalRing.maximalIdeal R
  have hIfg : I.FG := IsNoetherian.noetherian I
  let R₁ := AdicCompletion I R
  let τ₁ : TopologicalSpace R₁ := I.adicModuleTopology R₁
  obtain ⟨hdom₁, hdvr₁⟩ := (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := R)).mp
    ⟨inferInstance, inferInstance⟩
  have hadic₁ : _root_.IsAdic (IsLocalRing.maximalIdeal R₁) :=
    adicModuleTopology_adicCompletion_eq
  have htop₁ : IsTopologicalRing R₁ :=
    hadic₁ ▸ (Ideal.nonarchimedean (IsLocalRing.maximalIdeal R₁)).toIsTopologicalRing
  let hlin₁ : IsLinearTopology R₁ R₁ := _root_.IsAdic.isLinearTopology hadic₁
  have hc₁ : IsAdicComplete (IsLocalRing.maximalIdeal R₁) R₁ := inferInstance
  have hw₁ : TopologicalRing.IsWeaklyAdmissible R₁ :=
    TopologicalRing.isWeaklyAdmissible_of_isAdicComplete hadic₁ hc₁
  have hR₁S : B.Contains (Spec (.of R₁)) :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hRS (by
      rw [Scheme.size_Spec]
      exact (mk_adicCompletion_le R I).trans le_rfl)
  let a₁ : Spec (.of R₁) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R R₁)) ≫ a
  let D : QuotientSystem B S hS R₁ := quotientSystemOfSpec hR₁S a₁
  have hq₁ : ∀ J : { K : Ideal R₁ // TopologicalRing.IsWeakIdealOfDefinition K },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ a₁ = D.overS J :=
    quotientSystemOfSpec_overS hR₁S a₁
  have hD : QuotientSystemCompatible B S hS a I D := fun J ↦ by
    refine (hq₁ J).symm.trans ?_
    simp only [a₁, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let V := siteObject B S hS hRS a
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  let Φ := completionComparison B S hS hRS a I D hD
  have : IsIso Φ := isIso_completionComparison B S hS hRS a I hIfg D hD
  have hset : zeroLocusPoints B S hS hRS a I = Space.pointsMap B S hS _ h ⁻¹' T := by
    ext x
    show x ∈ zeroLocusPoints B S hS hRS a I ↔ Space.pointsMap B S hS _ h x ∈ T
    rw [hpre x]
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    have hzl : ∀ y : PrimeSpectrum R, y ∈ PrimeSpectrum.zeroLocus (I : Set R) ↔
        y = IsLocalRing.closedPoint R := by
      intro y
      rw [PrimeSpectrum.mem_zeroLocus]
      constructor
      · intro hy
        ext1
        exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le y.isPrime.ne_top hy).symm
      · rintro rfl
        exact le_rfl
    constructor
    · intro hx
      exact (hzl _).1 (hx p rfl)
    · intro hx q hq
      refine (hzl _).2 ?_
      have : Space.pointsToScheme B S hS V (q.class B S hS (yoneda.obj V)) =
          Space.pointsToScheme B S hS V (Quot.mk _ p) := congrArg _ hq
      exact this.trans hx
  let ε := eqToHom (congrArg (Space.completionSheaf B S hS (yoneda.obj V)) hset)
  let P : formalSpectrum D ⟶ Space.completionSheaf B S hS Y T :=
    Φ ≫ ε ≫ Space.completionSheafMap B S hS h T
  have hP : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS P.hom := by
    have hrep := Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS hVsp hY h T
    let e₀ : formalSpectrum D ≅ Space.completionSheaf B S hS (yoneda.obj V)
        (Space.pointsMap B S hS _ h ⁻¹' T) :=
      asIso Φ ≪≫ eqToIso (congrArg (Space.completionSheaf B S hS (yoneda.obj V)) hset)
    refine Space.isRepresentableByAlgebraicSpacesULift_of_iso B S hS
      ((sheafToPresheaf _ _).mapIso e₀.symm) (Iso.refl _) ?_ hrep
    have he₀ : P = e₀.hom ≫ Space.completionSheafMap B S hS h T :=
      (Category.assoc _ _ _).symm
    rw [he₀]
    show _ ≫ 𝟙 _ = (sheafToPresheaf _ _).map e₀.inv ≫
      (sheafToPresheaf _ _).map (e₀.hom ≫ Space.completionSheafMap B S hS h T)
    rw [Category.comp_id, ← Functor.map_comp, ← Category.assoc, e₀.inv_hom_id, Category.id_comp]
    rfl
  obtain ⟨R', _, _, _, _, hext, _, _, _, hadic', hc', D', e, x, he, hx⟩ :=
    hrs R₁ hadic₁ hc₁ hw₁ D P hP
  have hR'N : IsNoetherianCompleteLocalRing R' := ⟨inferInstance, inferInstance, hc'⟩
  have hR'S : B.Contains (Spec (.of R')) := contains_spec_of_quotientSystem hadic' hc' D'
  let ψ : R →+* R' := e.toRingHom.comp (algebraMap R R₁)
  have hq' : ∀ K : { K : Ideal R' // TopologicalRing.IsWeakIdealOfDefinition K },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫
        (Spec.map (CommRingCat.ofHom ψ) ≫ a) = D'.overS K := by
    intro K
    obtain ⟨J, hJ⟩ := exists_weakIdealOfDefinition_le_comap hadic₁ e.continuous K
    rw [← e.overS J K hJ, ← hq₁ J]
    simp only [a₁, ψ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
  obtain ⟨y₀, hy₀⟩ := surjective_map_into_algebraicSpace hR'N D'
    (exists_pow_le_of_isWeakIdealOfDefinition hadic') (exists_weakIdealOfDefinition_le_pow hadic')
    hR'S _ hq' Z hZ (x ≫ completionToUpliftedSheaf Z hZ _)
  have : IsLocalHom (algebraMap R₁ R') := hext.toIsLocalHom
  have : FaithfulSMul R₁ R' := hext.toFaithfulSMul
  have hψe : ψ = (algebraMap R₁ R').comp (algebraMap R R₁) := by
    simp only [ψ, he]
  have hψl : IsLocalHom ψ := by rw [hψe]; infer_instance
  have hψi : Function.Injective ψ := by
    rw [hψe]
    exact (FaithfulSMul.algebraMap_injective R₁ R').comp (AdicCompletion.of_injective I R)
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let hUpφ : upliftedSheaf Z hZ ⟶ upliftedSheaf Y hY :=
    ObjectProperty.homMk (Functor.whiskerRight φ uliftFunctor.{u + 1})
  let hUph : upliftedSheaf (yoneda.obj V) hVsp ⟶ upliftedSheaf Y hY :=
    ObjectProperty.homMk (Functor.whiskerRight h uliftFunctor.{u + 1})
  let hSh : sY.obj V ⟶ upliftedSheaf Y hY :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm (ULift.up (yonedaEquiv h))
  have hSh' : (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (F := upliftedSheaf (yoneda.obj V) hVsp)).symm (ULift.up (𝟙 _)) ≫ hUph = hSh := by
    refine (Sheaf.sectionEquiv_symm_comp (BigFppfOver.topology B S hS) hUph _).symm.trans ?_
    rfl
  have hnatφ := completionSheafMap_comp_completionToUpliftedSheaf hZ hY φ T
  have hnath := completionSheafMap_comp_completionToUpliftedSheaf hVsp hY h T
  have hC3 := completionComparison_comp_completionToUpliftedSheaf hRS a I D hD hR₁S hq₁
  have hstage := formalSpectrumMap_comp_formalSpectrumToSpec_comp hadic₁ hw₁ hRS a
    (algebraMap R R₁) hR₁S hR'S e hq₁ hq'
  have hεtoUp := eqToHom_comp_completionToUpliftedSheaf hVsp hset
  have hy₀' : formalSpectrumToSpec D' hR'S _ hq' ≫ y₀ = x ≫ completionToUpliftedSheaf Z hZ _ := hy₀
  have hkey : formalSpectrumToSpec D' hR'S _ hq' ≫ (y₀ ≫ hUpφ) =
      formalSpectrumToSpec D' hR'S _ hq' ≫ (sY.map (Space.specSiteObjectMap ψ hRS hR'S a) ≫
          hSh) := by
    have e1 := (Category.assoc (formalSpectrumToSpec D' hR'S _ hq') y₀ hUpφ).symm
    have e2 := congrArg (· ≫ hUpφ) hy₀'
    have e3 := (Category.assoc x (completionToUpliftedSheaf Z hZ _) hUpφ).trans
      (congrArg (x ≫ ·) hnatφ.symm)
    have e4 := (Category.assoc x (Space.completionSheafMap B S hS φ T)
      (completionToUpliftedSheaf Y hY T)).symm
    have e5 := congrArg (· ≫ completionToUpliftedSheaf Y hY T) hx
    have e6 : (formalSpectrumMap hw₁ e ≫ P) ≫ completionToUpliftedSheaf Y hY T =
        formalSpectrumMap hw₁ e ≫ Φ ≫ ε ≫
          (Space.completionSheafMap B S hS h T ≫ completionToUpliftedSheaf Y hY T) :=
      (Category.assoc _ _ _).trans (congrArg (formalSpectrumMap hw₁ e ≫ ·)
        ((Category.assoc _ _ _).trans (congrArg (Φ ≫ ·) (Category.assoc _ _ _))))
    have e7 := congrArg (fun t ↦ formalSpectrumMap hw₁ e ≫ Φ ≫ ε ≫ t) hnath
    have e8 := congrArg (fun t ↦ formalSpectrumMap hw₁ e ≫ Φ ≫ t)
      ((Category.assoc ε _ hUph).symm.trans (congrArg (· ≫ hUph) hεtoUp))
    have e9 := congrArg (formalSpectrumMap hw₁ e ≫ ·)
      (Category.assoc Φ (completionToUpliftedSheaf (yoneda.obj V) hVsp _) hUph).symm
    have e10 := congrArg (fun t ↦ formalSpectrumMap hw₁ e ≫ (t ≫ hUph)) hC3
    have e11 := congrArg (formalSpectrumMap hw₁ e ≫ ·)
      ((Category.assoc _ _ _).trans (congrArg (formalSpectrumToSpec D hR₁S _ hq₁ ≫ ·)
        ((Category.assoc _ _ _).trans (congrArg
          (sY.map (Space.specSiteObjectMap (algebraMap R R₁) hRS hR₁S a) ≫ ·) hSh'))))
    have e12 := (congrArg (formalSpectrumMap hw₁ e ≫ ·)
      (Category.assoc (formalSpectrumToSpec D hR₁S _ hq₁)
        (sY.map (Space.specSiteObjectMap (algebraMap R R₁) hRS hR₁S a)) hSh).symm).trans
      (Category.assoc (formalSpectrumMap hw₁ e) _ hSh).symm
    have e13 := congrArg (· ≫ hSh) hstage
    have e14 := Category.assoc (formalSpectrumToSpec D' hR'S _ hq')
      (sY.map (Space.specSiteObjectMap ψ hRS hR'S a)) hSh
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans
      (e9.trans (e10.trans (e11.trans (e12.trans (e13.trans e14))))))))))))
  have hb := injective_map_into_algebraicSpace hR'N D' (exists_weakIdealOfDefinition_le_pow hadic')
    hR'S _ hq' Y hY hkey
  refine ⟨R', inferInstance, inferInstance, inferInstance, ψ, hψl, hψi, hc', hR'S,
    yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) y₀).down, ?_⟩
  have l1 := Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS) y₀ hUpφ
  have l2 := Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS)
    (Space.specSiteObjectMap ψ hRS hR'S a) hSh
  have l3 : Sheaf.sectionEquiv (BigFppfOver.topology B S hS) hSh = ULift.up (yonedaEquiv h) :=
    Equiv.apply_symm_apply _ _
  have l4 := l1.symm.trans ((congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) hb).trans
    (l2.trans (congrArg _ l3)))
  have l5 := congrArg ULift.down l4
  apply yonedaEquiv.injective
  refine (yonedaEquiv_comp _ _).trans ?_
  exact (congrArg (φ.app _) (Equiv.apply_symm_apply yonedaEquiv _)).trans
    (l5.trans (yonedaEquiv_naturality h (Space.specSiteObjectMap ψ hRS hR'S a)))

end Lift

section Trichotomy

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- Every prime of a discrete valuation ring is zero or maximal. -/
theorem eq_bot_or_eq_closedPoint {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (y : PrimeSpectrum R) :
    y.asIdeal = ⊥ ∨ y = IsLocalRing.closedPoint R := by
  refine or_iff_not_imp_left.2 fun hy ↦ ?_
  ext1
  exact IsLocalRing.eq_maximalIdeal (y.isPrime.isMaximal hy)

/-- A ring map from a discrete valuation ring to a field which is injective does not send the
point of the field to the closed point. -/
theorem spec_map_ne_closedPoint {R L : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] (ι : R →+* L) (hι : Function.Injective ι)
    (z : Spec (.of L)) : (Spec.map (CommRingCat.ofHom ι)) z ≠ IsLocalRing.closedPoint R := by
  intro h
  have hideal := congrArg PrimeSpectrum.asIdeal h
  have : z.asIdeal.IsPrime := z.isPrime
  have hz : z.asIdeal = ⊥ := Ideal.eq_bot_of_prime z.asIdeal
  change Ideal.comap ι z.asIdeal = IsLocalRing.maximalIdeal R at hideal
  rw [hz, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hι] at hideal
  exact IsDiscreteValuationRing.not_isField R
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hideal.symm)

/-- For a point `g : Spec R ⟶ Y` of an algebraic space with `R` a discrete valuation ring and a
closed set `T` of points of `Y`, either all of `Spec R` lies over `T`, or none of it does, or
exactly its closed point does. -/
theorem range_subset_or_range_subset_compl_or_iff_closedPoint
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS Y)) (hT : IsClosed T)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hRS : B.Contains (Spec (.of R))) (a : Spec (.of R) ⟶ S)
    (g : yoneda.obj (siteObject B S hS hRS a) ⟶ Y) :
    Set.range (Space.pointsMap B S hS _ g) ⊆ T ∨ Set.range (Space.pointsMap B S hS _ g) ⊆ Tᶜ ∨
      ∀ x, Space.pointsMap B S hS _ g x ∈ T ↔
        Space.pointsToScheme B S hS (siteObject B S hS hRS a) x = IsLocalRing.closedPoint R := by
  classical
  let V := siteObject B S hS hRS a
  let H := Space.schemePointsHomeomorph B S hS V
  let Z : Set (PrimeSpectrum R) := H '' (Space.pointsMap B S hS _ g ⁻¹' T)
  have hZ : IsClosed Z := H.isClosedMap _ (hT.preimage (Space.continuous_pointsMap B S hS g))
  have hmem : ∀ x, Space.pointsMap B S hS _ g x ∈ T ↔ Space.pointsToScheme B S hS V x ∈ Z :=
    fun x ↦ ⟨fun hx ↦ ⟨x, hx, rfl⟩, fun ⟨_, hx', hxx'⟩ ↦ H.injective hxx' ▸ hx'⟩
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hpt : ∀ y : PrimeSpectrum R, y = η ∨ y = IsLocalRing.closedPoint R := fun y ↦
    (eq_bot_or_eq_closedPoint y).imp (fun h ↦ PrimeSpectrum.ext h) id
  have hpts : ∀ x, Space.pointsToScheme B S hS V x = η ∨
      Space.pointsToScheme B S hS V x = IsLocalRing.closedPoint R := fun x ↦ hpt _
  by_cases hη : η ∈ Z
  · left
    have hcl : closure ({η} : Set (PrimeSpectrum R)) ⊆ Z :=
      hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)
    rw [PrimeSpectrum.closure_singleton] at hcl
    have hall : ∀ y : PrimeSpectrum R, y ∈ Z := fun y ↦ by
      apply hcl
      rw [PrimeSpectrum.mem_zeroLocus]
      intro r hr
      have hr0 : r = 0 := hr
      rw [hr0]
      exact y.asIdeal.zero_mem
    rintro _ ⟨x, rfl⟩
    exact (hmem x).2 (hall _)
  by_cases hc : IsLocalRing.closedPoint R ∈ Z
  · right; right
    intro x
    rw [hmem x]
    exact ⟨fun hx ↦ (hpts x).resolve_left fun h ↦ hη (h ▸ hx), fun hx ↦ hx ▸ hc⟩
  · right; left
    rintro _ ⟨x, rfl⟩ hx
    have hx' := (hmem x).1 hx
    exact (hpts x).elim (fun h ↦ hη (h ▸ hx')) fun h ↦ hc (h ▸ hx')

end Trichotomy

section Converse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- The completion of the relative diagonal of `f` along the inverse image of `T` is
rig-surjective when the relative diagonal of `f_{/T}` is. -/
theorem isRigSurjective_completionSheafMap_diagonal {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hΔ : IsRigSurjective B S hS (pullback.diagonal (Space.completionSheafMap B S hS f T))) :
    IsRigSurjective B S hS (Space.completionSheafMap B S hS (pullback.diagonal f)
      (Space.pullbackPoints B S hS f f T)) := by
  rw [Space.pullback_diagonal_completionSheafMap B S hS f T,
    Space.completionSheafDiagonal_eq_completionSheafMap_diagonal, Category.assoc] at hΔ
  have h1 := IsRigSurjective.comp_isIso _
    (Space.isPullback_completionSheafPullback B S hS f f T).isoPullback.inv hΔ
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h1
  have h2 := IsRigSurjective.isIso_comp (eqToHom (congrArg (Space.completionSheaf B S hS X')
    (Space.pointsMap_diagonal_preimage_pullbackPoints B S hS f T))) _ h1
  simpa using h2

/-- The dominating extension of a valuative square along a lift over an extension of
complete discrete valuation rings whose generic point avoids `T`. -/
theorem nonempty_lift_dominatingExtensionOfRingHom {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X' ⟶ X} {T : Set (Space.points B S hS X)}
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (q : Space.ValuativeSquare f) (hdvr : IsDiscreteValuationRing q.R)
    (hpre : ∀ x, Space.pointsMap B S hS _ q.special x ∈ T ↔
      Space.pointsToScheme B S hS (siteObject B S hS q.ring_mem q.base) x =
        IsLocalRing.closedPoint q.R)
    {R' : Type u} [CommRing R'] [IsDomain R'] [ValuationRing R'] (ψ : q.R →+* R')
    (hψl : IsLocalHom ψ) (hR'S : B.Contains (Spec (.of R')))
    (y : yoneda.obj (siteObject B S hS hR'S (Spec.map (CommRingCat.ofHom ψ) ≫ q.base)) ⟶ X')
    (hy : y ≫ f = yoneda.map (Space.specSiteObjectMap ψ q.ring_mem hR'S q.base) ≫ q.special)
    (L : Type u) [Field L] [Algebra R' L] [IsFractionRing R' L] (hL : B.Contains (Spec (.of L)))
    (jK : q.K →+* L) (hij : (algebraMap R' L).comp ψ = jK.comp (algebraMap q.R q.K)) :
    Nonempty (Space.dominatingExtensionOfRingHom q hR'S hL ψ jK hψl hij).square.Lift := by
  let e := Space.dominatingExtensionOfRingHom q hR'S hL ψ jK hψl hij
  refine ⟨⟨y, ?_, hy⟩⟩
  let jq := yoneda.map (Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem) :
    siteObject B S hS q.field_mem (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base)
  have hrange : Set.range (Space.pointsMap B S hS _ (yoneda.map e.genericOver ≫ jq ≫ q.special))
      ⊆ Tᶜ := by
    rintro _ ⟨w, rfl⟩ hw
    rw [← Category.assoc, ← Functor.map_comp, Space.pointsMap_comp_apply] at hw
    have h1 := (hpre _).1 hw
    rw [Space.pointsToScheme_pointsMap_yoneda] at h1
    have hι : Function.Injective (jK.comp (algebraMap q.R q.K)) :=
      jK.injective.comp (IsFractionRing.injective q.R q.K)
    refine spec_map_ne_closedPoint _ hι (Space.pointsToScheme B S hS _ w) ?_
    refine Eq.trans ?_ h1
    show _ = (Spec.map (CommRingCat.ofHom jK) ≫
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨k, hk⟩ := (Space.exists_factor_openSubspaceOfPoints_iff B S hS Tᶜ _).2 hrange
  refine eq_of_comp_eq_of_isIso_pullback_snd hfU _ _ k ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hy).trans (Eq.trans ?_ hk.symm))
    show yoneda.map _ ≫ yoneda.map e.specialOver ≫ q.special =
      yoneda.map e.genericOver ≫ jq ≫ q.special
    rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    congr 2
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom (algebraMap R' L)) ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom jK) ≫ Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hij]
  · show (yoneda.map e.genericOver ≫ q.generic) ≫ f = _
    rw [Category.assoc, q.comm, hk]

/-- An injective ring map `A →+* R'` into a domain with fraction field `L` extends to a map of
fraction fields `K →+* L`. -/
private theorem exists_comp_algebraMap_eq_of_injective {A K R' L : Type u} [CommRing A]
    [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [CommRing R'] [Field L]
    [Algebra R' L] [IsFractionRing R' L] (ψ : A →+* R') (hψi : Function.Injective ψ) :
    ∃ jK : K →+* L, (algebraMap R' L).comp ψ = jK.comp (algebraMap A K) := by
  have hg : Function.Injective ((algebraMap R' L).comp ψ) :=
    (IsFractionRing.injective R' L).comp hψi
  exact ⟨IsFractionRing.lift hg,
    RingHom.ext fun r ↦ (IsFractionRing.lift_algebraMap hg r).symm⟩

/-- A lift over an extension of complete discrete valuation rings gives a dominating
extension of the valuative square carrying a dotted arrow. -/
theorem exists_dominatingExtension_of_lift {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X' ⟶ X} {T : Set (Space.points B S hS X)}
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (q : Space.ValuativeSquare f) (hdvr : IsDiscreteValuationRing q.R)
    (hpre : ∀ x, Space.pointsMap B S hS _ q.special x ∈ T ↔
      Space.pointsToScheme B S hS (siteObject B S hS q.ring_mem q.base) x =
        IsLocalRing.closedPoint q.R)
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] (ψ : q.R →+* R')
    (hψl : IsLocalHom ψ) (hψi : Function.Injective ψ) (hR'S : B.Contains (Spec (.of R')))
    (hc' : IsAdicComplete (IsLocalRing.maximalIdeal R') R')
    (y : yoneda.obj (siteObject B S hS hR'S (Spec.map (CommRingCat.ofHom ψ) ≫ q.base)) ⟶ X')
    (hy : y ≫ f = yoneda.map (Space.specSiteObjectMap ψ q.ring_mem hR'S q.base) ≫ q.special)
    (L : Type u) [Field L] [Algebra R' L] [IsFractionRing R' L]
    (hL : B.Contains (Spec (.of L))) :
    ∃ e : q.DominatingExtension, IsDiscreteValuationRing e.square.R ∧
      IsAdicComplete (IsLocalRing.maximalIdeal e.square.R) e.square.R ∧
        Nonempty e.square.Lift := by
  obtain ⟨jK, hij⟩ := exists_comp_algebraMap_eq_of_injective (K := q.K) (L := L) ψ hψi
  exact ⟨Space.dominatingExtensionOfRingHom q hR'S hL ψ jK hψl hij,
    (inferInstance : IsDiscreteValuationRing R'), hc',
    nonempty_lift_dominatingExtensionOfRingHom hfU q hdvr hpre ψ hψl hR'S y hy L hL _ hij⟩

/-- A lift of a valuative square through a dominating extension, for a square lying over `T`
at its closed point only. -/
theorem exists_dominatingExtension_lift_of_iff_closedPoint
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    {f : X' ⟶ X} {T : Set (Space.points B S hS X)}
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hrs : IsRigSurjective B S hS (Space.completionSheafMap B S hS f T))
    (q : Space.ValuativeSquare f) (hdvr : IsDiscreteValuationRing q.R)
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal q.R) q.R)
    (hpre : ∀ x, Space.pointsMap B S hS _ q.special x ∈ T ↔
      Space.pointsToScheme B S hS (siteObject B S hS q.ring_mem q.base) x =
        IsLocalRing.closedPoint q.R) :
    ∃ e : q.DominatingExtension, IsDiscreteValuationRing e.square.R ∧
      IsAdicComplete (IsLocalRing.maximalIdeal e.square.R) e.square.R ∧
        Nonempty e.square.Lift := by
  obtain ⟨R', _, _, _, ψ, hψl, hψi, hc', hR'S, y, hy⟩ :=
    exists_lift_of_isRigSurjective_completionSheafMap hX' hX f T hrs q.R hc q.ring_mem q.base
      q.special hpre
  exact exists_dominatingExtension_of_lift hfU q hdvr hpre ψ hψl hψi hR'S hc' y hy
    (FractionRing R') (Space.contains_spec_fractionRing hR'S)

/-- Two dotted arrows of a valuative square agreeing after an extension of valuation rings
agree. -/
theorem eq_of_restrict_eq {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') {f : X' ⟶ X} (q : Space.ValuativeSquare f)
    {R' : Type u} [CommRing R'] [IsDomain R'] [ValuationRing R'] (ψ : q.R →+* R')
    (hψl : IsLocalHom ψ) (hψi : Function.Injective ψ) (hR'S : B.Contains (Spec (.of R')))
    (L : Type u) [Field L] [Algebra R' L] [IsFractionRing R' L] (hL : B.Contains (Spec (.of L)))
    (l₁ l₂ : q.Lift)
    (hres : yoneda.map (Space.specSiteObjectMap ψ q.ring_mem hR'S q.base) ≫ l₁.map =
      yoneda.map (Space.specSiteObjectMap ψ q.ring_mem hR'S q.base) ≫ l₂.map) :
    l₁ = l₂ := by
  obtain ⟨jK, hij⟩ := exists_comp_algebraMap_eq_of_injective (K := q.K) (L := L) ψ hψi
  let e := Space.dominatingExtensionOfRingHom q hR'S hL ψ jK hψl hij
  have hXinj := (Presieve.isSeparatedFor_singleton (P := X')).mp
    (hX'.isSeparatedFor_fpqc (Space.dominatingExtension_specialOver_mem_fpqc q e))
  have hmap : l₁.map = l₂.map := by
    apply yonedaEquiv.injective
    apply hXinj
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv hres
  cases l₁
  cases l₂
  cases hmap
  rfl

/-- A valuative square for `f : X' ⟶ X` over a complete discrete valuation ring whose bottom edge
meets `T` exactly in the closed point has at most one dotted arrow, as soon as the relative
diagonal of the completion `f_{/T}` is rig-surjective. -/
theorem subsingleton_lift_of_iff_closedPoint
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    {f : X' ⟶ X} {T : Set (Space.points B S hS X)}
    (hΔ : IsRigSurjective B S hS (pullback.diagonal (Space.completionSheafMap B S hS f T)))
    (q : Space.ValuativeSquare f) (hdvr : IsDiscreteValuationRing q.R)
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal q.R) q.R)
    (hpre : ∀ x, Space.pointsMap B S hS _ q.special x ∈ T ↔
      Space.pointsToScheme B S hS (siteObject B S hS q.ring_mem q.base) x =
        IsLocalRing.closedPoint q.R) :
    Subsingleton q.Lift := by
  classical
  refine ⟨fun l₁ l₂ ↦ ?_⟩
  let σ := pullback.lift l₁.map l₂.map (l₁.special_comm.trans l₂.special_comm.symm)
  have hP : IsAlgebraicSpace B S hS
      (pullback f f) := isAlgebraicSpace_pullback B S hS f f hX' hX' hX
  have hσpre : ∀ x, Space.pointsMap B S hS _ σ x ∈ Space.pullbackPoints B S hS f f T ↔
      Space.pointsToScheme B S hS (siteObject B S hS q.ring_mem q.base) x =
        IsLocalRing.closedPoint q.R := by
    intro x
    show Space.pointsMap B S hS _ (pullback.fst f f ≫ f) (Space.pointsMap B S hS _ σ x) ∈ T ↔ _
    rw [← Space.pointsMap_comp_apply, ← Category.assoc, pullback.lift_fst, l₁.special_comm]
    exact hpre x
  obtain ⟨R', _, _, _, ψ, hψl, hψi, hc', hR'S, y, hy⟩ :=
    exists_lift_of_isRigSurjective_completionSheafMap hX' hP (pullback.diagonal f) _
      (isRigSurjective_completionSheafMap_diagonal f T hΔ) q.R hc q.ring_mem q.base σ hσpre
  have hres : yoneda.map (Space.specSiteObjectMap ψ q.ring_mem hR'S q.base) ≫ l₁.map =
      yoneda.map (Space.specSiteObjectMap ψ q.ring_mem hR'S q.base) ≫ l₂.map := by
    have h1 := congrArg (· ≫ pullback.fst f f) hy
    have h2 := congrArg (· ≫ pullback.snd f f) hy
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      σ, pullback.lift_fst, pullback.lift_snd] at h1 h2
    exact h1.symm.trans h2
  exact eq_of_restrict_eq hX' q ψ hψl hψi hR'S (FractionRing R')
    (Space.contains_spec_fractionRing hR'S) l₁ l₂ hres

/-- Uniqueness of dotted arrows over a complete discrete valuation ring. -/
theorem subsingleton_lift_of_isFormalModification
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    {f : X' ⟶ X} {T : Set (Space.points B S hS X)} (hT : IsClosed T)
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hg : IsProper B S hS (Space.completionSheafMap B S hS f T))
    (hΔ : IsRigSurjective B S hS (pullback.diagonal (Space.completionSheafMap B S hS f T)))
    (q : Space.ValuativeSquare f) (hdvr : IsDiscreteValuationRing q.R)
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal q.R) q.R) :
    Subsingleton q.Lift := by
  classical
  rcases range_subset_or_range_subset_compl_or_iff_closedPoint T hT q.ring_mem q.base
    q.special with h | h | hpre
  · exact (unique_lift_of_range_subset hX' hX hg q h).2
  · exact (unique_lift_of_range_subset_compl hfU q h).2
  exact subsingleton_lift_of_iff_closedPoint hX' hX hΔ q hdvr hc hpre

/-- A finite-type modification `f : X' ⟶ X` of a locally Noetherian algebraic space outside the
complement of a closed set `T`, whose completion `f_{/T}` is proper, rig-surjective and has
rig-surjective relative diagonal, is proper. -/
theorem isProper_of_isProper_completionSheafMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hN : Space.HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T))
    (f : X' ⟶ X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hg : IsProper B S hS (Space.completionSheafMap B S hS f T))
    (hrs : IsRigSurjective B S hS (Space.completionSheafMap B S hS f T))
    (hΔ : IsRigSurjective B S hS (pullback.diagonal (Space.completionSheafMap B S hS f T))) :
    Space.IsProper B S hS f := by
  have hqc := isQuasiCompact_of_isProper_completionSheafMap hX' hX hN f T hT hfU hg
  have hqs := isQuasiSeparated_of_isProper_completionSheafMap hX' hX hN f hf T hT hfU hg
  refine (Space.isProper_iff_completeDiscreteValuativeCriterion B S hS hX' hX f hN ⟨hf, hqc⟩
    hqs).2 fun q hd hc ↦ ?_
  rcases range_subset_or_range_subset_compl_or_iff_closedPoint T hT q.ring_mem q.base
    q.special with h | h | hpre
  · obtain ⟨hne, hsub⟩ := unique_lift_of_range_subset hX' hX hg q h
    exact ⟨q.idDominatingExtension, hd, hc, hne, hsub⟩
  · obtain ⟨hne, hsub⟩ := unique_lift_of_range_subset_compl hfU q h
    exact ⟨q.idDominatingExtension, hd, hc, hne, hsub⟩
  · obtain ⟨e, hd', hc', hne⟩ :=
      exists_dominatingExtension_lift_of_iff_closedPoint hX' hX hfU hrs q hd hc hpre
    exact ⟨e, hd', hc', hne,
      subsingleton_lift_of_isFormalModification hX' hX hT hfU hg hΔ e.square hd' hc'⟩

end Converse

section Statement

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be closed with open
complement `U`, and let `f : X' ⟶ X` be a finite-type modification of `X` outside `U`
(Stacks 0AS2), corresponding to an object `g : W ⟶ X_{/T}` of the right-hand category of
Stacks 0AR5 — a rig-étale morphism with `W` a locally Noetherian formal algebraic space — through
an isomorphism over `X_{/T}` between `f_{/T}` and `g`. Then `f` is proper if and only if `g` is a
formal modification (Definition 0GDK). -/
@[stacks 0ARX "the correspondence `f ↔ g` of Theorem 0ARB is rendered as an isomorphism over \
`X_{/T}` between the image `f_{/T}` of `f` under the completion functor of Stacks 0AR5 and an \
object `g` of the right-hand category of Stacks 0AR5; the equivalence of Theorem 0ARB itself is \
not used"]
theorem isProper_iff_isFormalModification_of_iso
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (P : RigEtaleOverCompletion B S hS X T)
    (e : (Space.completionOverFunctor B S hS T).obj M.obj ≅ P.obj) :
    Space.IsProper B S hS M.obj.hom ↔ IsFormalModification B S hS P.obj.hom := by
  refine ⟨isFormalModification_of_isProper_of_iso hX hXN T hT M P e, fun hP ↦ ?_⟩
  have hX' : IsAlgebraicSpace B S hS M.obj.left := M.property.1.1
  have hN : Space.HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T) :=
    (Space.exists_atlas_iff_forall_etale B S hS X _ hX).mpr fun W q hq ↦
      hXN W q ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).2 hq)
  have : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have hg : Space.completionSheafMap B S hS M.obj.hom T = e.hom.left ≫ P.obj.hom :=
    (Over.w e.hom).symm
  refine isProper_of_isProper_completionSheafMap hX' hX hN M.obj.hom M.property.2 T hT
    M.property.1.2 ?_ ?_ ?_ <;> rw [hg]
  · exact isProper_isIso_comp e.hom.left P.obj.hom hP.isProper
  · exact IsRigSurjective.isIso_comp e.hom.left P.obj.hom hP.isRigSurjective
  · exact isRigSurjective_diagonal_isIso_comp e.hom.left P.obj.hom hP.isRigSurjective_diagonal

/-- For the completion functor of Stacks 0AR5 on finite-type modifications, a finite-type
modification is proper exactly when an object isomorphic to its image is a formal
modification. -/
theorem isProper_iff_isFormalModification_of_completionFiniteTypeModificationFunctor
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXsp : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (P : RigEtaleOverCompletion B S hS X T)
    (e : (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).obj M ≅ P) :
    Space.IsProper B S hS M.obj.hom ↔ IsFormalModification B S hS P.obj.hom :=
  isProper_iff_isFormalModification_of_iso hXsp hX T hT M P ((ObjectProperty.ι _).mapIso e)

end Statement

end AlgebraicGeometry.FormalSpace

end
