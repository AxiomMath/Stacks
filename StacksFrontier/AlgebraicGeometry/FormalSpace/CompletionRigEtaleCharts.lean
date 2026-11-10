module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineRigEtaleAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocalStructure.OpenCopies
public import StacksFrontier.RingTheory.Rig.RigEtaleCompletionMap
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineRigEtaleAlgebraization
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleFromCompletionSpace
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# The completion of a morphism étale off the closed set is rig-étale

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of algebraic
spaces over `S`, let `T ⊆ |X|` be closed and write `T' = |f|⁻¹T`, `U = X ∖ T`, `U' = f⁻¹U`.
**Stacks 0AR2** says that if `X` is locally Noetherian, `f` is locally of finite type and
`U' → U` is étale, then `f_{/T} : X'_{/T'} ⟶ X_{/T}` is rig-étale.

This file proves the affine case: for a morphism `Spec C ⟶ Spec A` of affine objects of the site
with `A` Noetherian, locally of finite type and étale at every point over the complement of a
closed `T`, the completion `(Spec C)_{/T_C} ⟶ (Spec A)_{/T}` corresponds to a rig-étale map in
`WAdm^{Noeth}`.

## Main results

* `AlgebraicGeometry.FormalSpace.mem_etaleLocus_of_etaleAt_specMap`: a ring map whose spectrum is
  étale at a point is étale at the corresponding prime.
* `AlgebraicGeometry.FormalSpace.formalSpectrumMap_comp_completionComparison_eq`: under the
  identifications `Spf (A^) = (Spec A)_{/V(I)}` and `Spf (C^) = (Spec C)_{/V(IC)}` of Stacks 0GBA
  (2), the completion of `Spec C ⟶ Spec A` is the formal spectrum of any continuous map
  `A^ → C^` extending `A → C`.
* `AlgebraicGeometry.FormalSpace.correspondsToRigEtaleMap_completionSheafMap_of_etaleAt`: the
  affine case of Stacks 0AR2, in the form of condition (4) of Stacks 0GCZ on one chart.

## Implementation notes

The proof is the source's: by Stacks 0GBA (2) the completion of `Spec C ⟶ Spec A` along `V(I)` is
`Spf` of the completed map `A^ → C^`, and that map is rig-étale by part (1) of Stacks 0ALQ, in the
form `Rig.isRigEtaleHom_completionMap_of_isEtaleOutside`. The compatibility of the two
identifications with the completed map is checked after the monomorphism `(Spec A)_{/T} ⟶ Spec A`,
on each quotient stage of `C^`, as in the proof of Stacks 0AR4.

## References

* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Étaleness at a point of a spectrum -/

/-- **Étaleness of `Spec R' ⟶ Spec R` at a point is étaleness of `R'` at the prime.** If the
morphism of spectra of a ring map `φ : R → R'` is étale at a point `x`, then `x` lies in the
étale locus of `R'` over `R`: some basic open neighbourhood `D(c)` of `x` lies in an open on which
the morphism is étale, so `Spec R'_c ⟶ Spec R` is étale and `R'_c` is étale over `R`. -/
theorem mem_etaleLocus_of_etaleAt_specMap {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (x : PrimeSpectrum R')
    (hx : EtaleAt (Spec.map (CommRingCat.ofHom φ)) x) :
    letI : Algebra R R' := φ.toAlgebra
    x ∈ Algebra.etaleLocus R R' := by
  let : Algebra R R' := φ.toAlgebra
  obtain ⟨U, hxU, hU⟩ := exists_open_etale_of_etaleAt _ hx
  obtain ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, hxc, hcU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  let j := Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away c)))
  have hrange : Set.range j ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    intro y hy
    exact hcU (PrimeSpectrum.localization_away_comap_range (Localization.Away c) c ▸ hy)
  let j' := IsOpenImmersion.lift U.ι j hrange
  have hfac : j' ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  have het : Etale (j ≫ Spec.map (CommRingCat.ofHom φ)) := by
    rw [← hfac, Category.assoc]
    infer_instance
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at het
  have hE : ((algebraMap R' (Localization.Away c)).comp φ).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  have hE' : (algebraMap R (Localization.Away c)).Etale := by
    rw [IsScalarTower.algebraMap_eq R R' (Localization.Away c)]
    exact hE
  have : Algebra.Etale R (Localization.Away c) := RingHom.etale_algebraMap.mp hE'
  exact (Algebra.basicOpen_subset_etaleLocus_iff (R := R) (A := R') (f := c)).mpr inferInstance
    hxc

/-! ### The completion of a morphism of affine objects -/

section Affine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `J`-adic topology on the `J`-adic completion `AdicCompletion J R`. -/
local instance instTopologicalSpaceAdicCompletionCharts {R : Type u} [CommRing R] (J : Ideal R) :
    TopologicalSpace (AdicCompletion J R) :=
  J.adicModuleTopology (AdicCompletion J R)

attribute [local instance] Space.pointTopology

/-- The completion of an algebraic space is a subsheaf of its universe-lifted sheaf. -/
theorem mono_completionToUpliftedSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) :
    Mono (completionToUpliftedSheaf X hX T) :=
  Sheaf.Hom.mono_of_presheaf_mono _ _
    (h := Space.mono_completionSheafToAmbient B S hS X (upliftedSheaf X hX).property T)

/-- On the quotient stage `Spec (R ⧸ K)` of the formal spectrum of `R`, the formal spectrum map of
`χ : A^ → R` followed by `(Spec A)_{/V(I)} ⟶ Spec A` is the ring map `A → A^ → R ⧸ K`. -/
theorem formalSpectrumInclusion_comp_formalSpectrumMap_comp_completionComparison {A R : Type u}
    [CommRing A] [CommRing R] [TopologicalSpace R] (hA : B.Contains (Spec (.of A)))
    (s : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) [IsTopologicalRing (AdicCompletion I A)]
    [IsLinearTopology (AdicCompletion I A) (AdicCompletion I A)]
    (hwA : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A)) {E : QuotientSystem B S hS R}
    (χ : ContinuousHom (adicQuotientSystem B S hS hA s I hI) E)
    (J : { J : Ideal (AdicCompletion I A) // IsWeakIdealOfDefinition J })
    (K : { K : Ideal R // IsWeakIdealOfDefinition K }) (hJK : J.1 ≤ Ideal.comap χ.toRingHom K.1) :
    formalSpectrumInclusion E (OrderDual.toDual K) ≫ formalSpectrumMap hwA χ ≫
        completionComparison B S hS hA s I (adicQuotientSystem B S hS hA s I hI)
          (quotientSystemCompatible_adicQuotientSystem B S hS hA s I hI) ≫
        completionToUpliftedSheaf (yoneda.obj (affineOver B S hS hA s))
          (isAlgebraicSpace_yoneda B S hS _) (zeroLocusPoints B S hS hA s I) =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (ULift.up ((BigAffineFppf.inclusion B S hS).map (χ.stageMap J K hJK) ≫
          quotientStageToAffine B S hS hA s I (adicQuotientSystem B S hS hA s I hI)
            (quotientSystemCompatible_adicQuotientSystem B S hS hA s I hI) J)) := by
  let X := affineOver B S hS hA s
  let D := adicQuotientSystem B S hS hA s I hI
  let hD := quotientSystemCompatible_adicQuotientSystem B S hS hA s I hI
  let cmp := completionComparison B S hS hA s I D hD
  let ιX := completionToUpliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X)
    (zeroLocusPoints B S hS hA s I)
  let Yf := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ cmp ≫ ιX) (formalSpectrumMap_spec hwA χ J K hJK)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (Yf.map ((BigAffineFppf.inclusion B S hS).map (χ.stageMap J K hJK)) ≫ ·)
          (formalSpectrumInclusion_comp_completionComparison_comp_completionToUpliftedSheaf
            B S hS hA s I D hD J)).trans
          (Sheaf.sectionEquiv_symm_map (BigFppfOver.topology B S hS)
            ((BigAffineFppf.inclusion B S hS).map (χ.stageMap J K hJK))
            (F := upliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X))
            (ULift.up (quotientStageToAffine B S hS hA s I D hD J))).symm)))

/-- **The completion of a morphism of affine objects is a formal spectrum map.** Let
`α : Spec C ⟶ Spec A` be a morphism of affine objects of the site whose underlying morphism of
schemes is `Spec` of `φ : A → C`, let `I ⊆ A` be finitely generated and let `χ : A^ → C^` be a
continuous map over `S` of the completions along `I` and `IC` extending `φ`. Then, under the
identifications of Stacks 0GBA (2), `α_{/V(I)}` is `Spf χ`.

Both sides are checked after the monomorphism `(Spec A)_{/V(I)} ⟶ Spec A`, on each quotient
stage `Spec (C^ ⧸ K)`, where both are the morphism `Spec (C^ ⧸ K) ⟶ Spec A` of the ring map
`A → C → C^ ⧸ K`. -/
theorem formalSpectrumMap_comp_completionComparison_eq {A C : Type u} [CommRing A] [CommRing C]
    (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    (hC : B.Contains (Spec (.of C))) (sC : Spec (.of C) ⟶ S)
    (α : affineOver B S hS hC sC ⟶ affineOver B S hS hA s) (φ : A →+* C)
    (hφ : (BigFppfOver.toScheme B S hS).map α = Spec.map (CommRingCat.ofHom φ))
    (I : Ideal A) (hI : I.FG) (hI' : (I.map φ).FG)
    [IsTopologicalRing (AdicCompletion I A)]
    [IsLinearTopology (AdicCompletion I A) (AdicCompletion I A)]
    (hwA : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A))
    (χ : ContinuousHom (adicQuotientSystem B S hS hA s I hI)
      (adicQuotientSystem B S hS hC sC (I.map φ) hI'))
    (hχ : χ.toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap C (AdicCompletion (I.map φ) C)).comp φ)
    (hT' : Space.pointsMap B S hS (yoneda.obj (affineOver B S hS hC sC)) (yoneda.map α) ⁻¹'
        zeroLocusPoints B S hS hA s I = zeroLocusPoints B S hS hC sC (I.map φ)) :
    formalSpectrumMap hwA χ ≫ completionComparison B S hS hA s I
        (adicQuotientSystem B S hS hA s I hI)
        (quotientSystemCompatible_adicQuotientSystem B S hS hA s I hI) =
      completionComparison B S hS hC sC (I.map φ)
          (adicQuotientSystem B S hS hC sC (I.map φ) hI')
          (quotientSystemCompatible_adicQuotientSystem B S hS hC sC (I.map φ) hI') ≫
        eqToHom (congrArg (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hC sC)))
          hT'.symm) ≫
        Space.completionSheafMap B S hS (yoneda.map α) (zeroLocusPoints B S hS hA s I) := by
  let X := affineOver B S hS hA s
  let X' := affineOver B S hS hC sC
  let I' := I.map φ
  let D := adicQuotientSystem B S hS hA s I hI
  let hD := quotientSystemCompatible_adicQuotientSystem B S hS hA s I hI
  let D' := adicQuotientSystem B S hS hC sC I' hI'
  let hD' := quotientSystemCompatible_adicQuotientSystem B S hS hC sC I' hI'
  let cmp := completionComparison B S hS hA s I D hD
  let cmp' := completionComparison B S hS hC sC I' D' hD'
  let ιX := completionToUpliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X)
    (zeroLocusPoints B S hS hA s I)
  have : Mono ιX := mono_completionToUpliftedSheaf B S hS _ _ _
  let ιX' := completionToUpliftedSheaf (yoneda.obj X') (isAlgebraicSpace_yoneda B S hS X')
    (zeroLocusPoints B S hS hC sC I')
  let upl : upliftedSheaf (yoneda.obj X') (isAlgebraicSpace_yoneda B S hS X') ⟶
      upliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X) :=
    ObjectProperty.homMk (Functor.whiskerRight (yoneda.map α) uliftFunctor.{u + 1})
  refine (cancel_mono ιX).mp ?_
  refine formalSpectrum_hom_ext D' _ fun K ↦ ?_
  obtain ⟨Jw, hJw⟩ := exists_isWeakIdealOfDefinition_le_comap hwA.1 χ.toRingHom χ.continuous K
  have key2 : (cmp' ≫ eqToHom (congrArg (Space.completionSheaf B S hS (yoneda.obj X'))
        hT'.symm) ≫ Space.completionSheafMap B S hS (yoneda.map α)
          (zeroLocusPoints B S hS hA s I)) ≫ ιX = cmp' ≫ ιX' ≫ upl := by
    rw [Category.assoc, Category.assoc, completionSheafMap_comp_completionToUpliftedSheaf
      (isAlgebraicSpace_yoneda B S hS X') (isAlgebraicSpace_yoneda B S hS X),
      ← Category.assoc (eqToHom _),
      eqToHom_comp_completionToUpliftedSheaf (isAlgebraicSpace_yoneda B S hS X') hT'.symm]
  have hmor : (BigAffineFppf.inclusion B S hS).map (χ.stageMap Jw K hJw) ≫
      quotientStageToAffine B S hS hA s I D hD Jw =
      quotientStageToAffine B S hS hC sC I' D' hD' K ≫ α := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 χ.toRingHom hJw)) ≫
        Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk Jw.1).comp (algebraMap A _))) =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K.1).comp (algebraMap C _))) ≫
        (BigFppfOver.toScheme B S hS).map α
    rw [hφ, ← Spec.map_comp]
    refine (congrArg Spec.map ?_).trans (Spec.map_comp _ _)
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext r
    exact congrArg (Ideal.Quotient.mk K.1) (RingHom.congr_fun hχ r)
  have hr : formalSpectrumInclusion D' (OrderDual.toDual K) ≫ cmp' ≫ ιX' ≫ upl =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (ULift.up (quotientStageToAffine B S hS hC sC I' D' hD' K ≫ α)) :=
    (formalSpectrumInclusion_comp_completionComparison_comp_completionToUpliftedSheaf_assoc
      B S hS hC sC I' D' hD' K upl).trans
      (Sheaf.sectionEquiv_symm_comp (BigFppfOver.topology B S hS) upl
        (ULift.up (quotientStageToAffine B S hS hC sC I' D' hD' K))).symm
  calc formalSpectrumInclusion D' (OrderDual.toDual K) ≫ (formalSpectrumMap hwA χ ≫ cmp) ≫ ιX
      = formalSpectrumInclusion D' (OrderDual.toDual K) ≫ formalSpectrumMap hwA χ ≫
          cmp ≫ ιX := congrArg _ (Category.assoc _ _ _)
    _ = (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (ULift.up (quotientStageToAffine B S hS hC sC I' D' hD' K ≫ α)) :=
      (formalSpectrumInclusion_comp_formalSpectrumMap_comp_completionComparison B S hS hA s I hI
        hwA χ Jw K hJw).trans (congrArg _ (congrArg ULift.up hmor))
    _ = formalSpectrumInclusion D' (OrderDual.toDual K) ≫ cmp' ≫ ιX' ≫ upl := hr.symm
    _ = _ := congrArg (formalSpectrumInclusion D' (OrderDual.toDual K) ≫ ·) key2.symm

/-- For a morphism `α : Spec C ⟶ Spec A` of affine objects which is `Spec` of `φ : A → C`, a point
`p` of `Spec C` maps into `V(I)` exactly when its prime pulls back along `φ` into `V(I)`. -/
private theorem pointsMap_mem_zeroLocusPoints_iff {A C : Type u} [CommRing A] [CommRing C]
    (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    (hC : B.Contains (Spec (.of C))) (sC : Spec (.of C) ⟶ S)
    (α : affineOver B S hS hC sC ⟶ affineOver B S hS hA s) (φ : A →+* C)
    (hφ : (BigFppfOver.toScheme B S hS).map α = Spec.map (CommRingCat.ofHom φ)) (I : Ideal A)
    (p : Space.points B S hS (yoneda.obj (affineOver B S hS hC sC))) :
    Space.pointsMap B S hS _ (yoneda.map α) p ∈ zeroLocusPoints B S hS hA s I ↔
      PrimeSpectrum.comap φ (Space.pointsToScheme B S hS _ p) ∈
        PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [zeroLocusPoints_eq_preimage_pointsToScheme]
  change Space.pointsToScheme B S hS _ (Space.pointsMap B S hS _ (yoneda.map α) p) ∈
    PrimeSpectrum.zeroLocus (I : Set A) ↔ _
  rw [Space.pointsToScheme_pointsMap, hφ]
  rfl

/-- For a morphism `α : Spec C ⟶ Spec A` of affine objects which is `Spec` of `φ : A → C`, the
inverse image of `V(I)` under `|α|` is `V(IC)`. -/
theorem preimage_zeroLocusPoints_eq_zeroLocusPoints_map {A C : Type u} [CommRing A] [CommRing C]
    (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    (hC : B.Contains (Spec (.of C))) (sC : Spec (.of C) ⟶ S)
    (α : affineOver B S hS hC sC ⟶ affineOver B S hS hA s) (φ : A →+* C)
    (hφ : (BigFppfOver.toScheme B S hS).map α = Spec.map (CommRingCat.ofHom φ)) (I : Ideal A) :
    Space.pointsMap B S hS (yoneda.obj (affineOver B S hS hC sC)) (yoneda.map α) ⁻¹'
      zeroLocusPoints B S hS hA s I = zeroLocusPoints B S hS hC sC (I.map φ) := by
  ext x
  rw [Set.mem_preimage, pointsMap_mem_zeroLocusPoints_iff B S hS hA s hC sC α φ hφ I,
    zeroLocusPoints_eq_preimage_pointsToScheme]
  exact Ideal.map_le_iff_le_comap.symm

/-- If `α : Spec C ⟶ Spec A`, which is `Spec` of `φ : A → C`, is étale at every point of
`Spec C` lying over the complement of `V(I)`, then `C` is étale over `A` outside `V(I)`. -/
theorem isEtaleOutside_of_etaleAt {A C : Type u} [CommRing A] [CommRing C]
    (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    (hC : B.Contains (Spec (.of C))) (sC : Spec (.of C) ⟶ S)
    (α : affineOver B S hS hC sC ⟶ affineOver B S hS hA s) (φ : A →+* C)
    (hφ : (BigFppfOver.toScheme B S hS).map α = Spec.map (CommRingCat.ofHom φ)) (I : Ideal A)
    (het : ∀ p : Space.points B S hS (yoneda.obj (affineOver B S hS hC sC)),
      Space.pointsMap B S hS _ (yoneda.map α) p ∉ zeroLocusPoints B S hS hA s I →
        EtaleAt ((BigFppfOver.toScheme B S hS).map α)
          (Space.pointsToScheme B S hS (affineOver B S hS hC sC) p)) :
    letI : Algebra A C := φ.toAlgebra
    Rig.IsEtaleOutside I C := by
  intro q hq
  obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B S hS (affineOver B S hS hC sC) q
  have hp : Space.pointsMap B S hS _ (yoneda.map α) p ∉ zeroLocusPoints B S hS hA s I :=
    fun hmem ↦ hq ((pointsMap_mem_zeroLocusPoints_iff B S hS hA s hC sC α φ hφ I p).mp hmem)
  have h := het p hp
  rw [hφ] at h
  exact mem_etaleLocus_of_etaleAt_specMap φ _ h

/-- **A rig-étale completed map presents the completion.** In the situation of
`formalSpectrumMap_comp_completionComparison_eq`, if the completions `A^` and `C^` are Noetherian
adic and `χ : A^ → C^` is rig-étale, then `α_{/V(I)}` corresponds to a rig-étale map in
`WAdm^{Noeth}`. -/
theorem correspondsToRigEtaleMap_completionSheafMap_of_isRigEtaleHom {A C : Type u}
    [CommRing A] [CommRing C]
    (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    (hC : B.Contains (Spec (.of C))) (sC : Spec (.of C) ⟶ S)
    (α : affineOver B S hS hC sC ⟶ affineOver B S hS hA s) (φ : A →+* C)
    (hφ : (BigFppfOver.toScheme B S hS).map α = Spec.map (CommRingCat.ofHom φ))
    (I : Ideal A) (hI : I.FG) (hI' : (I.map φ).FG)
    [IsTopologicalRing (AdicCompletion I A)]
    [IsLinearTopology (AdicCompletion I A) (AdicCompletion I A)]
    [IsTopologicalRing (AdicCompletion (I.map φ) C)]
    [IsLinearTopology (AdicCompletion (I.map φ) C) (AdicCompletion (I.map φ) C)]
    (hnA : IsNoetherianAdic (AdicCompletion I A))
    (hnC : IsNoetherianAdic (AdicCompletion (I.map φ) C))
    (hwA : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A))
    (χ : ContinuousHom (adicQuotientSystem B S hS hA s I hI)
      (adicQuotientSystem B S hS hC sC (I.map φ) hI'))
    (hχ : χ.toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap C (AdicCompletion (I.map φ) C)).comp φ)
    (hrig : IsRigEtaleHom χ.toRingHom) :
    CorrespondsToRigEtaleMap B S hS
      (Space.completionSheafMap B S hS (yoneda.map α) (zeroLocusPoints B S hS hA s I)) := by
  have hT' := preimage_zeroLocusPoints_eq_zeroLocusPoints_map B S hS hA s hC sC α φ hφ I
  have := isIso_completionComparison_adicQuotientSystem B S hS hA s I hI
  have := isIso_completionComparison_adicQuotientSystem B S hS hC sC (I.map φ) hI'
  let cmp := completionComparison B S hS hA s I (adicQuotientSystem B S hS hA s I hI)
    (quotientSystemCompatible_adicQuotientSystem B S hS hA s I hI)
  let cmp' := completionComparison B S hS hC sC (I.map φ)
    (adicQuotientSystem B S hS hC sC (I.map φ) hI')
    (quotientSystemCompatible_adicQuotientSystem B S hS hC sC (I.map φ) hI')
  let eT := eqToIso (congrArg (Space.completionSheaf B S hS
    (yoneda.obj (affineOver B S hS hC sC))) hT')
  refine ⟨AdicCompletion I A, AdicCompletion (I.map φ) C, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hnA, hnC, hwA, adicQuotientSystem B S hS hA s I hI,
    adicQuotientSystem B S hS hC sC (I.map φ) hI', eT ≪≫ (asIso cmp').symm, (asIso cmp).symm, χ,
    ?_, hrig⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.symm_inv, asIso_hom, Category.assoc]
  change _ = eT.hom ≫ inv cmp' ≫ formalSpectrumMap hwA χ ≫ cmp
  rw [formalSpectrumMap_comp_completionComparison_eq B S hS hA s hC sC α φ hφ I hI hI' hwA χ hχ
    hT', IsIso.inv_hom_id_assoc]
  simp [eT]

/-- **Stacks 0AR2, the affine case.** Let `α : Spec C ⟶ Spec A` be a morphism of affine objects
of the site with `A` Noetherian, locally of finite type, let `T ⊆ |Spec A|` be closed and assume
`α` is étale at every point of `Spec C` lying over the complement of `T`. Then the completion
`α_{/T} : (Spec C)_{/T_C} ⟶ (Spec A)_{/T}` corresponds to a rig-étale map in `WAdm^{Noeth}`.

With `T = V(I)`, the two completions are `Spf (A^)` and `Spf (C^)` for the completions along `I`
and `IC` (Stacks 0GBA (2)), `α_{/T}` is `Spf` of the completed map
(`formalSpectrumMap_comp_completionComparison_eq`), and that map is rig-étale by part (1) of
Stacks 0ALQ (`Rig.isRigEtaleHom_completionMap_of_isEtaleOutside`). -/
theorem correspondsToRigEtaleMap_completionSheafMap_of_etaleAt {A C : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing C]
    (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    (hC : B.Contains (Spec (.of C))) (sC : Spec (.of C) ⟶ S)
    (α : affineOver B S hS hC sC ⟶ affineOver B S hS hA s)
    (hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α))
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA s)))) (hT : IsClosed T)
    (het : ∀ p : Space.points B S hS (yoneda.obj (affineOver B S hS hC sC)),
      Space.pointsMap B S hS _ (yoneda.map α) p ∉ T →
        EtaleAt ((BigFppfOver.toScheme B S hS).map α)
          (Space.pointsToScheme B S hS (affineOver B S hS hC sC) p)) :
    CorrespondsToRigEtaleMap B S hS (Space.completionSheafMap B S hS (yoneda.map α) T) := by
  classical
  obtain ⟨I, rfl⟩ := exists_zeroLocusPoints_eq_of_isClosed B S hS hA s T hT
  obtain ⟨φ, hφ⟩ : ∃ φ : A →+* C,
      (BigFppfOver.toScheme B S hS).map α = Spec.map (CommRingCat.ofHom φ) :=
    let g : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of A) :=
      (BigFppfOver.toScheme B S hS).map α
    ⟨(Spec.preimage g).hom, by
      rw [CommRingCat.ofHom_hom]
      exact (Spec.map_preimage g).symm⟩
  let : Algebra A C := φ.toAlgebra
  have : Algebra.FiniteType A C := by
    have h : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) := hφ ▸ hlft
    exact RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h)
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  -- the completed map is étale off `V(I)`
  have hEt : Rig.IsEtaleOutside I C := isEtaleOutside_of_etaleAt B S hS hA s hC sC α φ hφ I het
  -- the presentations of Stacks 0GBA (2)
  have hI : I.FG := I.fg_of_isNoetherianRing
  have hI' : (I.map φ).FG := (I.map φ).fg_of_isNoetherianRing
  obtain ⟨_, _, hJadic, haA, hwA⟩ := adicCompletion_isAdic I hI
  obtain ⟨_, _, hJ'adic, haC, hwC⟩ := adicCompletion_isAdic (I.map φ) hI'
  have : IsNoetherianRing (AdicCompletion I A) := Stacks.AdicCompletion.NoetherianRing.solution I
  have : IsNoetherianRing (AdicCompletion (I.map φ) C) :=
    Stacks.AdicCompletion.NoetherianRing.solution _
  obtain ⟨hcont, hrig⟩ :=
    Rig.isRigEtaleHom_completionMap_of_isEtaleOutside I hEt hJadic hJ'adic haA haC
  have hsC : Spec.map (CommRingCat.ofHom φ) ≫ s = sC := by
    rw [← hφ]
    exact congrArg (fun h ↦ h.hom) (Over.w α)
  let χ : ContinuousHom (adicQuotientSystem B S hS hA s I hI)
      (adicQuotientSystem B S hS hC sC (I.map φ) hI') :=
    { toRingHom := (AdicCompletion.completionMap (B := C) I).toRingHom
      continuous := hcont
      overS := fun J K h ↦ by
        change Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1
            (AdicCompletion.completionMap (B := C) I).toRingHom h)) ≫
            (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J.1).comp
              (algebraMap A (AdicCompletion I A)))) ≫ s) =
          Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K.1).comp
            (algebraMap C (AdicCompletion (I.map φ) C)))) ≫ sC
        rw [← hsC, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 2 }
  exact correspondsToRigEtaleMap_completionSheafMap_of_isRigEtaleHom B S hS hA s hC sC α φ hφ I
    hI hI' ⟨haA, inferInstance⟩ ⟨haC, inferInstance⟩ hwA χ
    (RingHom.ext fun r ↦ AdicCompletion.completionMap_algebraMap I r) hrig

end Affine

/-! ### Stacks 0AR2 -/

section Global

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of fppf sheaves is deep
/-- Pullbacks of fppf sheaves (instance search times out without this shortcut). -/
local instance hasPullbacks_fppfSheaf_CompletionRigEtaleCharts :
    HasPullbacks (FppfSheaf B S hS) := inferInstance

local instance (priority := high) hasPullback_fppfSheaf_CompletionRigEtaleCharts
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- If `Spec C` is locally Noetherian then `C` is a Noetherian ring. -/
private theorem isNoetherianRing_of_isLocallyNoetherian_spec {C : Type u} [CommRing C]
    (h : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of C))) : IsNoetherianRing C :=
  have : _root_.AlgebraicGeometry.IsNoetherian (Spec (.of C)) := ⟨⟩
  isNoetherian_Spec.mp this

/-- The completion of a locally Noetherian affine object along a closed set of points is an affine
formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_completionSheaf_of_isLocallyNoetherian {C : Type u}
    [CommRing C] {hC : B.Contains (Spec (.of C))} {sC : Spec (.of C) ⟶ S}
    (hCN : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of C)))
    {T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hC sC)))} (hT : IsClosed T) :
    IsAffineFormalAlgebraicSpace B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hC sC)) T) := by
  have := isNoetherianRing_of_isLocallyNoetherian_spec hCN
  exact (isNoetherian_completionSheaf B S hS hC sC T hT).1.1

/-- Precomposing a morphism corresponding to a rig-étale map with an isomorphism keeps it
corresponding to a rig-étale map. -/
theorem correspondsToRigEtaleMap_iso_hom_comp {U U' V : FppfSheaf B S hS} (e : U' ≅ U)
    {t : U ⟶ V} (ht : CorrespondsToRigEtaleMap B S hS t) :
    CorrespondsToRigEtaleMap B S hS (e.hom ≫ t) := by
  obtain ⟨A, R, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, hCA, hCR, hA, D, E, eU, eV, g, rfl, hgP⟩ := ht
  exact ⟨A, R, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, hCA, hCR, hA, D, E, e ≪≫ eU, eV, g, by simp, hgP⟩

/-- The base changes along `f : X' ⟶ X` of a family `a` of maps to `X` whose sheafified universe
lifts are jointly locally surjective have jointly locally surjective sheafified universe lifts. -/
theorem isLocallySurjective_sigmaDesc_sheafifiedULiftMap_pullback_snd
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) {K : Type u}
    {Y : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : ∀ k, Y k ⟶ X)
    (hcov : Sheaf.IsLocallySurjective (Sigma.desc fun j : ULift.{u + 1} K ↦
      Space.sheafifiedULiftMap B S hS (a j.down))) :
    Sheaf.IsLocallySurjective (Sigma.desc fun j : ULift.{u + 1} K ↦
      Space.sheafifiedULiftMap B S hS (pullback.snd (a j.down) f)) := by
  have hbase := Sheaf.isLocallySurjective_sigmaDesc_pullback_snd
    (Space.sheafifiedULiftMap B S hS f)
    (fun j : ULift.{u + 1} K ↦ Space.sheafifiedULiftMap B S hS (a j.down)) hcov
  let e : ∀ j : ULift.{u + 1} K, Space.sheafifiedULift B S hS (pullback (a j.down) f) ≅
      pullback (Space.sheafifiedULiftMap B S hS (a j.down))
        (Space.sheafifiedULiftMap B S hS f) := fun j ↦
    (Space.isPullback_sheafifiedULiftMap_of_isPullback B S hS
      (IsPullback.of_hasPullback (a j.down) f)).isoPullback
  let t : (∐ fun j : ULift.{u + 1} K ↦ Space.sheafifiedULift B S hS (pullback (a j.down) f)) ⟶
      ∐ fun j : ULift.{u + 1} K ↦ pullback (Space.sheafifiedULiftMap B S hS (a j.down))
        (Space.sheafifiedULiftMap B S hS f) :=
    Sigma.desc fun j ↦ (e j).hom ≫ Sigma.ι (fun i : ULift.{u + 1} K ↦
      pullback (Space.sheafifiedULiftMap B S hS (a i.down))
        (Space.sheafifiedULiftMap B S hS f)) j
  have hts : IsSplitEpi t :=
    ⟨⟨Sigma.desc fun j ↦ (e j).inv ≫ Sigma.ι (fun i : ULift.{u + 1} K ↦
        Space.sheafifiedULift B S hS (pullback (a i.down) f)) j,
      Sigma.hom_ext _ _ fun j ↦ by simp [t]⟩⟩
  have hfac : (Sigma.desc fun j : ULift.{u + 1} K ↦
      Space.sheafifiedULiftMap B S hS (pullback.snd (a j.down) f)) =
      t ≫ Sigma.desc fun j : ULift.{u + 1} K ↦ pullback.snd
        (Space.sheafifiedULiftMap B S hS (a j.down)) (Space.sheafifiedULiftMap B S hS f) := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp only [t, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc]
    exact ((Space.isPullback_sheafifiedULiftMap_of_isPullback B S hS
      (IsPullback.of_hasPullback (a j.down) f)).isoPullback_hom_snd).symm
  rw [hfac, Sheaf.isLocallySurjective_iff_epi]
  have : Epi t := hts.epi
  have : Epi (Sigma.desc fun j : ULift.{u + 1} K ↦ pullback.snd
      (Space.sheafifiedULiftMap B S hS (a j.down)) (Space.sheafifiedULiftMap B S hS f)) :=
    (Sheaf.isLocallySurjective_iff_epi _).mp hbase
  exact epi_comp _ _

/-- **The completed charts cover.** If the maps `a k : Y k ⟶ X` jointly cover `X` and, for each
`k`, the maps `b k l` jointly cover `Y k ×_X X'`, then the completions along any set `T'` of points
of `X'` of the composites `Z k l ⟶ X'` are jointly locally surjective. -/
theorem isLocallySurjective_sigmaDesc_completionSheafMap_comp_pullback_snd
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) {K : Type u}
    {Y : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : ∀ k, Y k ⟶ X)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun j : ULift.{u + 1} K ↦
        Space.sheafifiedULiftMap B S hS (a j.down)))
    {L : K → Type u} {Z : ∀ k, L k → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (b : ∀ k l, Z k l ⟶ pullback (a k) f)
    (hbcov : ∀ k, letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun l : ULift.{u + 1} (L k) ↦
        Space.sheafifiedULiftMap B S hS (b k l.down)))
    (T' : Set (Space.points B S hS X')) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc fun x : Σ j : ULift.{u + 1} K, ULift.{u + 1} (L j.down) ↦
      Space.completionSheafMap B S hS (b x.1.down x.2.down ≫ pullback.snd (a x.1.down) f) T') := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine (Sheaf.isLocallySurjective_iff_epi _).mpr (epi_sigmaDesc_completionSheafMap T'
    (fun x : Σ j : ULift.{u + 1} K, ULift.{u + 1} (L j.down) ↦
      b x.1.down x.2.down ≫ pullback.snd (a x.1.down) f) ?_)
  simpa only [Space.sheafifiedULiftMap_comp] using isLocallySurjective_sigmaDesc_comp_sigma
    B S hS (fun j : ULift.{u + 1} K ↦ Space.sheafifiedULiftMap B S hS (pullback.snd (a j.down) f))
    (isLocallySurjective_sigmaDesc_sheafifiedULiftMap_pullback_snd f a hcov)
    (K := fun j ↦ ULift.{u + 1} (L j.down))
    (fun x ↦ Space.sheafifiedULiftMap B S hS (b x.1.down x.2.down)) (fun j ↦ hbcov j.down)

/-- **Completion of a commuting square.** For a commuting square `p ≫ f = g ≫ a` of presheaves
and a set `T` of points of the common target, the completions along the inverse images of `T`
form a commuting square, up to the transport along the equality of the two inverse images. -/
theorem completionSheafMap_comp_eq_of_comm {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : Y' ⟶ X'} {f : X' ⟶ X} {g : Y' ⟶ Y} {a : Y ⟶ X} (h : p ≫ f = g ≫ a)
    (T : Set (Space.points B S hS X)) :
    Space.completionSheafMap B S hS p (Space.pointsMap B S hS X' f ⁻¹' T) ≫
        Space.completionSheafMap B S hS f T =
      eqToHom (congrArg (Space.completionSheaf B S hS Y')
          (Space.preimage_pointsMap_eq_of_comm B S hS h T)) ≫
        Space.completionSheafMap B S hS g (Space.pointsMap B S hS Y a ⁻¹' T) ≫
        Space.completionSheafMap B S hS a T := by
  have := Space.mono_completionSheafInclusion B S hS X T
  apply (cancel_mono (Space.completionSheafInclusion B S hS X T)).1
  have h1 := (Space.isPullback_completionSheafMap B S hS p (Space.pointsMap B S hS X' f ⁻¹' T)).w
  have h2 := (Space.isPullback_completionSheafMap B S hS f T).w
  have h3 := (Space.isPullback_completionSheafMap B S hS g (Space.pointsMap B S hS Y a ⁻¹' T)).w
  have h4 := (Space.isPullback_completionSheafMap B S hS a T).w
  have h5 := Space.completionSheafInclusion_transport B S hS _
    (Space.preimage_pointsMap_eq_of_comm B S hS h T)
  simp only [Category.assoc]
  rw [← h2, ← reassoc_of% h1, ← h4, ← reassoc_of% h3, reassoc_of% h5,
    ← Space.sheafifiedULiftMap_comp, ← Space.sheafifiedULiftMap_comp, h]

/-- **The chart maps of Stacks 0AR2.** In the situation of
`isRigEtale_completionSheafMap_of_isEtale`, let `a : Spec A ⟶ X` be an affine étale chart and
`b : Spec C ⟶ Spec A ×_X X'` an affine étale chart of the fibre product. Then the completion of
the induced `Spec C ⟶ Spec A` along the inverse image of `T` corresponds to a rig-étale map. -/
theorem correspondsToRigEtaleMap_completionSheafMap_chart
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hXN : Space.IsLocallyNoetherian B S hS X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))} {s : Spec (.of A) ⟶ S}
    (a : yoneda.obj (affineOver B S hS hA s) ⟶ X) (ha : Space.IsEtale B S hS a)
    {C : Type u} [CommRing C] {hC : B.Contains (Spec (.of C))} {sC : Spec (.of C) ⟶ S}
    (b : yoneda.obj (affineOver B S hS hC sC) ⟶ pullback a f) (hb : Space.IsEtale B S hS b) :
    CorrespondsToRigEtaleMap B S hS (Space.completionSheafMap B S hS
      (yoneda.map (yoneda.preimage (b ≫ pullback.fst a f)))
      (Space.pointsMap B S hS _ a ⁻¹' T)) := by
  let α := yoneda.preimage (b ≫ pullback.fst a f)
  have hα : yoneda.map α = b ≫ pullback.fst a f := Functor.map_preimage _ _
  have hsq : (b ≫ pullback.snd a f) ≫ f = yoneda.map α ≫ a := by
    simp only [hα, Category.assoc, pullback.condition]
  have hpr : Space.IsEtale B S hS (b ≫ pullback.snd a f) :=
    Space.isEtale_comp B S hS hb
      (Space.isEtale_pullback_snd B S hS hX' hX (isAlgebraicSpace_yoneda B S hS _) a f ha)
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) :=
    hf _ _ _ a α ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).1 hpr)
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).1 ha) hsq.symm
  have : IsNoetherianRing A :=
    isNoetherianRing_of_isLocallyNoetherian_spec (hXN (affineOver B S hS hA s) a ha)
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA s)) :=
    hXN (affineOver B S hS hA s) a ha
  have hAf : Space.IsEtale B S hS
      ((Space.openSubspaceOfPoints B S hS X' (Space.pointsMap B S hS X' f ⁻¹' Tᶜ)).ι ≫ f) := by
    rw [← Space.openComplementRestriction_ι]
    exact Space.isEtale_comp B S hS het (Space.isEtale_ι_of_isOpenSubspace
      (Space.isOpenSubspace_openSubspaceOfPoints B S hS hX Tᶜ hT.isOpen_compl))
  have hpts : ∀ p, Space.pointsMap B S hS X' f (Space.pointsMap B S hS _ (b ≫ pullback.snd a f) p) =
      Space.pointsMap B S hS _ a (Space.pointsMap B S hS _ (yoneda.map α) p) := fun p ↦ by
    rw [← Space.pointsMap_comp_apply, ← Space.pointsMap_comp_apply, hsq]
  refine correspondsToRigEtaleMap_completionSheafMap_of_etaleAt B S hS hA s hC sC α hlft _
    (hT.preimage (Space.continuous_pointsMap B S hS a)) fun p hp ↦
      etaleAt_of_isEtale_restriction B S hS hX' f
        (hT.isOpen_compl.preimage (Space.continuous_pointsMap B S hS f)) hAf
        (b ≫ pullback.snd a f) hpr a ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).1 ha) α
        hsq.symm p ?_
  change Space.pointsMap B S hS X' f (Space.pointsMap B S hS _ (b ≫ pullback.snd a f) p) ∉ T
  rw [hpts]
  exact hp

/-- **Stacks 0AR2, on charts.** In the situation of `isRigEtale_completionSheafMap_of_isEtale`,
given affine étale charts `a k : Spec A_k ⟶ X` covering `X` and, for each `k`, affine étale charts
`b k l : Spec C_kl ⟶ Spec A_k ×_X X'` covering the fibre product, `f_{/T}` is rig-étale. -/
theorem isRigEtale_completionSheafMap_of_charts {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hXN : Space.IsLocallyNoetherian B S hS X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    {K : Type u} {A : K → Type u} [∀ k, CommRing (A k)] {hA : ∀ k, B.Contains (Spec (.of (A k)))}
    {str : ∀ k, Spec (.of (A k)) ⟶ S} (a : ∀ k, yoneda.obj (affineOver B S hS (hA k) (str k)) ⟶ X)
    (haet : ∀ k, Space.IsEtale B S hS (a k))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun i : ULift.{u + 1} K ↦
        Space.sheafifiedULiftMap B S hS (a i.down)))
    {L : K → Type u} {C : ∀ k, L k → Type u} [∀ k l, CommRing (C k l)]
    {hC : ∀ k l, B.Contains (Spec (.of (C k l)))} {strC : ∀ k l, Spec (.of (C k l)) ⟶ S}
    (b : ∀ k l, yoneda.obj (affineOver B S hS (hC k l) (strC k l)) ⟶ pullback (a k) f)
    (hbet : ∀ k l, Space.IsEtale B S hS (b k l))
    (hbcov : ∀ k, letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun i : ULift.{u + 1} (L k) ↦
        Space.sheafifiedULiftMap B S hS (b k i.down))) :
    IsRigEtale B S hS (Space.completionSheafMap B S hS f T) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- the chart maps
  let pr : ∀ k l, yoneda.obj (affineOver B S hS (hC k l) (strC k l)) ⟶ X' := fun k l ↦
    b k l ≫ pullback.snd (a k) f
  let α : ∀ k l, affineOver B S hS (hC k l) (strC k l) ⟶ affineOver B S hS (hA k) (str k) :=
    fun k l ↦ yoneda.preimage (b k l ≫ pullback.fst (a k) f)
  have hsq : ∀ k l, pr k l ≫ f = yoneda.map (α k l) ≫ a k := fun k l ↦ by
    simp only [pr, α, Functor.map_preimage, Category.assoc, pullback.condition]
  have hpr : ∀ k l, Space.IsEtale B S hS (pr k l) := fun k l ↦
    Space.isEtale_comp B S hS (hbet k l)
      (Space.isEtale_pullback_snd B S hS hX' hX (isAlgebraicSpace_yoneda B S hS _) (a k) f
        (haet k))
  -- the covering of `X'_{/T'}`
  let uc : ∀ x : Σ j : ULift.{u + 1} K, ULift.{u + 1} (L j.down),
      _ ⟶ Space.completionSheaf B S hS X' (Space.pointsMap B S hS X' f ⁻¹' T) :=
    fun x ↦ Space.completionSheafMap B S hS (pr x.1.down x.2.down) _
  let tc : ∀ x : Σ j : ULift.{u + 1} K, ULift.{u + 1} (L j.down), _ ⟶ Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS (hA x.1.down) (str x.1.down)))
      (Space.pointsMap B S hS _ (a x.1.down) ⁻¹' T) := fun x ↦
    eqToHom (congrArg (Space.completionSheaf B S hS _)
        (Space.preimage_pointsMap_eq_of_comm B S hS (hsq x.1.down x.2.down) T)) ≫
      Space.completionSheafMap B S hS (yoneda.map (α x.1.down x.2.down)) _
  refine (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover B S hS _
      ⟨_, _, uc, ⟨fun x ↦ ?_, fun x ↦ ?_, ?_⟩, fun x ↦ ⟨_, _, tc x, ?_, ?_,
        (completionSheafMap_comp_eq_of_comm (hsq x.1.down x.2.down) T).trans
          (Category.assoc _ _ _).symm, ?_⟩⟩)
  -- the members of the covering are affine and representable étale
  · exact isAffineFormalAlgebraicSpace_completionSheaf_of_isLocallyNoetherian
      (isLocallyNoetherian_of_isLocallyOfFiniteType hX' hX f hf hXN _ (pr x.1.down x.2.down)
        (hpr x.1.down x.2.down))
      ((hT.preimage (Space.continuous_pointsMap B S hS f)).preimage
        (Space.continuous_pointsMap B S hS _))
  · exact isEtale_completionSheafMap B S hS (isAlgebraicSpace_yoneda B S hS _) hX' _ _
      (hpr x.1.down x.2.down)
  -- the covering is jointly surjective
  · exact isLocallySurjective_sigmaDesc_completionSheafMap_comp_pullback_snd f a hcov b hbcov
      (Space.pointsMap B S hS X' f ⁻¹' T)
  · exact isAffineFormalAlgebraicSpace_completionSheaf_of_isLocallyNoetherian
      (hXN _ (a x.1.down) (haet x.1.down))
      (hT.preimage (Space.continuous_pointsMap B S hS (a x.1.down)))
  · exact isEtale_completionSheafMap B S hS (isAlgebraicSpace_yoneda B S hS _) hX (a x.1.down) T
      (haet x.1.down)
  -- the factorizations through the charts of `X_{/T}`
  · exact correspondsToRigEtaleMap_iso_hom_comp
      (eqToIso (congrArg (Space.completionSheaf B S hS _)
        (Space.preimage_pointsMap_eq_of_comm B S hS (hsq x.1.down x.2.down) T)))
      (correspondsToRigEtaleMap_completionSheafMap_chart hX' hX f T hT hXN hf het (a x.1.down)
        (haet x.1.down) (b x.1.down x.2.down) (hbet x.1.down x.2.down))

/-- **Stacks 0AR2.** Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S`, let `T ⊆ |X|`
be closed and let `U' ⟶ U` be the restriction of `f` to the open complements of `T' = |f|⁻¹T`
and `T`. If `X` is locally Noetherian, `f` is locally of finite type and `U' ⟶ U` is étale, then
`f_{/T} : X'_{/T'} ⟶ X_{/T}` is rig-étale.

The proof is the source's, through condition (4) of Stacks 0GCZ. Cover `X` by affine étale
charts `Spec A_k ⟶ X` (`exists_affine_etale_charts`) and each `Spec A_k ×_X X'` by affine étale
charts `Spec C_kl`; the completions `(Spec C_kl)_{/T}` cover `X'_{/T'}` (Stacks 0APV), each
factors through the chart `(Spec A_k)_{/T}` of `X_{/T}` by the completion of
`Spec C_kl ⟶ Spec A_k`, and that completion corresponds to a rig-étale map by the affine case
(`correspondsToRigEtaleMap_completionSheafMap_of_etaleAt`, which is part (1) of Stacks 0ALQ):
the chart map `Spec C_kl ⟶ Spec A_k` is locally of finite type, `A_k` is Noetherian, and the
chart map is étale over the complement of `T` because `U' ⟶ U` is. -/
@[stacks 0AR2]
theorem isRigEtale_completionSheafMap_of_isEtale {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hXN : Space.IsLocallyNoetherian B S hS X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T)) :
    IsRigEtale B S hS (Space.completionSheafMap B S hS f T) := by
  -- the affine étale charts of `X`
  obtain ⟨U₀, K, A, _, hA, str, a, -, -, haet, hcov⟩ := exists_affine_etale_charts hX
  -- the affine étale charts of the fibre products `Spec A_k ×_X X'`
  choose U₁ L C instC hC strC b hLsize hCsize hbet hbcov using fun k ↦
    exists_affine_etale_charts
      (isAlgebraicSpace_pullback B S hS (a k) f (isAlgebraicSpace_yoneda B S hS _) hX' hX)
  exact isRigEtale_completionSheafMap_of_charts hX' hX f T hT hXN hf het a haet hcov b hbet hbcov

end Global

end AlgebraicGeometry.FormalSpace

end
