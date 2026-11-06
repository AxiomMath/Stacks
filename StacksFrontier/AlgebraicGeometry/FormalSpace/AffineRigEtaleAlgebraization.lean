module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputProper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
import StacksFrontier.RingTheory.Rig.Algebraization.RigEtaleAlgebraization
import StacksFrontier.RingTheory.Rig.RigEtaleOverAdicCompletion
import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical
import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Algebraization of a rig-étale affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X = Spec R` be a Noetherian affine
scheme over `S` in that site and let `T ⊆ |X|` be closed. Stacks 0AR4 says that a rig-étale
morphism `g : W ⟶ X_{/T}` from a Noetherian affine formal algebraic space `W` is the completion of
a finite type morphism of affine schemes `f : X' ⟶ X` which is étale over `X ∖ T`: there is an
isomorphism `X'_{/f⁻¹T} ≅ W` over `X_{/T}`. Moreover, if `g` is étale, then so is `f`. Here `f`
being of finite type is recorded as locally of finite type and quasi-compact, and étaleness over
`X ∖ T` is recorded pointwise, at every point of `X'` lying over the complement of `T`.

## Main results

* `AlgebraicGeometry.FormalSpace.adicQuotientSystem`: the quotient-system presentation of the
  `I`-adic completion of `A` over `S` for a finitely generated `I ⊆ A`.
* `AlgebraicGeometry.FormalSpace.isIso_completionComparison_adicQuotientSystem`: for that
  presentation, the canonical comparison `Spf (A^∧) ⟶ X_{/T}` is an isomorphism.
* `AlgebraicGeometry.FormalSpace.exists_affine_algebraization_of_isRigEtale`: a rig-étale morphism
  from a Noetherian affine formal algebraic space to the completion of a Noetherian affine scheme
  is the completion of a finite type morphism of affine schemes étale away from `T`.

## References

* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### The adic topology on a completion -/

section AdicTopology

/-- The `I`-adic topology of an `A`-module `C` which is an `A`-algebra is the `IC`-adic topology
of the ring `C`. -/
private theorem adicModuleTopology_eq_adicTopology_map
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) : I.adicModuleTopology C = (I.map (algebraMap A C)).adicTopology := by
  let : TopologicalSpace A := I.adicTopology
  apply IsTopologicalAddGroup.ext
  · infer_instance
  · infer_instance
  ext U
  rw [(I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis C)).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff,
    (I.map (algebraMap A C)).hasBasis_nhds_zero_adic.mem_iff]
  refine ⟨fun ⟨_, ⟨n, rfl⟩, hn⟩ ↦ ⟨n, trivial, ?_⟩, fun ⟨n, _, hn⟩ ↦ ⟨_, ⟨n, rfl⟩, ?_⟩⟩ <;>
    simpa only [id_eq, Ideal.smul_top_eq_map, Ideal.map_pow,
      Submodule.coe_restrictScalars] using hn

/-- With its `I`-adic module topology, the `I`-adic completion of `A` for a finitely generated
`I` is an adic, weakly admissible, linearly topologized topological ring, its topology being the
`IA^∧`-adic one. -/
private theorem adicCompletion_isAdic {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) :
    letI : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
    ∃ (_ : IsTopologicalRing (AdicCompletion I A))
      (_ : IsLinearTopology (AdicCompletion I A) (AdicCompletion I A)),
      _root_.IsAdic (I.map (algebraMap A (AdicCompletion I A))) ∧
        TopologicalRing.IsAdic (AdicCompletion I A) ∧
          TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A) := by
  rw [adicModuleTopology_eq_adicTopology_map I]
  let J := I.map (algebraMap A (AdicCompletion I A))
  let : TopologicalSpace (AdicCompletion I A) := J.adicTopology
  have hJ : _root_.IsAdic J := rfl
  let : IsLinearTopology (AdicCompletion I A) (AdicCompletion I A) := J.isLinearTopology
  let : UniformSpace (AdicCompletion I A) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (AdicCompletion I A) := isUniformAddGroup_of_addCommGroup
  have hc := hJ.isAdicComplete_iff.mp (AdicCompletion.isAdicComplete_self I hI)
  have hd := TopologicalRing.isIdealOfDefinition_of_isAdic hJ
  exact ⟨inferInstance, inferInstance, hJ, ⟨⟨J, hd, hJ⟩, hc.2, hc.1⟩,
    TopologicalRing.isWeaklyAdmissible_of_isAdic hJ (AdicCompletion.isAdicComplete_self I hI)⟩

/-- With its `I`-adic module topology, the `I`-adic completion of `A` for a finitely generated
`I` is an adic, weakly admissible, linearly topologized topological ring, its topology being the
`IA^∧`-adic one. -/
alias exists_isTopologicalRing_isAdic_adicCompletion := adicCompletion_isAdic

end AdicTopology

/-! ### The quotient-system presentation of `A^∧` and Stacks 0GBA (2) -/

section QuotientSystem

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A]

local instance instTopologicalSpaceAdicCompletion (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

/-- The quotient-system presentation of the `I`-adic completion `A^∧` of `A`, with its `I`-adic
topology, as a topological ring over `S`, for a finitely generated `I`: the structure morphism of
the quotient `A^∧ ⧸ J` by a weak ideal of definition is the one induced by `A → A^∧ ⧸ J`. -/
def adicQuotientSystem (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : I.FG) : AdicQuotientSystem B S hS I where
  inSite J := by
    have hsurj : Function.Surjective
        ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))) := by
      let : TopologicalSpace A := I.adicTopology
      obtain ⟨-, ⟨n, rfl⟩, hn⟩ :=
        (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis
          (AdicCompletion I A))).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp
          (J.2.1.mem_nhds J.1.zero_mem)
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨a, ha⟩ := (I ^ n • (⊤ : Submodule A A)).mkQ_surjective
        (AdicCompletion.eval I A n x)
      refine ⟨a, ?_⟩
      apply Ideal.Quotient.eq.mpr
      apply hn
      change algebraMap A (AdicCompletion I A) a - x ∈
        I ^ n • (⊤ : Submodule A (AdicCompletion I A))
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
      change AdicCompletion.eval I A n (algebraMap A (AdicCompletion I A) a - x) = 0
      rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
      exact sub_eq_zero.mpr ha
    have : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))))) :=
      IsClosedImmersion.spec_of_surjective _ hsurj
    exact lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))))) hA
  overS J := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))) ≫ f
  compatible J L h := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

/-- The structure morphisms of `adicQuotientSystem` are the ones induced by `Spec A ⟶ S`. -/
theorem quotientSystemCompatible_adicQuotientSystem (hA : B.Contains (Spec (.of A)))
    (f : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) :
    QuotientSystemCompatible B S hS f I (adicQuotientSystem B S hS hA f I hI) :=
  fun _ ↦ rfl

/-- Let `X = Spec A` be an affine scheme over `S` in the big fppf site and let `T = V(I)` for a
finitely generated ideal `I ⊆ A`. Then the canonical comparison `Spf (A^∧) ⟶ X_{/T}` is an
isomorphism, for the presentation `adicQuotientSystem` of the `I`-adic completion `A^∧`. -/
@[stacks 0GBA "formal spectrum, for the constructed quotient-system presentation \
`AlgebraicGeometry.FormalSpace.adicQuotientSystem` of the completion"]
theorem isIso_completionComparison_adicQuotientSystem (hA : B.Contains (Spec (.of A)))
    (f : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) :
    IsIso (completionComparison B S hS hA f I (adicQuotientSystem B S hS hA f I hI)
      (quotientSystemCompatible_adicQuotientSystem B S hS hA f I hI)) :=
  isIso_completionComparison B S hS hA f I hI _ _

/-- On a quotient stage of `A^∧`, the comparison of Stacks 0GBA (2) followed by the inclusion of
the completion into `Spec A` is the morphism `Spec (A^∧ ⧸ J) ⟶ Spec A` induced by
`A → A^∧ ⧸ J`. -/
@[reassoc]
theorem formalSpectrumInclusion_comp_completionComparison_comp_completionToUpliftedSheaf
    (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S) (I : Ideal A)
    (D : AdicQuotientSystem B S hS I) (hD : QuotientSystemCompatible B S hS f I D)
    (J : { K : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) K }) :
    formalSpectrumInclusion D (OrderDual.toDual J) ≫ completionComparison B S hS hA f I D hD ≫
        completionToUpliftedSheaf (yoneda.obj (affineOver B S hS hA f))
          (isAlgebraicSpace_yoneda B S hS _) (zeroLocusPoints B S hS hA f I) =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (ULift.up (quotientStageToAffine B S hS hA f I D hD J)) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [completionComparison_stage, quotientStageToCompletion]
  refine (Sheaf.sectionEquiv_symm_comp (BigFppfOver.topology B S hS) _ _).symm.trans ?_
  exact congrArg _ (congrArg (fun φ ↦ φ.app
      (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))
      ⟨⟨quotientStageToAffine B S hS hA f I D hD J⟩,
        quotientStage_hasImageIn B S hS hA f I D hD J⟩)
    (Space.toSheafify_comp_completionSheafToAmbient B S hS (yoneda.obj (affineOver B S hS hA f))
      (upliftedSheaf (yoneda.obj (affineOver B S hS hA f))
        (isAlgebraicSpace_yoneda B S hS _)).property (zeroLocusPoints B S hS hA f I)))

/-- The completion of a Noetherian affine scheme along a closed subset is the formal spectrum of
a Noetherian adic ring: for `T = V(I)` it is `Spf (A^∧)` for the quotient-system presentation
`adicQuotientSystem` of the `I`-adic completion `A^∧`. -/
theorem exists_formalSpectrum_iso_completionSheaf {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA f))))
    (hT : @IsClosed _ (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))) T) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : TopologicalSpace A') (_ : IsTopologicalRing A')
      (_ : IsLinearTopology A' A') (_ : TopologicalRing.IsAdic A' ∧ IsNoetherianRing A')
      (D : QuotientSystem B S hS A'),
      Nonempty (formalSpectrum D ≅
        Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f)) T) := by
  obtain ⟨I, rfl⟩ := exists_zeroLocusPoints_eq_of_isClosed B S hS hA f T hT
  have hI : I.FG := I.fg_of_isNoetherianRing
  let : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
  obtain ⟨htA, hlA, -, haA, -⟩ := adicCompletion_isAdic I hI
  have : IsNoetherianRing (AdicCompletion I A) := Stacks.AdicCompletion.NoetherianRing.solution I
  have := isIso_completionComparison_adicQuotientSystem B S hS hA f I hI
  exact ⟨AdicCompletion I A, inferInstance, _, htA, hlA, ⟨haA, inferInstance⟩,
    adicQuotientSystem B S hS hA f I hI, ⟨asIso (completionComparison B S hS hA f I
      (adicQuotientSystem B S hS hA f I hI)
      (quotientSystemCompatible_adicQuotientSystem B S hS hA f I hI))⟩⟩

end QuotientSystem

/-! ### Étaleness at a point of the spectrum of an algebra -/

/-- A morphism `Spec R' ⟶ Spec R` of finite presentation is étale at every point of the étale
locus of `R'` over `R`. -/
private theorem etaleAt_specMap_of_mem_etaleLocus {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] [Algebra.FinitePresentation R R'] (x : PrimeSpectrum R')
    (hx : x ∈ Algebra.etaleLocus R R') :
    EtaleAt (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x := by
  have : Algebra.IsEtaleAt R x.asIdeal := hx
  obtain ⟨g, hg, hge⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) x.asIdeal
  obtain ⟨y, rfl⟩ : x ∈ Set.range
      (PrimeSpectrum.comap (algebraMap R' (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hg
  let j := Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away g)))
  have hcomp : j ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have het : Etale (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [hcomp]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hge)
  exact Stacks.FundamentalGroup.ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp j _ y
    ((etale_iff_forall_etaleAt _).mp het y)

/-! ### Stacks 0AR4 -/

section Algebraization

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- Discrete limits of presheaves on the big fppf site (instance search times out without
this shortcut in Lean v4.35.0). -/
local instance (priority := high) hasLimitsOfShape_discrete_affineRigEtaleAlgebraization
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- A continuous homomorphism over the base between two topological `R`-algebras whose quotient
systems have the structure morphisms induced by a fixed `Spec R ⟶ S`, given by an `R`-algebra
map. -/
private def continuousHomOfAlgHom {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace C] [Algebra R A] [Algebra R C]
    (s : Spec (.of R) ⟶ S) (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (hD : ∀ J, D.overS J = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk J.1).comp (algebraMap R A))) ≫ s)
    (hE : ∀ K, E.overS K = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk K.1).comp (algebraMap R C))) ≫ s)
    (g : A →ₐ[R] C) (hg : Continuous g) : ContinuousHom D E where
  toRingHom := g.toRingHom
  continuous := hg
  overS J K h := by
    rw [hD, hE, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact congrArg (Ideal.Quotient.mk K.1) (g.commutes r)

/-- The identity of a topological ring, as a continuous homomorphism over the base. -/
private def continuousHomId {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A) : ContinuousHom D D where
  toRingHom := RingHom.id A
  continuous := continuous_id
  overS J K h := D.compatible J K h

/-- An isomorphism of topological `R`-algebras whose quotient systems have the structure
morphisms induced by a fixed `Spec R ⟶ S` induces an isomorphism of formal spectra. -/
private def formalSpectrumIsoOfAlgEquiv {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] [TopologicalSpace A] [TopologicalSpace C] [Algebra R A] [Algebra R C]
    [IsTopologicalRing A] [IsLinearTopology A A] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (s : Spec (.of R) ⟶ S) (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (hD : ∀ J, D.overS J = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk J.1).comp (algebraMap R A))) ≫ s)
    (hE : ∀ K, E.overS K = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk K.1).comp (algebraMap R C))) ≫ s)
    (e : A ≃ₐ[R] C) (he : Continuous e) (he' : Continuous e.symm) :
    formalSpectrum E ≅ formalSpectrum D where
  hom := formalSpectrumMap hA (continuousHomOfAlgHom B S hS s D E hD hE e.toAlgHom he)
  inv := formalSpectrumMap hC (continuousHomOfAlgHom B S hS s E D hE hD e.symm.toAlgHom he')
  hom_inv_id := by
    rw [formalSpectrumMap_comp hC hA _ _ (continuousHomId B S hS E)
      (by ext x; exact (e.apply_symm_apply x).symm)]
    exact formalSpectrumMap_id hC _ rfl
  inv_hom_id := by
    rw [formalSpectrumMap_comp hA hC _ _ (continuousHomId B S hS D)
      (by ext x; exact (e.symm_apply_apply x).symm)]
    exact formalSpectrumMap_id hA _ rfl

/-- Let `X = Spec R` be a Noetherian affine scheme over `S` in the big fppf
site, let `T ⊆ |X|` be closed, let `W` be a Noetherian affine formal algebraic space and let
`g : W ⟶ X_{/T}` be rig-étale. Then there are an affine scheme `X'` and a morphism
`f : X' ⟶ X` of finite type (locally of finite type and quasi-compact), étale at every point
lying over `X ∖ T`, and an isomorphism `X'_{/f⁻¹T} ≅ W` compatible with `f_{/T}` and `g`.
Moreover, if `g` is étale, that is representable by algebraic spaces and étale, then `f` is
étale. -/
@[stacks 0AR4]
theorem exists_affine_algebraization_of_isRigEtale
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (hWaff : IsAffineFormalAlgebraicSpace B S hS W)
    (hWnoeth : IsNoetherian B S hS W)
    (g : W ⟶ Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T)
    (hg : IsRigEtale B S hS g) :
    ∃ (X' : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj X'))
      (f : X' ⟶ affineOver B S hS hR s)
      (e : Space.completionSheaf B S hS (yoneda.obj X')
          (Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) ⁻¹' T) ≅ W),
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f) ∧
      QuasiCompact ((BigFppfOver.toScheme B S hS).map f) ∧
      (∀ p : Space.points B S hS (yoneda.obj X'),
        Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) p ∉ T →
          EtaleAt ((BigFppfOver.toScheme B S hS).map f) (Space.pointsToScheme B S hS X' p)) ∧
      e.hom ≫ g = Space.completionSheafMap B S hS (yoneda.map f) T ∧
      (IsRepresentableEtale B S hS g → Etale ((BigFppfOver.toScheme B S hS).map f)) := by
  classical
  obtain ⟨I, rfl⟩ := exists_zeroLocusPoints_eq_of_isClosed B S hS hR s T hT
  have hI : I.FG := I.fg_of_isNoetherianRing
  let X := affineOver B S hS hR s
  let A := AdicCompletion I R
  let : TopologicalSpace A := I.adicModuleTopology A
  obtain ⟨htA, hlA, hJadic, haA, hwA⟩ := adicCompletion_isAdic I hI
  have : IsNoetherianRing A := Stacks.AdicCompletion.NoetherianRing.solution I
  let D := adicQuotientSystem B S hS hR s I hI
  let hD := quotientSystemCompatible_adicQuotientSystem B S hS hR s I hI
  have := isIso_completionComparison_adicQuotientSystem B S hS hR s I hI
  let cmp := completionComparison B S hS hR s I D hD
  let V := Space.completionSheaf B S hS (yoneda.obj X) (zeroLocusPoints B S hS hR s I)
  have hVaff : IsAffineFormalAlgebraicSpace B S hS V :=
    (isNoetherian_completionSheaf B S hS hR s (zeroLocusPoints B S hS hR s I) hT).1.1
  obtain ⟨-, C, _, tC, htC, hlC, ⟨hwC, ⟨P⟩⟩, hnC, haC⟩ := hWnoeth
  let E := P.quotientSystem
  let eW : W ≅ formalSpectrum E := P.formalSpectrumIso
  obtain ⟨φ, hφ, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hwA hwC (eW.inv ≫ g ≫ inv cmp)
  have hφg : formalSpectrumMap hwA φ ≫ cmp = eW.inv ≫ g := by
    rw [hφ]
    simp
  have hφrig : RingHom.IsRigEtale φ.toRingHom := by
    obtain ⟨hrW, heW⟩ := isRepresentableEtale_id B S hS W
    obtain ⟨hrV, heV⟩ := isRepresentableEtale_id B S hS V
    exact hg W V hWaff hVaff (𝟙 W) (𝟙 V) g hrW hrV heW heV (by simp) A C haA haC hwA D E eW
      (asIso cmp).symm φ (by rw [hφ]; simp)
  have hJdef : TopologicalRing.IsIdealOfDefinition (I.map (algebraMap R A)) :=
    TopologicalRing.isIdealOfDefinition_of_isAdic hJadic
  have hφJ := ((Rig.rigEtaleOver_iff_forall_idealOfDefinition φ.toRingHom φ.continuous haA
    haC).mp hφrig).2 _ hJdef
  have hCadic : _root_.IsAdic ((I.map (algebraMap R A)).map φ.toRingHom) :=
    (hφrig.1 _ hJdef).1
  have hCR := Rig.isRigEtaleOver_comp_algebraMap_of_isRigEtaleOver I φ.toRingHom hφJ
  let : Algebra R C := (φ.toRingHom.comp (algebraMap R A)).toAlgebra
  obtain ⟨hcR, hfR, hrigR⟩ := hCR
  obtain ⟨R', _, _, hftR', hetR', ⟨eR'⟩⟩ :=
    (Rig.isRigEtale_iff_exists_isEtaleOutside_algEquiv
      (Rig.AdicFiniteTypeAlgebra.of (I := I) C hcR)).mp hrigR
  change C ≃ₐ[R] AdicCompletion (I.map (algebraMap R R')) R' at eR'
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have : Algebra.FinitePresentation R R' := Algebra.FinitePresentation.of_finiteType.mp hftR'
  have hR' : B.Contains (Spec (.of R')) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R R' hR
  let s' := Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ s
  let X' := affineOver B S hS hR' s'
  let f : X' ⟶ X := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  have hfmap : (BigFppfOver.toScheme B S hS).map f =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) := rfl
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr hftR')
  have hX'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj X') :=
    inferInstanceAs (IsAffine (Spec (.of R')))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj X) :=
    inferInstanceAs (IsAffine (Spec (.of R)))
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map f) := inferInstance
  let I' := I.map (algebraMap R R')
  have hI' : I'.FG := I'.fg_of_isNoetherianRing
  have hT' : Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) ⁻¹'
      zeroLocusPoints B S hS hR s I = zeroLocusPoints B S hS hR' s' I' := by
    rw [zeroLocusPoints_eq_preimage_pointsToScheme, zeroLocusPoints_eq_preimage_pointsToScheme]
    ext x
    show Space.pointsToScheme B S hS X (Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) x)
        ∈ PrimeSpectrum.zeroLocus (I : Set R) ↔
      Space.pointsToScheme B S hS X' x ∈ PrimeSpectrum.zeroLocus (I' : Set R')
    rw [Space.pointsToScheme_pointsMap, hfmap]
    show I ≤ Ideal.comap (algebraMap R R') _ ↔ I' ≤ _
    exact Ideal.map_le_iff_le_comap.symm
  let A' := AdicCompletion I' R'
  let : TopologicalSpace A' := I'.adicModuleTopology A'
  obtain ⟨htA', hlA', hJ'adic, haA', hwA'⟩ := adicCompletion_isAdic I' hI'
  let D' := adicQuotientSystem B S hS hR' s' I' hI'
  let hD' := quotientSystemCompatible_adicQuotientSystem B S hS hR' s' I' hI'
  have := isIso_completionComparison_adicQuotientSystem B S hS hR' s' I' hI'
  let cmp' := completionComparison B S hS hR' s' I' D' hD'
  have hCE : ∀ K, E.overS K = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk K.1).comp (algebraMap R C))) ≫ s := by
    intro K
    obtain ⟨Jw, hJw⟩ := exists_isWeakIdealOfDefinition_le_comap hwA.1 φ.toRingHom φ.continuous K
    rw [← φ.overS Jw K hJw]
    show Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJw)) ≫
        (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk Jw.1).comp (algebraMap R A))) ≫ s) = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hD'R : ∀ K, D'.overS K = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk K.1).comp (algebraMap R A'))) ≫ s := by
    intro K
    show Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K.1).comp (algebraMap R' A'))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ s = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
  have hmapC : (I.map (algebraMap R A)).map φ.toRingHom = I.map (algebraMap R C) := by
    rw [Ideal.map_map]
    rfl
  have hmapA' : (I.map (algebraMap R C)).map eR'.toRingHom = I'.map (algebraMap R' A') := by
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    exact RingHom.ext eR'.commutes
  have hecont : Continuous eR' :=
    continuous_of_isAdic_of_map_le (hmapC ▸ hCadic) hJ'adic eR'.toRingHom hmapA'.le
  have hecont' : Continuous eR'.symm := by
    refine continuous_of_isAdic_of_map_le hJ'adic (hmapC ▸ hCadic) eR'.symm.toRingHom ?_
    have hcomp : eR'.symm.toRingHom.comp eR'.toRingHom = RingHom.id C :=
      RingHom.ext fun x ↦ eR'.symm_apply_apply x
    rw [← hmapA', Ideal.map_map, hcomp, Ideal.map_id]
  let eSpf := formalSpectrumIsoOfAlgEquiv B S hS hwC hwA' s E D' hCE hD'R eR' hecont hecont'
  let eT := eqToIso (congrArg (Space.completionSheaf B S hS (yoneda.obj X')) hT')
  let e : Space.completionSheaf B S hS (yoneda.obj X')
      (Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) ⁻¹'
        zeroLocusPoints B S hS hR s I) ≅ W :=
    eT ≪≫ (asIso cmp').symm ≪≫ eSpf ≪≫ eW.symm
  have hcompat : e.hom ≫ g = Space.completionSheafMap B S hS (yoneda.map f)
      (zeroLocusPoints B S hS hR s I) := by
    let ιX := completionToUpliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X)
      (zeroLocusPoints B S hS hR s I)
    have : Mono ιX := Sheaf.Hom.mono_of_presheaf_mono _ _
      (h := Space.mono_completionSheafToAmbient B S hS (yoneda.obj X)
        (upliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X)).property
        (zeroLocusPoints B S hS hR s I))
    refine (cancel_mono ιX).mp ?_
    refine (cancel_epi (cmp' ≫ eT.inv)).mp ?_
    refine formalSpectrum_hom_ext D' _ fun K ↦ ?_
    let ψ := continuousHomOfAlgHom B S hS s E D' hCE hD'R eR'.toAlgHom hecont
    let χ := ContinuousHom.comp hwC hwA ψ φ
    obtain ⟨Jw, hJw⟩ := exists_isWeakIdealOfDefinition_le_comap hwA.1 χ.toRingHom χ.continuous K
    have h1 : (cmp' ≫ eT.inv) ≫ e.hom = eSpf.hom ≫ eW.inv := by
      simp [e]
    have h2 : eSpf.hom ≫ eW.inv ≫ g = formalSpectrumMap hwA χ ≫ cmp := by
      rw [← hφg, ← Category.assoc]
      exact congrArg (· ≫ cmp) (formalSpectrumMap_comp_eq hwC hwA ψ φ)
    have key1 : (cmp' ≫ eT.inv) ≫ (e.hom ≫ g) ≫ ιX = formalSpectrumMap hwA χ ≫ cmp ≫ ιX :=
      calc (cmp' ≫ eT.inv) ≫ (e.hom ≫ g) ≫ ιX = ((cmp' ≫ eT.inv) ≫ e.hom) ≫ g ≫ ιX := by
            simp only [Category.assoc]
        _ = (eSpf.hom ≫ eW.inv ≫ g) ≫ ιX := by rw [h1]; simp only [Category.assoc]
        _ = formalSpectrumMap hwA χ ≫ cmp ≫ ιX := by rw [h2, Category.assoc]
    have key2 : (cmp' ≫ eT.inv) ≫ Space.completionSheafMap B S hS (yoneda.map f)
        (zeroLocusPoints B S hS hR s I) ≫ ιX =
        cmp' ≫ completionToUpliftedSheaf (yoneda.obj X') (isAlgebraicSpace_yoneda B S hS X')
          (zeroLocusPoints B S hS hR' s' I') ≫
          (ObjectProperty.homMk (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1}) :
            upliftedSheaf (yoneda.obj X') (isAlgebraicSpace_yoneda B S hS X') ⟶
              upliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X)) := by
      rw [completionSheafMap_comp_completionToUpliftedSheaf (isAlgebraicSpace_yoneda B S hS X')
        (isAlgebraicSpace_yoneda B S hS X), Category.assoc, ← Category.assoc eT.inv,
        eqToIso.inv, eqToHom_comp_completionToUpliftedSheaf (isAlgebraicSpace_yoneda B S hS X')
          hT'.symm]
    let Yf := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
    let ιX' := completionToUpliftedSheaf (yoneda.obj X') (isAlgebraicSpace_yoneda B S hS X')
      (zeroLocusPoints B S hS hR' s' I')
    let upl : upliftedSheaf (yoneda.obj X') (isAlgebraicSpace_yoneda B S hS X') ⟶
        upliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X) :=
      ObjectProperty.homMk (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1})
    have hmor : (BigAffineFppf.inclusion B S hS).map (χ.stageMap Jw K hJw) ≫
        quotientStageToAffine B S hS hR s I D hD Jw =
        quotientStageToAffine B S hS hR' s' I' D' hD' K ≫ f := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      show Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 χ.toRingHom hJw)) ≫
          Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk Jw.1).comp (algebraMap R A))) =
        Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K.1).comp (algebraMap R' A'))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R'))
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      show Ideal.Quotient.mk K.1 (eR' (algebraMap R C r)) =
        Ideal.Quotient.mk K.1 (algebraMap R' A' (algebraMap R R' r))
      rw [eR'.commutes, ← IsScalarTower.algebraMap_apply]
    have hl : formalSpectrumInclusion D' (OrderDual.toDual K) ≫ formalSpectrumMap hwA χ ≫
        cmp ≫ ιX = (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
          (ULift.up ((BigAffineFppf.inclusion B S hS).map (χ.stageMap Jw K hJw) ≫
            quotientStageToAffine B S hS hR s I D hD Jw)) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ cmp ≫ ιX) (formalSpectrumMap_spec hwA χ Jw K hJw)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (Yf.map ((BigAffineFppf.inclusion B S hS).map (χ.stageMap Jw K hJw)) ≫ ·)
              (formalSpectrumInclusion_comp_completionComparison_comp_completionToUpliftedSheaf
                B S hS hR s I D hD Jw)).trans
              (Sheaf.sectionEquiv_symm_map (BigFppfOver.topology B S hS)
                ((BigAffineFppf.inclusion B S hS).map (χ.stageMap Jw K hJw))
                (F := upliftedSheaf (yoneda.obj X) (isAlgebraicSpace_yoneda B S hS X))
                (ULift.up (quotientStageToAffine B S hS hR s I D hD Jw))).symm)))
    have hr : formalSpectrumInclusion D' (OrderDual.toDual K) ≫ cmp' ≫ ιX' ≫ upl =
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
          (ULift.up (quotientStageToAffine B S hS hR' s' I' D' hD' K ≫ f)) :=
      (formalSpectrumInclusion_comp_completionComparison_comp_completionToUpliftedSheaf_assoc
        B S hS hR' s' I' D' hD' K upl).trans
        (Sheaf.sectionEquiv_symm_comp (BigFppfOver.topology B S hS) upl
          (ULift.up (quotientStageToAffine B S hS hR' s' I' D' hD' K))).symm
    calc formalSpectrumInclusion D' (OrderDual.toDual K) ≫ (cmp' ≫ eT.inv) ≫ (e.hom ≫ g) ≫ ιX
        = formalSpectrumInclusion D' (OrderDual.toDual K) ≫ formalSpectrumMap hwA χ ≫
            cmp ≫ ιX := congrArg (formalSpectrumInclusion D' (OrderDual.toDual K) ≫ ·) key1
      _ = (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
          (ULift.up (quotientStageToAffine B S hS hR' s' I' D' hD' K ≫ f)) :=
        hl.trans (congrArg _ (congrArg ULift.up hmor))
      _ = formalSpectrumInclusion D' (OrderDual.toDual K) ≫ cmp' ≫ ιX' ≫ upl := hr.symm
      _ = _ := congrArg (formalSpectrumInclusion D' (OrderDual.toDual K) ≫ ·) key2.symm
  have haway : ∀ p : Space.points B S hS (yoneda.obj X'),
      Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) p ∉
          zeroLocusPoints B S hS hR s I →
        EtaleAt ((BigFppfOver.toScheme B S hS).map f) (Space.pointsToScheme B S hS X' p) := by
    intro p hp
    rw [zeroLocusPoints_eq_preimage_pointsToScheme] at hp
    change Space.pointsToScheme B S hS X (Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) p)
      ∉ PrimeSpectrum.zeroLocus (I : Set R) at hp
    rw [Space.pointsToScheme_pointsMap, hfmap] at hp
    rw [hfmap]
    exact etaleAt_specMap_of_mem_etaleLocus _ (hetR' hp)
  refine ⟨X', hX'aff, f, e, hlft, hqc, haway, hcompat,
    fun hge ↦ ?_⟩
  have hetale : IsRepresentableEtale B S hS
      (Space.completionSheafMap B S hS (yoneda.map f) (zeroLocusPoints B S hS hR s I)) := by
    rw [← hcompat]
    exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isIso B S hS e.hom) hge
  let i : Spec (.of (R ⧸ I)) ⟶ (BigFppfOver.toScheme B S hS).obj X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : AlgebraicGeometry.IsClosedImmersion i :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj X) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)))
  have hrange : Set.range i =
      Space.pointsToScheme B S hS X '' zeroLocusPoints B S hS hR s I := by
    rw [zeroLocusPoints_eq_preimage_pointsToScheme]
    refine Eq.trans ?_ (Set.image_preimage_eq _ (Space.surjective_pointsToScheme B S hS X)).symm
    show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R)
    ext x
    constructor
    · rintro ⟨y, rfl⟩ a ha
      show Ideal.Quotient.mk I a ∈ y.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact y.asIdeal.zero_mem
    · intro hx
      have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ x.asIdeal := by rwa [Ideal.mk_ker]
      refine ⟨⟨x.asIdeal.map (Ideal.Quotient.mk I),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩, ?_⟩
      ext a
      show Ideal.Quotient.mk I a ∈ x.asIdeal.map (Ideal.Quotient.mk I) ↔ a ∈ x.asIdeal
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
      refine ⟨?_, fun ha ↦ ⟨a, ha, rfl⟩⟩
      rintro ⟨b, hb, hab⟩
      have hd : b - a ∈ x.asIdeal := hker (by rw [RingHom.mem_ker, map_sub, hab, sub_self])
      simpa using x.asIdeal.sub_mem hb hd
  have hlocft : Space.IsLocallyOfFiniteType B S hS (yoneda.map f) := by
    intro U V a b k ha hb hk
    obtain ⟨a', rfl⟩ := yoneda.map_surjective a
    obtain ⟨b', rfl⟩ := yoneda.map_surjective b
    have := (Space.presheaf_yoneda_map_etale_iff B S hS b').mp hb
    have := (Space.presheaf_yoneda_map_etale_iff B S hS a').mp ha
    have hk' : k ≫ b' = a' ≫ f := yoneda.map_injective (by simpa using hk)
    have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k ≫
        (BigFppfOver.toScheme B S hS).map b') := by
      rw [← Functor.map_comp, hk', Functor.map_comp]
      infer_instance
    exact locallyOfFiniteType_of_comp _ ((BigFppfOver.toScheme B S hS).map b')
  have hf := isEtale_of_isEtale_completionSheafMap B S hS f (zeroLocusPoints B S hS hR s I)
    i hrange hlocft haway hetale
  rwa [Space.isEtale_iff_presheaf_of_yoneda, Space.presheaf_yoneda_map_etale_iff] at hf

end Algebraization

end AlgebraicGeometry.FormalSpace

end
