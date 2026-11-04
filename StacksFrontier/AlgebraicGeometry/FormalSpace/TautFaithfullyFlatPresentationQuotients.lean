module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFaithfullyFlatPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatOfRepresentableFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentationQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFromRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.TautOpenIdealQuotients

/-!
# Faithfully flat quotients of a taut presentation

A surjective flat morphism of fppf sheaves, representable by algebraic spaces, onto an affine
formal algebraic space is presented by a continuous taut ring homomorphism all of whose maps on
quotients by open ideals are faithfully flat.

## Main results

* `AlgebraicGeometry.Space.flatPropertyULift_respectsIso`: flatness of morphisms of algebraic
  spaces is invariant under isomorphisms.
* `AlgebraicGeometry.FormalSpace.isSurjective_formalSpectrumMap_iff_surjective_stage`: a
  morphism of formal spectra is surjective if and only if it is surjective on a quotient stage.
* `AlgebraicGeometry.FormalSpace.faithfullyFlat_quotientMap_of_surjective_flat_formalSpectrumMap`:
  the stage maps of a taut, surjective, flat morphism of formal spectra are faithfully flat.
* `AlgebraicGeometry.FormalSpace.exists_taut_faithfullyFlatQuotients_of_surjective_flat`: a
  surjective flat morphism onto an affine formal algebraic space is presented by a continuous
  taut homomorphism with faithfully flat quotient maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Flatness in the Bootstrap sense is invariant under isomorphisms of algebraic spaces over
`S` with values in `Type (max w u)`, as being locally of finite type is. -/
instance flatPropertyULift_respectsIso :
    (flatPropertyULift.{w} B S hS).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf ↦ ?_) (fun e f hf ↦ ?_)
  · have := isIso_hom_of_iso B S hS e
    exact holdsOnEveryEtaleChartULift_precomp B S hS _ e.hom.hom f.hom hf
  · have := isIso_hom_of_iso B S hS e
    exact holdsOnEveryEtaleChartULift_postcomp B S hS _ e.hom.hom f.hom hf

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-! ### Surjectivity on a quotient stage -/

/-- A morphism `Spf φ : Spf C ⟶ Spf A` of formal spectra of
weakly admissible topological rings over `S` is surjective exactly when the morphism
`Spec (C ⧸ K) ⟶ Spec (A ⧸ I)` of quotient stages attached to a pair of weak ideals of
definition with `I ⊆ φ⁻¹ K` is surjective. -/
theorem isSurjective_formalSpectrumMap_iff_surjective_stage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (φ : ContinuousHom D E)
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (K : TopologicalRing.WeakIdealOfDefinitionIndex C)
    (hIK : I.1 ≤ Ideal.comap φ.toRingHom K.1) :
    IsSurjective B S hS (formalSpectrumMap hA φ) ↔
      Surjective (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap K.1 φ.toRingHom hIK))) := by
  have hsource := bijective_pointsMapULift_formalSpectrumInclusion B S hS hC E K
  have htarget := bijective_pointsMapULift_formalSpectrumInclusion B S hS hA D I
  have hspec := formalSpectrumMap_spec hA φ I K hIK
  refine (surjective_iff_of_commutes
    (Space.pointsMapULift.{u + 1} B S hS _
      (formalSpectrumInclusion E (OrderDual.toDual K)).hom)
    (Space.pointsMapULift.{u + 1} B S hS _
      (formalSpectrumInclusion D (OrderDual.toDual I)).hom)
    (Space.pointsMapULift.{u + 1} B S hS _
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (φ.stageMap I K hIK))).hom)
    (Space.pointsMapULift.{u + 1} B S hS _ (formalSpectrumMap hA φ).hom)
    hsource htarget fun p ↦ (pointsMapULift_square hspec p).symm).symm.trans
    (surjective_pointsMapULift_sheafifiedYoneda_iff B S hS
      ((BigAffineFppf.inclusion B S hS).map (φ.stageMap I K hIK)))

/-! ### Faithful flatness on the quotient stages -/

/-- The stage maps of a taut morphism of formal spectra which is representable by algebraic
spaces, surjective and flat in the Bootstrap sense are faithfully flat: for every weak ideal
of definition `I` of `A` the ring map `A ⧸ I → C ⧸ closure (I C)` is faithfully flat. -/
theorem faithfullyFlat_quotientMap_of_surjective_flat_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (φ : ContinuousHom D E)
    (hφ : RingHom.IsTaut φ.toRingHom)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hA φ).hom)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS (Space.flatPropertyULift.{u + 1} B S hS)
      (formalSpectrumMap hA φ).hom hrep)
    (hsurj : IsSurjective B S hS (formalSpectrumMap hA φ))
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    (Ideal.quotientMap (Ideal.closure (I.map φ.toRingHom)) φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp subset_closure)).FaithfullyFlat := by
  have hKdef : TopologicalRing.IsWeakIdealOfDefinition
      (Ideal.closure (I.map φ.toRingHom)) :=
    ⟨hφ.1 I hI.1, TopologicalRing.closure_map_le_topologicalNilradical φ.toRingHom
      φ.continuous I hI.2⟩
  have hstage := (isSurjective_formalSpectrumMap_iff_surjective_stage B S hS hA hC D E φ
    ⟨I, hI⟩ ⟨Ideal.closure (I.map φ.toRingHom), hKdef⟩
    (Ideal.map_le_iff_le_comap.mp subset_closure)).mp hsurj
  have hflatStage := flat_quotientMap_of_flatULift_formalSpectrumMap hA hC D E φ hφ hrep
    hflat I hI
  exact (flat_and_surjective_SpecMap_iff _).mp
    ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mpr hflatStage, hstage⟩

/-- Let `f : X ⟶ Y` be a morphism of fppf sheaves over `S` which is representable by
algebraic spaces, surjective and flat, with `Y` an affine formal algebraic space, let `C` be a
presenting ring of `X` and let `A` be a presenting ring of `Y`. Then there is a continuous taut
homomorphism `φ : A → C` all of whose maps `A ⧸ I → C ⧸ closure (I C)` on quotients by open
ideals of `A` are faithfully flat. -/
theorem exists_taut_faithfullyFlatQuotients_of_surjective_flat
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f)
    (hflat : ∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
      Space.HasPropertyULift.{u + 1} B S hS (Space.flatPropertyULift.{u + 1} B S hS) f.hom hf)
    (hC : IsPresentingRing B S hS C X) (hA : IsPresentingRing B S hS A Y) :
    ∃ φ : A →+* C, Continuous φ ∧ RingHom.IsTaut φ ∧
      ∀ I : Ideal A, IsOpen (I : Set A) →
        (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
          (Ideal.map_le_iff_le_comap.mp subset_closure)).FaithfullyFlat := by
  obtain ⟨hfrep, hfflat⟩ := hflat
  obtain ⟨E, ⟨eX⟩⟩ := exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing hC
  obtain ⟨D, ⟨eY⟩⟩ := exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing hA
  have hDaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
    isAffineFormalAlgebraicSpace_of_iso B S hS eY hY
  obtain ⟨φ, hφeq, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hA.1 hC.1 (eX.inv ≫ f ≫ eY.hom)
  have hsq : IsPullback (formalSpectrumMap hA.1 φ) eX.inv eY.inv f := by
    rw [hφeq]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  have hsqp := hsq.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hrep := Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS
    eX.inv.hom (formalSpectrumMap hA.1 φ).hom f.hom eY.inv.hom hsqp hfrep
  have hflat' := Space.hasPropertyULift_of_isPullback B S hS hsqp hfrep hfflat
  have hsurj' : IsSurjective B S hS (formalSpectrumMap hA.1 φ) :=
    IsSurjective.of_isPullback B S hS hsq hsurj
  have htaut : RingHom.IsTaut φ.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap B S hS hA.1 hC.1 D E φ hrep
  exact ⟨φ.toRingHom, φ.continuous, htaut,
    RingHom.faithfullyFlat_closure_quotientMap_of_isOpen hA.1 φ.toRingHom htaut
      (faithfullyFlat_quotientMap_of_surjective_flat_formalSpectrumMap B S hS hA.1 hC.1 D E φ
        htaut hrep hflat' hsurj')⟩

end AlgebraicGeometry.FormalSpace

end
