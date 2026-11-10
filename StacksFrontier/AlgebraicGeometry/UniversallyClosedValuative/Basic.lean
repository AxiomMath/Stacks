module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Limits.UniversallyClosedTest
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksCore.Tactic.StacksAttribute

/-!
# Testing universal closedness over a locally Noetherian scheme

For a finite type morphism whose target is locally Noetherian, universal closedness can be tested
after taking products with finite-dimensional affine spaces, by the existence part of the
valuative criterion, or just on discrete valuation rings.

## Main results

* `AlgebraicGeometry.universallyClosed_tfae_valuative`: the four equivalent criteria for
  universal closedness (Stacks 05JY).

## Implementation notes

A finite type morphism is represented by `LocallyOfFiniteType` together with `QuasiCompact`, and
the morphism `A^n × X ⟶ A^n × S` is the functorial morphism `AffineSpace.map` indexed by
`ULift (Fin n)`. Arbitrary valuative diagrams are represented by `ValuativeCommSq f`; the final
condition restricts their valuation ring to a discrete valuation ring.

## References

* [Stacks Project, Tag 05JY](https://stacks.math.columbia.edu/tag/05JY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If every valuative square for `f` over a discrete valuation ring has a lift, then `f` is a
specializing map. -/
private theorem specializingMap_of_discreteValuativeCriterion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (h : ∀ D : ValuativeCommSq f, IsDiscreteValuationRing D.R → D.commSq.HasLift) :
    SpecializingMap f := by
  intro x' y hxy
  by_cases hne : f x' ≠ y
  · let K := X.residueField x'
    let : Algebra (Y.residueField (f x')) K := (f.residueFieldMap x').hom.toAlgebra
    have : Algebra.EssFiniteType (Y.residueField (f x')) K :=
      RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x')
    obtain ⟨A, _, _, hA_dvr, q, hη, hclosed, e, he⟩ :=
      exists_dvr_morphism_of_specializes_with_residueField_equiv Y hxy (Ne.symm hne) K
    let η := genericPoint (Spec (.of A))
    let K' := FractionRing A
    let : Field K' := FractionRing.field A
    let : IsFractionRing A K' := inferInstance
    let : Algebra A K' := inferInstance
    let : η.asIdeal.IsPrime := η.isPrime
    let baseEquiv : A ⧸ η.asIdeal ≃+* A :=
      (Ideal.quotientEquiv _ ⊥ (RingEquiv.refl A) (by simp [η])).trans
        (RingEquiv.quotientBot A)
    let eFrac : η.asIdeal.ResidueField ≃+* K' :=
      IsFractionRing.ringEquivOfRingEquiv baseEquiv
    let eSpecIso : (Spec (.of A)).residueField η ≅ CommRingCat.of K' :=
      Scheme.Spec.residueFieldIso (.of A) η ≪≫ eFrac.toCommRingCatIso
    let eSpec : (Spec (.of A)).residueField η ≃+* K' :=
      eSpecIso.commRingCatIsoToRingEquiv
    let α : K' ≃+* K := eSpec.symm.trans e
    let i₁ : Spec (.of K') ⟶ X :=
      Spec.map (CommRingCat.ofHom α.symm.toRingHom) ≫ X.fromSpecResidueField x'
    have hgenFrac :
        (Spec.map (CommRingCat.ofHom (algebraMap A K')))
            (genericPoint (Spec (.of K'))) = η := by
      apply PrimeSpectrum.ext
      rw [genericPoint_eq_bot_of_affine (.of K')]
      change Ideal.comap (algebraMap A K') (⊥ : Ideal K') =
        (genericPoint (Spec (.of A))).asIdeal
      rw [genericPoint_eq_bot_of_affine (.of A)]
      ext a
      simp
    have hSpecFrac :
        Spec.map (CommRingCat.ofHom (algebraMap A K')) =
          Spec.map eSpecIso.hom ≫ (Spec (.of A)).fromSpecResidueField η := by
      rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
      simp only [← Spec.map_comp]
      rw [Spec.map_inj]
      ext a
      simp only [eSpecIso, Iso.trans_hom, ConcreteCategory.comp_apply,
        Iso.inv_hom_id_apply]
      change algebraMap A K' a = eFrac (algebraMap A _ a)
      rw [← Ideal.algebraMap_quotient_residueField_mk,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      simp [baseEquiv]
    have hhom :
        f.residueFieldMap x' ≫ CommRingCat.ofHom α.symm.toRingHom =
          (Y.residueFieldCongr hη.symm).hom ≫ q.residueFieldMap η ≫ eSpecIso.hom := by
      apply CommRingCat.hom_ext
      ext a
      change α.symm ((algebraMap (Y.residueField (f x')) K) a) =
        eSpec (q.residueFieldMap η ((Y.residueFieldCongr hη.symm).hom a))
      rw [← he a]
      simp [α, η]
    have hDcomm : i₁ ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap A K')) ≫ q := by
      calc
        i₁ ≫ f =
            Spec.map (f.residueFieldMap x' ≫ CommRingCat.ofHom α.symm.toRingHom) ≫
              Y.fromSpecResidueField (f x') := by
          dsimp [i₁]
          simp only [Category.assoc,
            ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
            ← Spec.map_comp_assoc]
          rfl
        _ = Spec.map
              ((Y.residueFieldCongr hη.symm).hom ≫ q.residueFieldMap η ≫
                eSpecIso.hom) ≫ Y.fromSpecResidueField (f x') := by rw [hhom]
        _ = Spec.map eSpecIso.hom ≫ Spec.map (q.residueFieldMap η) ≫
              Spec.map ((Y.residueFieldCongr hη.symm).hom) ≫
                Y.fromSpecResidueField (f x') := by
          rw [Spec.map_comp_assoc, Spec.map_comp]
          rfl
        _ = Spec.map eSpecIso.hom ≫ Spec.map (q.residueFieldMap η) ≫
              Y.fromSpecResidueField (q η) := by
          simp only [Scheme.residueFieldCongr_fromSpecResidueField hη.symm, η]
        _ = Spec.map eSpecIso.hom ≫ (Spec (.of A)).fromSpecResidueField η ≫ q := by
          simp only [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
        _ = Spec.map (CommRingCat.ofHom (algebraMap A K')) ≫ q := by
          rw [← Category.assoc, ← hSpecFrac]
    let D : ValuativeCommSq f :=
      { R := A
        K := K'
        i₁ := i₁
        i₂ := q
        commSq := ⟨hDcomm⟩ }
    obtain ⟨l, hl₁, hl₂⟩ := h D hA_dvr
    dsimp [D] at l hl₁ hl₂
    let pA : Spec (.of A) := IsLocalRing.closedPoint A
    refine ⟨l pA, ?_, ?_⟩
    · have hgen : l η = x' := by
        have heval := congrArg (fun k : Spec (.of K') ⟶ X => k (genericPoint _)) hl₁
        have hsource : i₁ (genericPoint (Spec (.of K'))) = x' := by
          change X.fromSpecResidueField x'
            ((Spec.map (CommRingCat.ofHom α.symm.toRingHom))
              (genericPoint (Spec (.of K')))) = x'
          simp
        simpa only [Scheme.Hom.comp_apply, hgenFrac, hsource] using heval
      change x' ⤳ l pA
      rw [← hgen]
      exact (IsLocalRing.specializes_closedPoint (R := A) η).map l.continuous
    · have heval := congrArg (fun k : Spec (.of A) ⟶ Y => k pA) hl₂
      have hp : f (l pA) = q pA := by
        simpa only [Scheme.Hom.comp_apply] using heval
      exact hp.trans (by simpa [pA] using hclosed)
  · exact ⟨x', specializes_refl _, Classical.not_not.mp hne⟩

/-- For a finite type morphism to a locally Noetherian scheme, universal closedness, closedness
after adjoining any finite number of affine coordinates, the existence part of the valuative
criterion, and its restriction to discrete valuation rings are equivalent. -/
@[stacks 05JY, ega "II 7.3.8" "fin. type, Noeth. base"]
theorem universallyClosed_tfae_valuative {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian S] :
    List.TFAE
      [ UniversallyClosed f,
        ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f),
        ValuativeCriterion.Existence f,
        ∀ (D : ValuativeCommSq f), IsDiscreteValuationRing D.R → D.commSq.HasLift ] := by
  tfae_have 1 ↔ 2 := (universallyClosed_tfae f).out 1 3
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hu
      rw [UniversallyClosed.eq_valuativeCriterion] at hu
      exact hu.1
    · exact UniversallyClosed.of_valuativeCriterion f
  tfae_have 3 → 4 := fun h D _ ↦ h D
  tfae_have 4 → 2 := by
    intro h n
    let ι := ULift.{u} (Fin n)
    let P := AffineSpace ι X
    let B := AffineSpace ι S
    let g := AffineSpace.map ι f
    let pX : P ⟶ X := (AffineSpace ι X ↘ X)
    let pS : B ⟶ S := (AffineSpace ι S ↘ S)
    let pb := AffineSpace.isPullback_map (n := ι) f
    have : LocallyOfFiniteType g :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback pb.flip inferInstance
    have : QuasiCompact g :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback pb.flip inferInstance
    have : LocallyOfFiniteType pS := inferInstance
    have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian pS
    have hmap : pX ≫ f = g ≫ pS := pb.w.symm
    have hg : ∀ Dg : ValuativeCommSq g, IsDiscreteValuationRing Dg.R →
        Dg.commSq.HasLift := by
      intro Dg hD
      let Df : ValuativeCommSq f :=
        { R := Dg.R
          K := Dg.K
          i₁ := Dg.i₁ ≫ pX
          i₂ := Dg.i₂ ≫ pS
          commSq := ⟨by
            rw [Category.assoc, hmap, ← Category.assoc, Dg.commSq.w, Category.assoc]⟩ }
      obtain ⟨l, hl₁, hl₂⟩ := h Df hD
      let lP := pb.lift Dg.i₂ l hl₂.symm
      have hlP_B : lP ≫ g = Dg.i₂ := pb.lift_fst Dg.i₂ l hl₂.symm
      have hlP_X : lP ≫ pX = l := pb.lift_snd Dg.i₂ l hl₂.symm
      have htop :
          Spec.map (CommRingCat.ofHom (algebraMap Dg.R Dg.K)) ≫ lP = Dg.i₁ := by
        apply pb.hom_ext
        · rw [Category.assoc, hlP_B]
          exact Dg.commSq.w.symm
        · rw [Category.assoc, hlP_X]
          exact hl₁
      exact ⟨⟨lP, htop, hlP_B⟩⟩
    exact (isClosedMap_iff_specializingMap g).2 (specializingMap_of_discreteValuativeCriterion g hg)
  tfae_finish

end AlgebraicGeometry
