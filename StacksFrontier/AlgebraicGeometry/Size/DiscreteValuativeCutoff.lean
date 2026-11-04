module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.UniversallyClosedCutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.UniversallyClosedValuative.Basic

/-!
# The discrete valuative criterion for universal closedness, tested inside the size cutoff

`AlgebraicGeometry.universallyClosed_tfae_valuative` tests universal closedness of a finite type
morphism over a locally Noetherian base on *all* discrete valuation rings in `Type u`. A
condition formulated inside a big fppf site `B` — such as the uniqueness part of the valuative
criterion for a morphism of algebraic spaces, whose valuative squares carry spectra belonging to
the site — provides lifts only for the discrete valuation rings whose spectrum, together with
that of the fraction field, is an object of the site. This file closes that gap: for a morphism
whose source is inside `B`, lifting those squares alone already gives universal closedness.

## Main results

* `AlgebraicGeometry.universallyClosed_of_contained_discreteValuativeCriterion`: the
  size-cutoff form of the discrete valuative criterion for universal closedness.

## Implementation notes

The discrete valuation ring produced by **Stacks 054F** in the proof of
`AlgebraicGeometry.universallyClosed_tfae_valuative` has prescribed generic residue field, and
that field may be taken to be the residue field of the source point. The spectrum of a residue
field of a scheme in the site is in the site, because the morphism from it is a quasi-compact
monomorphism; the fraction field of the valuation ring is isomorphic to that residue field, and
the valuation ring injects into its fraction field, so both spectra are in the site as well.
These are the bounds of `StacksFrontier.AlgebraicGeometry.Size.Cutoff`.

Universal closedness is reached through closedness of the base changes to affine `n`-space, as
in the source tag, so the hypothesis has to be transported to `A^n_X ⟶ A^n_Y`; the transported
valuative squares have the *same* valuation ring and fraction field, so their membership of the
site is unaffected, and affine `n`-space over a scheme in the site is again in the site.

## References

* [Stacks Project, Tag 054F](https://stacks.math.columbia.edu/tag/054F)
* [Stacks Project, Tag 05JY](https://stacks.math.columbia.edu/tag/05JY)
* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The morphism from the spectrum of the fraction field of a domain maps the generic point to
the generic point. -/
theorem Spec_map_algebraMap_genericPoint (A K : Type u) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] :
    Spec.map (CommRingCat.ofHom (algebraMap A K)) (genericPoint (Spec (.of K))) =
      genericPoint (Spec (.of A)) := by
  apply PrimeSpectrum.ext
  rw [genericPoint_eq_bot_of_affine (.of K)]
  show Ideal.comap (algebraMap A K) (⊥ : Ideal K) = (genericPoint (Spec (.of A))).asIdeal
  rw [genericPoint_eq_bot_of_affine (.of A)]
  ext a
  simp

/-- The ideal of the generic point of the spectrum of a domain is prime. -/
instance isPrime_genericPoint_asIdeal (A : Type u) [CommRing A] [IsDomain A] :
    (genericPoint (Spec (.of A))).asIdeal.IsPrime :=
  (genericPoint (Spec (.of A))).isPrime

/-- The residue field of the generic point of a domain `A` is the fraction field of `A`. -/
noncomputable def genericPointResidueFieldEquiv (A : Type u) [CommRing A] [IsDomain A] :
    (genericPoint (Spec (.of A))).asIdeal.ResidueField ≃+* FractionRing A :=
  IsFractionRing.ringEquivOfRingEquiv
    ((Ideal.quotientEquiv (genericPoint (Spec (.of A))).asIdeal ⊥ (RingEquiv.refl A)
      (by simp)).trans (RingEquiv.quotientBot A))

/-- The morphism from the spectrum of the fraction field of a domain `A` to `Spec A` is the
inclusion of the residue field at the generic point. -/
theorem Spec_map_algebraMap_fractionRing (A : Type u) [CommRing A] [IsDomain A] :
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) =
      Spec.map (Scheme.Spec.residueFieldIso (.of A) (genericPoint (Spec (.of A))) ≪≫
          (genericPointResidueFieldEquiv A).toCommRingCatIso).hom ≫
        (Spec (.of A)).fromSpecResidueField _ := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [← Spec.map_comp]
  rw [Spec.map_inj]
  ext a
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  show algebraMap A (FractionRing A) a = genericPointResidueFieldEquiv A (algebraMap A _ a)
  rw [genericPointResidueFieldEquiv, ← Ideal.algebraMap_quotient_residueField_mk,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp

/-- A morphism `q : Spec A ⟶ Y` from the spectrum of a domain, sending the generic point to
`f x'` with an identification of the residue field there with that of `x'` compatible with `f`,
is the bottom of a commutative square for `f` whose top map sends the generic point to `x'`. -/
theorem exists_spec_fractionRing_comp_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x' : X)
    {A : Type u} [CommRing A] [IsDomain A] (q : Spec (.of A) ⟶ Y)
    (hη : q (genericPoint (Spec (.of A))) = f x')
    (e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≃+* X.residueField x')
    (he : ∀ a, e (q.residueFieldMap (genericPoint (Spec (.of A)))
      ((Y.residueFieldCongr hη.symm).hom a)) = (f.residueFieldMap x').hom a) :
    ∃ i₁ : Spec (.of (FractionRing A)) ⟶ X,
      i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ q ∧
        i₁ (genericPoint _) = x' := by
  let η := genericPoint (Spec (.of A))
  let eSpecIso : (Spec (.of A)).residueField η ≅ CommRingCat.of (FractionRing A) :=
    Scheme.Spec.residueFieldIso (.of A) η ≪≫ (genericPointResidueFieldEquiv A).toCommRingCatIso
  let eSpec : (Spec (.of A)).residueField η ≃+* FractionRing A :=
    eSpecIso.commRingCatIsoToRingEquiv
  let α : FractionRing A ≃+* X.residueField x' := eSpec.symm.trans e
  have hhom :
      f.residueFieldMap x' ≫ CommRingCat.ofHom α.symm.toRingHom =
        (Y.residueFieldCongr hη.symm).hom ≫ q.residueFieldMap η ≫ eSpecIso.hom := by
    apply CommRingCat.hom_ext
    ext a
    show α.symm ((f.residueFieldMap x').hom a) =
      eSpec (q.residueFieldMap η ((Y.residueFieldCongr hη.symm).hom a))
    rw [← he a]
    simp [α, η]
  refine ⟨Spec.map (CommRingCat.ofHom α.symm.toRingHom) ≫ X.fromSpecResidueField x', ?_, ?_⟩
  · calc
      _ = Spec.map (f.residueFieldMap x' ≫ CommRingCat.ofHom α.symm.toRingHom) ≫
            Y.fromSpecResidueField (f x') := by
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
        simp only [Scheme.residueFieldCongr_fromSpecResidueField hη.symm]
        simp only [η]
      _ = Spec.map eSpecIso.hom ≫ (Spec (.of A)).fromSpecResidueField η ≫ q := by
        simp only [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      _ = _ := by
        rw [← Category.assoc]
        exact congrArg (· ≫ q) (Spec_map_algebraMap_fractionRing A).symm
  · show X.fromSpecResidueField x'
      ((Spec.map (CommRingCat.ofHom α.symm.toRingHom))
        (genericPoint (Spec (.of (FractionRing A))))) = x'
    simp

/-- If every valuative square for `f` whose valuation ring is discrete and whose two spectra
belong to the big fppf site has a lift, then `f` is a specializing map.

The specialization is realized by a morphism from the spectrum of a discrete valuation ring
whose generic residue field is the residue field of the source point, by **Stacks 054F**; the
residue field of a point of a scheme in the site has spectrum in the site, so the valuation
ring and its fraction field are in the site too, and lifting that square and evaluating at the
closed point produces the required point. -/
private theorem specializingMap_of_contained_discreteValuativeCriterion
    (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) (hX : B.Contains X)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (h : ∀ D : ValuativeCommSq f, IsDiscreteValuationRing D.R →
      B.Contains (Spec (.of D.R)) → B.Contains (Spec (.of D.K)) → D.commSq.HasLift) :
    SpecializingMap f := by
  intro x' y hxy
  by_cases hne : f x' = y
  · exact ⟨x', specializes_refl _, hne⟩
  let : Algebra (Y.residueField (f x')) (X.residueField x') :=
    (f.residueFieldMap x').hom.toAlgebra
  have : Algebra.EssFiniteType (Y.residueField (f x')) (X.residueField x') :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x')
  obtain ⟨A, _, _, hA_dvr, q, hη, hclosed, e, he⟩ :=
    exists_dvr_morphism_of_specializes_with_residueField_equiv Y hxy (Ne.symm hne)
      (X.residueField x')
  obtain ⟨i₁, hDcomm, hsource⟩ := exists_spec_fractionRing_comp_eq f x' q hη e he
  let D : ValuativeCommSq f :=
    { R := A
      K := FractionRing A
      i₁ := i₁
      i₂ := q
      commSq := ⟨hDcomm⟩ }
  let α : FractionRing A ≃+* X.residueField x' :=
    ((Scheme.Spec.residueFieldIso (.of A) _ ≪≫
      (genericPointResidueFieldEquiv A).toCommRingCatIso).commRingCatIsoToRingEquiv).symm.trans e
  have hK' : B.Contains (Spec (.of (FractionRing A))) := by
    have hKsite := B.residueField_spec_contains hX x'
    show (Spec (.of (FractionRing A))).size < B.cutoff
    change (Spec (.of (X.residueField x'))).size < B.cutoff at hKsite
    rw [Scheme.size_Spec] at hKsite ⊢
    simpa only [Cardinal.mk_congr α.toEquiv] using hKsite
  have hA : B.Contains (Spec (.of A)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hK'
      ((Cardinal.mk_le_of_injective (IsFractionRing.injective A (FractionRing A))).trans
        (le_max_right _ _))
  obtain ⟨l, hl₁, hl₂⟩ := h D hA_dvr hA hK'
  dsimp [D] at l hl₁ hl₂
  let pA : Spec (.of A) := IsLocalRing.closedPoint A
  refine ⟨l pA, ?_, ?_⟩
  · have hgen : l (genericPoint (Spec (.of A))) = x' := by
      simpa only [Scheme.Hom.comp_apply, Spec_map_algebraMap_genericPoint, hsource] using
        congrArg (fun k : Spec (.of (FractionRing A)) ⟶ X => k (genericPoint _)) hl₁
    show x' ⤳ l pA
    rw [← hgen]
    exact (IsLocalRing.specializes_closedPoint (R := A) _).map l.continuous
  · have hp : f (l pA) = q pA := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : Spec (.of A) ⟶ Y => k pA) hl₂
    exact hp.trans (by simpa [pA] using hclosed)

/-- **The size-cutoff form of the discrete valuative criterion for universal closedness.** A
finite type morphism of schemes to a locally Noetherian scheme, whose source belongs to a big
fppf site, is universally closed as soon as every valuative square over a discrete valuation
ring whose spectrum and whose fraction field spectrum belong to that site has a lift — even
though `AlgebraicGeometry.universallyClosed_tfae_valuative` tests all discrete valuation
rings.

This is what makes the uniqueness part of the valuative criterion for morphisms of algebraic
spaces over `S`, whose valuative squares live inside the site, strong enough to give universal
closedness of a chart base change. -/
@[ega "IV 18.10.20" "partial"]
theorem universallyClosed_of_contained_discreteValuativeCriterion
    (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) (hX : B.Contains X)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian Y]
    (h : ∀ D : ValuativeCommSq f, IsDiscreteValuationRing D.R →
      B.Contains (Spec (.of D.R)) → B.Contains (Spec (.of D.K)) → D.commSq.HasLift) :
    UniversallyClosed f := by
  refine ((universallyClosed_tfae_valuative f).out 2 1).mp fun n ↦ ?_
  let ι := ULift.{u} (Fin n)
  let pX : AffineSpace ι X ⟶ X := AffineSpace ι X ↘ X
  let pY : AffineSpace ι Y ⟶ Y := AffineSpace ι Y ↘ Y
  let g := AffineSpace.map ι f
  let pb := AffineSpace.isPullback_map (n := ι) f
  have hlft : LocallyOfFiniteType g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback pb.flip
      (inferInstance : LocallyOfFiniteType f)
  have : LocallyOfFinitePresentation pY := inferInstance
  have : LocallyOfFiniteType pY := inferInstance
  have hNoeth : IsLocallyNoetherian (AffineSpace ι Y) :=
    LocallyOfFiniteType.isLocallyNoetherian pY
  have hmap : pX ≫ f = g ≫ pY := pb.w.symm
  have hg : ∀ Dg : ValuativeCommSq g, IsDiscreteValuationRing Dg.R →
      B.Contains (Spec (.of Dg.R)) → B.Contains (Spec (.of Dg.K)) → Dg.commSq.HasLift := by
    intro Dg hD hDR hDK
    let Df : ValuativeCommSq f :=
      { R := Dg.R
        K := Dg.K
        i₁ := Dg.i₁ ≫ pX
        i₂ := Dg.i₂ ≫ pY
        commSq := ⟨by rw [Category.assoc, hmap, reassoc_of% Dg.commSq.w]⟩ }
    obtain ⟨l, hl₁, hl₂⟩ := h Df hD hDR hDK
    let lP := pb.lift Dg.i₂ l hl₂.symm
    have hlP_B : lP ≫ g = Dg.i₂ := pb.lift_fst Dg.i₂ l hl₂.symm
    have hlP_X : lP ≫ pX = l := pb.lift_snd Dg.i₂ l hl₂.symm
    have htop :
        Spec.map (CommRingCat.ofHom (algebraMap Dg.R Dg.K)) ≫ lP = Dg.i₁ := by
      apply pb.hom_ext
      · rw [Category.assoc, hlP_B, Dg.commSq.w]
      · rw [Category.assoc, hlP_X]
        exact hl₁
    exact ⟨⟨lP, htop, hlP_B⟩⟩
  have hqc : QuasiCompact g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback pb.flip
      (inferInstance : QuasiCompact f)
  exact (isClosedMap_iff_specializingMap g).2
    (specializingMap_of_contained_discreteValuativeCriterion B g
      (B.contains_affineSpace hX n) hg)

end AlgebraicGeometry

end
