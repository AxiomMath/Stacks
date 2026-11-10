module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Inseparable
public import StacksCore.Tactic.StacksAttribute

/-!
# Specialization of points of a scheme

Two results about the specialization order on the points of a scheme.

First, every specialization `s' ⤳ s` in a scheme `S` is witnessed by a valuation ring: there is a
valuation ring `A` and a morphism `Spec A ⟶ S` carrying the generic point of `Spec A` to `s'` and
its closed point to `s`. Moreover the valuation ring can be chosen so that the extension of
residue fields at the generic point is any prescribed extension of `κ(s')`.

Second, the image of a quasi-compact morphism of schemes is closed precisely when it is stable
under specialization.

## Main results

* `AlgebraicGeometry.exists_valuation_ring_of_specializes`: a specialization is realized by the
  spectrum of a valuation ring, with a prescribed residue-field extension at the generic point.
* `AlgebraicGeometry.isClosed_range_iff_stableUnderSpecialization`: the image of a quasi-compact
  morphism is closed if and only if it is stable under specialization.

## References

* [Stacks Project, Tag 01J8](https://stacks.math.columbia.edu/tag/01J8)
* [Stacks Project, Tag 05JL](https://stacks.math.columbia.edu/tag/05JL)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

universe u

/-- A specialization of points of a scheme is witnessed by a valuation ring.  The valuation
ring may be chosen so that the residue-field extension at its generic point is any prescribed
extension. -/
@[stacks 01J8]
public lemma exists_valuation_ring_of_specializes (S : AlgebraicGeometry.Scheme.{u})
    {s' s : S} (h : s' ⤳ s) (K : Type u) [Field K]
    (i : S.residueField s' ⟶ CommRingCat.of K) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (f : AlgebraicGeometry.Spec (.of A) ⟶ S)
      (e : (AlgebraicGeometry.Spec (.of A)).residueField
        (genericPoint (AlgebraicGeometry.Spec (.of A))) ≅ CommRingCat.of K)
      (hη : f (genericPoint (AlgebraicGeometry.Spec (.of A))) = s'),
      f (closedPoint A) = s ∧
        (S.residueFieldCongr hη).inv ≫
          f.residueFieldMap (genericPoint (AlgebraicGeometry.Spec (.of A))) ≫ e.hom = i := by
  let φ : S.presheaf.stalk s ⟶ CommRingCat.of K :=
    S.presheaf.stalkSpecializes h ≫ S.residue s' ≫ i
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing φ.hom
  let a : S.presheaf.stalk s ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (φ.hom.codRestrict A.toSubring hA)
  let : IsLocalHom a.hom := hA_local
  let f : AlgebraicGeometry.Spec (.of A) ⟶ S :=
    AlgebraicGeometry.Spec.map a ≫ S.fromSpecStalk s
  let j : A →+* K := A.subtype
  let q : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of A) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom j)
  have hqf : q ≫ f = AlgebraicGeometry.Spec.map i ≫
      S.fromSpecResidueField s' := by
    dsimp only [q, f]
    rw [← Category.assoc, ← AlgebraicGeometry.Spec.map_comp]
    change AlgebraicGeometry.Spec.map (S.presheaf.stalkSpecializes h ≫
      S.residue s' ≫ i) ≫ S.fromSpecStalk s = _
    rw [AlgebraicGeometry.Scheme.fromSpecResidueField]
    calc
      _ = AlgebraicGeometry.Spec.map (S.residue s' ≫ i) ≫
          (AlgebraicGeometry.Spec.map (S.presheaf.stalkSpecializes h) ≫
            S.fromSpecStalk s) :=
        AlgebraicGeometry.Spec.map_comp_assoc _ _ _
      _ = AlgebraicGeometry.Spec.map (S.residue s' ≫ i) ≫
          S.fromSpecStalk s' := congrArg _
        (AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk h)
      _ = _ := AlgebraicGeometry.Spec.map_comp_assoc _ _ _
  have hqη : q (closedPoint K) = genericPoint (AlgebraicGeometry.Spec (.of A)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap j (IsLocalRing.maximalIdeal K) = _
    ext x
    simp [j, AlgebraicGeometry.genericPoint_eq_bot_of_affine]
  let : (genericPoint (AlgebraicGeometry.Spec (.of A))).asIdeal.IsPrime :=
    (genericPoint (AlgebraicGeometry.Spec (.of A))).isPrime
  let baseEquiv : A ⧸
      (genericPoint (AlgebraicGeometry.Spec (.of A))).asIdeal ≃+* A :=
    (Ideal.quotientEquiv _ ⊥ (RingEquiv.refl A) (by simp)).trans (RingEquiv.quotientBot A)
  let eFrac : (genericPoint (AlgebraicGeometry.Spec (.of A))).asIdeal.ResidueField ≃+* K :=
    IsFractionRing.ringEquivOfRingEquiv baseEquiv
  let e : (AlgebraicGeometry.Spec (.of A)).residueField
      (genericPoint (AlgebraicGeometry.Spec (.of A))) ≅ CommRingCat.of K :=
    AlgebraicGeometry.Scheme.Spec.residueFieldIso (.of A)
        (genericPoint (AlgebraicGeometry.Spec (.of A))) ≪≫
      eFrac.toCommRingCatIso
  have hq_repr : q = AlgebraicGeometry.Spec.map e.hom ≫
      (AlgebraicGeometry.Spec (.of A)).fromSpecResidueField
        (genericPoint (AlgebraicGeometry.Spec (.of A))) := by
    rw [← AlgebraicGeometry.Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [← AlgebraicGeometry.Spec.map_comp]
    dsimp only [q]
    rw [AlgebraicGeometry.Spec.map_inj]
    ext x
    simp only [e, Iso.trans_hom, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
    change j x = eFrac (algebraMap A _ x)
    rw [← Ideal.algebraMap_quotient_residueField_mk,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    simp [baseEquiv, j]
  have hη : f (genericPoint (AlgebraicGeometry.Spec (.of A))) = s' := by
    have := congrArg (fun g ↦ g (closedPoint K)) hqf
    change f (q (closedPoint K)) = _ at this
    rw [hqη] at this
    change f (genericPoint (AlgebraicGeometry.Spec (.of A))) =
      S.fromSpecResidueField s' (AlgebraicGeometry.Spec.map i (closedPoint K)) at this
    simpa only [AlgebraicGeometry.Scheme.fromSpecResidueField_apply] using this
  refine ⟨A, inferInstance, inferInstance, inferInstance, f, e, hη, ?_, ?_⟩
  · dsimp only [f]
    change S.fromSpecStalk s (PrimeSpectrum.comap a.hom (closedPoint A)) = s
    rw [IsLocalRing.comap_closedPoint a.hom,
      AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint]
  · have ht := hqf
    rw [hq_repr, Category.assoc,
      ← AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at ht
    rw [← AlgebraicGeometry.Spec.map_comp_assoc] at ht
    change (AlgebraicGeometry.Scheme.SpecToEquivOfField K S).symm
        ⟨f (genericPoint (AlgebraicGeometry.Spec (.of A))),
          f.residueFieldMap (genericPoint (AlgebraicGeometry.Spec (.of A))) ≫ e.hom⟩ =
      (AlgebraicGeometry.Scheme.SpecToEquivOfField K S).symm ⟨s', i⟩ at ht
    have H := congrArg (AlgebraicGeometry.Scheme.SpecToEquivOfField K S) ht
    simp only [Equiv.apply_symm_apply] at H
    rw [AlgebraicGeometry.Scheme.SpecToEquivOfField_eq_iff] at H
    obtain ⟨_, he⟩ := H
    change f.residueFieldMap (genericPoint (AlgebraicGeometry.Spec (.of A))) ≫ e.hom =
      (S.residueFieldCongr hη).hom ≫ i at he
    rw [he, Iso.inv_hom_id_assoc]

/-- Over an affine target, a specialization-stable image of a morphism from a quasi-compact
scheme is closed. -/
private theorem closedRange_of_compact_affineTarget {X S : Scheme} (f : X ⟶ S)
    [CompactSpace X] [IsAffine S]
    (hstable : StableUnderSpecialization (Set.range (f : X → S))) :
    IsClosed (Set.range (f : X → S)) := by
  let e := S.isoSpec.hom
  let eh : S ≃ₜ Spec Γ(S, ⊤) := TopCat.homeoOfIso (asIso S.isoSpec.hom.base)
  have hE : Set.range (f ≫ e : X → Spec Γ(S, ⊤)) = eh '' Set.range (f : X → S) :=
    Set.range_comp eh f
  have hstable' : StableUnderSpecialization (Set.range (f ≫ e : X → Spec Γ(S, ⊤))) := by
    rw [hE]
    exact eh.isClosedMap.specializingMap.stableUnderSpecialization_image hstable
  obtain ⟨R, g, hg⟩ := (compactSpace_iff_exists (X := X)).mp inferInstance
  have hEq : Set.range (g ≫ (f ≫ e) : Spec R → Spec Γ(S, ⊤)) =
      Set.range (f ≫ e : X → Spec Γ(S, ⊤)) :=
    hg.range_comp (f ≫ e : X → Spec Γ(S, ⊤))
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective (g ≫ (f ≫ e))
  have hphi : g ≫ (f ≫ e) = Spec.map φ := by simpa [Spec.homEquiv] using hφ.symm
  have Hraw : @StableUnderSpecialization (PrimeSpectrum Γ(S, ⊤)) PrimeSpectrum.zariskiTopology
      (Set.range (PrimeSpectrum.comap φ.hom)) := by
    rwa [← hEq, hphi] at hstable'
  have hc : IsClosed (Set.range (f ≫ e : X → Spec Γ(S, ⊤))) := by
    rw [← hEq, hphi]
    exact PrimeSpectrum.isClosed_range_of_stableUnderSpecialization φ.hom Hraw
  rw [hE] at hc
  exact eh.isClosed_image.mp hc

/-- The image of a quasi-compact morphism of schemes which is stable under specialization is
closed. -/
private theorem closedRange_of_quasiCompact_stable {X S : Scheme} (f : X ⟶ S)
    [QuasiCompact f] (hstable : StableUnderSpecialization (Set.range (f : X → S))) :
    IsClosed (Set.range (f : X → S)) := by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top S)]
  intro U
  let U' : S.Opens := U.1
  let V : X.Opens := f ⁻¹ᵁ U'
  have hU : IsAffineOpen U' := U.2
  let : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hU.isCompact)
  let : IsAffine U' := hU
  have hrange : Set.range (f ∣_ U' : V.toScheme → U') =
      (U'.ι : U' → S) ⁻¹' Set.range (f : X → S) := by
    ext y
    change (∃ x : V.toScheme, (f ∣_ U') x = y) ↔ ∃ x : X, f x = U'.ι y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.1, (morphismRestrict_base_coe f U' x).symm.trans (congrArg U'.ι hx)⟩
    · rintro ⟨x, hx⟩
      have hxU : f x ∈ U' := by rw [hx]; exact y.2
      exact ⟨⟨x, hxU⟩, U'.ι.isOpenEmbedding.injective
        ((morphismRestrict_base_coe f U' ⟨x, hxU⟩).trans hx)⟩
  have hstableU : StableUnderSpecialization
      (Set.range (f ∣_ U' : V.toScheme → U')) := by
    rw [hrange]; exact hstable.preimage U'.ι.continuous
  change IsClosed ((U'.ι : U' → S) ⁻¹' Set.range (f : X → S))
  rw [← hrange]
  exact closedRange_of_compact_affineTarget (f ∣_ U') hstableU

/-- The image of a quasi-compact morphism of schemes is closed if and only if it
is stable under specialization. -/
@[stacks 05JL]
public theorem isClosed_range_iff_stableUnderSpecialization
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] :
    IsClosed (Set.range (f : X → S)) ↔
      StableUnderSpecialization (Set.range (f : X → S)) :=
  ⟨IsClosed.stableUnderSpecialization, closedRange_of_quasiCompact_stable f⟩

end AlgebraicGeometry
