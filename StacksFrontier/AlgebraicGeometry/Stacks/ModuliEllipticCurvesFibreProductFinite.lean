module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCoordinateChangeFinite

/-!
# The fibre product over the moduli stack of elliptic curves is finite over the product

Let `E` be an elliptic curve over `S` and `E'` one over `S'`, and let `P` be a fibre product
`S ×_{𝓜₁,₁} S'`, the scheme of triples `(a, a', α)` of
`StacksFrontier/AlgebraicGeometry/Stacks/ModuliEllipticCurves.lean`. Then the morphism
`P ⟶ S × S'` recording `(a, a')` is **finite**: the isomorphisms between two elliptic curves form
a finite scheme.

Zariski locally on `S × S'` both curves are restrictions of the Weierstrass family, and there `P`
is the base change of the scheme `H × W ⟶ W × W` of coordinate changes between two Weierstrass
equations, which is finite by
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isFinite_prodLift_actionMap_productToBase`.
This file treats the case where `E` is a restriction of the Weierstrass family over all of `S`,
which is the case of an elliptic curve over a field.

## Main results

* `CategoryTheory.Limits.isPullback_prodMap_id_snd`: the square formed by `𝟙 × g` and the two
  second projections is cartesian.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.isFinite_prodLift`: if `E` is
  the restriction of the Weierstrass family along a morphism `S ⟶ W` and `E'` is an elliptic
  curve, then `S ×_{𝓜₁,₁} S' ⟶ S × S'` is finite.

## Implementation notes

Finiteness is Zariski local on the target, which is used through
`Stacks.Morphisms.isFinite_isZariskiLocalAtTarget` and `Stacks.Morphisms.isFinite_respectsIso`
because the corresponding instances do not synthesize at the current Mathlib pin. The open
cover of `S × S'` is by the products `S × U` with `U` an open of `S'` over which `E'` is a
restriction of the Weierstrass family; over `S × U` the preimage of `P` is the open of `P` over
which the second projection lands in `U`, which is a fibre product of `(E, E'|_U)`
(`AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.restrictSnd`), and the base
change of `H × W` is another one
(`AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.ofComparisons`); the two are
identified by `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.uniqueIso`.

## References

* [Stacks Project, Tag 072M](https://stacks.math.columbia.edu/tag/072M)
-/

@[expose] public section

open CategoryTheory Limits

universe u

/-- **Products are base changes of their factors.** For `g : B ⟶ C` the square formed by
`𝟙 A × g : A ⨯ B ⟶ A ⨯ C`, the two second projections and `g` is cartesian. -/
theorem CategoryTheory.Limits.isPullback_prodMap_id_snd {C : Type*} [Category C]
    [HasBinaryProducts C] (A : C) {B D : C} (g : B ⟶ D) :
    IsPullback (prod.map (𝟙 A) g) prod.snd prod.snd g := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ prod.lift (s.fst ≫ prod.fst) s.snd)
    (fun s ↦ ?_) (fun s ↦ by simp) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · refine prod.hom_ext (by simp) ?_
    simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc]
    exact s.condition.symm
  · refine prod.hom_ext ?_ (by simpa using h₂)
    simp only [prod.lift_fst, ← h₁, Category.assoc, prod.map_fst, Category.comp_id]

namespace AlgebraicGeometry.ModuliEllipticCurves

attribute [local instance] Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  Stacks.Morphisms.isFinite_respectsIso

variable {S S' P : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}

/-- **The fibre product `S ×_{𝓜₁,₁} S'` is finite over `S × S'`**, when the first family is the
restriction of the Weierstrass family along a morphism `S ⟶ W` (witnessed by a triple `x₀` whose
second morphism is the identity) and the second family is an elliptic curve. -/
theorem RepresentsComparisons.isFinite_prodLift (r : RepresentsComparisons E E' P)
    (x₀ : Comparison Weierstrass.family.{u} E S) (hx₀ : x₀.snd = 𝟙 S) (hE' : E'.IsElliptic) :
    IsFinite (prod.lift (r.homEquiv P (𝟙 P)).fst (r.homEquiv P (𝟙 P)).snd) := by
  set F := prod.lift (r.homEquiv P (𝟙 P)).fst (r.homEquiv P (𝟙 P)).snd
  choose U hU x hx using
    Weierstrass.localWeierstrassAt_of_noetherian Weierstrass.localWeierstrassNoetherian E' hE'
  let m (s : S') : S ⨯ (U s).toScheme ⟶ S ⨯ S' := prod.map (𝟙 S) (U s).ι
  have hm (s : S') : IsPullback (m s) prod.snd prod.snd (U s).ι :=
    isPullback_prodMap_id_snd S (U s).ι
  have : ∀ s, IsOpenImmersion (m s) := fun s ↦
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hm s).flip inferInstance
  have hcov : ⨆ s, (m s).opensRange = ⊤ := by
    let q : S ⨯ S' ⟶ S' := prod.snd
    refine eq_top_iff.2 fun z _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨q z, ?_⟩
    obtain ⟨y, hy⟩ : q z ∈ Set.range (U (q z)).ι := by
      rw [Scheme.Opens.range_ι]
      exact hU _
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := q)
      (g := (U (q z)).ι) z y hy.symm
    refine ⟨(hm (q z)).isoPullback.inv w, ?_⟩
    rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun s ↦ (m s).opensRange) hcov fun s ↦ ?_
  refine (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictOpensRange F (m s))).2 ?_
  let r₁ := r.restrictSnd (U s)
  let FU := prod.lift (r₁.homEquiv _ (𝟙 _)).fst (r₁.homEquiv _ (𝟙 _)).snd
  have hpb : IsPullback (r.restrictSndOpen (U s)).ι FU F (m s) := by
    refine IsPullback.of_bot ?_ ?_ (hm s)
    · have e₁ : FU ≫ prod.snd = (r.homEquiv P (𝟙 P)).snd ∣_ (U s) := by
        simpa only [FU, prod.lift_snd] using r.restrictSnd_snd (U s)
      have e₂ : F ≫ prod.snd = (r.homEquiv P (𝟙 P)).snd := by simp [F]
      rw [e₁, e₂]
      exact (isPullback_morphismRestrict (r.homEquiv P (𝟙 P)).snd (U s)).flip
    · refine prod.hom_ext ?_ ?_
      · simp only [F, FU, m, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
        exact (r.restrictSnd_fst (U s)).symm
      · simp only [F, FU, m, Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc]
        rw [r.restrictSnd_snd (U s), morphismRestrict_ι]
  let r₂ := (Weierstrass.representsComparisons_coordinateChange.ofComparisons x₀ (x s) hx₀
    (hx s)).ofFamilyIso E.pullbackIdIso (FamilyIso.refl _)
  have hFU : FU = (RepresentsComparisons.uniqueIso r₁ r₂).hom ≫
      Limits.pullback.snd _ (prod.map x₀.fst (x s).fst) := by
    refine prod.hom_ext ?_ ?_
    · simp only [FU, prod.lift_fst]
      rw [← RepresentsComparisons.uniqueIso_hom_fst r₁ r₂]
      rfl
    · simp only [FU, prod.lift_snd]
      rw [← RepresentsComparisons.uniqueIso_hom_snd r₁ r₂]
      rfl
  have : IsFinite (prod.lift
      (Weierstrass.representsComparisons_coordinateChange.{u}.homEquiv _ (𝟙 _)).fst
      (Weierstrass.representsComparisons_coordinateChange.{u}.homEquiv _ (𝟙 _)).snd) := by
    rw [Weierstrass.representsComparisons_coordinateChange_homEquiv_id_fst,
      Weierstrass.representsComparisons_coordinateChange_homEquiv_id_snd]
    exact Weierstrass.isFinite_prodLift_actionMap_productToBase
  have : IsFinite FU := by
    rw [hFU]
    infer_instance
  rw [← hpb.isoPullback_inv_snd]
  infer_instance

end AlgebraicGeometry.ModuliEllipticCurves
