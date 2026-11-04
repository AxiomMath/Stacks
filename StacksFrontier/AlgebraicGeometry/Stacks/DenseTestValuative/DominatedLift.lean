module

public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness

/-!
# Descending a dotted arrow from a dominating valuation ring

Let `b : Z ⟶ V` be a morphism of schemes, `η` a point of `Z`, and `A ⊂ κ(η)` a valuation ring
with fraction field `κ(η)`, together with a commutative square
```
Spec κ(η) ---> Z
    |          | b
    v          v
  Spec A ----> V
```
whose upper arrow is the canonical one. If, after an extension `K'/κ(η)` and passage to a
valuation ring `R' ⊂ K'` dominating `A`, the square has a dotted arrow `Spec R' ⟶ Z`, then it
already has one over `A`.

## Main results

* `AlgebraicGeometry.exists_liftStruct_fromSpecResidueField_of_dominating`: the dotted arrow
  descends.

## Implementation notes

No hypothesis on `b` is needed. The closed point of `Spec R'` maps to a specialization `z` of
`η`, and the local homomorphism `𝒪_{Z,z} ⟶ R'` attached to the dotted arrow agrees, inside
`K'`, with the composite of the specialization map `𝒪_{Z,z} ⟶ 𝒪_{Z,η}` and the residue map to
`κ(η)`. So that composite lands in the preimage of `R'` in `κ(η)`, which is `A` because a
valuation ring is maximal for domination; the resulting local homomorphism `𝒪_{Z,z} ⟶ A` gives
the dotted arrow `Spec A ⟶ 𝒪_{Z,z} ⟶ Z`. Its lower triangle is checked on the closed point and
after restriction to the generic point, by
`AlgebraicGeometry.hom_ext_of_closedPoint_eq_of_specMap_comp_eq`.

This is the scheme case of **Stacks 0ARH**, which the proof of **Stacks 0CQM** applies to the
algebraic-space and scheme covers it produces.

## References

* [Stacks Project, Tag 0ARH](https://stacks.math.columbia.edu/tag/0ARH)
* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **A valuation ring is maximal for domination, read through a field homomorphism.** Let
`A ⊂ K` be a valuation ring with fraction field `K`, let `ψ : A ⟶ R'` be a local homomorphism to
a domain with fraction field `K'`, and let `χ : K ⟶ K'` extend it. Then every `t ∈ K` with
`χ t ∈ R'` lies in `A`. -/
theorem mem_of_map_mem_range_of_isLocalHom {K : Type*} [Field K] (A : Subring K)
    [ValuationRing A] [IsFractionRing A K]
    {R' K' : Type*} [CommRing R'] [IsDomain R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] (ψ : A →+* R') [IsLocalHom ψ] (χ : K →+* K')
    (hcomm : (algebraMap R' K').comp ψ = χ.comp A.subtype) (t : K)
    (ht : χ t ∈ Set.range (algebraMap R' K')) : t ∈ A := by
  obtain ⟨r, hr⟩ := ht
  rcases ValuationRing.isInteger_or_isInteger A t with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [← ha]
    exact a.2
  · by_cases ht0 : t = 0
    · rw [ht0]
      exact A.zero_mem
    have hχa : algebraMap R' K' (ψ a) = (χ t)⁻¹ := by
      refine (RingHom.congr_fun hcomm a).trans ?_
      show χ (algebraMap A K a) = _
      rw [ha, map_inv₀]
    have hχt : χ t ≠ 0 := (map_ne_zero χ).mpr ht0
    have hunit : ψ a * r = 1 := by
      apply IsFractionRing.injective R' K'
      rw [map_mul, hχa, hr, map_one, inv_mul_cancel₀ (hr ▸ hχt)]
    have ha' : IsUnit a := (isUnit_map_iff ψ a).mp (IsUnit.of_mul_eq_one _ hunit)
    obtain ⟨v, hv⟩ := ha'
    have h2 : t⁻¹ * (((v⁻¹ : Aˣ) : A) : K) = 1 := by
      have hvv : ((v : A) : K) * (((v⁻¹ : Aˣ) : A) : K) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
      rw [hv] at hvv
      rw [← ha]
      exact hvv
    have htv : t = ((v⁻¹ : Aˣ) : A) := (inv_mul_eq_one₀ ht0).mp h2
    rw [htv]
    exact ((v⁻¹ : Aˣ) : A).2

/-- **A dotted arrow over a dominating valuation ring descends** to the canonical square at a
residue field. Let `b : Z ⟶ V`, let `A ⊂ κ(η)` be a valuation ring with fraction field `κ(η)`,
and let `sq` be a commutative square with upper arrow `Spec κ(η) ⟶ Z` and lower arrow
`i₂ : Spec A ⟶ V`. If `ψ : A ⟶ R'` is a local homomorphism to a valuation ring with fraction
field `K'`, `χ : κ(η) ⟶ K'` extends it, and `l' : Spec R' ⟶ Z` fills the induced square, then
`sq` has a dotted arrow. -/
theorem exists_liftStruct_fromSpecResidueField_of_dominating
    {Z V : Scheme.{u}} (b : Z ⟶ V) (η : Z) (A : Subring (Z.residueField η))
    [ValuationRing A] [IsFractionRing A (Z.residueField η)]
    (i₂ : Spec (.of A) ⟶ V)
    (sq : CommSq (Z.fromSpecResidueField η) (Spec.map (CommRingCat.ofHom A.subtype)) b i₂)
    {R' K' : Type u} [CommRing R'] [IsDomain R'] [ValuationRing R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] (ψ : A →+* R') [IsLocalHom ψ] (χ : Z.residueField η →+* K')
    (hcomm : (algebraMap R' K').comp ψ = χ.comp A.subtype)
    (l' : Spec (.of R') ⟶ Z)
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ l' =
      Spec.map (CommRingCat.ofHom χ) ≫ Z.fromSpecResidueField η)
    (h₂ : l' ≫ b = Spec.map (CommRingCat.ofHom ψ) ≫ i₂) :
    Nonempty sq.LiftStruct := by
  -- the generic point of `Spec R'` maps to `η`, so `η` specializes to the image `z` of the
  -- closed point
  have hgen : ∀ p : Spec (.of K'),
      l' (Spec.map (CommRingCat.ofHom (algebraMap R' K')) p) = η := by
    intro p
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hsp : η ⤳ l' (closedPoint (CommRingCat.of R')) := by
    rw [← hgen (closedPoint K')]
    exact (specializes_closedPoint _).map l'.continuous
  let σ : Z.presheaf.stalk (l' (closedPoint (CommRingCat.of R'))) ⟶ Z.residueField η :=
    Z.presheaf.stalkSpecializes hsp ≫ Z.residue η
  let τ := Scheme.stalkClosedPointTo l'
  -- the two maps from the stalk to `K'` agree
  have hσ : Spec.map σ ≫ Z.fromSpecStalk (l' (closedPoint (CommRingCat.of R'))) =
      Z.fromSpecResidueField η := by
    refine (congrArg (· ≫ Z.fromSpecStalk _) (Spec.map_comp _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (Spec.map (Z.residue η) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)
  have hKI : τ ≫ CommRingCat.ofHom (algebraMap R' K') = σ ≫ CommRingCat.ofHom χ := by
    apply Spec.map_injective
    apply (cancel_mono (Z.fromSpecStalk (l' (closedPoint (CommRingCat.of R'))))).mp
    refine ((congrArg (· ≫ Z.fromSpecStalk _) (Spec.map_comp τ _)).trans ?_).trans
      (congrArg (· ≫ Z.fromSpecStalk _) (Spec.map_comp σ (CommRingCat.ofHom χ))).symm
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ ·)
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk l')).trans ?_
    refine h₁.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (Spec.map (CommRingCat.ofHom χ) ≫ ·) hσ.symm
  have hKI' : ∀ s, algebraMap R' K' (τ.hom s) = χ (σ.hom s) := fun s =>
    congrArg (fun k => k.hom s) hKI
  have hmem : ∀ s, σ.hom s ∈ A := fun s =>
    mem_of_map_mem_range_of_isLocalHom A ψ χ hcomm _ ⟨τ.hom s, hKI' s⟩
  let θ : Z.presheaf.stalk (l' (closedPoint (CommRingCat.of R'))) →+* A := σ.hom.codRestrict A hmem
  have hψθ : ∀ s, ψ (θ s) = τ.hom s := by
    intro s
    apply IsFractionRing.injective R' K'
    rw [hKI' s]
    exact RingHom.congr_fun hcomm (θ s)
  have hθloc : IsLocalHom θ :=
    ⟨fun s hs => (isUnit_map_iff τ.hom s).mp (hψθ s ▸ hs.map ψ)⟩
  let l : Spec (.of A) ⟶ Z := Spec.map (CommRingCat.ofHom θ) ≫ Z.fromSpecStalk _
  have hθσ : CommRingCat.ofHom θ ≫ CommRingCat.ofHom A.subtype = σ := by
    ext s
    rfl
  have hleft : Spec.map (CommRingCat.ofHom A.subtype) ≫ l = Z.fromSpecResidueField η := by
    show Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom θ) ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp, hθσ, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  refine ⟨⟨l, hleft, ?_⟩⟩
  refine hom_ext_of_closedPoint_eq_of_specMap_comp_eq (K := Z.residueField η) (l ≫ b) i₂ ?_ ?_
  · have hl : l (closedPoint A) = l' (closedPoint (CommRingCat.of R')) := by
      show Z.fromSpecStalk _ (Spec.map (CommRingCat.ofHom θ) (closedPoint A)) = _
      rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
    show b (l (closedPoint A)) = i₂ (closedPoint A)
    rw [hl]
    have h3 := congrArg (fun k => k (closedPoint (CommRingCat.of R'))) h₂
    change b (l' _) = i₂ (Spec.map (CommRingCat.ofHom ψ) _) at h3
    rw [h3, Spec_closedPoint]
  · show Spec.map (CommRingCat.ofHom A.subtype) ≫ l ≫ b =
      Spec.map (CommRingCat.ofHom A.subtype) ≫ i₂
    rw [← Category.assoc, hleft, sq.w]
    rfl

end AlgebraicGeometry

end
