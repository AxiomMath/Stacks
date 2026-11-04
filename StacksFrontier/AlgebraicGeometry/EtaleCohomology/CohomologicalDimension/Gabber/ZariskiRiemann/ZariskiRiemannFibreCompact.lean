module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenteredGermDeathOfValuation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannPatchCompact

/-!
# The Zariski–Riemann fibre over a point of a model is quasi-compact

Let `B` be a local domain with fraction field `K`, `M` a proper model `f : Y ⟶ Spec B` with point
`j : Spec K ⟶ Y`, and `y ∈ Y`. When some valuation ring of `K` is centered at `y`, the point
`j(η)` specializes to `y`, and the specialization map `𝒪_{Y,y} ⟶ 𝒪_{Y,j(η)}` followed by the
stalk map of `j` is a ring map `σ : 𝒪_{Y,y} ⟶ K`. A valuation ring `V` of `K` dominating `B` is
centered at `y` exactly when `V` contains `σ(𝒪_{Y,y})` and the nonzero elements of
`σ(𝔪_y)` have their inverses outside `V`:

* if `V` is centered at `y`, `σ` is the local homomorphism `𝒪_{Y,y} ⟶ V` of the center
  followed by `V ⊆ K`
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerStalkMap_comp_algebraMap`);
* conversely, `σ` then corestricts to a local homomorphism `τ : 𝒪_{Y,y} ⟶ V`, and
  `Spec V ⟶ Spec 𝒪_{Y,y} ⟶ Y` solves the valuative problem, so it is the center by uniqueness, and
  it sends the closed point to `y`.

With the images of `B` and of `𝔪_B` added to the conditions (for "contains `B`" and "dominates
`B`"), the Zariski–Riemann fibre over `y` is therefore cut out by containment conditions, and it
is quasi-compact by `ValuationSubring.exists_finset_subcover_of_forall_subset`. This proves the
input `AlgebraicGeometry.Scheme.ZariskiRiemann.ZariskiRiemannFibreQuasiCompact` of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centeredGermDeath_of_valuationGermDeath`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkSpecializes_comp_mem_of_centerPoint_eq`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerPoint_eq_of_stalk_mem`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.zariskiRiemannFibreQuasiCompact`

## References

* O. Zariski, P. Samuel, *Commutative Algebra*, Vol. II, Chapter VI, §17
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

/-- An element of a valuation subring that is nonzero in `K` and whose inverse lies in the
subring is a unit. -/
theorem isUnit_of_coe_inv_mem {K : Type*} [Field K] {V : ValuationSubring K} (x : V)
    (hx : (x : K) ≠ 0) (h : (x : K)⁻¹ ∈ V) : IsUnit x :=
  IsUnit.of_mul_eq_one (⟨_, h⟩ : V) (Subtype.ext (by simp [hx]))

/-- A ring map from a local ring to a valuation subring is local when the nonzero images of the
maximal ideal have their inverses outside the subring. -/
theorem isLocalHom_of_forall_inv_notMem {K : Type*} [Field K] {V : ValuationSubring K}
    {A : Type*} [CommRing A] [IsLocalRing A] (φ : A →+* V)
    (h : ∀ a ∈ maximalIdeal A, (φ a : K) ≠ 0 → (φ a : K)⁻¹ ∉ V) : IsLocalHom φ := by
  refine ⟨fun a ha ↦ ?_⟩
  by_contra hna
  obtain ⟨w, hw⟩ := ha
  have hmul : ((↑w⁻¹ : V) : K) * ((w : V) : K) = 1 := congrArg Subtype.val w.inv_mul
  have h0 : ((w : V) : K) ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  have hinv : ((w : V) : K)⁻¹ = ((↑w⁻¹ : V) : K) := inv_eq_of_mul_eq_one_left hmul
  rw [hw] at h0 hinv
  exact h a ((mem_maximalIdeal a).2 hna) h0 (hinv ▸ (↑w⁻¹ : V).2)

/-- Under a local ring map to a valuation subring, the nonzero images of the maximal ideal have
their inverses outside the subring. -/
private theorem inv_notMem_of_isLocalHom {K : Type*} [Field K] {V : ValuationSubring K}
    {A : Type*} [CommRing A] [IsLocalRing A] (φ : A →+* V) [IsLocalHom φ] {a : A}
    (ha : a ∈ maximalIdeal A) (h0 : (φ a : K) ≠ 0) : (φ a : K)⁻¹ ∉ V := fun hinv ↦
  (mem_maximalIdeal _).1 (map_nonunit φ a ha) (isUnit_of_coe_inv_mem _ h0 hinv)

/-- Two morphisms `Spec V ⟶ Spec A` agreeing after `Spec K ⟶ Spec V`, for a valuation subring
`V ⊆ K`, are equal (`V ⟶ K` is injective). -/
theorem eq_of_specMap_comp_eq {K : Type u} [Field K] {V : ValuationSubring K} {A : CommRingCat.{u}}
    {f₁ f₂ : Spec (.of V) ⟶ Spec A}
    (h : Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ f₁ =
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ f₂) : f₁ = f₂ := by
  rw [← Spec.map_preimage f₁, ← Spec.map_preimage f₂] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  congr 1
  ext x
  exact congrArg (fun g : A ⟶ CommRingCat.of K ↦ g.hom x) (Spec.map_injective h)

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)
  (V : ValuationSubring (FractionRing B)) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

/-- **The stalk at the center lands in `V`, the maximal ideal in the non-units.** If `V` is
centered at `y`, the specialization map `𝒪_{Y,y} ⟶ 𝒪_{Y,j(η)}` followed by the stalk map of `j`
takes values in `V`, and the nonzero images of the maximal ideal have their inverses outside
`V`. -/
theorem stalkSpecializes_comp_mem_of_centerPoint_eq {y : ↥M.Y} (hc : M.centerPoint V hV = y)
    (hsp : M.j (closedPoint (FractionRing B)) ⤳ y) (a : M.Y.presheaf.stalk y) :
    (M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j).hom a ∈ V ∧
      (a ∈ maximalIdeal (M.Y.presheaf.stalk y) →
        (M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j).hom a ≠ 0 →
        ((M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j).hom a)⁻¹ ∉ V) := by
  subst hc
  have e : M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j =
      M.centerStalkMap V hV ≫ CommRingCat.ofHom (algebraMap V (FractionRing B)) :=
    (M.centerStalkMap_comp_algebraMap V hV).symm
  rw [e]
  change (((M.centerStalkMap V hV).hom a : V) : FractionRing B) ∈ V ∧
    (a ∈ maximalIdeal _ → (((M.centerStalkMap V hV).hom a : V) : FractionRing B) ≠ 0 →
      (((M.centerStalkMap V hV).hom a : V) : FractionRing B)⁻¹ ∉ V)
  exact ⟨((M.centerStalkMap V hV).hom a).2, fun ha h0 ↦
    inv_notMem_of_isLocalHom (M.centerStalkMap V hV).hom ha h0⟩

/-- **A valuation ring containing the stalk, with the maximal ideal in its non-units, is
centered at `y`.** The corestriction `𝒪_{Y,y} ⟶ V` is local, and
`Spec V ⟶ Spec 𝒪_{Y,y} ⟶ Y` solves the valuative problem of `V`, so it is the center. -/
theorem centerPoint_eq_of_stalk_mem {y : ↥M.Y} (hsp : M.j (closedPoint (FractionRing B)) ⤳ y)
    (hR : ∀ a, (M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j).hom a ∈ V)
    (hP : ∀ a ∈ maximalIdeal (M.Y.presheaf.stalk y),
      (M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j).hom a ≠ 0 →
      ((M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j).hom a)⁻¹ ∉ V) :
    M.centerPoint V hV = y := by
  set σ := M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j with hσ
  let τ : M.Y.presheaf.stalk y →+* V := σ.hom.codRestrict V.toSubring hR
  have : IsLocalHom τ := isLocalHom_of_forall_inv_notMem τ hP
  have : IsLocalHom (CommRingCat.ofHom τ).hom := ‹IsLocalHom τ›
  have hτ : CommRingCat.ofHom τ ≫ CommRingCat.ofHom (algebraMap V (FractionRing B)) = σ := by
    ext x
    rfl
  let l : Spec (.of V) ⟶ M.Y := Spec.map (CommRingCat.ofHom τ) ≫ M.Y.fromSpecStalk y
  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing B))) ≫ l = M.j := by
    simp only [l]
    rw [← Category.assoc, ← Spec.map_comp, hτ, hσ, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have h₂ : l ≫ M.f = Spec.map (CommRingCat.ofHom (valuationSubringBaseMap V hV)) := by
    apply eq_of_specMap_comp_eq
    rw [← Category.assoc, h₁, M.fac, ← Spec.map_comp, valuationSubringBaseMap_comp]
  rw [centerPoint, ← M.eq_center V hV h₁ h₂]
  change M.Y.fromSpecStalk y ((Spec.map (CommRingCat.ofHom τ)) (closedPoint V)) = y
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

end ProperModel

/-- **The Zariski–Riemann fibre over a point of a model is quasi-compact** for covers by basic
open sets: the valuation rings of `Frac B` dominating the local domain `B` and centered at `y`
are cut out by containment conditions, and
`ValuationSubring.exists_finset_subcover_of_forall_subset` applies. -/
theorem zariskiRiemannFibreQuasiCompact : ZariskiRiemannFibreQuasiCompact.{u} := by
  intro B _ _ _ M y I S hcov
  classical
  by_cases hne : ∃ (V : ValuationSubring (FractionRing B))
      (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
      IsLocalHom (valuationSubringBaseMap V hV) ∧ M.centerPoint V hV = y
  swap
  · exact ⟨∅, fun V hV hl hc ↦ absurd ⟨V, hV, hl, hc⟩ hne⟩
  obtain ⟨V₀, hV₀, -, hc₀⟩ := hne
  have hsp : M.j (closedPoint (FractionRing B)) ⤳ y := hc₀ ▸ M.j_specializes_centerPoint V₀ hV₀
  set σ := M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j
  let R : Set (FractionRing B) := Set.range σ.hom ∪ Set.range (algebraMap B (FractionRing B))
  let P : Set (FractionRing B) := {x | x ≠ 0 ∧
    ((∃ a ∈ maximalIdeal (M.Y.presheaf.stalk y), σ.hom a = x) ∨
      ∃ b ∈ maximalIdeal B, algebraMap B (FractionRing B) b = x)}
  have hfwd : ∀ (V : ValuationSubring (FractionRing B))
      (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
      IsLocalHom (valuationSubringBaseMap V hV) → M.centerPoint V hV = y →
      (∀ r ∈ R, r ∈ V) ∧ ∀ x ∈ P, x⁻¹ ∉ V := by
    intro V hV hl hc
    refine ⟨?_, ?_⟩
    · rintro r (⟨a, rfl⟩ | ⟨b, rfl⟩)
      · exact (M.stalkSpecializes_comp_mem_of_centerPoint_eq V hV hc hsp a).1
      · exact hV b
    · rintro x ⟨hx0, ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩⟩
      · exact (M.stalkSpecializes_comp_mem_of_centerPoint_eq V hV hc hsp a).2 ha hx0
      · exact inv_notMem_of_isLocalHom (valuationSubringBaseMap V hV) hb hx0
  have hbwd : ∀ V : ValuationSubring (FractionRing B), (∀ r ∈ R, r ∈ V) → (∀ x ∈ P, x⁻¹ ∉ V) →
      ∃ hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V,
        IsLocalHom (valuationSubringBaseMap V hV) ∧ M.centerPoint V hV = y := by
    intro V hR hP
    have hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V := fun b ↦ hR _ (Or.inr ⟨b, rfl⟩)
    refine ⟨hV, isLocalHom_of_forall_inv_notMem _ fun b hb h0 ↦ hP _ ⟨h0, Or.inr ⟨b, hb, rfl⟩⟩,
      M.centerPoint_eq_of_stalk_mem V hV hsp (fun a ↦ hR _ (Or.inl ⟨a, rfl⟩))
        fun a ha h0 ↦ hP _ ⟨h0, Or.inl ⟨a, ha, rfl⟩⟩⟩
  obtain ⟨J, hJ⟩ := ValuationSubring.exists_finset_subcover_of_forall_subset R P S
    fun V hR hP ↦ by
      obtain ⟨hV, hl, hc⟩ := hbwd V hR hP
      exact hcov V hV hl hc
  exact ⟨J, fun V hV hl hc ↦ hJ V (hfwd V hV hl hc).1 (hfwd V hV hl hc).2⟩

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
