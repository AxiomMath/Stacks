module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannFibreCompact

/-!
# The center map is continuous for the Zariski–Riemann topology

Let `B` be a domain with fraction field `K`, `M` a proper model `f : Y ⟶ Spec B` with point
`j : Spec K ⟶ Y`, and `V` a valuation ring of `K` containing `B`, with center `y_Y(V)` in an open
set `N` of `Y`. Choose an affine open `U ⊆ N` containing `y_Y(V)`, with ring of sections
`A = Γ(Y, U)`; it is a finitely generated `B`-algebra, `f` being locally of finite type.

* The center `Spec V ⟶ Y` factors through `Spec A ⟶ Y`: every point of `Spec V` specializes to
  the closed point, whose image lies in the open `U`. This gives `τ : A ⟶ V`, and
  `ρ : A ⟶ V ⊆ K` is the ring map of `j` (`Spec ρ` followed by `Spec A ⟶ Y` is `j`).
* Let `S ⊆ V` be the images under `ρ` of finitely many generators of `A` over `B`. If a valuation
  ring `V'` of `K` contains `B` and `S`, it contains `ρ(A)`, and `ρ` corestricts to `A ⟶ V'`. Then
  `Spec V' ⟶ Spec A ⟶ Y` solves the valuative problem of `V'`, so it is the center of `V'` by
  uniqueness (`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.eq_center`), and the center
  point of `V'` lies in `U ⊆ N`.

This proves the input `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterOpenBasic` of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centeredGermDeath_of_valuationGermDeath`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_finset_of_isAffineOpen` — the
  statement for an affine open `U` containing the center.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerOpenBasic`

## References

* O. Zariski, P. Samuel, *Commutative Algebra*, Vol. II, Chapter VI, §17
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)
  (V : ValuationSubring (FractionRing B)) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

/-- The center of `V` lands in every open set containing the center point: every point of
`Spec V` specializes to the closed point. -/
theorem range_center_subset {U : M.Y.Opens} (hc : M.centerPoint V hV ∈ U) :
    Set.range (M.center V hV) ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact ((specializes_closedPoint x).map (M.center V hV).continuous).mem_open U.2 hc

/-- **Continuity of the center at an affine open.** If the center of `V` lies in an affine open
`U` of the model, there is a finite subset `S ⊆ V` of `Frac B` (the images of generators of
`Γ(Y, U)` over `B`) such that every valuation ring containing `B` and `S` has its center in
`U`. -/
theorem exists_finset_of_isAffineOpen {U : M.Y.Opens} (hU : IsAffineOpen U)
    (hc : M.centerPoint V hV ∈ U) :
    ∃ S : Finset (FractionRing B), (∀ x ∈ S, x ∈ V) ∧
      ∀ (V' : ValuationSubring (FractionRing B))
        (hV' : ∀ b : B, algebraMap B (FractionRing B) b ∈ V'),
        (∀ x ∈ S, x ∈ V') → M.centerPoint V' hV' ∈ U := by
  classical
  have hr : Set.range (M.center V hV) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact M.range_center_subset V hV hc
  obtain ⟨cA, hcA⟩ : ∃ cA : Spec (.of V) ⟶ Spec Γ(M.Y, U), cA ≫ hU.fromSpec = M.center V hV :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Γ(M.Y, U) ⟶ CommRingCat.of V, Spec.map τ = cA :=
    ⟨_, Spec.map_preimage _⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Γ(M.Y, U) ⟶ CommRingCat.of (FractionRing B),
      ρ = τ ≫ CommRingCat.ofHom (algebraMap V (FractionRing B)) := ⟨_, rfl⟩
  have hρ : Spec.map ρ ≫ hU.fromSpec = M.j := by
    rw [hρdef, Spec.map_comp, Category.assoc, hτ, hcA, specMap_comp_center]
  obtain ⟨β, hβ⟩ : ∃ β : CommRingCat.of B ⟶ Γ(M.Y, U), Spec.map β = hU.fromSpec ≫ M.f :=
    ⟨_, Spec.map_preimage _⟩
  have hft : β.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hβ]
    infer_instance
  have hβρ : β ≫ ρ = CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hβ, ← Category.assoc, hρ, M.fac]
  let : Algebra B Γ(M.Y, U) := β.hom.toAlgebra
  obtain ⟨t, ht⟩ := (hft : Algebra.FiniteType B Γ(M.Y, U)).out
  refine ⟨t.image ρ.hom, ?_, fun V' hV' hS ↦ ?_⟩
  · intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    rw [hρdef]
    exact (τ.hom a).2
  have hall : ∀ a : Γ(M.Y, U), ρ.hom a ∈ V' := by
    let A' : Subalgebra B Γ(M.Y, U) :=
      { V'.toSubring.comap ρ.hom with
        algebraMap_mem' := fun b ↦ by
          have e := congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of (FractionRing B) ↦
            φ.hom b) hβρ
          change ρ.hom (β.hom b) = algebraMap B (FractionRing B) b at e
          change ρ.hom (β.hom b) ∈ V'
          rw [e]
          exact hV' b }
    have hle : Algebra.adjoin B (t : Set Γ(M.Y, U)) ≤ A' :=
      Algebra.adjoin_le fun a ha ↦ hS _ (Finset.mem_image_of_mem _ ha)
    exact fun a ↦ hle (by rw [ht]; exact Algebra.mem_top)
  let τ' : Γ(M.Y, U) →+* V' := ρ.hom.codRestrict V'.toSubring hall
  let l : Spec (.of V') ⟶ M.Y := Spec.map (CommRingCat.ofHom τ') ≫ hU.fromSpec
  have hτ' : CommRingCat.ofHom τ' ≫ CommRingCat.ofHom (algebraMap V' (FractionRing B)) = ρ := by
    ext x
    rfl
  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap V' (FractionRing B))) ≫ l = M.j := by
    simp only [l]
    rw [← Category.assoc, ← Spec.map_comp, hτ', hρ]
  have h₂ : l ≫ M.f = Spec.map (CommRingCat.ofHom (valuationSubringBaseMap V' hV')) := by
    apply eq_of_specMap_comp_eq
    rw [← Category.assoc, h₁, M.fac, ← Spec.map_comp, valuationSubringBaseMap_comp]
  have hl := M.eq_center V' hV' h₁ h₂
  have hmem : l (closedPoint V') ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
  rw [hU.range_fromSpec, hl] at hmem
  exact hmem

end ProperModel

/-- **The center map is continuous for the Zariski–Riemann topology**: if the center of `V` on a
proper model lies in an open `N`, the images of generators of the ring of sections of an affine
open neighbourhood of the center inside `N` form a finite subset `S ⊆ V` such that every
valuation ring containing `B` and `S` has its center in `N`. -/
theorem centerOpenBasic : CenterOpenBasic.{u} := by
  intro B _ _ M V hV N hN hc
  obtain ⟨U, hU, hcU, hUN⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 M.Y.isBasis_affineOpens
      (show M.centerPoint V hV ∈ (⟨N, hN⟩ : M.Y.Opens) from hc)
  obtain ⟨S, hSV, hS⟩ := M.exists_finset_of_isAffineOpen V hV hU hcU
  exact ⟨S, hSV, fun V' hV' hSV' ↦ hUN (hS V' hV' hSV')⟩

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
