module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionDegreewise

/-!
# Surjectivity of restriction across a morphism with controlled kernel and cokernel

Let `i : Y ⟶ X` be a morphism of schemes and `c : A ⟶ B` a morphism of abelian sheaves on
`X_étale`. Writing `K` for the kernel of `c`, `I` for its coimage and `C` for the cokernel of the
monomorphism `I ⟶ B`, the restriction maps `r_q` along `i` satisfy:

* `r_q(A)` is surjective as soon as `r_q(K)` and `r_q(B)` are, `r_{q+1}(K)` and `r_q(C)` are
  injective, and `r_{q-1}(C)` is surjective (`surjective_etaleCohomologyRestrictionMap_source`);
* `r_q(B)` is surjective as soon as `r_q(A)`, `r_{q+1}(K)` and `r_q(C)` are surjective and
  `r_{q+1}(A)` and `r_{q+1}(I)` are injective (`surjective_etaleCohomologyRestrictionMap_target`).

In the dévissage of Stacks Project Tag 03SC part (7) the restriction map is injective for every
sheaf, so the conditions reduce to surjectivity on the kernel and cokernel; these are supported
on finitely many closed points, or handled one degree lower. The quotient half of the four
lemma, `surjective_etaleCohomologyRestrictionMap_X₃_of_shortExact`, is recorded on the way.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Passage to a quotient.** For `0 → F₁ → F₂ → F₃ → 0`, if restriction along `i` is surjective
in degree `q` on `F₂`, surjective in degree `q + 1` on `F₁` and injective in degree `q + 1` on
`F₂`, then it is surjective in degree `q` on `F₃`. -/
theorem surjective_etaleCohomologyRestrictionMap_X₃_of_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (q : ℕ)
    (h₂ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q))
    (h₁ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ (q + 1)))
    (h₂' : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ (q + 1))) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)
  intro y
  obtain ⟨z, hz⟩ := h₁ (y.comp hS'.extClass rfl)
  have hz0 : z.comp (Ext.mk₀ S.f) (add_zero (q + 1)) = 0 := by
    apply h₂'
    rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.f (q + 1) z, hz, map_zero,
      Ext.comp_assoc_of_third_deg_zero]
    have h0 := hS'.extClass_comp
    simp only [ShortComplex.map_f] at h0
    rw [h0, Ext.comp_zero]
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hS z hz0 rfl
  have hδ' : (hS'.extClass.postcomp _ rfl)
      (y - etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q x₃) = 0 := by
    rw [map_sub]
    refine sub_eq_zero.mpr ?_
    change y.comp hS'.extClass rfl =
      (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q x₃).comp hS'.extClass rfl
    rw [← etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} i hS q (q + 1) rfl, hx₃, hz]
  have hδ : (y - etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q x₃).comp
      hS'.extClass rfl = 0 := hδ'
  obtain ⟨w', hw'⟩ := Ext.covariant_sequence_exact₃ _ hS' _ rfl hδ
  obtain ⟨w₂, hw₂⟩ := h₂ w'
  refine ⟨x₃ + w₂.comp (Ext.mk₀ S.g) (add_zero q), ?_⟩
  rw [map_add, etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.g q w₂, hw₂]
  have hw'' : w'.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.g)) (add_zero q) =
      y - etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q x₃ := hw'
  rw [hw'']
  abel

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- The short exact sequence `0 → ker c → A → coim c → 0`. -/
lemma shortExact_kernel_coimage
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (c : A ⟶ B) :
    (ShortComplex.mk (kernel.ι c) (cokernel.π (kernel.ι c)) (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_cokernel (kernel.ι c) }

/-- **Surjectivity on the source of a morphism.** -/
theorem surjective_etaleCohomologyRestrictionMap_source
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (c : A ⟶ B) (q : ℕ)
    (hK : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i (kernel c) q))
    (hK' : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i (kernel c) (q + 1)))
    (hB : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i B q))
    (hC : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i
      (cokernel (Abelian.factorThruCoimage c)) q))
    (hC' : ∀ m, q = m + 1 → Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i
      (cokernel (Abelian.factorThruCoimage c)) m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i A q) :=
  surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_injective.{u, v, w} i
    (shortExact_kernel_coimage c) q hK
    (surjective_etaleCohomologyRestrictionMap_of_mono.{u, v, w} i
      (Abelian.factorThruCoimage c) q hB hC hC') hK'

/-- **Surjectivity on the target of a morphism.** -/
theorem surjective_etaleCohomologyRestrictionMap_target
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (c : A ⟶ B) (q : ℕ)
    (hA : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i A q))
    (hA' : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i A (q + 1)))
    (hK : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i (kernel c) (q + 1)))
    (hI : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i
      (cokernel (kernel.ι c)) (q + 1)))
    (hC : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i
      (cokernel (Abelian.factorThruCoimage c)) q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i B q) :=
  surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_injective.{u, v, w} i
    (S := ShortComplex.mk (Abelian.factorThruCoimage c)
      (cokernel.π (Abelian.factorThruCoimage c)) (cokernel.condition _))
    { exact := ShortComplex.exact_cokernel _ } q
    (surjective_etaleCohomologyRestrictionMap_X₃_of_shortExact.{u, v, w} i
      (shortExact_kernel_coimage c) q hA hK hA') hC hI

end Stacks.EtaleCohomology

end
