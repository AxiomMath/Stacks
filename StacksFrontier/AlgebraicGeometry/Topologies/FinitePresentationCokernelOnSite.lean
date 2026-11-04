module

public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationExtensionOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeLocality

/-!
# Cokernels of maps of sheaves of modules of finite presentation on a site

Let `φ : X₁ ⟶ X₂` be a map of sheaves of modules on a ringed site and `ψ : X₂ ⟶ X₃` a cokernel of
`φ`. If `X₁` and `X₂` are of finite presentation in the sense of Stacks 03DL(7) then so is `X₃`.
This is the cokernel half of Stacks 01BO for finite presentation, read on an arbitrary site.

## Main results

* `Stacks.SheafOfModules.hasSectionsPresentation_cokernel_of_data`: over an object `Z` on which
  `X₂` carries section-level presentation data, finitely many sections of `X₁` generating it,
  whose images are combinations of the generators of `X₂`, give section-level presentation data
  for `X₃`: the images of the generators of `X₂`, with the relations of `X₂` together with the
  rows of coefficients of the images of the generators of `X₁`.
* `Stacks.SheafOfModules.isFinitePresentationOnSite_cokernel_of_isColimit`: **the cokernel of a
  map of sheaves of modules of finite presentation is of finite presentation.**
* `Stacks.SheafOfModules.isFinitePresentationOnSite_of_isZero`: a zero sheaf of modules is of
  finite presentation.

## References

* [Stacks Project, Tag 01BO](https://stacks.math.columbia.edu/tag/01BO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules SheafOfModules

universe u v w

namespace Stacks.SheafOfModules

section Cokernel

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

open Sectionwise

/-- A morphism of presheaves of modules commutes with restriction of sections. -/
private theorem hom_app_restrictₛₗ {R' : Cᵒᵖ ⥤ RingCat.{w}} {P Q : PresheafOfModules.{w} R'}
    (φ : P ⟶ Q) {U V : C} (f : V ⟶ U) (x : P.obj (op U)) :
    Hom.app φ (op V) (P.restrictₛₗ f.op x) = Q.restrictₛₗ f.op (Hom.app φ (op U) x) :=
  PresheafOfModules.naturality_apply φ f.op x

/-- Let `ψ` be a cokernel of `φ : X₁ ⟶ X₂`. Suppose that over `Z` the sheaf `X₂` carries
section-level presentation data `(s₂, r₂)`, that `s₁` generates `X₁` there, and that the image of
each `s₁ j` is the combination of the `s₂` with coefficients `c j`. Then `X₃` carries
section-level presentation data over `Z`: the images of the `s₂`, with the rows `r₂` and `c`. -/
theorem hasSectionsPresentation_cokernel_of_data {X₁ X₂ X₃ : SheafOfModules.{w} R}
    {φ : X₁ ⟶ X₂} {ψ : X₂ ⟶ X₃} (hz : φ ≫ ψ = 0) (hψ : IsColimit (CokernelCofork.ofπ ψ hz))
    {Z : C} {n₁ n₂ q₂ : ℕ}
    (s₁ : Fin n₁ → X₁.val.obj (op Z)) (hs₁ : Generates J X₁.val s₁)
    (s₂ : Fin n₂ → X₂.val.obj (op Z)) (r₂ : Fin q₂ → Fin n₂ → R.obj.obj (op Z))
    (hr₂ : ∀ k, ∑ i, r₂ k i • s₂ i = 0) (hs₂ : Generates J X₂.val s₂)
    (hrel₂ : ∀ (V : C) (hV : V ⟶ Z) (τ : Fin n₂ → R.obj.obj (op V)),
      (∑ i, τ i • X₂.val.restrictₛₗ hV.op (s₂ i) = 0) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : Fin q₂ → R.obj.obj (op B), ∀ i,
          ∑ k, d k * R.obj.map (g ≫ hV).op (r₂ k i) = R.obj.map g.op (τ i))
    (c : Fin n₁ → Fin n₂ → R.obj.obj (op Z))
    (hc : ∀ j, Hom.app φ.val (op Z) (s₁ j) = ∑ i, c j i • s₂ i) :
    HasSectionsPresentation J X₃ Z := by
  have : Epi ψ := epi_of_isColimit_cofork hψ
  refine ⟨n₂, q₂ + n₁, fun i => Hom.app ψ.val (op Z) (s₂ i), Fin.append r₂ c, ?_,
    generates_of_locallySurjective ψ.val (exists_cover_preimage_of_epi ψ) s₂ hs₂, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun j => ?_)
    · simp only [Fin.append_left]
      rw [← hom_app_sum_smul ψ.val (op Z) (r₂ k) s₂, hr₂ k, map_zero]
    · simp only [Fin.append_right]
      rw [← hom_app_sum_smul ψ.val (op Z) (c j) s₂, ← hc j, ← comp_val_app_apply, hz]
      rfl
  · intro V hV τ hτ
    have hx : Hom.app ψ.val (op V) (∑ i, τ i • X₂.val.restrictₛₗ hV.op (s₂ i)) = 0 := by
      rw [hom_app_sum_smul ψ.val (op V)]
      simpa only [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.naturality_apply] using hτ
    have hT₁ := imageSieveOfHom_mem_of_isColimit hz hψ (op V) _ hx
    refine ⟨relationCombinationSieve (Fin.append r₂ c) hV τ, ?_, fun B g hg => hg⟩
    refine J.transitive hT₁ _ fun B g hg => ?_
    obtain ⟨y, hy⟩ := (LocalImage.mem_imageSieveOfHom φ _ g).1 hg
    obtain ⟨T₂, hT₂, hcomb⟩ := hs₁ B (g ≫ hV) y
    refine J.transitive hT₂ _ fun B' k hk => ?_
    obtain ⟨b, hb⟩ := hcomb B' k hk
    let τ' : Fin n₂ → R.obj.obj (op B') := fun i =>
      R.obj.map (k ≫ g).op (τ i) - ∑ j, b j * R.obj.map (k ≫ g ≫ hV).op (c j i)
    have hτ' : ∑ i, τ' i • X₂.val.restrictₛₗ (k ≫ g ≫ hV).op (s₂ i) = 0 := by
      have h1 : X₂.val.restrictₛₗ (k ≫ g).op (∑ i, τ i • X₂.val.restrictₛₗ hV.op (s₂ i)) =
          ∑ i, R.obj.map (k ≫ g).op (τ i) • X₂.val.restrictₛₗ (k ≫ g ≫ hV).op (s₂ i) := by
        rw [restrict_sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Category.assoc]
      have h2 : X₂.val.restrictₛₗ (k ≫ g).op (∑ i, τ i • X₂.val.restrictₛₗ hV.op (s₂ i)) =
          ∑ i, (∑ j, b j * R.obj.map (k ≫ g ≫ hV).op (c j i)) •
            X₂.val.restrictₛₗ (k ≫ g ≫ hV).op (s₂ i) := by
        rw [← restrict_restrict g k]
        show X₂.val.restrictₛₗ k.op (X₂.val.map g.op _) = _
        rw [← hy, ← hom_app_restrictₛₗ φ.val k y, ← hb, hom_app_sum_smul φ.val (op B')]
        have hj : ∀ j, Hom.app φ.val (op B') (X₁.val.restrictₛₗ (k ≫ g ≫ hV).op (s₁ j)) =
            ∑ i, R.obj.map (k ≫ g ≫ hV).op (c j i) •
              X₂.val.restrictₛₗ (k ≫ g ≫ hV).op (s₂ i) := fun j => by
          rw [hom_app_restrictₛₗ φ.val, hc j, Sectionwise.restrict_sum_smul]
        simp only [hj, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_smul]
      simp only [τ', sub_smul, Finset.sum_sub_distrib]
      rw [h1.symm.trans h2, sub_self]
    obtain ⟨T₃, hT₃, hd⟩ := hrel₂ B' (k ≫ g ≫ hV) τ' hτ'
    refine J.superset_covering (fun B'' h hh => ?_) hT₃
    obtain ⟨d, hd⟩ := hd h hh
    refine ⟨Fin.append d (fun j => R.obj.map h.op (b j)), fun i => ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have e1 : ((h ≫ k) ≫ g) ≫ hV = h ≫ k ≫ g ≫ hV := by simp only [Category.assoc]
    have e2 : (h ≫ k) ≫ g = h ≫ k ≫ g := Category.assoc _ _ _
    rw [e1, e2, hd i]
    simp only [τ', map_sub, ring_map_sum_mul]
    have e3 : ∀ j, R.obj.map (h ≫ k ≫ g ≫ hV).op (c j i) =
        R.obj.map h.op (R.obj.map (k ≫ g ≫ hV).op (c j i)) := fun j =>
      (ring_map_map (k ≫ g ≫ hV) h (c j i)).symm
    simp only [e3]
    rw [sub_add_cancel, ring_map_map]

/-- **The cokernel of a map of sheaves of modules of finite presentation is of finite
presentation**, on an arbitrary site: if `ψ` is a cokernel of `φ : X₁ ⟶ X₂` and `X₁`, `X₂` are
of finite presentation in the sense of Stacks 03DL(7), so is `X₃`. -/
theorem isFinitePresentationOnSite_cokernel_of_isColimit {X₁ X₂ X₃ : SheafOfModules.{w} R}
    {φ : X₁ ⟶ X₂} {ψ : X₂ ⟶ X₃} (hz : φ ≫ ψ = 0) (hψ : IsColimit (CokernelCofork.ofπ ψ hz))
    (h₁ : X₁.IsFinitePresentationOnSite) (h₂ : X₂.IsFinitePresentationOnSite) :
    X₃.IsFinitePresentationOnSite := by
  constructor
  intro U
  refine ⟨{ V : Over U // HasSectionsPresentation J X₃ V.left }, fun i => i.1.left,
    fun i => i.1.hom, ?_,
    fun i => hasFiniteGlobalPresentation_over_of_hasSectionsPresentation i.2⟩
  obtain ⟨I₁, V₁, f₁, hc₁, hpr₁⟩ := h₁.locally_hasFiniteGlobalPresentation U
  obtain ⟨I₂, V₂, f₂, hc₂, hpr₂⟩ := h₂.locally_hasFiniteGlobalPresentation U
  refine J.transitive (J.intersection_covering hc₁ hc₂) _ fun Y g hg => ?_
  obtain ⟨i₁, b₁, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg.1
  obtain ⟨i₂, b₂, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg.2
  obtain ⟨n₁, q₁, s₁, r₁, -, hs₁, -⟩ := HasSectionsPresentation.restrict b₁
    (hasSectionsPresentation_of_hasFiniteGlobalPresentation X₁ (V₁ i₁) (hpr₁ i₁))
  obtain ⟨n₂, q₂, s₂, r₂, hr₂, hs₂, hrel₂⟩ := HasSectionsPresentation.restrict b₂
    (hasSectionsPresentation_of_hasFiniteGlobalPresentation X₂ (V₂ i₂) (hpr₂ i₂))
  choose S hS hcomb using fun j : Fin n₁ => hs₂ Y (𝟙 Y) (Hom.app φ.val (op Y) (s₁ j))
  obtain ⟨T, hT, hle⟩ := exists_sieve_le_of_fin n₁ S hS
  refine J.superset_covering (fun B u hu => ?_) hT
  choose c hc using fun j => hcomb j B u (hle j u hu)
  have hdata : HasSectionsPresentation J X₃ B := by
    refine hasSectionsPresentation_cokernel_of_data hz hψ
      (fun j => X₁.val.restrictₛₗ u.op (s₁ j)) (Sectionwise.generates_restrict u s₁ hs₁)
      (fun i => X₂.val.restrictₛₗ u.op (s₂ i)) (fun k i => R.obj.map u.op (r₂ k i))
      (fun k => by rw [← Sectionwise.restrict_sum_smul u (r₂ k) s₂, hr₂ k, map_zero])
      (Sectionwise.generates_restrict u s₂ hs₂) (generatesRelations_restrict s₂ r₂ hrel₂ u) c
      (fun j => ?_)
    rw [hom_app_restrictₛₗ φ.val u, ← hc j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Category.comp_id]
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr
    ⟨⟨Over.mk (u ≫ g), hdata⟩, 𝟙 B, (Category.id_comp (u ≫ g)).symm⟩

end Cokernel

section Zero

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A zero sheaf of modules is of finite presentation. -/
theorem isFinitePresentationOnSite_of_isZero {Z : SheafOfModules.{w} R} (hZ : IsZero Z) :
    Z.IsFinitePresentationOnSite :=
  _root_.SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite Z
    (isCoherentOnSite_zero hZ)

end Zero

end Stacks.SheafOfModules

end
