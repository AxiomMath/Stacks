module

public import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# Retractions from sections of the second map of a biproduct triangle

Let `A ⟶ B ⊞ C ⟶ D ⟶ A[1]` be a distinguished triangle in a pretriangulated category, whose
first map has components `u₁ : A ⟶ B` and `u₂ : A ⟶ C` and whose second map has components
`e : B ⟶ D` and `-c : C ⟶ D`. The proof of [Stacks, Tag 0FUW] produces a retraction of `u₁` from a
section of the second map whose image contains the summand `C`: by [Stacks, Tag 05QT] the first
map then has a retraction vanishing on `C`, and its restriction to `B` is a retraction of `u₁`.

This file proves that step, together with the purely additive step of the same proof which turns
a decomposition `A ⊕ M ≅ R` with a factorisation of the second component into a section of the
map `A ⊕ R' ⟶ R`.

## Main results

* `CategoryTheory.Pretriangulated.exists_retraction_of_distTriang_biprod`: the retraction of `u₁`.
* `CategoryTheory.Limits.exists_retraction_and_section_of_isIso_biprod_desc`: the section built
  from a biproduct decomposition.
* `CategoryTheory.Limits.exists_retraction_and_section_of_iso`: such a section transported along
  isomorphisms.
* `CategoryTheory.Pretriangulated.exists_retraction_and_section_of_forall_map`: such a section
  from its images under a jointly faithful family of triangulated functors, as for the
  restrictions to the members of a decomposition of a space into open and closed pieces.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 05QT](https://stacks.math.columbia.edu/tag/05QT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Limits

/-- **Transporting a normalised section along isomorphisms.** Let `c : A ⟶ R`, `Θ : W ⟶ R` and
`c' : A ⟶ R'`, `Θ' : W' ⟶ R'` correspond under isomorphisms `α : R ≅ R'` and `β : W ≅ W'`. If
`c' ⊕ Θ'` has a section restricting to the inclusion of `A` along `c'`, then `c ⊕ Θ` has one
restricting to the inclusion of `A` along `c`. -/
theorem exists_retraction_and_section_of_iso {C : Type*} [Category* C] [Preadditive C]
    {A R R' W W' : C} (c : A ⟶ R) (c' : A ⟶ R')
    (Θ : W ⟶ R) (Θ' : W' ⟶ R') (α : R ≅ R') (β : W ≅ W') (hc : c ≫ α.hom = c')
    (hΘ : Θ ≫ α.hom = β.hom ≫ Θ')
    (H : ∃ (τ : R' ⟶ A) (ν : R' ⟶ W'), c' ≫ τ = 𝟙 A ∧ c' ≫ ν = 0 ∧ τ ≫ c' + ν ≫ Θ' = 𝟙 R') :
    ∃ (τ : R ⟶ A) (ν : R ⟶ W), c ≫ τ = 𝟙 A ∧ c ≫ ν = 0 ∧ τ ≫ c + ν ≫ Θ = 𝟙 R := by
  obtain ⟨τ, ν, h₁, h₂, h₃⟩ := H
  have hc' : c = c' ≫ α.inv := by rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hΘ' : β.inv ≫ Θ = Θ' ≫ α.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hΘ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine ⟨α.hom ≫ τ, α.hom ≫ ν ≫ β.inv, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hc, h₁]
  · rw [← Category.assoc, hc, ← Category.assoc, h₂, zero_comp]
  · rw [Category.assoc, Category.assoc, Category.assoc, hΘ', hc', ← Category.assoc τ,
      ← Category.assoc ν Θ' α.inv, ← Preadditive.comp_add, ← Preadditive.add_comp, h₃,
      Category.id_comp, Iso.hom_inv_id]

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- A section `σ` of `c ⊕ Θ` with `c ≫ σ = inl` gives a normalised section of `c ⊕ Θ`. -/
private theorem exists_retraction_and_section_of_lift {A R W : C} (c : A ⟶ R) (Θ : W ⟶ R)
    (σ : R ⟶ A ⊞ W) (hc : c ≫ σ = biprod.inl) (hσ : σ ≫ biprod.desc c Θ = 𝟙 R) :
    ∃ (τ : R ⟶ A) (ν : R ⟶ W), c ≫ τ = 𝟙 A ∧ c ≫ ν = 0 ∧ τ ≫ c + ν ≫ Θ = 𝟙 R := by
  refine ⟨σ ≫ biprod.fst, σ ≫ biprod.snd, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hc, biprod.inl_fst]
  · rw [← Category.assoc, hc, biprod.inl_snd]
  · rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, ← biprod.desc_eq, hσ]

/-- **A biproduct decomposition gives a section.** Let `c ⊕ μ : A ⊕ M ⟶ R` be an isomorphism and
let `μ` factor as `λ ≫ Θ` through `Θ : R' ⟶ R`. Then there are `τ : R ⟶ A` and `ν : R ⟶ R'` with
`c ≫ τ = 𝟙`, `c ≫ ν = 0` and `τ ≫ c + ν ≫ Θ = 𝟙`: the map `c ⊕ Θ : A ⊕ R' ⟶ R` has a section
whose restriction along `c` is the inclusion of `A`. -/
theorem exists_retraction_and_section_of_isIso_biprod_desc {A R M R' : C} (c : A ⟶ R)
    (μ : M ⟶ R) [IsIso (biprod.desc c μ)] (Θ : R' ⟶ R) (l : M ⟶ R') (hl : l ≫ Θ = μ) :
    ∃ (τ : R ⟶ A) (ν : R ⟶ R'), c ≫ τ = 𝟙 A ∧ c ≫ ν = 0 ∧ τ ≫ c + ν ≫ Θ = 𝟙 R := by
  have hc : c ≫ inv (biprod.desc c μ) = biprod.inl := by
    rw [IsIso.comp_inv_eq, biprod.inl_desc]
  refine exists_retraction_and_section_of_lift c Θ (inv (biprod.desc c μ) ≫ biprod.map (𝟙 A) l)
    ?_ ?_
  · rw [← Category.assoc, hc, biprod.inl_map, Category.id_comp]
  · rw [Category.assoc, IsIso.inv_comp_eq, Category.comp_id]
    ext <;> simp [hl]

end Limits

namespace Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **A retraction of the first component of the first map of a biproduct triangle.** Let
`A ⟶ B ⊞ C ⟶ D ⟶ A[1]` be a distinguished triangle whose first map is `lift u₁ u₂` and whose
second map is `desc e (-c)`. Let `s : D ⟶ B` and `t : D ⟶ C` satisfy `s ≫ e + t ≫ c = 𝟙`,
`c ≫ s = 0` and `c ≫ t = 𝟙`, so that `lift s (-t)` is a section of the second map sending `c`
to minus the inclusion of `C`. Then `u₁` has a retraction.

By [Stacks, Tag 05QT] the map `lift u₁ u₂ ⊕ lift s (-t) : A ⊕ D ⟶ B ⊞ C` is an isomorphism; the
first component of its inverse is a retraction of the first map vanishing on `C`, and its
restriction to `B` is the retraction of `u₁`. -/
theorem exists_retraction_of_distTriang_biprod {A B C' D : C} (u₁ : A ⟶ B) (u₂ : A ⟶ C')
    (e : B ⟶ D) (c : C' ⟶ D) (w : D ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift u₁ u₂) (biprod.desc e (-c)) w ∈ distTriang C)
    (s : D ⟶ B) (t : D ⟶ C') (h₁ : s ≫ e + t ≫ c = 𝟙 D) (h₂ : c ≫ s = 0)
    (h₃ : c ≫ t = 𝟙 C') :
    ∃ r : B ⟶ A, u₁ ≫ r = 𝟙 A := by
  have hσ : biprod.lift s (-t) ≫ biprod.desc e (-c) = 𝟙 D := by
    simpa using h₁
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : A ⊞ D ⟶ B ⊞ C',
      Φ = biprod.desc (biprod.lift u₁ u₂) (biprod.lift s (-t)) := ⟨_, rfl⟩
  have : IsIso Φ := hΦ ▸ isIso_biprod_desc_of_distTriang _ hT (biprod.lift s (-t)) hσ
  have hinl : biprod.lift u₁ u₂ ≫ inv Φ = biprod.inl := by
    rw [IsIso.comp_inv_eq, hΦ, biprod.inl_desc]
  have hinr : biprod.inr ≫ inv Φ ≫ biprod.fst = (0 : C' ⟶ A) := by
    have hcσ : c ≫ biprod.lift s (-t) = -biprod.inr := by
      ext <;> simp [h₂, h₃]
    have hσΦ : biprod.lift s (-t) ≫ inv Φ = biprod.inr := by
      rw [IsIso.comp_inv_eq, hΦ, biprod.inr_desc]
    have : (-biprod.inr : C' ⟶ B ⊞ C') ≫ inv Φ ≫ biprod.fst = 0 := by
      rw [← hcσ, Category.assoc, ← Category.assoc _ (inv Φ), hσΦ, biprod.inr_fst, comp_zero]
    simpa using this
  refine ⟨biprod.inl ≫ inv Φ ≫ biprod.fst, ?_⟩
  have h : biprod.lift u₁ u₂ ≫ inv Φ ≫ biprod.fst = 𝟙 A := by
    rw [← Category.assoc, hinl, biprod.inl_fst]
  rw [← h, biprod.lift_eq, Preadditive.add_comp, Category.assoc, Category.assoc u₂, hinr,
    comp_zero, add_zero]

/-- **The retraction from a section through two factorisations.** In the situation of
`exists_retraction_of_distTriang_biprod`, assume the second map of the triangle is
`desc (Rb κ ≫ Ψ) (-(Ri c₀))`, where `Rb : C' ⥤ C` and `Ri : C'' ⥤ C`, `Rj : E ⥤ C'` and
`Rp : E ⥤ C''` are functors and `Ψ_K : Rb (Rj K) ≅ Ri (Rp K)` is natural in `K`. Let
`θ : W ⟶ Ω` be a morphism of `E`, with `κ : Ω' ⟶ Rj Ω` and `c₀ : A₀ ⟶ Rp Ω`. If

* `τ : Rp Ω ⟶ A₀` and `ν : Rp Ω ⟶ Rp W` satisfy `c₀ ≫ τ = 𝟙`, `c₀ ≫ ν = 0` and
  `τ ≫ c₀ + ν ≫ Rp θ = 𝟙`, and
* `δ : Rj W ⟶ Ω'` satisfies `δ ≫ κ = Rj θ`,

then `u₁` has a retraction. This is the formal part of the proof of [Stacks, Tag 0FUW], with
`Rb`, `Ri`, `Rj`, `Rp` the derived direct images along the blowup, the centre, the exceptional
divisor and its projection to the centre. -/
theorem exists_retraction_of_distTriang_of_factorisations {C' C'' E : Type*} [Category* C']
    [Category* C''] [Preadditive C''] [Category* E] (Rb : C' ⥤ C) (Ri : C'' ⥤ C) [Ri.Additive]
    (Rj : E ⥤ C') (Rp : E ⥤ C'') (Ψ : ∀ K, Rb.obj (Rj.obj K) ≅ Ri.obj (Rp.obj K))
    (hΨ : ∀ {K K' : E} (φ : K ⟶ K'),
      Rb.map (Rj.map φ) ≫ (Ψ K').hom = (Ψ K).hom ≫ Ri.map (Rp.map φ))
    {A : C} {Ω' : C'} {A₀ : C''} {Ω W : E} (u₁ : A ⟶ Rb.obj Ω') (u₂ : A ⟶ Ri.obj A₀)
    (e : Rb.obj Ω' ⟶ Ri.obj (Rp.obj Ω)) (c : Ri.obj A₀ ⟶ Ri.obj (Rp.obj Ω))
    (κ : Ω' ⟶ Rj.obj Ω) (c₀ : A₀ ⟶ Rp.obj Ω) (he : e = Rb.map κ ≫ (Ψ Ω).hom)
    (hc : c = Ri.map c₀) (w : Ri.obj (Rp.obj Ω) ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift u₁ u₂) (biprod.desc e (-c)) w ∈ distTriang C)
    (θ : W ⟶ Ω) (τ : Rp.obj Ω ⟶ A₀) (ν : Rp.obj Ω ⟶ Rp.obj W) (hτ : c₀ ≫ τ = 𝟙 A₀)
    (hν : c₀ ≫ ν = 0) (hτν : τ ≫ c₀ + ν ≫ Rp.map θ = 𝟙 _) (δ : Rj.obj W ⟶ Ω')
    (hδ : δ ≫ κ = Rj.map θ) :
    ∃ r : Rb.obj Ω' ⟶ A, u₁ ≫ r = 𝟙 A := by
  subst he hc
  refine exists_retraction_of_distTriang_biprod _ _ _ _ w hT
    (Ri.map ν ≫ (Ψ W).inv ≫ Rb.map δ) (Ri.map τ) ?_ ?_ ?_
  · rw [Category.assoc, Category.assoc, ← Rb.map_comp_assoc, hδ, hΨ, Iso.inv_hom_id_assoc,
      ← Ri.map_comp, ← Ri.map_comp, ← Ri.map_add, add_comm, hτν, Ri.map_id]
  · rw [← Ri.map_comp_assoc, hν, Ri.map_zero, zero_comp]
  · rw [← Ri.map_comp, hτ, Ri.map_id]

/-- **A normalised section of `c ⊕ Θ` from its images under a jointly faithful family of
triangulated functors.** Let `F r : C ⥤ D r` be triangulated functors such that a morphism of `C`
vanishes as soon as all its images vanish. Let `c : A ⟶ R` and `Θ : W ⟶ R` be such that, for every
`r`, `F r (c)` has a retraction `τ` and there is `ν` with `τ ≫ F r (c) + ν ≫ F r (Θ) = 𝟙`. Then
there are `τ : R ⟶ A` and `ν : R ⟶ W` with `c ≫ τ = 𝟙`, `c ≫ ν = 0` and `τ ≫ c + ν ≫ Θ = 𝟙`.

The connecting map of a triangle on `c` vanishes because its images do, so `c` has a retraction;
the second map of a triangle on `c ⊕ Θ` vanishes for the same reason, so `c ⊕ Θ` has a section,
which the retraction of `c` corrects to one restricting to the inclusion of `A` along `c`. -/
theorem exists_retraction_and_section_of_forall_map {ι : Type*} {D : ι → Type*}
    [∀ r, Category* (D r)] [∀ r, Preadditive (D r)] [∀ r, HasZeroObject (D r)]
    [∀ r, HasShift (D r) ℤ] [∀ r (n : ℤ), (shiftFunctor (D r) n).Additive]
    [∀ r, Pretriangulated (D r)] (F : ∀ r, C ⥤ D r) [∀ r, (F r).CommShift ℤ]
    [∀ r, (F r).Additive] [∀ r, (F r).IsTriangulated]
    (hF : ∀ {X Y : C} (f : X ⟶ Y), (∀ r, (F r).map f = 0) → f = 0)
    {A R W : C} (c : A ⟶ R) (Θ : W ⟶ R)
    (h : ∀ r, ∃ (τ : (F r).obj R ⟶ (F r).obj A) (ν : (F r).obj R ⟶ (F r).obj W),
      (F r).map c ≫ τ = 𝟙 _ ∧ τ ≫ (F r).map c + ν ≫ (F r).map Θ = 𝟙 _) :
    ∃ (τ : R ⟶ A) (ν : R ⟶ W), c ≫ τ = 𝟙 A ∧ c ≫ ν = 0 ∧ τ ≫ c + ν ≫ Θ = 𝟙 R := by
  obtain ⟨Q, v, w, hT⟩ := distinguished_cocone_triangle c
  have hw : w = 0 := hF w fun r => by
    obtain ⟨τ, ν, h₁, -⟩ := h r
    have : IsSplitMono ((F r).map c) := IsSplitMono.mk' ⟨τ, h₁⟩
    have h₀ : (F r).map w ≫ ((F r).commShiftIso (1 : ℤ)).hom.app A = 0 :=
      Triangle.mor₃_eq_zero_of_mono₁ _ ((F r).map_distinguished _ hT)
        (by exact (inferInstance : Mono ((F r).map c)))
    exact (Preadditive.IsIso.comp_right_eq_zero _ _).mp h₀
  obtain ⟨e, he, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT hw
  have hτ₀ : c ≫ e.hom ≫ biprod.fst = 𝟙 A := by
    rw [← Category.assoc]
    exact (congrArg (· ≫ biprod.fst) he).trans biprod.inl_fst
  obtain ⟨Q', v', w', hT'⟩ := distinguished_cocone_triangle (biprod.desc c Θ)
  have hv : v' = 0 := hF v' fun r => by
    obtain ⟨τ, ν, -, h₃⟩ := h r
    have : IsSplitEpi ((F r).map (biprod.desc c Θ)) := IsSplitEpi.mk'
      ⟨τ ≫ (F r).map biprod.inl + ν ≫ (F r).map biprod.inr, by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, ← Functor.map_comp,
          ← Functor.map_comp, biprod.inl_desc, biprod.inr_desc, h₃]⟩
    exact Triangle.mor₂_eq_zero_of_epi₁ _ ((F r).map_distinguished _ hT')
      (by exact (inferInstance : Epi ((F r).map (biprod.desc c Θ))))
  obtain ⟨σ₀, hσ⟩ := Triangle.coyoneda_exact₂ _ hT' (𝟙 R) (by simp [hv])
  let σ : R ⟶ A ⊞ W := σ₀
  have hσ' : σ ≫ biprod.desc c Θ = 𝟙 R := hσ.symm
  let τ₀ : R ⟶ A := e.hom ≫ biprod.fst
  have hτ₀' : c ≫ τ₀ = 𝟙 A := hτ₀
  let σ₁ : R ⟶ A ⊞ W := σ - τ₀ ≫ (c ≫ σ - biprod.inl)
  have hc₁ : c ≫ σ₁ = biprod.inl := by
    simp only [σ₁, Preadditive.comp_sub, ← Category.assoc, hτ₀', Category.id_comp, sub_sub_cancel]
  have hσ₁ : σ₁ ≫ biprod.desc c Θ = 𝟙 R := by
    simp only [σ₁, Preadditive.sub_comp, Category.assoc, hσ', biprod.inl_desc, Category.comp_id,
      sub_self, comp_zero, sub_zero]
  exact exists_retraction_and_section_of_lift c Θ σ₁ hc₁ hσ₁

end Pretriangulated

end CategoryTheory
