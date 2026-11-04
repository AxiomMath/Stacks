module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# A curried action out of a rank-one object is invertible

Let `B`, `D`, `E` be objects of a category with a functor `T` ("`- ⊗ B`") and bijections
`curry : (Z ⟶ D) ≃ (T Z ⟶ E)` natural in `Z`, as for an internal Hom `D = Hom(B, E)`. Let
`mul : T B ⟶ B` be a "multiplication" with a natural section `s : B ⟶ T B` up to automorphism,
that is `s ≫ T(c) = c ≫ s` for endomorphisms `c` of `B` and `s ≫ mul` invertible. If the
endomorphisms of `B` commute, `Hom(B, E)` is free of rank one over them on a generator `θ`, and
`B ≅ D`, then the map `B ⟶ D` curried from `mul ≫ θ` is an isomorphism.

This is the formal part of the second condition of a relative dualizing complex
([Stacks, Tag 0E9W]): the map `Δ_*𝒪_X ⟶ R𝓗om(Δ_*𝒪_X, E)` that `θ` defines through the derived
multiplication is invertible once `R𝓗om(Δ_*𝒪_X, E)` is abstractly isomorphic to `Δ_*𝒪_X`.

## Main definitions

* `CategoryTheory.IsRankOneHom` — `Hom(B, E)` is free of rank one over a commutative `End(B)`.

## Main results

* `CategoryTheory.isIso_curry_symm_mul_comp` — the criterion.
* `CategoryTheory.IsRankOneHom.of_adjunction` — rank one through an adjunction `L ⊣ R` with
  `R E ≅ O`, and its transport along isomorphisms and fully faithful functors.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C] {B D E : C} (T : C ⥤ C)
  (curry : ∀ Z : C, (Z ⟶ D) ≃ (T.obj Z ⟶ E))
  (hcurry : ∀ {Z Z' : C} (c : Z' ⟶ Z) (g : Z ⟶ D), curry Z' (c ≫ g) = T.map c ≫ curry Z g)
  (mul : T.obj B ⟶ B) (s : B ⟶ T.obj B) (hs : ∀ c : B ⟶ B, s ≫ T.map c = c ≫ s)
  [IsIso (s ≫ mul)] (hcomm : ∀ c d : B ⟶ B, c ≫ d = d ≫ c)
  (θ : B ⟶ E) (hθ : Function.Bijective (fun c : B ⟶ B => c ≫ θ)) (ψ : B ≅ D)

include hcurry hs hcomm hθ ψ in
/-- **A curried action out of a rank-one object is invertible.** With the data above, the map
`B ⟶ D` corresponding under `curry` to `mul ≫ θ` is an isomorphism. -/
theorem isIso_curry_symm_mul_comp : IsIso ((curry B).symm (mul ≫ θ)) := by
  set a := (curry B).symm (mul ≫ θ) with ha
  set α : B ⟶ B := a ≫ ψ.inv with hα
  obtain ⟨β, hβ⟩ := hθ.2 (s ≫ curry B ψ.hom)
  have haα : a = α ≫ ψ.hom := by rw [hα, Category.assoc, ψ.inv_hom_id, Category.comp_id]
  have key : (α ≫ β) ≫ θ = (s ≫ mul) ≫ θ := by
    have h1 : s ≫ curry B a = s ≫ mul ≫ θ := by rw [ha, Equiv.apply_symm_apply]
    rw [haα, hcurry, ← Category.assoc, hs, Category.assoc] at h1
    have hβ' : β ≫ θ = s ≫ curry B ψ.hom := hβ
    rw [Category.assoc, hβ', h1, Category.assoc]
  have hu : α ≫ β = s ≫ mul := hθ.1 key
  have hαiso : IsIso α := by
    refine ⟨β ≫ inv (s ≫ mul), ?_, ?_⟩
    · rw [← Category.assoc, hu, IsIso.hom_inv_id]
    · rw [Category.assoc, hcomm (inv (s ≫ mul)) α, ← Category.assoc, hcomm β α, hu,
        IsIso.hom_inv_id]
  rw [haα]
  infer_instance

/-- `CategoryTheory.isIso_curry_symm_mul_comp` for bijections that are additive, in a
preadditive category. -/
theorem isIso_curry_symm_mul_comp_of_addEquiv [Preadditive C]
    (curry : ∀ Z : C, (Z ⟶ D) ≃+ (T.obj Z ⟶ E))
    (hcurry : ∀ {Z Z' : C} (c : Z' ⟶ Z) (g : Z ⟶ D), curry Z' (c ≫ g) = T.map c ≫ curry Z g)
    (mul : T.obj B ⟶ B) (s : B ⟶ T.obj B) (hs : ∀ c : B ⟶ B, s ≫ T.map c = c ≫ s)
    (hsm : IsIso (s ≫ mul)) (hcomm : ∀ c d : B ⟶ B, c ≫ d = d ≫ c)
    (θ : B ⟶ E) (hθ : Function.Bijective (fun c : B ⟶ B => c ≫ θ)) (ψ : B ≅ D) :
    IsIso ((curry B).symm (mul ≫ θ)) :=
  isIso_curry_symm_mul_comp T (fun Z => (curry Z).toEquiv) hcurry mul s hs hcomm θ hθ ψ

end CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- `Hom(B, E)` is free of rank one over the commutative ring `End(B)`: the endomorphisms of
`B` commute, and some `θ : B ⟶ E` makes `c ↦ c ≫ θ` a bijection `End(B) ≃ Hom(B, E)`. -/
def IsRankOneHom (B E : C) : Prop :=
  (∀ c d : B ⟶ B, c ≫ d = d ≫ c) ∧ ∃ θ : B ⟶ E, Function.Bijective (fun c : B ⟶ B => c ≫ θ)

namespace IsRankOneHom

variable {B E B' E' : C}

/-- Endomorphisms of `O` that commute still commute after applying a functor that is surjective
on them. -/
private theorem comm_of_surjective_map {D : Type*} [Category D] {F : C ⥤ D} {O : C}
    (hcomm : ∀ c d : O ⟶ O, c ≫ d = d ≫ c)
    (hsurj : Function.Surjective (fun c : O ⟶ O => F.map c)) (c d : F.obj O ⟶ F.obj O) :
    c ≫ d = d ≫ c := by
  obtain ⟨c, rfl⟩ := hsurj c
  obtain ⟨d, rfl⟩ := hsurj d
  rw [← F.map_comp, ← F.map_comp, hcomm]

/-- Being free of rank one is invariant under isomorphisms of both objects. -/
theorem of_iso (h : IsRankOneHom B E) (e : B ≅ B') (e' : E ≅ E') : IsRankOneHom B' E' := by
  obtain ⟨hcomm, θ, hθ⟩ := h
  refine ⟨fun c d => ?_, e.inv ≫ θ ≫ e'.hom, ?_, ?_⟩
  · have := hcomm (e.hom ≫ c ≫ e.inv) (e.hom ≫ d ≫ e.inv)
    simpa using congrArg (fun t => e.inv ≫ t ≫ e.hom) this
  · intro c d hcd
    have : (e.hom ≫ c ≫ e.inv) ≫ θ = (e.hom ≫ d ≫ e.inv) ≫ θ := by
      have := congrArg (fun t => e.hom ≫ t ≫ e'.inv) hcd
      simpa using this
    simpa using congrArg (fun t => e.inv ≫ t ≫ e.hom) (hθ.1 this)
  · intro g
    obtain ⟨c, hc⟩ := hθ.2 (e.hom ≫ g ≫ e'.inv)
    refine ⟨e.inv ≫ c ≫ e.hom, ?_⟩
    have hc' : c ≫ θ = e.hom ≫ g ≫ e'.inv := hc
    simp [reassoc_of% hc']

/-- Being free of rank one is reflected by a fully faithful functor. -/
theorem of_fullyFaithful {D : Type*} [Category D] {F : C ⥤ D} (hF : F.FullyFaithful)
    (h : IsRankOneHom (F.obj B) (F.obj E)) : IsRankOneHom B E := by
  obtain ⟨hcomm, θ, hθ⟩ := h
  refine ⟨fun c d => hF.map_injective (by simpa using hcomm (F.map c) (F.map d)),
    hF.preimage θ, ?_, ?_⟩
  · intro c d hcd
    refine hF.map_injective (hθ.1 ?_)
    have := congrArg F.map hcd
    simpa using this
  · intro g
    obtain ⟨c, hc⟩ := hθ.2 (F.map g)
    refine ⟨hF.preimage c, hF.map_injective ?_⟩
    have hc' : c ≫ θ = F.map g := hc
    simp [hc']

/-- Being free of rank one is preserved by a fully faithful functor. -/
theorem map {D : Type*} [Category D] {F : C ⥤ D} (hF : F.FullyFaithful)
    (h : IsRankOneHom B E) : IsRankOneHom (F.obj B) (F.obj E) := by
  obtain ⟨hcomm, θ, hθ⟩ := h
  refine ⟨comm_of_surjective_map hcomm hF.map_surjective, F.map θ, ?_, ?_⟩
  · intro c d hcd
    obtain ⟨c, rfl⟩ := hF.map_surjective c
    obtain ⟨d, rfl⟩ := hF.map_surjective d
    have hcd' : F.map (c ≫ θ) = F.map (d ≫ θ) := by simpa using hcd
    rw [hθ.1 (hF.map_injective hcd')]
  · intro g
    obtain ⟨g, rfl⟩ := hF.map_surjective g
    obtain ⟨c, hc⟩ := hθ.2 g
    exact ⟨F.map c, by simpa using congrArg F.map hc⟩

/-- **Rank one through an adjunction.** For `L ⊣ R`, an object `O` with commuting
endomorphisms on which `L` is surjective, and `E` with `R E ≅ O`, the group `Hom(L O, E)` is
free of rank one over `End(L O)`. -/
theorem of_adjunction {D : Type*} [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {O : C} {E : D} (hcomm : ∀ c d : O ⟶ O, c ≫ d = d ≫ c)
    (hsurj : Function.Surjective (fun c : O ⟶ O => L.map c)) (φ : R.obj E ≅ O) :
    IsRankOneHom (L.obj O) E := by
  refine ⟨comm_of_surjective_map hcomm hsurj, (adj.homEquiv O E).symm φ.inv, ?_, ?_⟩
  · intro c d hcd
    obtain ⟨c, rfl⟩ := hsurj c
    obtain ⟨d, rfl⟩ := hsurj d
    dsimp only at hcd ⊢
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_left_symm]
      at hcd
    have := (adj.homEquiv O E).symm.injective hcd
    have := congrArg (fun t => t ≫ φ.hom) this
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at this
    rw [this]
  · intro g
    refine ⟨L.map (adj.homEquiv O E g ≫ φ.hom), ?_⟩
    dsimp only
    rw [← Adjunction.homEquiv_naturality_left_symm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Equiv.symm_apply_apply]

end IsRankOneHom

end CategoryTheory
