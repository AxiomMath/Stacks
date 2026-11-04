module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.LocallyConstantPushforward

/-!
# Locally constant maps on an étale scheme over a normal integral scheme and its generic fibre

Let `Y` be an integral normal scheme with generic point `ξ`, let `g : Spec κ(ξ) ⟶ Y` be the
inclusion of the generic point and let `T ⟶ Y` be étale. Pulling locally constant maps back along
the projection `T ×_Y Spec κ(ξ) ⟶ T` is a bijection
`LC(T, M) ≃ LC(T ×_Y Spec κ(ξ), M)`: every point of `T` lies in an integral open, whose generic
point is the only point of that open over `ξ`, and the generic fibre `T ×_Y Spec κ(ξ)` maps
injectively onto the set of those generic points.

On sheaves this says that the comparison `𝓛_Y(M) ⟶ g_* 𝓛_{κ(ξ)}(M)` of the sheaves of locally
constant `M`-valued maps is an isomorphism, which is Stacks 09Z5 (1) for the sheaf of locally
constant maps (that sheaf being the constant sheaf by
`AlgebraicGeometry.smallEtaleConstantSheafIsoLocallyConstantMapsModule`).

## Main results

* `Stacks.EtaleCohomology.bijective_comap_pullbackFst_genericPointInclusion` — the bijection on
  locally constant maps.
* `Stacks.EtaleCohomology.isIso_locallyConstantToDirectImage_genericPointInclusion` — the
  comparison of sheaves is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

universe u r

namespace Stacks.EtaleCohomology

section Topology

variable {Y T : Scheme.{u}} [IsIntegral Y] [IsNormal Y] (q : T ⟶ Y) [Etale q]

omit [IsNormal Y] in
/-- An integral scheme étale over `Y` has its generic point over the generic point of `Y`. -/
theorem etale_genericPoint_eq {Z : Scheme.{u}} [IsIntegral Z] (p : Z ⟶ Y) [Etale p] :
    p (genericPoint Z) = genericPoint Y := by
  have h : p (genericPoint Z) ∈ genericPoints Y :=
    genericPoints_image_of_generalizingMap p.base (Flat.generalizingMap p)
      (by simp [genericPoints_eq_singleton])
  rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at h

/-- If a pullback has at most one point, matching pairs of points are equal componentwise. -/
private theorem eq_and_eq_of_subsingleton_pullback {X₁ X₂ S : Scheme.{u}} (f : X₁ ⟶ S)
    (g : X₂ ⟶ S) [Subsingleton ↥(pullback f g)] {x₁ x₂ : X₁} {y₁ y₂ : X₂}
    (h₁ : f x₁ = g y₁) (h₂ : f x₂ = g y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  obtain ⟨w₁, hx₁, hy₁⟩ := Scheme.Pullback.exists_preimage_pullback x₁ y₁ h₁
  obtain ⟨w₂, hx₂, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback x₂ y₂ h₂
  rw [← hx₁, ← hx₂, ← hy₁, ← hy₂, Subsingleton.elim w₁ w₂]
  exact ⟨rfl, rfl⟩

omit [IsNormal Y] in
/-- An integral scheme étale over `Y` has at most one point over the generic point of `Y`. -/
theorem eq_of_etale_of_eq_genericPoint {Z : Scheme.{u}} [IsIntegral Z] (p : Z ⟶ Y) [Etale p]
    {z₁ z₂ : Z} (h₁ : p z₁ = genericPoint Y) (h₂ : p z₂ = genericPoint Y) : z₁ = z₂ := by
  have := subsingleton_pullback_genericPointInclusion (X := Y) (Z := Z) p
  exact (eq_and_eq_of_subsingleton_pullback p (genericPointInclusion Y)
    (h₁.trans (genericPointInclusion_closedPoint Y).symm)
    (h₂.trans (genericPointInclusion_closedPoint Y).symm)).1

omit [IsNormal Y] in
/-- Two points of `T` over the generic point of `Y` which lie in a common integral open of `T`
are equal. -/
theorem eq_of_mem_range_of_isIntegral {Z : Scheme.{u}} (e : Z ⟶ T) [IsOpenImmersion e]
    [IsIntegral Z] {t₁ t₂ : T} (ht₁ : t₁ ∈ Set.range e.base) (ht₂ : t₂ ∈ Set.range e.base)
    (h₁ : q t₁ = genericPoint Y) (h₂ : q t₂ = genericPoint Y) : t₁ = t₂ := by
  obtain ⟨z₁, rfl⟩ := ht₁
  obtain ⟨z₂, rfl⟩ := ht₂
  rw [eq_of_etale_of_eq_genericPoint (e ≫ q) h₁ h₂]

/-- The projection from the generic fibre `T ×_Y Spec κ(ξ) ⟶ T` is injective. -/
theorem injective_pullbackFst_genericPointInclusion :
    Function.Injective (pullback.fst q (genericPointInclusion Y)) := by
  intro p₁ p₂ hp
  set π := pullback.fst q (genericPointInclusion Y)
  obtain ⟨Z, e, he, hZ, z, hz⟩ := exists_isIntegral_open_of_etale q (π p₁)
  have : Subsingleton ↥(pullback (e ≫ q) (genericPointInclusion Y)) :=
    subsingleton_pullback_genericPointInclusion (X := Y) (Z := Z) (e ≫ q)
  let iso := pullbackRightPullbackFstIso q (genericPointInclusion Y) e
  have hsub : Subsingleton ↥(pullback e π) :=
    ⟨fun a b => by simpa using congrArg iso.inv (Subsingleton.elim (iso.hom a) (iso.hom b))⟩
  exact (eq_and_eq_of_subsingleton_pullback e π hz (hz.trans hp)).2

omit [IsNormal Y] in
/-- The image of the generic point of an integral open of `T` lies in the generic fibre. -/
theorem mem_range_pullbackFst_of_isIntegral {Z : Scheme.{u}} (e : Z ⟶ T) [IsOpenImmersion e]
    [IsIntegral Z] :
    e (genericPoint Z) ∈ Set.range (pullback.fst q (genericPointInclusion Y)) := by
  rw [Scheme.Pullback.range_fst, range_genericPointInclusion Y]
  exact etale_genericPoint_eq (e ≫ q)

/-- The image of the generic point of `Z` lies in every open of `T` meeting the image of `Z`. -/
private theorem mem_of_isGenericPoint_of_isOpen {Z : Scheme.{u}} (e : Z ⟶ T) {η : Z}
    (hη : IsGenericPoint η ⊤) {U : Set T} (hU : IsOpen U) {z : Z} (hz : e z ∈ U) : e η ∈ U :=
  ((hη.specializes (Set.mem_univ z)).map e.base.hom.continuous).mem_open hU hz

/-- A locally constant map is constant on the image of an irreducible scheme. -/
private theorem apply_eq_apply_of_mem_range {Z : Scheme.{u}} [IrreducibleSpace Z] (e : Z ⟶ T)
    {η : Z} {M : Type*} (s : LocallyConstant T M) {t : T} (ht : t ∈ Set.range e.base) :
    s t = s (e η) := by
  have hirr : IsPreirreducible (Set.range e.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ Z).isPreirreducible.image _
      e.base.hom.continuous.continuousOn
  exact s.apply_eq_of_isPreconnected hirr.isPreconnected ht (Set.mem_range_self η)

/-- **Locally constant maps on an étale `Y`-scheme are those on its generic fibre.** Let `Y` be
an integral normal scheme, `T ⟶ Y` étale and `M` a set. Pulling back along the projection
`T ×_Y Spec κ(ξ) ⟶ T` of the generic fibre is a bijection on locally constant `M`-valued maps. -/
theorem bijective_comap_pullbackFst_genericPointInclusion (M : Type*) :
    Function.Bijective (LocallyConstant.comap
      (pullback.fst q (genericPointInclusion Y)).base.hom : LocallyConstant T M →
        LocallyConstant ↥(pullback q (genericPointInclusion Y)) M) := by
  classical
  set π := pullback.fst q (genericPointInclusion Y)
  choose Z e he hZ ht using exists_isIntegral_open_of_etale q
  have hgen : ∀ t, ∃ z : Z t, IsGenericPoint z ⊤ := fun t => by
    have := hZ t
    exact ⟨_, genericPoint_spec (Z t)⟩
  choose η hη using hgen
  let ξ : T → T := fun t => (e t) (η t)
  have hξ : ∀ t, ξ t ∈ Set.range π := fun t => by
    have := he t
    have := hZ t
    have h := mem_range_pullbackFst_of_isIntegral q (e t)
    rwa [← (hη t).eq (genericPoint_spec (Z t))] at h
  choose p hp using hξ
  have hπq : ∀ x, q (π x) = genericPoint Y := fun x => by
    have h : π x ∈ Set.range π := ⟨x, rfl⟩
    rwa [Scheme.Pullback.range_fst, range_genericPointInclusion Y] at h
  have hξq : ∀ t, q (ξ t) = genericPoint Y := fun t => hp t ▸ hπq (p t)
  have hξmem : ∀ t t', t' ∈ Set.range (e t).base → ξ t ∈ Set.range (e t').base := by
    rintro t _ ⟨z, rfl⟩
    exact mem_of_isGenericPoint_of_isOpen (e t) (hη t) (he _).base_open.isOpen_range (ht _)
  have hξeq : ∀ t t', t' ∈ Set.range (e t).base → ξ t = ξ t' := by
    intro t t' ht'
    have := he t'
    have := hZ t'
    exact eq_of_mem_range_of_isIntegral q (e t') (hξmem t t' ht') (hξmem t' t' (ht t'))
      (hξq t) (hξq t')
  have hξπ : ∀ x, ξ (π x) = π x := fun x => by
    have := he (π x)
    have := hZ (π x)
    exact eq_of_mem_range_of_isIntegral q (e (π x)) (hξmem _ _ (ht _)) (ht _) (hξq _) (hπq x)
  have hconst : ∀ (s : LocallyConstant T M) (t t' : T), t' ∈ Set.range (e t).base →
      s t' = s (ξ t) := fun s t _ ht' => by
    have := hZ t
    exact apply_eq_apply_of_mem_range (e t) s ht'
  refine ⟨fun s₁ s₂ h => ?_, fun s => ?_⟩
  · ext t
    rw [hconst s₁ t t (ht t), hconst s₂ t t (ht t), ← hp t]
    exact DFunLike.congr_fun h (p t)
  · refine ⟨⟨fun t => s (p t), ?_⟩, ?_⟩
    · refine (IsLocallyConstant.iff_exists_open _).2 fun t => ⟨Set.range (e t).base,
        (he t).base_open.isOpen_range, ht t, fun t' ht' => ?_⟩
      rw [injective_pullbackFst_genericPointInclusion q
        ((hp t').trans ((hξeq t t' ht').symm.trans (hp t).symm))]
    · ext x
      change s (p (π x)) = s x
      rw [injective_pullbackFst_genericPointInclusion q ((hp (π x)).trans (hξπ x))]

end Topology

variable (Λ : Type r) [Ring Λ] (M : Type (max (u + 1) r)) [AddCommGroup M] [Module Λ M]

/-- **Stacks 09Z5 (1) for locally constant maps.** On an integral normal scheme `Y` the
comparison `𝓛_Y(M) ⟶ g_* 𝓛_{κ(ξ)}(M)` along the inclusion `g` of the generic point is an
isomorphism. -/
instance isIso_locallyConstantToDirectImage_genericPointInclusion (Y : Scheme.{u})
    [IsIntegral Y] [IsNormal Y] :
    IsIso (locallyConstantToDirectImage.{u, r} Λ M (genericPointInclusion Y)) := by
  refine isIso_of_bijective_app Λ _ fun W => ?_
  have : Etale W.hom := W.prop
  exact bijective_comap_pullbackFst_genericPointInclusion (Y := Y) W.hom M

end Stacks.EtaleCohomology

end
