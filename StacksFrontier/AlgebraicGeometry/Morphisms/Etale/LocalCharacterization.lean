module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Étaleness is local on source and target

A morphism of schemes `f : X ⟶ S` is étale exactly when the ring map `𝒪_S(V) → 𝒪_X(U)` is étale
for every pair of affine opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`. Equivalently, there is an open
covering `S = ⋃ⱼ Vⱼ` and, for each `j`, an open covering `f⁻¹(Vⱼ) = ⋃ᵢ Uᵢ` such that each
restriction `Uᵢ → Vⱼ` is étale; or the same with affine coverings and étaleness of the ring maps
`𝒪_S(Vⱼ) → 𝒪_X(Uᵢ)`. Moreover the restriction `U → V` of an étale morphism to opens `U ⊆ X`,
`V ⊆ S` with `f(U) ⊆ V` is étale.

## Main results

* `AlgebraicGeometry.etale_tfae`: the four characterizations of étaleness agree.
* `AlgebraicGeometry.etale_resLE`: the restriction of an étale morphism to open subschemes is
  étale.
* `AlgebraicGeometry.etale_tfae_and_resLE`: both statements together.

## Implementation notes

Mathlib's `AlgebraicGeometry.Etale` is the property of morphisms associated with the local
property `RingHom.Etale` of ring maps, and the results are instances of the general
`HasRingHomProperty` API. A subset `U ⊆ X` with `f(U) ⊆ V` is written as `U ≤ f ⁻¹ᵁ V`, the
restriction `f|_U : U → V` is `AlgebraicGeometry.Scheme.Hom.resLE`, and the ring map
`𝒪_S(V) → 𝒪_X(U)` is `AlgebraicGeometry.Scheme.Hom.appLE`. The coverings are families of opens:
the covering of `S` is indexed by a type `J`, and the covering of `f⁻¹(Vⱼ)` by a type `I j`
depending on `j`, both in the universe of the schemes.

## References

* [Stacks Project, Tag 02GJ](https://stacks.math.columbia.edu/tag/02GJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- If `f` is étale then so is its restriction `U → V` to any opens `U ⊆ X`, `V ⊆ S` with
`f(U) ⊆ V`. -/
@[stacks 02GJ "moreover: restriction to open subschemes"]
theorem etale_resLE {f : X ⟶ S} (hf : Etale f) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) : Etale (f.resLE V U e) :=
  have := hf
  inferInstance

/-- Étaleness of a morphism of schemes can be checked on all pairs of affine opens, on open
coverings of the target and of the preimages of their members, or on affine such coverings. -/
@[stacks 02GJ "equivalence of (1), (2), (3) and (4)"]
theorem etale_tfae (f : X ⟶ S) :
    List.TFAE [
      Etale f,
      ∀ (U : X.affineOpens) (V : S.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.Etale,
      ∃ (J : Type u) (V : J → S.Opens) (I : J → Type u) (U : ∀ j, I j → X.Opens),
        ⨆ j, V j = ⊤ ∧ (∀ j, ⨆ i, U j i = f ⁻¹ᵁ V j) ∧
          ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, Etale (f.resLE (V j) (U j i) e),
      ∃ (J : Type u) (V : J → S.affineOpens) (I : J → Type u) (U : ∀ j, I j → X.affineOpens),
        ⨆ j, (V j).1 = ⊤ ∧ (∀ j, ⨆ i, (U j i).1 = f ⁻¹ᵁ (V j).1) ∧
          ∀ j i, ∃ e : (U j i).1 ≤ f ⁻¹ᵁ (V j).1, (f.appLE (V j) (U j i) e).hom.Etale] := by
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have : IsZariskiLocalAtTarget @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u}) (Q := RingHom.Etale)
  have : MorphismProperty.RespectsRight @Etale.{u} @IsOpenImmersion :=
    ⟨fun i _ f hf ↦ by have : Etale f := hf; exact inferInstance⟩
  tfae_have 1 → 2 := fun hf U V e ↦ HasRingHomProperty.appLE @Etale f hf V U e
  tfae_have 2 → 4 := by
    intro h
    refine ⟨S.affineOpens, id, fun V ↦ {U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V.1},
      fun _ U ↦ U.1, iSup_affineOpens_eq_top S, fun V ↦ ?_, fun V U ↦ ⟨U.2, h U.1 V U.2⟩⟩
    refine le_antisymm (iSup_le fun U ↦ U.2) fun x hx ↦ ?_
    obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩
  tfae_have 4 → 1 := by
    rintro ⟨J, V, I, U, hV, hU, H⟩
    refine (HasRingHomProperty.iff_exists_appLE (P := @Etale)
      (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        (RingHom.Etale.propertyIsLocal.HoldsForLocalizationAway
          RingHom.Etale.containsIdentities)).1).mpr fun x ↦ ?_
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show f x ∈ ⨆ j, (V j).1 by rw [hV]; trivial)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
      (show x ∈ ⨆ i, (U j i).1 by rw [hU j]; exact hj)
    obtain ⟨e, he⟩ := H j i
    exact ⟨V j, U j i, hi, e, he⟩
  tfae_have 1 → 3 := fun hf ↦ ⟨PUnit, fun _ ↦ ⊤, fun _ ↦ PUnit, fun _ _ ↦ f ⁻¹ᵁ ⊤,
    iSup_const, fun _ ↦ iSup_const, fun _ _ ↦ ⟨le_rfl, etale_resLE hf _ _ _⟩⟩
  tfae_have 3 → 1 := by
    rintro ⟨J, V, I, U, hV, hU, H⟩
    refine (IsZariskiLocalAtSource.iff_exists_resLE (P := @Etale)).mpr fun x ↦ ?_
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show f x ∈ ⨆ j, V j by rw [hV]; trivial)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, U j i by rw [hU j]; exact hj)
    obtain ⟨e, he⟩ := H j i
    exact ⟨V j, U j i, hi, e, he⟩
  tfae_finish

/-- The whole statement: the four characterizations of étaleness agree, and étaleness passes to
restrictions to open subschemes. -/
@[stacks 02GJ]
theorem etale_tfae_and_resLE (f : X ⟶ S) :
    List.TFAE [
      Etale f,
      ∀ (U : X.affineOpens) (V : S.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.Etale,
      ∃ (J : Type u) (V : J → S.Opens) (I : J → Type u) (U : ∀ j, I j → X.Opens),
        ⨆ j, V j = ⊤ ∧ (∀ j, ⨆ i, U j i = f ⁻¹ᵁ V j) ∧
          ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, Etale (f.resLE (V j) (U j i) e),
      ∃ (J : Type u) (V : J → S.affineOpens) (I : J → Type u) (U : ∀ j, I j → X.affineOpens),
        ⨆ j, (V j).1 = ⊤ ∧ (∀ j, ⨆ i, (U j i).1 = f ⁻¹ᵁ (V j).1) ∧
          ∀ j i, ∃ e : (U j i).1 ≤ f ⁻¹ᵁ (V j).1, (f.appLE (V j) (U j i) e).hom.Etale] ∧
    (Etale f → ∀ (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V), Etale (f.resLE V U e)) :=
  ⟨etale_tfae f, fun hf U V e ↦ etale_resLE hf U V e⟩

end AlgebraicGeometry

end
