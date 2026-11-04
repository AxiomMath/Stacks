module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import Mathlib.Data.List.TFAE

/-!
# Characterizations of syntomic morphisms

Syntomicity of a morphism of schemes may be checked on every pair of compatible affine opens, on
arbitrary open coverings by syntomic morphisms, or on affine open coverings by syntomic ring
maps. It is also preserved when the source and target are restricted to compatible open
subschemes.

## Main results

* `AlgebraicGeometry.syntomic_tfae` gives four equivalent characterizations of a syntomic
  morphism.
* `AlgebraicGeometry.syntomic_resLE` shows that syntomicity is preserved by restriction to
  compatible open subschemes.

## Implementation notes

The four entries of `syntomic_tfae` are, in order, global syntomicity, the condition on every
compatible pair of affine opens, an open-covering criterion using restricted morphisms, and an
affine-open-covering criterion using maps on rings of sections. The restriction result states
the clause following the list of equivalent conditions in the source.

Both proofs are consequences of `AlgebraicGeometry.Syntomic.hasRingHomProperty`: the Zariski
locality of syntomicity on source and target, and its invariance under composition with open
immersions, are then supplied by instance search.

## References

* [Stacks Project, Tag 01UD](https://stacks.math.columbia.edu/tag/01UD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The restriction of a morphism to affine opens is syntomic when its map on sections is. -/
private theorem syntomic_resLE_of_syntomic_appLE {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens}
    {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)
    (h : (f.appLE V U hUV).hom.Syntomic) : Syntomic (f.resLE V U hUV) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Syntomic)]
  exact (RingHom.syntomic_propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f V U hUV)).mpr h

/-- The four characterizations of a syntomic morphism: the global condition, the condition on
every compatible pair of affine opens, an open-covering criterion, and an affine-open-covering
criterion on rings of sections. -/
@[stacks 01UD "syntomic characterization"]
theorem syntomic_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE [
      Syntomic f,
      ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
        (hUV : U ≤ f ⁻¹ᵁ V),
        letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
        Algebra.Syntomic Γ(S, V) Γ(X, U),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            ∀ i, Syntomic (f.resLE (V j) (U i) ((le_iSup U i).trans hU.le)),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i,
                let hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
                letI : Algebra Γ(S, V j) Γ(X, U i) := (f.appLE (V j) (U i) hUV).hom.toAlgebra
                Algebra.Syntomic Γ(S, V j) Γ(X, U i)] := by
  tfae_have 1 ↔ 2 :=
    ⟨fun hf U hU V hV hUV => (RingHom.syntomic_iff _).mp
        ((HasRingHomProperty.iff_appLE (P := @Syntomic) (f := f)).mp hf ⟨V, hV⟩ ⟨U, hU⟩ hUV),
      fun h => (HasRingHomProperty.iff_appLE (P := @Syntomic) (f := f)).mpr
        fun V U hUV => (RingHom.syntomic_iff _).mpr (h U.1 U.2 V.1 V.2 hUV)⟩
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hf
      refine ⟨ULift.{u} Unit, fun _ => ⊤, by simp [IsOpenCover], fun _ => ?_⟩
      refine ⟨ULift.{u} Unit, fun _ => ⊤, by simp, fun _ => ?_⟩
      exact IsZariskiLocalAtSource.resLE (P := @Syntomic) (by simp) hf
    · rintro ⟨J, V, hV, hU⟩
      apply (IsZariskiLocalAtSource.iff_exists_resLE (P := @Syntomic) (f := f)).mpr
      intro x
      obtain ⟨j, hxj⟩ := hV.exists_mem (f x)
      obtain ⟨I, U, hU, hUi⟩ := hU j
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp
        (hU.symm ▸ (show x ∈ f ⁻¹ᵁ V j by simpa using hxj))
      exact ⟨V j, U i, hxi, (le_iSup U i).trans hU.le, hUi i⟩
  tfae_have 1 → 4 := by
    intro hf
    let V : S.affineOpens → S.Opens := fun j => j.1
    refine ⟨S.affineOpens, V, iSup_affineOpens_eq_top S, fun j => j.2, fun j => ?_⟩
    let U : {U : X.affineOpens // (U : X.Opens) ≤ f ⁻¹ᵁ V j} → X.Opens := fun i => i.1.1
    have hU : (⨆ i, U i) = f ⁻¹ᵁ V j := by
      refine le_antisymm (iSup_le fun i => i.2) fun x hx => ?_
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx (f ⁻¹ᵁ V j).isOpen
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hxW⟩
    refine ⟨_, U, hU, fun i => i.1.2, fun i => ?_⟩
    exact tfae_1_iff_2.mp hf _ i.1.2 _ j.2 _
  tfae_have 4 → 3 := by
    rintro ⟨J, V, hV, hVaff, hProp⟩
    refine ⟨J, V, hV, fun j => ?_⟩
    obtain ⟨I, U, hU, hUi, hQ⟩ := hProp j
    exact ⟨I, U, hU, fun i =>
      syntomic_resLE_of_syntomic_appLE f (hUi i) (hVaff j) _ ((RingHom.syntomic_iff _).mpr (hQ i))⟩
  tfae_finish

/-- Restricting a syntomic morphism to compatible open subschemes of its source and target is
syntomic. -/
@[stacks 01UD "restriction of a syntomic morphism"]
theorem syntomic_resLE {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Syntomic f) (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    Syntomic (f.resLE V U hUV) :=
  IsZariskiLocalAtSource.resLE hUV hf

end AlgebraicGeometry
