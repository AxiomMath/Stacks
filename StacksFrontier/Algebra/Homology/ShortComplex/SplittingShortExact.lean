module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Two out of three for short exactness along a split sequence of short complexes

Let `𝒜` be an abelian category. A short complex of short complexes of `𝒜` which is split —
a retraction of its first map and a section of its second map decomposing the identity of the
middle term — has the property that short exactness of two of its three terms implies short
exactness of the third.

A split short complex of short complexes identifies the middle term with the direct sum of the
outer two, and short exactness is a direct sum of three conditions: monomorphy of the first map,
epimorphy of the second and exactness. The proofs below are the three conditions handled
separately rather than through such an identification.

## Main results

* `CategoryTheory.ShortComplex.Splitting.shortExact_X₁` and `shortExact_X₃`: a term of a split
  short complex of short complexes which is a retract of a short exact term is short exact.
* `CategoryTheory.ShortComplex.Splitting.shortExact_X₂`: if both outer terms of a split short
  complex of short complexes are short exact, so is the middle one.

## Implementation notes

Exactness is handled through the additive homology functor `ShortComplex 𝒜 ⥤ 𝒜`: a splitting
identity goes to a splitting identity between the homology objects, and a retract of a zero
object is a zero object, as is a direct sum of two zero objects.

The monomorphy and epimorphy of a retract are read off the two commuting squares of the
morphism of short complexes realising it, whose other leg is a split monomorphism, respectively
a split epimorphism. For the middle term they are instead the cancellation criteria
`CategoryTheory.Preadditive.mono_iff_cancel_zero` and `epi_iff_cancel_zero`, applied to the
decomposition of the identity.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {T : ShortComplex (ShortComplex 𝒜)}

namespace Splitting

/-- A retract of a short exact short complex is short exact. -/
private theorem shortExact_of_retract {S S' : ShortComplex 𝒜} (i : S ⟶ S') (r : S' ⟶ S)
    (hir : i ≫ r = 𝟙 S) (h : S'.ShortExact) : S.ShortExact := by
  have hr₁ : i.τ₁ ≫ r.τ₁ = 𝟙 _ := by rw [← comp_τ₁, hir, id_τ₁]
  have hr₃ : i.τ₃ ≫ r.τ₃ = 𝟙 _ := by rw [← comp_τ₃, hir, id_τ₃]
  have : IsSplitMono i.τ₁ := ⟨⟨⟨r.τ₁, hr₁⟩⟩⟩
  have : IsSplitEpi r.τ₃ := ⟨⟨⟨i.τ₃, hr₃⟩⟩⟩
  have := h.mono_f
  have := h.epi_g
  refine ShortExact.mk' ?_ ?_ ?_
  · rw [exact_iff_isZero_homology]
    have e : (homologyFunctor 𝒜).map i ≫ (homologyFunctor 𝒜).map r = 𝟙 _ := by
      rw [← Functor.map_comp, hir, Functor.map_id]
    have hz : IsZero ((homologyFunctor 𝒜).obj S') := (exact_iff_isZero_homology _).1 h.exact
    refine (Limits.IsZero.iff_id_eq_zero ((homologyFunctor 𝒜).obj S)).2 ?_
    rw [← e, hz.eq_of_tgt ((homologyFunctor 𝒜).map i) 0, zero_comp]
  · have hc : Mono (S.f ≫ i.τ₂) := by
      rw [← i.comm₁₂]; exact mono_comp _ _
    exact mono_of_mono S.f i.τ₂
  · have hc : Epi (r.τ₂ ≫ S.g) := by
      rw [r.comm₂₃]; exact epi_comp _ _
    exact epi_of_epi r.τ₂ S.g

/-- A retract of a short exact short complex, along a split monomorphism of short complexes with
the retraction compatible with the structure maps, is short exact. -/
theorem shortExact_X₁ (sp : T.Splitting) (h : T.X₂.ShortExact) : T.X₁.ShortExact :=
  shortExact_of_retract T.f sp.r sp.f_r h

/-- A retract of a short exact short complex, along a split epimorphism of short complexes with
the section compatible with the structure maps, is short exact. -/
theorem shortExact_X₃ (sp : T.Splitting) (h : T.X₂.ShortExact) : T.X₃.ShortExact :=
  shortExact_of_retract sp.s T.g sp.s_g h

/-- If both outer terms of a split short complex of short complexes are short exact, so is the
middle term. -/
theorem shortExact_X₂ (sp : T.Splitting) (h₁ : T.X₁.ShortExact) (h₃ : T.X₃.ShortExact) :
    T.X₂.ShortExact := by
  have hid₁ : sp.r.τ₁ ≫ T.f.τ₁ + T.g.τ₁ ≫ sp.s.τ₁ = 𝟙 _ := by
    rw [← comp_τ₁, ← comp_τ₁, ← add_τ₁, sp.id, id_τ₁]
  have hid₃ : sp.r.τ₃ ≫ T.f.τ₃ + T.g.τ₃ ≫ sp.s.τ₃ = 𝟙 _ := by
    rw [← comp_τ₃, ← comp_τ₃, ← add_τ₃, sp.id, id_τ₃]
  have := h₁.mono_f
  have := h₁.epi_g
  have := h₃.mono_f
  have := h₃.epi_g
  refine ShortExact.mk' ?_ ?_ ?_
  · rw [exact_iff_isZero_homology]
    have hz₁ : IsZero ((homologyFunctor 𝒜).obj T.X₁) :=
      (exact_iff_isZero_homology _).1 h₁.exact
    have hz₃ : IsZero ((homologyFunctor 𝒜).obj T.X₃) :=
      (exact_iff_isZero_homology _).1 h₃.exact
    have e : (homologyFunctor 𝒜).map (sp.r ≫ T.f) +
        (homologyFunctor 𝒜).map (T.g ≫ sp.s) = 𝟙 _ := by
      rw [← Functor.map_add, sp.id, Functor.map_id]
    refine (Limits.IsZero.iff_id_eq_zero ((homologyFunctor 𝒜).obj T.X₂)).2 ?_
    rw [← e, Functor.map_comp, Functor.map_comp,
      hz₁.eq_of_src ((homologyFunctor 𝒜).map T.f) 0,
      hz₃.eq_of_tgt ((homologyFunctor 𝒜).map T.g) 0, comp_zero, zero_comp, add_zero]
  · rw [Preadditive.mono_iff_cancel_zero]
    intro Z u hu
    have hg : u ≫ T.g.τ₁ = 0 := by
      refine (Preadditive.mono_iff_cancel_zero T.X₃.f).1 h₃.mono_f Z (u ≫ T.g.τ₁) ?_
      rw [assoc, T.g.comm₁₂, ← assoc, hu, zero_comp]
    have hrr : u ≫ sp.r.τ₁ = 0 := by
      refine (Preadditive.mono_iff_cancel_zero T.X₁.f).1 h₁.mono_f Z (u ≫ sp.r.τ₁) ?_
      rw [assoc, sp.r.comm₁₂, ← assoc, hu, zero_comp]
    rw [← comp_id u, ← hid₁, Preadditive.comp_add, ← assoc, ← assoc, hg, hrr, zero_comp,
      zero_comp, add_zero]
  · rw [Preadditive.epi_iff_cancel_zero]
    intro Z u hu
    have hf : T.f.τ₃ ≫ u = 0 := by
      refine (Preadditive.epi_iff_cancel_zero T.X₁.g).1 h₁.epi_g Z (T.f.τ₃ ≫ u) ?_
      rw [← assoc, ← T.f.comm₂₃, assoc, hu, comp_zero]
    have hss : sp.s.τ₃ ≫ u = 0 := by
      refine (Preadditive.epi_iff_cancel_zero T.X₃.g).1 h₃.epi_g Z (sp.s.τ₃ ≫ u) ?_
      rw [← assoc, ← sp.s.comm₂₃, assoc, hu, comp_zero]
    rw [← id_comp u, ← hid₃, Preadditive.add_comp, assoc, assoc, hf, hss, comp_zero, comp_zero,
      add_zero]

end Splitting

end ShortComplex

end CategoryTheory
