module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Basic

/-!
# Examples of affine chart indices

Two instances of `AlgebraicGeometry.Scheme.AffineChartIndex`, refinement being the passage to a
basic open: the index of all affine opens of a scheme, and, for a morphism `f : Y ⟶ X`, the index
of pairs of affine opens `U ⊆ X`, `V ⊆ Y` with `V ≤ f⁻¹ U`, refinement being the passage to a basic
open in both components. The latter is the index on which determinants of naive cotangent
complexes of `Γ(X, U) → Γ(Y, V)` are glued.

## Main definitions

* `AlgebraicGeometry.Scheme.IsBasicOpenOf U W`: `W` is a basic open `D(g)` of `U`.
* `AlgebraicGeometry.Scheme.AffineChartIndex.affineOpens`: the index of all affine opens.
* `AlgebraicGeometry.Scheme.AffineChartIndex.ofHom`: the index of pairs of affine opens over a
  morphism of schemes.

## Main results

* `AlgebraicGeometry.Scheme.IsBasicOpenOf.trans`: a basic open of a basic open of an affine open is
  a basic open of it.
* `AlgebraicGeometry.Scheme.IsBasicOpenOf.exists_common`: two affine opens have, near each point of
  their intersection, a common basic open.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- `W` is a basic open of the open `U`: `W = D(g)` for some `g : Γ(X, U)`. -/
def Scheme.IsBasicOpenOf (U W : X.Opens) : Prop :=
  ∃ g : Γ(X, U), W = X.basicOpen g

namespace Scheme.IsBasicOpenOf

/-- An open is a basic open of itself. -/
theorem refl (U : X.Opens) : X.IsBasicOpenOf U U :=
  ⟨1, (X.basicOpen_one (U := U)).symm⟩

/-- A basic open of a basic open of an affine open is a basic open of it. -/
theorem trans {U W W' : X.Opens} (hU : IsAffineOpen U) (h : X.IsBasicOpenOf U W)
    (h' : X.IsBasicOpenOf W W') : X.IsBasicOpenOf U W' := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := h'
  obtain ⟨f, hf⟩ := hU.basicOpen_basicOpen_is_basicOpen g g'
  exact ⟨f, hf.symm⟩

/-- A basic open of `U` is contained in `U`. -/
theorem le {U W : X.Opens} (h : X.IsBasicOpenOf U W) : W ≤ U := by
  obtain ⟨g, rfl⟩ := h
  exact X.basicOpen_le g

/-- A basic open of an affine open is affine. -/
theorem isAffineOpen {U W : X.Opens} (hU : IsAffineOpen U) (h : X.IsBasicOpenOf U W) :
    IsAffineOpen W := by
  obtain ⟨g, rfl⟩ := h
  exact hU.basicOpen g

/-- The basic opens of an affine open form a basis of its topology. -/
theorem exists_mem_le {U W : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) (hxW : x ∈ W) :
    ∃ W', X.IsBasicOpenOf U W' ∧ x ∈ W' ∧ W' ≤ W := by
  obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxW⟩ hxU
  exact ⟨_, ⟨f, rfl⟩, hxf, hfW⟩

/-- Near a point of the intersection of two affine opens, and inside any neighbourhood of it,
there is an open which is a basic open of both. -/
theorem exists_common {U₁ U₂ W : X.Opens} (h₁ : IsAffineOpen U₁) (h₂ : IsAffineOpen U₂) {x : X}
    (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) (hxW : x ∈ W) :
    ∃ W', X.IsBasicOpenOf U₁ W' ∧ X.IsBasicOpenOf U₂ W' ∧ x ∈ W' ∧ W' ≤ W := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter h₁ h₂ x ⟨hx₁, hx₂⟩
  obtain ⟨W', hW', hxW', hW'W⟩ := exists_mem_le (h₁.basicOpen f) hxf hxW
  exact ⟨W', trans h₁ ⟨f, rfl⟩ hW', trans h₂ ⟨g, rfl⟩ (hfg ▸ hW'), hxW', hW'W⟩

end Scheme.IsBasicOpenOf

namespace Scheme.AffineChartIndex

/-- **The index of all affine opens of `X`**, refinement being the passage to a basic open. -/
noncomputable def affineOpens (X : Scheme.{u}) : X.AffineChartIndex where
  ι := X.affineOpens
  V := id
  Refines V' V := X.IsBasicOpenOf V.1 V'.1
  exists_eq_basicOpen h := h
  refines_refl V := IsBasicOpenOf.refl V.1
  refines_trans {_ _ c} h' h := IsBasicOpenOf.trans c.2 h h'
  exists_mem x := by
    obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_affineOpens X) (Opens.mem_top x)
    exact ⟨⟨V, hV⟩, hxV⟩
  exists_refines_le {V} _ hy _ hyW := by
    obtain ⟨W', hW', hyW', hW'W⟩ := IsBasicOpenOf.exists_mem_le V.2 hy hyW
    exact ⟨⟨W', hW'.isAffineOpen V.2⟩, hW', hyW', hW'W⟩
  exists_refines_refines {V₁ V₂} _ hy₁ hy₂ := by
    obtain ⟨W', h₁, h₂, hyW', -⟩ :=
      IsBasicOpenOf.exists_common V₁.2 V₂.2 hy₁ hy₂ (Opens.mem_top _)
    exact ⟨⟨W', h₁.isAffineOpen V₁.2⟩, h₁, h₂, hyW'⟩

variable {Y : Scheme.{u}} (f : Y ⟶ X)

/-- **The index of pairs of affine charts over a morphism `f : Y ⟶ X`.** A chart is a pair of
affine opens `U ⊆ X` and `V ⊆ Y` with `V ≤ f⁻¹ U`; its open is `V`, and a pair refines another
when both of its components are basic opens of the other's. -/
noncomputable def ofHom : Y.AffineChartIndex where
  ι := {p : X.affineOpens × Y.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1}
  V p := p.1.2
  Refines p' p := X.IsBasicOpenOf p.1.1.1 p'.1.1.1 ∧ Y.IsBasicOpenOf p.1.2.1 p'.1.2.1
  exists_eq_basicOpen h := h.2
  refines_refl p := ⟨IsBasicOpenOf.refl _, IsBasicOpenOf.refl _⟩
  refines_trans {_ _ p} h' h :=
    ⟨IsBasicOpenOf.trans p.1.1.2 h.1 h'.1, IsBasicOpenOf.trans p.1.2.2 h.2 h'.2⟩
  exists_mem y := by
    obtain ⟨U, hU, hyU, -⟩ :=
      Opens.isBasis_iff_nbhd.mp (isBasis_affineOpens X) (Opens.mem_top (f y))
    obtain ⟨V, hV, hyV, hVU⟩ :=
      Opens.isBasis_iff_nbhd.mp (isBasis_affineOpens Y) (show y ∈ f ⁻¹ᵁ U from hyU)
    exact ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩, hyV⟩
  exists_refines_le {p} _ hy _ hyW := by
    obtain ⟨W', hW', hyW', hW'W⟩ := IsBasicOpenOf.exists_mem_le p.1.2.2 hy hyW
    exact ⟨⟨(p.1.1, ⟨W', hW'.isAffineOpen p.1.2.2⟩), hW'.le.trans p.2⟩,
      ⟨IsBasicOpenOf.refl _, hW'⟩, hyW', hW'W⟩
  exists_refines_refines {p₁ p₂} y hy₁ hy₂ := by
    obtain ⟨U', hU'₁, hU'₂, hyU', -⟩ := IsBasicOpenOf.exists_common p₁.1.1.2 p₂.1.1.2
      (p₁.2 hy₁) (p₂.2 hy₂) (Opens.mem_top (f y))
    obtain ⟨V', hV'₁, hV'₂, hyV', hV'U'⟩ := IsBasicOpenOf.exists_common p₁.1.2.2 p₂.1.2.2
      hy₁ hy₂ (show y ∈ f ⁻¹ᵁ U' from hyU')
    exact ⟨⟨(⟨U', hU'₁.isAffineOpen p₁.1.1.2⟩, ⟨V', hV'₁.isAffineOpen p₁.1.2.2⟩), hV'U'⟩,
      ⟨hU'₁, hV'₁⟩, ⟨hU'₂, hV'₂⟩, hyV'⟩

end Scheme.AffineChartIndex

end AlgebraicGeometry
