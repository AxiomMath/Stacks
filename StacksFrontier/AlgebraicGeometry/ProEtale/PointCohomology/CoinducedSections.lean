module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.ContinuousSheaf

/-!
# Sections of the sheaf of a coinduced module

Let `X` be a topological representation of the absolute Galois group `G` of a field, with
jointly continuous action, and let `C(G, X)` be the coinduced representation, on which `g` acts
by `f ↦ (x ↦ g • f (g⁻¹ x))`. Over an affine object `V` of the pro-étale site of the field,
the continuous equivariant functions on geometric points with values in `C(G, X)` are the
continuous functions with values in `X`, by evaluation at the identity (Frobenius
reciprocity). Equivariance is used up: a section is determined by its values at `1`, and any
continuous function `h` is the value at `1` of the section `φ ↦ (x ↦ x • h (x⁻¹ • φ))`.

## Main results

* `AlgebraicGeometry.GaloisSheaf.coindSectionsEquiv`: Frobenius reciprocity on sections over an
  affine object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology ContinuousMap

universe u r w

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K] {Λ : Type r} [Ring Λ] [TopologicalSpace Λ]
  (X : TopRep.{w} Λ (galoisGroup K))

/-- The coinduced representation, as a plain representation. -/
abbrev coindRep : Representation Λ (galoisGroup K) C(galoisGroup K, X) :=
  X.ρ.coind₁.toRepresentation

variable {X}

/-- The coinduced action is `(g • f) x = g • f (g⁻¹ * x)`. -/
lemma coindRep_apply_apply (g : galoisGroup K) (f : C(galoisGroup K, X)) (x : galoisGroup K) :
    coindRep X g f x = X.ρ g (f (g⁻¹ * x)) := rfl

variable (hX : Continuous fun p : galoisGroup K × X ↦ X.ρ p.1 p.2)

include hX in
/-- Frobenius reciprocity, the inverse construction: for a continuous `h : GeomPt K V → X`, the
map `(φ, x) ↦ x • h (x⁻¹ • φ)` is jointly continuous. -/
lemma continuous_coindLift {V : (base K).ProEt} (h : GeomPt K V → X) (hh : Continuous h) :
    Continuous fun p : GeomPt K V × galoisGroup K ↦ X.ρ p.2 (h (p.2⁻¹ • p.1)) := by
  have h1 : Continuous fun p : GeomPt K V × galoisGroup K ↦ p.2⁻¹ • p.1 :=
    GeomPt.continuous_smul_comp V (continuous_inv.comp continuous_snd) continuous_fst
  have h3 : Continuous fun p : GeomPt K V × galoisGroup K ↦ h (p.2⁻¹ • p.1) := hh.comp h1
  have h2 : Continuous fun p : GeomPt K V × galoisGroup K ↦ (p.2, h (p.2⁻¹ • p.1)) :=
    Continuous.prodMk (f := fun p : GeomPt K V × galoisGroup K ↦ p.2) continuous_snd h3
  exact hX.comp h2

/-- **Frobenius reciprocity on sections over an affine object.** -/
def coindSectionsEquiv (V : (base K).ProEt) [IsAffine V.left] :
    contSections Λ (coindRep X) V ≃+ C(GeomPt K V, X) where
  toFun s := ⟨fun φ ↦ s.1 φ 1, by
    have hs := ((mem_contSections_iff_of_isAffine s.1).1 s.2).2
    exact (continuous_eval_const (1 : galoisGroup K)).comp hs⟩
  invFun h :=
    ⟨fun φ ↦ ⟨fun x ↦ X.ρ x (h (x⁻¹ • φ)), (continuous_coindLift hX h h.continuous).comp
      (continuous_const.prodMk continuous_id)⟩, by
    rw [mem_contSections_iff_of_isAffine]
    refine ⟨fun g φ ↦ ?_, ?_⟩
    · ext x
      change X.ρ x (h (x⁻¹ • g • φ)) = X.ρ g (X.ρ (g⁻¹ * x) (h ((g⁻¹ * x)⁻¹ • φ)))
      rw [show X.ρ g (X.ρ (g⁻¹ * x) (h ((g⁻¹ * x)⁻¹ • φ))) =
          X.ρ (g * (g⁻¹ * x)) (h ((g⁻¹ * x)⁻¹ • φ)) by rw [map_mul X.ρ g (g⁻¹ * x)]; rfl,
        mul_inv_cancel_left, mul_inv_rev, inv_inv, mul_smul]
    · exact ContinuousMap.continuous_of_continuous_uncurry _
        (continuous_coindLift hX h h.continuous)⟩
  left_inv s := by
    apply Subtype.ext
    funext φ
    ext x
    change X.ρ x (s.1 (x⁻¹ • φ) 1) = s.1 φ x
    rw [s.2.1 x⁻¹ φ, coindRep_apply_apply, inv_inv, mul_one,
      show X.ρ x (X.ρ x⁻¹ (s.1 φ x)) = X.ρ (x * x⁻¹) (s.1 φ x) by rw [map_mul X.ρ x x⁻¹]; rfl,
      mul_inv_cancel, map_one]
    rfl
  right_inv h := by
    ext φ
    change X.ρ 1 (h (1⁻¹ • φ)) = h φ
    rw [inv_one, one_smul, map_one]
    rfl
  map_add' _ _ := rfl

end AlgebraicGeometry.GaloisSheaf
