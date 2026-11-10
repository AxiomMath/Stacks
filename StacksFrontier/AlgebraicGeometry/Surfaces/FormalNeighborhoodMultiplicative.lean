module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodFiltration
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction

/-!
# The projection-kernel filtration is multiplicative

Let `D` be an ideal sheaf on a scheme `X` and let
`A = AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing D` be the ring of compatible
global functions on the infinitesimal thickenings `Eₙ₊₁ = (D ^ (n + 1)).subscheme`, filtered by
the kernels `Iₙ` of the projections `A ⟶ Γ(Eₙ, 𝒪)`. This file proves that `Iₘ · Iₙ ⊆ Iₘ₊ₙ`, with
no hypothesis on `D` or `X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.mul_eq_zero_of_appTop_inclusion_eq_zero`: two global
  functions on the subscheme of `K` that vanish on the subschemes of `I` and of `J`, where
  `I · J ≤ K` on affine opens, have product zero.
* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningRestrictionLE_formalNeighborhoodProjection`:
  the projections out of the ring of compatible functions are compatible with restriction between
  arbitrary thickenings.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration_mul_le`: the
  projection-kernel filtration is multiplicative.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-! ### Products of functions vanishing on nested closed subschemes -/

/-- Let `I`, `J` and `K` be ideal sheaves with `K ≤ I`, `K ≤ J` and `I(U) · J(U) ≤ K(U)` on every
affine open `U`. If a global function on the subscheme cut out by `K` restricts to zero on the
subscheme cut out by `I`, and another restricts to zero on the subscheme cut out by `J`, then their
product is zero. -/
public theorem mul_eq_zero_of_appTop_inclusion_eq_zero (I J K : X.IdealSheafData)
    (hIK : K ≤ I) (hJK : K ≤ J) (hmul : ∀ U : X.affineOpens, I.ideal U * J.ideal U ≤ K.ideal U)
    {u v : Γ(K.subscheme, ⊤)}
    (hu : (inclusion hIK).appTop u = 0) (hv : (inclusion hJK).appTop v = 0) :
    u * v = 0 := by
  refine K.subscheme.sheaf.eq_of_locally_eq'
    (fun U : X.affineOpens => K.subschemeι ⁻¹ᵁ U.1) ⊤ (fun _ => homOfLE le_top)
    (le_of_eq (K.subschemeι.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)).symm) _ 0 ?_
  intro U
  set res := (K.subscheme.presheaf.map
    (homOfLE (le_top (a := K.subschemeι ⁻¹ᵁ U.1))).op).hom with hres
  have key : ∀ (L : X.IdealSheafData) (h : K ≤ L) (w : Γ(K.subscheme, ⊤)),
      ((inclusion h).app ⊤).hom w = 0 →
      ((inclusion h).app (K.subschemeι ⁻¹ᵁ U.1)).hom (res w) = 0 := by
    intro L h w hw
    have hnat := congrArg (fun φ : Γ(K.subscheme, ⊤) ⟶ Γ(L.subscheme, _) =>
        (CommRingCat.Hom.hom φ) w)
      (Scheme.Hom.naturality (inclusion h) (U' := ⊤) (U := K.subschemeι ⁻¹ᵁ U.1)
        (homOfLE (le_top (a := K.subschemeι ⁻¹ᵁ U.1))).op)
    simp only [CommRingCat.comp_apply] at hnat
    rw [hres, hnat, hw, map_zero]
  have mem : ∀ (L : X.IdealSheafData) (h : K ≤ L) (w : Γ(K.subscheme, ⊤)) (z : Γ(X, U.1)),
      (K.subschemeι.app U.1).hom z = res w → ((inclusion h).app ⊤).hom w = 0 → z ∈ L.ideal U := by
    intro L h w z hz hw
    have happ : (K.subschemeι.app U.1 ≫ (inclusion h).app (K.subschemeι ⁻¹ᵁ U.1)).hom z = 0 := by
      rw [CommRingCat.comp_apply, hz]
      exact key L h w hw
    rw [← ker_subschemeι_app L U, RingHom.mem_ker, ← inclusion_subschemeι h, Scheme.Hom.comp_app]
    exact happ
  obtain ⟨x, hx⟩ := K.subschemeι_app_surjective U (res u)
  obtain ⟨y, hy⟩ := K.subschemeι_app_surjective U (res v)
  have hxyK : x * y ∈ K.ideal U :=
    hmul U (Ideal.mul_mem_mul (mem I hIK u x hx hu) (mem J hJK v y hy hv))
  change res (u * v) = res 0
  rw [map_zero, map_mul, ← hx, ← hy, ← map_mul]
  exact RingHom.mem_ker.mp ((ker_subschemeι_app K U).ge hxyK)

variable (D : X.IdealSheafData)

/-- The product of the ideals of two powers of an ideal sheaf on an affine open is contained in
the ideal of the sum of the powers. -/
public theorem ideal_pow_mul_ideal_pow_le (p q : ℕ) (U : X.affineOpens) :
    (D ^ (p + 1)).ideal U * (D ^ (q + 1)).ideal U ≤ (D ^ (p + q + 1 + 1)).ideal U := by
  simp only [ideal_pow, Pi.pow_apply, ← pow_add]
  exact (congrArg _ (by omega)).le

/-! ### Multiplicativity of the projection-kernel filtration -/

/-- The projections out of the ring of compatible functions are compatible with restriction
between arbitrary thickenings, not just successive ones. -/
public theorem thickeningRestrictionLE_formalNeighborhoodProjection {i j : ℕ} (h : i ≤ j)
    (a : formalNeighborhoodRing D) :
    thickeningRestrictionLE D h (formalNeighborhoodProjection D j a) =
      formalNeighborhoodProjection D i a := by
  induction j, h using Nat.le_induction with
  | base => exact thickeningRestrictionLE_self D i _
  | succ k hik ih =>
    rw [← thickeningRestrictionLE_comp D hik (Nat.le_succ k), thickeningRestrictionLE_succ,
      thickeningRestriction_formalNeighborhoodProjection, ih]

/-- The projection-kernel filtration is multiplicative: `Iₘ · Iₙ ⊆ Iₘ₊ₙ` for the filtration of the
ring of compatible functions by the kernels of the projections to the infinitesimal thickenings,
for an arbitrary ideal sheaf on an arbitrary scheme. -/
public theorem formalNeighborhoodFiltration_mul_le (m n : ℕ) :
    formalNeighborhoodFiltration D m * formalNeighborhoodFiltration D n ≤
      formalNeighborhoodFiltration D (m + n) := by
  match m, n with
  | 0, n => simp
  | (p + 1), 0 => exact Ideal.mul_le_left
  | (p + 1), (q + 1) =>
    rw [show p + 1 + (q + 1) = p + q + 1 + 1 from by omega, Ideal.mul_le]
    intro a ha b hb
    rw [mem_formalNeighborhoodFiltration_succ_iff] at ha hb ⊢
    refine mul_eq_zero_of_appTop_inclusion_eq_zero (D ^ (p + 1)) (D ^ (q + 1)) (D ^ (p + q + 1 + 1))
      (pow_succ_le_pow_succ D (by omega)) (pow_succ_le_pow_succ D (by omega))
      (ideal_pow_mul_ideal_pow_le D p q) ?_ ?_
    · exact (thickeningRestrictionLE_formalNeighborhoodProjection D
        (show p ≤ p + q + 1 by omega) a).trans ha
    · exact (thickeningRestrictionLE_formalNeighborhoodProjection D
        (show q ≤ p + q + 1 by omega) b).trans hb

end AlgebraicGeometry.Scheme.IdealSheafData

end
