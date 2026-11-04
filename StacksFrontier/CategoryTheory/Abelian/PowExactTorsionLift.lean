module

public import StacksFrontier.CategoryTheory.Abelian.PowExact

/-!
# Multiplication by `p^(m-a)` into the `p^a`-torsion

Let `X` be an object of an abelian category killed by `p^m` and `e : X[p^a] ⟶ X` its
`p^a`-torsion, `a ≤ m`.  Multiplication by `p^(m - a)` lands in the `p^a`-torsion, so it factors
as `μ ≫ e` for a unique `μ : X ⟶ X[p^a]`.  When `X` is pow-exact (flat over `ℤ/pᵐℤ`), `μ` is a
cokernel of multiplication by `p^a`: this is the isomorphism `X / p^a X ≅ X[p^a]` of a flat
`ℤ/pᵐℤ`-module.

## Main definitions

* `CategoryTheory.Abelian.IsTorsionKernel.torsionLift`: the map `μ`.

## Main results

* `CategoryTheory.Abelian.IsTorsionKernel.torsionLift_comp`: `μ ≫ e = p^(m - a)`.
* `CategoryTheory.Abelian.IsTorsionKernel.isColimitTorsionLift`: on a pow-exact object, `μ` is
  a cokernel of `p^a`.
* `CategoryTheory.Abelian.IsTorsionKernel.map_torsionLift`: a left exact functor preserves `μ`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Abelian

open CategoryTheory Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C] {p m a : ℕ} {X' X : C} {e : X' ⟶ X}

namespace IsTorsionKernel

variable (h : IsTorsionKernel (p ^ a) e) (hX : (p ^ m) • 𝟙 X = 0) (ha : a ≤ m)

/-- Multiplication by `p^(m - a)`, as a map into the `p^a`-torsion. -/
def torsionLift : X ⟶ X' :=
  h.isLimit.lift (KernelFork.ofι ((p ^ (m - a)) • 𝟙 X) (pow_sub_nsmul_comp_pow_nsmul hX ha))

/-- The composite of `torsionLift` with the torsion inclusion is multiplication by `p^(m - a)`. -/
@[reassoc (attr := simp)]
theorem torsionLift_comp : h.torsionLift hX ha ≫ e = (p ^ (m - a)) • 𝟙 X :=
  h.isLimit.fac _ WalkingParallelPair.zero

/-- `torsionLift` is the only map whose composite with the torsion inclusion is `p^(m - a)`. -/
theorem eq_torsionLift {s : X ⟶ X'} (hs : s ≫ e = (p ^ (m - a)) • 𝟙 X) :
    s = h.torsionLift hX ha := by
  have := h.mono
  rw [← cancel_mono e, hs, torsionLift_comp]

/-- `torsionLift` kills `p^a`. -/
theorem nsmul_comp_torsionLift : ((p ^ a) • 𝟙 X) ≫ h.torsionLift hX ha = 0 := by
  have := h.mono
  rw [← cancel_mono e, Category.assoc, torsionLift_comp, zero_comp, nsmul_comp, comp_nsmul,
    Category.id_comp, smul_smul, ← pow_add, Nat.add_sub_cancel' ha, hX]

/-- **On a pow-exact object, multiplication by `p^(m - a)` into the `p^a`-torsion is a cokernel
of `p^a`**: `X / p^a X ≅ X[p^a]`. -/
def isColimitTorsionLift (hP : PowExact p m X) :
    IsColimit (CokernelCofork.ofπ (h.torsionLift hX ha) (h.nsmul_comp_torsionLift hX ha)) := by
  have := h.mono
  have hex : (ShortComplex.mk _ _ (h.nsmul_comp_torsionLift hX ha)).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    have hx' : x ≫ ((p ^ (m - a)) • 𝟙 X) = 0 := by
      have : (x ≫ h.torsionLift hX ha) ≫ e = 0 := by
        change x ≫ h.torsionLift hX ha = 0 at hx
        rw [hx, zero_comp]
      rwa [Category.assoc, torsionLift_comp] at this
    obtain ⟨T', π, hπ, y, hy⟩ := hP (m - a) (Nat.sub_le m a) x hx'
    rw [Nat.sub_sub_self ha] at hy
    exact ⟨T', π, hπ, y, hy⟩
  have hepi : Epi (h.torsionLift hX ha) := by
    rw [epi_iff_surjective_up_to_refinements]
    intro T y
    have hy : (y ≫ e) ≫ ((p ^ a) • 𝟙 X) = 0 := by rw [Category.assoc, h.comp_eq_zero, comp_zero]
    obtain ⟨T', π, hπ, x, hx⟩ := hP a ha _ hy
    refine ⟨T', π, hπ, x, ?_⟩
    rw [← cancel_mono e, Category.assoc, Category.assoc, torsionLift_comp, ← hx]
  exact hex.gIsCokernel

/-- **A left exact additive functor preserves the multiplication into the torsion.** -/
theorem map_torsionLift {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] (hX' : (p ^ m) • 𝟙 (G.obj X) = 0) :
    G.map (h.torsionLift hX ha) = (h.map G).torsionLift hX' ha := by
  apply eq_torsionLift
  rw [← G.map_comp, torsionLift_comp, G.map_nsmul, G.map_id]

end IsTorsionKernel

end CategoryTheory.Abelian
