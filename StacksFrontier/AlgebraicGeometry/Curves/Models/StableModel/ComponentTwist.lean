module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberIntersectionForm
public import StacksFrontier.AlgebraicGeometry.Curves.Models.DegreePairingSymmetry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentDegreeHom
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.AmpleComponentDegree
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.NonnegativeSolution

/-!
# An invertible module of degree zero on a prescribed set of components

In the situation of [Stacks, Tag 0C61] suppose every component `Cᵢ` of the special fibre has
multiplicity one, and let `T` be a proper subset of the components. The intersection matrix
`(Cᵢ · Cⱼ)` is negative semidefinite with kernel spanned by the multiplicity vector
([Stacks, Tag 0C66]), so its restriction to `T` is negative definite; its off-diagonal entries
are nonnegative. Hence for the degree vector `d` of an ample invertible module `ℒ` on `X`
(positive on every component) the system `∑_{j ∈ T} (Cᵢ · Cⱼ) vⱼ = -dᵢ`, `i ∈ T`, has a
nonnegative rational solution, and after clearing denominators
`ℳ = ℒ^{⊗ a} ⊗ 𝒪_X(∑_{j ∈ T} nⱼ Cⱼ)` has degree zero on every component in `T` and positive degree
on every other component.

## Main results

* `Stacks.Models.RegularProperModelSituation.exists_isInvertible_specialFiberComponentDegree`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **An invertible module of degree zero exactly on a prescribed proper set of components.** If
every component of the special fibre has multiplicity one and `T` is a set of components missing
at least one component, there is an invertible `𝒪_X`-module whose degree is zero on every
component in `T` and positive on every component outside `T`. -/
theorem exists_isInvertible_specialFiberComponentDegree
    (hm : ∀ Z, S.specialFiberMultiplicity Z = 1)
    (T : Set (irreducibleComponents S.specialFiber)) (hT : ∃ Z, Z ∉ T) :
    ∃ (M : S.X.Modules) (hM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
        (structureSheafRing S.X.toRingedSpace).property M),
      ∀ Z, (Z ∈ T → S.specialFiberComponentDegree Z M hM = 0) ∧
        (Z ∉ T → 0 < S.specialFiberComponentDegree Z M hM) := by
  classical
  obtain ⟨L, hL, hpos⟩ := S.exists_isInvertible_forall_specialFiberComponentDegree_pos
  set s : Finset (irreducibleComponents S.specialFiber) := Finset.univ.filter (· ∈ T) with hs
  have hmem : ∀ Z, Z ∈ s ↔ Z ∈ T := fun Z => by simp [hs]
  -- the intersection matrix restricted to `T` is negative definite
  obtain ⟨a, ha, n, -, hn⟩ := Matrix.exists_pos_nat_finsetSum_mul_eq_neg_of_negDef
    S.specialFiberIntersectionMatrix s
    (fun Z Y h => (S.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff h).1)
    (fun v => (S.specialFiberIntersectionForm_nonpos_and_eq_zero_iff v).1)
    (fun v hv h0 => by
      obtain ⟨q, hq⟩ := ((S.specialFiberIntersectionForm_nonpos_and_eq_zero_iff v).2).1 h0
      obtain ⟨Z₀, hZ₀⟩ := hT
      have hq0 : q = 0 := by
        have h1 := hq Z₀
        rw [hv Z₀ ((hmem Z₀).not.2 hZ₀), hm Z₀] at h1
        simpa using h1.symm
      funext Z
      rw [hq Z, hq0, zero_mul, Pi.zero_apply])
    (fun Z => S.specialFiberComponentDegree Z L hL) (fun Z _ => (hpos Z).le)
  -- the class `a • [ℒ] + [𝒪_X(∑_{Y ∈ T} n_Y C_Y)]` in `Pic(X)`
  set x : Stacks.Picard.ofScheme S.X :=
    a • Stacks.SheafOfModules.picardClass S.X.presheaf
        (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace) L hL +
      Stacks.SheafOfModules.picardClass S.X.presheaf
        (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace)
        (S.specialFiberVerticalDivisorSheaf s fun Y => (n Y : ℤ))
        (S.isInvertible_specialFiberVerticalDivisorSheaf s fun Y => (n Y : ℤ)) with hx
  refine ⟨(Stacks.Picard.picardRepresentative S.X.toRingedSpace x).obj,
    (Stacks.Picard.picardRepresentative S.X.toRingedSpace x).property, fun Z => ?_⟩
  have hdeg : S.specialFiberComponentDegree Z
      (Stacks.Picard.picardRepresentative S.X.toRingedSpace x).obj
      (Stacks.Picard.picardRepresentative S.X.toRingedSpace x).property =
      (a : ℤ) * S.specialFiberComponentDegree Z L hL +
        ∑ Y ∈ s, (n Y : ℤ) * S.specialFiberIntersectionMatrix Z Y := by
    change S.specialFiberComponentDegreeHom Z x = _
    rw [hx, map_add, map_nsmul, S.specialFiberComponentDegreeHom_picardClass,
      S.specialFiberComponentDegreeHom_picardClass,
      S.specialFiberComponentDegree_specialFiberVerticalDivisorSheaf_eq_sum, nsmul_eq_mul]
  rw [hdeg]
  refine ⟨fun hZ => ?_, fun hZ => ?_⟩
  · rw [hn Z ((hmem Z).2 hZ)]
    ring
  · have hsum : 0 ≤ ∑ Y ∈ s, (n Y : ℤ) * S.specialFiberIntersectionMatrix Z Y :=
      Finset.sum_nonneg fun Y hY => mul_nonneg (Int.natCast_nonneg _)
        (S.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff
          (fun e : Z = Y => hZ (e ▸ (hmem Y).1 hY))).1
    have := hpos Z
    have : 0 < (a : ℤ) * S.specialFiberComponentDegree Z L hL :=
      mul_pos (by exact_mod_cast ha) this
    linarith

end Stacks.Models.RegularProperModelSituation

end
