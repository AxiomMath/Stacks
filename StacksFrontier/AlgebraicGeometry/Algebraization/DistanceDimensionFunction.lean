module

public import StacksFrontier.Topology.Dimension.DimensionFunctionIsCatenary
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension

/-!
# A lower bound for the distance from a closed subset

On a Noetherian scheme, a dimension function attains a maximum on every nonempty
closed subset. The distance from that subset to a point is at least the difference
between the dimension function at the point and this maximum.

## Main results

* `Stacks.Algebraization.exists_max_dimensionFunction_on_closed`
  gives the maximum value of a dimension function on a nonempty closed subset.
* `Stacks.Algebraization.distanceFunction_ge_dimensionFunction_sub_max`
  gives the lower bound for the distance function.

## Implementation notes

The maximum is expressed by `IsGreatest` on the image of the closed subset; it is attained
at the generic point of one of the finitely many irreducible closed pieces covering the
subset. The integer difference is converted to a natural number using `Int.toNat`, since
the distance takes values in `ℕ∞` and a negative lower bound is automatic. The lower bound
for a single system is a telescoping computation: by Stacks 02IA each leg's codimension is a
difference of values of the dimension function.

## References

* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

namespace Stacks.Algebraization

/-- A dimension function does not increase along a specialization. -/
private theorem dimensionFunction_le_of_specializes {X : Type*} [TopologicalSpace X]
    (δ : DimensionFunction X) {a b : X} (hab : a ⤳ b) : δ b ≤ δ a := by
  by_cases h : a = b
  · simp [h]
  · exact (δ.strictAnti_specializes hab h).le

/-- **Stacks Project, Tag 0EIY.** A dimension function has a maximum on a nonempty closed
subset of a Noetherian scheme. -/
@[stacks 0EIY "dimension_function_lower_bound"]
public theorem exists_max_dimensionFunction_on_closed
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y)
    (hZ : (Z : Set Y).Nonempty) (δ : DimensionFunction Y) :
    ∃ m : ℤ, IsGreatest (δ '' (Z : Set Y)) m := by
  classical
  obtain ⟨S, hSf, hSclosed, hSirreducible, hSunion⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (α := Y) Z.isClosed'
  let F := hSf.toFinset
  have hFmem {t : Set Y} : t ∈ F ↔ t ∈ S := hSf.mem_toFinset
  let η : F → Y := fun t => Classical.choose
    (QuasiSober.sober (hSirreducible t.1 (hFmem.mp t.2))
      (hSclosed t.1 (hFmem.mp t.2)))
  have hη (t : F) : IsGenericPoint (η t) (t : Set Y) :=
    Classical.choose_spec (QuasiSober.sober (hSirreducible t.1 (hFmem.mp t.2))
      (hSclosed t.1 (hFmem.mp t.2)))
  have hsubset (t : F) : (t : Set Y) ⊆ (Z : Set Y) := by
    show (t : Set Y) ⊆ Z.carrier
    rw [hSunion]
    exact Set.subset_sUnion_of_mem (hFmem.mp t.2)
  have : Nonempty F := by
    obtain ⟨x, hx⟩ := hZ
    have hx' : x ∈ ⋃₀ S := hSunion ▸ hx
    obtain ⟨t, ht, _⟩ := Set.mem_sUnion.mp hx'
    exact ⟨⟨t, hFmem.mpr ht⟩⟩
  let vals : Finset ℤ := Finset.univ.image (fun t : F => δ (η t))
  have hvalsNonempty : vals.Nonempty :=
    Finset.image_nonempty.mpr Finset.univ_nonempty
  let m : ℤ := vals.max' hvalsNonempty
  have hm_mem : m ∈ vals := Finset.max'_mem vals hvalsNonempty
  refine ⟨m, ?_, ?_⟩
  · obtain ⟨t, ht, hm⟩ := Finset.mem_image.mp hm_mem
    refine ⟨η t, hsubset t (hη t).mem, ?_⟩
    simp [m, vals, hm]
  · rintro n ⟨x, hxZ, rfl⟩
    have hx'' : x ∈ ⋃₀ S := hSunion ▸ hxZ
    obtain ⟨t, htS, hxt⟩ := Set.mem_sUnion.mp hx''
    let t' : F := ⟨t, hFmem.mpr htS⟩
    have hspec : η t' ⤳ x := (hη t').specializes hxt
    exact (dimensionFunction_le_of_specializes δ hspec).trans
      (Finset.le_max' vals _ (Finset.mem_image.mpr ⟨t', Finset.mem_univ _, rfl⟩))

/-- The weight of a single system is at least the drop of the dimension function from `y`
down to the maximum attained on `Z`. -/
private lemma distanceSystem_weight_ge_dimensionFunction_sub
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) (δ : DimensionFunction Y)
    (m : ℤ) (hm : IsGreatest (δ '' (Z : Set Y)) m) (y : Y)
    (s : DistanceSystem Y Z y) :
    (δ y - m).toNat ≤ s.weight := by
  classical
  let v : Fin (s.k + 1) → Y := fun i => (s.V i).isIrreducible'.genericPoint
  let w : Fin (s.k + 1) → Y := fun i => (s.W i).isIrreducible'.genericPoint
  have hv (i : Fin (s.k + 1)) : IsGenericPoint (v i) (s.V i : Set Y) :=
    (s.V i).isIrreducible'.isGenericPoint_genericPoint (s.V i).isClosed'
  have hw (i : Fin (s.k + 1)) : IsGenericPoint (w i) (s.W i : Set Y) :=
    (s.W i).isIrreducible'.isGenericPoint_genericPoint (s.W i).isClosed'
  have hcodInt {A B : IrreducibleCloseds Y} (h : A ≤ B) :
      ((IrreducibleClosedsCodim.topCodim A B).toNat : ℤ) =
        δ B.isIrreducible'.genericPoint - δ A.isIrreducible'.genericPoint := by
    have hA := A.isIrreducible'.isGenericPoint_genericPoint A.isClosed'
    have hB := B.isIrreducible'.isGenericPoint_genericPoint B.isClosed'
    have hspec := hB.specializes (h hA.mem)
    have hAc : closureSingleton A.isIrreducible'.genericPoint = A := IrreducibleCloseds.ext hA.def
    have hBc : closureSingleton B.isIrreducible'.genericPoint = B := IrreducibleCloseds.ext hB.def
    have hcod := (isCatenarySpace_and_topCodim_eq_of_isDimensionFunction Y
      (Stacks.Chow.scheme_stacksSober Y) δ
      (TopologicalSpace.DimensionFunction.isDimensionFunctionForCatenary δ)).2 _ _ hspec
    rw [hAc, hBc] at hcod
    rw [hcod, ENat.toNat_natCast,
      Int.toNat_of_nonneg (sub_nonneg.mpr (dimensionFunction_le_of_specializes δ hspec))]
  have hupInt (i : Fin (s.k + 1)) :
      (s.upCodimension i : ℤ) = δ (w i) - δ (v i) :=
    hcodInt (s.V_le_W i)
  have hdownInt (i : Fin s.k) :
      (s.downCodimension i : ℤ) = δ (w i.castSucc) - δ (v i.succ) :=
    hcodInt (s.V_next_le_W i)
  have htelV :
      (∑ i : Fin s.k, (δ (v i.succ) - δ (v i.castSucc))) =
        δ (v (Fin.last s.k)) - δ (v 0) := by
    have hsucc : (∑ i : Fin s.k, δ (v i.succ)) + δ (v 0) = ∑ i : Fin (s.k + 1), δ (v i) := by
      rw [Fin.sum_univ_succ]
      ring
    have hcast :
        (∑ i : Fin s.k, δ (v i.castSucc)) + δ (v (Fin.last s.k)) =
          ∑ i : Fin (s.k + 1), δ (v i) := by
      rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_sub_distrib]
    omega
  have hcap :
      (∑ i : Fin s.k,
        ((δ (w i.castSucc) - δ (v i.castSucc)) -
          (δ (w i.castSucc) - δ (v i.succ)))) =
        ∑ i : Fin s.k, (δ (v i.succ) - δ (v i.castSucc)) :=
    Finset.sum_congr rfl fun _ _ => by ring
  have hwlast : w (Fin.last s.k) = y := by
    apply (hw (Fin.last s.k)).eq
    rw [s.W_last_eq_closure]
    exact isGenericPoint_closure
  have htel :
      (∑ i : Fin (s.k + 1), (s.upCodimension i : ℤ)) -
        (∑ i : Fin s.k, (s.downCodimension i : ℤ)) =
          δ y - δ (v 0) := by
    calc
      _ = (∑ i : Fin s.k,
            ((s.upCodimension i.castSucc : ℤ) - (s.downCodimension i : ℤ))) +
              (s.upCodimension (Fin.last s.k) : ℤ) := by
          rw [Fin.sum_univ_castSucc, Finset.sum_sub_distrib]
          ring
      _ = δ y - δ (v 0) := by
          simp_rw [hupInt, hdownInt]
          rw [hcap, htelV, hwlast]
          ring
  have hδzero_le : δ (v 0) ≤ m := hm.2 ⟨v 0, s.V_zero_subset (hv 0).mem, rfl⟩
  by_cases hnonneg : 0 ≤ δ y - m
  · have hcastDiff : ((∑ i : Fin (s.k + 1), s.upCodimension i : ℕ) : ℤ) -
        ((∑ i : Fin s.k, s.downCodimension i : ℕ) : ℤ) = δ y - δ (v 0) := by
      simpa [Nat.cast_sum] using htel
    have hweight : s.k + ((∑ i : Fin (s.k + 1), s.upCodimension i) -
        ∑ i : Fin s.k, s.downCodimension i) ≤ s.weight := by
      unfold DistanceSystem.weight
      apply Nat.add_le_add_left
      have := Finset.le_sup
        (f := fun i : Fin (s.k + 1) =>
          (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) -
          (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0))
        (b := (0 : Fin (s.k + 1))) (Finset.mem_univ _)
      simpa using this
    omega
  · simp [Int.toNat_eq_zero.mpr (by omega : δ y - m ≤ 0)]

/-- **Stacks Project, Tag 0EIY.** The distance from `Z` is at least the value of a dimension
function minus its maximum value on `Z`. -/
@[stacks 0EIY "dimension_function_lower_bound"]
public theorem distanceFunction_ge_dimensionFunction_sub_max
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y)
    (δ : DimensionFunction Y) (m : ℤ)
    (hm : IsGreatest (δ '' (Z : Set Y)) m) (y : Y) :
    ((δ y - m).toNat : ℕ∞) ≤ distanceFunction Y Z y := by
  classical
  unfold distanceFunction
  by_cases h : (connectedComponent y ∩ (Z : Set Y)).Nonempty
  · simp only [ite_eq_left h]
    exact le_iInf fun s => ENat.natCast_le_natCast.mpr
      (distanceSystem_weight_ge_dimensionFunction_sub Y Z δ m hm y s)
  · simp only [ite_eq_right h]
    exact le_top

end Stacks.Algebraization
