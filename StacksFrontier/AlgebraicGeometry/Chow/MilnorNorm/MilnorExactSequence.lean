module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SimpleNorm
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.Completion

/-!
# Milnor's split exact sequence for `K^M_*(k(t))`

Let `k` be a field and `k(t) = RatFunc k`. This file assembles **Milnor's split exact sequence**

`0 ⟶ K^M_{i+1}(k) ⟶ K^M_{i+1}(k(t)) ⟶ ⨁_ψ K^M_i(k[t] ⧸ ψ) ⟶ 0`,

the sum running over the closed points of `A¹_k`, i.e. the monic irreducible polynomials `ψ`
(`Stacks.Chow.MonicIrreduciblePoint`), the second map being the inclusion of the constants
(`Stacks.Chow.constantInclusion`) and the third the family of residues
(`Stacks.Chow.milnorKTotalResidue`), which lands in the direct sum because a class has a nonzero
residue at only finitely many points
(`Stacks.Chow.exists_finset_forall_monicIrreducibleResidue_eq_zero`).

* injectivity, split by `Stacks.Chow.constantRetraction`: `Stacks.Chow.constantInclusion_injective`
  and `Stacks.Chow.constantRetraction_constantInclusion`;
* exactness in the middle: `Stacks.Chow.ker_milnorKTotalResidue`;
* surjectivity: `Stacks.Chow.milnorKTotalResidue_surjective`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), Theorem 2.3.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k]

attribute [local instance] Ideal.Quotient.field

/-- The closed points of `A¹_k`: the monic irreducible polynomials, indexed with their degree. -/
abbrev MonicIrreduciblePoint (k : Type u) [Field k] : Type u :=
  Σ d : ℕ, MonicIrreducibleOfDegree k d

/-- Two closed points with the same polynomial are equal. -/
theorem MonicIrreduciblePoint.ext_poly {ψ χ : MonicIrreduciblePoint k}
    (h : poly ψ.2 = poly χ.2) : ψ = χ := by
  obtain ⟨d, ψ⟩ := ψ
  obtain ⟨d', χ⟩ := χ
  obtain rfl : d = d' := by rw [← natDegree_eq ψ, h, natDegree_eq χ]
  obtain rfl := poly_injective h
  rfl

/-- The residue of the unit `1` vanishes. -/
theorem monicIrreducibleResidue_one {d : ℕ} (ψ : MonicIrreducibleOfDegree k d) :
    monicIrreducibleResidue ψ 1 = 0 := by
  rw [monicIrreducibleResidue_apply, map_one, MilnorKShift.shift_one, map_zero]

/-- **The residues vanish on the constants.** -/
theorem monicIrreducibleResidue_milnorKRingMap_constantsHom {d : ℕ}
    (ψ : MonicIrreducibleOfDegree k d) (z : MilnorKRing k) :
    monicIrreducibleResidue ψ (milnorKRingMap (constantsHom k) z) = 0 := by
  rw [← mul_one (milnorKRingMap (constantsHom k) z), monicIrreducibleResidue_constants_mul,
    monicIrreducibleResidue_one, mul_zero]

/-! ### The total residue -/

/-- A class has a nonzero residue at only finitely many closed points. -/
theorem finite_monicIrreducibleResidue_ne_zero (x : MilnorKRing (RatFunc k)) :
    ∃ s : Set (MonicIrreduciblePoint k), s.Finite ∧
      ∀ ψ ∉ s, monicIrreducibleResidue ψ.2 x = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_forall_monicIrreducibleResidue_eq_zero x
  refine ⟨(fun ψ : MonicIrreduciblePoint k ↦ poly ψ.2) ⁻¹' S,
    S.finite_toSet.preimage fun ψ _ χ _ h ↦ MonicIrreduciblePoint.ext_poly h,
    fun ψ hψ ↦ hS _ ψ.2 hψ⟩

/-- The family of residues of a class of `K^M_{i+1}(k(t))`, in `K^M_i`. -/
def residueFamily (i : ℕ) (x : MilnorKTheory (RatFunc k) (i + 1)) (ψ : MonicIrreduciblePoint k) :
    MilnorKTheory (Polynomial k ⧸ Ideal.span {poly ψ.2}) i :=
  ⟨monicIrreducibleResidue ψ.2 x, monicIrreducibleResidue_mem_milnorKGrading _ x.2⟩

/-- The family of residues of a class of `K^M_{i+1}(k(t))` has finite support. -/
theorem residueFamily_finite (i : ℕ) (x : MilnorKTheory (RatFunc k) (i + 1)) :
    {ψ | residueFamily i x ψ ≠ 0}.Finite := by
  obtain ⟨s, hs, h⟩ := finite_monicIrreducibleResidue_ne_zero (x : MilnorKRing (RatFunc k))
  exact hs.subset fun ψ hψ ↦ by_contra fun hψs ↦ hψ (Subtype.ext (h ψ hψs))

variable (k) in
/-- **The total residue `K^M_{i+1}(k(t)) ⟶ ⨁_ψ K^M_i(k[t] ⧸ ψ)`.** -/
def milnorKTotalResidue (i : ℕ) :
    MilnorKTheory (RatFunc k) (i + 1) →+
      DirectSum (MonicIrreduciblePoint k)
        (fun ψ ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly ψ.2}) i) :=
  letI := Classical.decEq (MonicIrreduciblePoint k)
  { toFun x := directSumOfFinite (residueFamily i x) (residueFamily_finite i x)
    map_zero' := DFinsupp.ext fun ψ ↦ by
      rw [directSumOfFinite_apply]
      exact Subtype.ext (map_zero _)
    map_add' x y := DFinsupp.ext fun ψ ↦ by
      rw [DFinsupp.add_apply, directSumOfFinite_apply, directSumOfFinite_apply,
        directSumOfFinite_apply]
      exact Subtype.ext (map_add _ _ _) }

/-- **The `ψ`-component of the total residue is the residue at `ψ`.** -/
theorem coe_milnorKTotalResidue_apply (i : ℕ) (x : MilnorKTheory (RatFunc k) (i + 1))
    (ψ : MonicIrreduciblePoint k) :
    (milnorKTotalResidue k i x ψ : MilnorKRing _) = monicIrreducibleResidue ψ.2 x := by
  let := Classical.decEq (MonicIrreduciblePoint k)
  exact congrArg Subtype.val
    (directSumOfFinite_apply (residueFamily i x) (residueFamily_finite i x) ψ)

/-! ### Exactness -/

/-- **Stacks 0EAY, Milnor's exact sequence, surjectivity: every finite family of classes
`α_ψ ∈ K^M_i(k[t] ⧸ ψ)` is the family of residues of a class of `K^M_{i+1}(k(t))`.** -/
theorem milnorKTotalResidue_surjective (i : ℕ) :
    Function.Surjective (milnorKTotalResidue k i) := by
  classical
  intro α
  induction α using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of ψ a =>
      obtain ⟨y, hyi, hy⟩ := exists_isSingleResidueLift' ψ.2 a.2
      refine ⟨⟨y, hyi⟩, DFinsupp.ext fun χ ↦ Subtype.ext ?_⟩
      rw [coe_milnorKTotalResidue_apply]
      by_cases h : χ = ψ
      · subst h
        rw [DirectSum.of_eq_same]
        exact hy.1
      · rw [DirectSum.of_eq_of_ne _ _ _ h]
        exact hy.2 _ χ.2 fun hp ↦ h (MonicIrreduciblePoint.ext_poly hp)
  | add α β hα hβ =>
      obtain ⟨x, rfl⟩ := hα
      obtain ⟨y, rfl⟩ := hβ
      exact ⟨x + y, map_add _ _ _⟩

/-- On the subgroup generated by the symbols of constants, the inclusion of the constants undoes
the retraction. -/
theorem milnorKRingMap_constantRetractionRing_of_mem {x : MilnorKRing (RatFunc k)}
    (hx : x ∈ milnorKPolyFiltration k 0) :
    milnorKRingMap (constantsHom k) (constantRetractionRing k x) = x := by
  refine milnorKPolyFiltration_le (H := AddMonoidHom.eqLocus
    ((milnorKRingMap (constantsHom k)).toAddMonoidHom.comp (constantRetractionRing k))
    (AddMonoidHom.id _)) (fun l hl ↦ ?_) hx
  obtain ⟨l₀, rfl⟩ := exists_constantUnitList hl
  change milnorKRingMap (constantsHom k) (constantRetractionRing k _) = _
  have h := milnorKRingMap_milnorKSymbolProd (constantsHom k) l₀
  change _ = milnorKSymbolProd (RatFunc k) (l₀.map (Units.map (constantsHom k).toMonoidHom)) at h
  rw [← h, constantRetractionRing_milnorKRingMap_constantsHom]
  rfl

/-- **Stacks 0EAY, Milnor's exact sequence, exactness in the middle: the classes of
`K^M_{i+1}(k(t))` with no residue are exactly those of `K^M_{i+1}(k)`.** -/
theorem ker_milnorKTotalResidue (i : ℕ) :
    (milnorKTotalResidue k i).ker = (constantInclusion (k := k) (i + 1)).range := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hres : ∀ (e : ℕ) (ψ : MonicIrreducibleOfDegree k (e + 1)),
        monicIrreducibleResidue ψ (x : MilnorKRing (RatFunc k)) = 0 := fun e ψ ↦ by
      rw [← coe_milnorKTotalResidue_apply i x ⟨e + 1, ψ⟩, AddMonoidHom.mem_ker.mp hx]
      rfl
    exact ⟨constantRetraction (i + 1) x, Subtype.ext
      (milnorKRingMap_constantRetractionRing_of_mem
        (mem_milnorKPolyFiltration_zero_of_forall_monicIrreducibleResidue_eq_zero hres))⟩
  · rintro ⟨z, rfl⟩
    refine AddMonoidHom.mem_ker.mpr (DFinsupp.ext fun ψ ↦ Subtype.ext ?_)
    rw [coe_milnorKTotalResidue_apply]
    exact monicIrreducibleResidue_milnorKRingMap_constantsHom ψ.2 z

end Stacks.Chow

end
