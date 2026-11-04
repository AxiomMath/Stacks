module

public import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic.Continuity.Init
import StacksCore.Algebra.Polynomial.Expand
import StacksCore.FieldTheory.IntermediateField.Adjoin.Basic
import StacksCore.GroupTheory.SpecificGroups.Cyclic.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Kummer extensions -/

@[expose] public section

add_to_stacks 09DX exists_root_adjoin_eq_top_of_isCyclic

open IntermediateField Polynomial

/-- Degree formula in a Kummer extension: if `L = K⟮z⟯` with `z^n ∈ K` (where `n = [L:K]`)
and `K` contains a primitive `n`-th root of unity, then for any `d ∣ n` we have
`[K⟮z^d⟯ : K] = n / d`. -/
theorem IntermediateField.finrank_pow_of_kummer
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {z : L} (hz : z ^ Module.finrank K L ∈ Set.range (algebraMap K L))
    (hgen : K⟮z⟯ = ⊤)
    (hroots : ∃ μ : K, IsPrimitiveRoot μ (Module.finrank K L))
    {d : ℕ} (hd : d ∣ Module.finrank K L) :
    Module.finrank K K⟮z ^ d⟯ = Module.finrank K L / d := by
  obtain ⟨a, ha⟩ := hz
  obtain ⟨μ, hμ⟩ := hroots
  obtain ⟨f, hf⟩ := hd
  have he0 : 0 < Module.finrank K L := Module.finrank_pos
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hgen
    |>.X_pow_sub_C_of_dvd he0.ne' ⟨d, hf.trans <| mul_comm _ _⟩
  have hmin : minpoly K (z ^ d) = X ^ f - C a := .symm <|
    minpoly.eq_of_irreducible_of_monic hirr (by simp [← pow_mul, ← hf, ← ha])
      (monic_X_pow_sub_C _ <| by grind)
  rw [finrank_adjoin, hmin, natDegree_X_pow_sub_C, hf, Nat.mul_div_cancel_left]
  grind

/-- **Stacks 0EXP**.
Description of the intermediate fields of a Kummer extension: if `L = K⟮z⟯` with `z^n ∈ K`
(where `n = [L:K]`) and `K` contains a primitive `n`-th root of unity, then every
intermediate field `F` of `L/K` has the form `K⟮z^[L:F]⟯`. -/
@[stacks 0EXP]
theorem IntermediateField.adjoin_pow_finrank_eq_of_kummer
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {z : L} (hz : z ^ Module.finrank K L ∈ Set.range (algebraMap K L))
    (hgen : K⟮z⟯ = ⊤)
    (hroots : ∃ μ : K, IsPrimitiveRoot μ (Module.finrank K L))
    (F : IntermediateField K L) :
    K⟮z ^ Module.finrank F L⟯ = F := by
  let ⟨μ, hμ⟩ := hroots
  have he : 0 < Module.finrank K L := Module.finrank_pos
  have hp : (primitiveRoots (Module.finrank K L) K).Nonempty := ⟨μ, by simpa [he]⟩
  have hgc := isCyclic_tfae K L hp |>.out 1 3 |>.mpr
  obtain ⟨_, hc⟩ := hgc ⟨z, hz, hgen⟩
  refine IsGalois.intermediateFieldEquivSubgroup.injective <| OrderDual.ext ?_
  refine IsCyclic.ext_subgroup_index ?_
  simp [← finrank_eq_fixingSubgroup_index, ← Module.finrank_mul_finrank K F L, Module.finrank_pos,
    finrank_pow_of_kummer hz hgen hroots (Module.finrank_dvd_finrank_left K F L)]

/-- **Stacks 0EXP**.
Description of the intermediate fields of a radical extension: if `L = K⟮z⟯` with `z^n ∈ K`
(where `n = [L:K]`) and every `n`-th root of unity in `L` lies in `K`, then every intermediate field
`F` of `L/K` has the form `K⟮z^[L:F]⟯`. -/
@[stacks 0EXP]
theorem IntermediateField.adjoin_pow_finrank_eq_of_forall_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {z : L} (hz : z ^ Module.finrank K L ∈ Set.range (algebraMap K L))
    (hgen : K⟮z⟯ = ⊤)
    (hroots : ∀ ζ : L, ζ ^ Module.finrank K L = 1 → ζ ∈ Set.range (algebraMap K L))
    (F : IntermediateField K L) :
    K⟮z ^ Module.finrank F L⟯ = F := by
  set e := Module.finrank K L
  set d := Module.finrank F L
  have hd : 0 < d := Module.finrank_pos
  obtain rfl | hz0 := eq_or_ne z 0
  · have : (⊥ : IntermediateField K L) = ⊤ := by simpa using hgen
    exact (subsingleton_of_bot_eq_top this).elim _ _
  have hK : ∀ x ∈ Set.range (algebraMap K L), x ∈ F := fun _ ⟨a, h⟩ ↦ h ▸ F.algebraMap_mem a
  have hN : ((Algebra.norm F z : F) : L) ^ e = (z ^ d) ^ e := by
    have h : Algebra.norm F z ^ e = ⟨z ^ e, hK _ hz⟩ ^ d := by
      rw [← map_pow]
      exact Algebra.norm_algebraMap (⟨z ^ e, hK _ hz⟩ : F)
    rw [← pow_mul, mul_comm, pow_mul]
    simpa using congr_arg ((↑) : F → L) h
  have hmem : z ^ d ∈ F := by
    have hNz : ((Algebra.norm F z : F) : L) ≠ 0 := by simpa using hz0
    have hζ := hK _ <| hroots (Algebra.norm F z / z ^ d) <| by
      rw [div_pow, hN, div_self (pow_ne_zero _ (pow_ne_zero _ hz0))]
    rw [show z ^ d = Algebra.norm F z / (Algebra.norm F z / z ^ d) by field_simp]
    exact div_mem (Algebra.norm F z).2 hζ
  have hle : K⟮z ^ d⟯ ≤ F := adjoin_simple_le_iff.mpr hmem
  refine eq_of_le_of_finrank_le hle (Nat.le_of_mul_le_mul_right ?_ hd)
  rw [Module.finrank_mul_finrank K F L, ← Module.finrank_mul_finrank K K⟮z ^ d⟯ L]
  refine Nat.mul_le_mul_left _ ?_
  set F' := K⟮z ^ d⟯
  have htop : F'⟮z⟯ = ⊤ := adjoin_eq_top_of_adjoin_eq_top K hgen
  rw [← finrank_top', ← htop, finrank_adjoin]
  have hp : aeval z (X ^ d - C (⟨z ^ d, mem_adjoin_simple_self K _⟩ : F')) = 0 := by simp
  exact (natDegree_le_of_dvd (minpoly.dvd F' z hp) (X_pow_sub_C_ne_zero hd _)).trans
    natDegree_X_pow_sub_C.le
