module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueSupport

/-!
# Every class of `K^M_*(k[X] ⧸ φ)` is a residue, diagonally in the degrees above `deg φ`

Let `k` be a field and `φ ∈ k[X]` monic irreducible of degree `e + 1`. Every class `α` of
`K^M_*(k[X] ⧸ φ)` is the residue at `φ` of a class `y` of `K^M_*(RatFunc k)` whose residue
vanishes at every other closed point of degree at least `e + 1`. This is the surjectivity half of
Milnor's exact sequence, in its diagonal form.

## Main results

* `Stacks.Chow.exists_unitList_of_polyRep`: the low-degree representatives of a list of classes
  lift to units of the local ring at `φ` with those classes as residues.
* `Stacks.Chow.exists_monicIrreducibleResidue_eq_milnorKSymbolProd`: the statement for a symbol.
* `Stacks.Chow.exists_monicIrreducibleResidue_eq`: the statement for an arbitrary class.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u

namespace Stacks.Chow

attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k]

/-! ### Lifting the representatives to units of the local ring -/

/-- **The low-degree representatives of a list of classes of `k[X] ⧸ φ` lift to units of the
local ring at `φ`** whose images in `RatFunc k` are those representatives and whose residues are
the given classes. -/
theorem exists_unitList_of_polyRep {e : ℕ} (φ : MonicIrreducibleOfDegree k (e + 1))
    (m : List (Polynomial k ⧸ Ideal.span {poly φ})ˣ) :
    ∃ l : List (Localization.AtPrime (Ideal.span {poly φ}))ˣ,
      l.map (Units.map (algebraMap (Localization.AtPrime (Ideal.span {poly φ})) (RatFunc k) :
          Localization.AtPrime (Ideal.span {poly φ}) →* RatFunc k)) =
        m.map (fun u ↦ polyUnit (polyRep_ne_zero (monic φ) (ne_one φ) u)) ∧
      l.map (fun w ↦ Units.map
        ((quotientRingEquivResidueField (Ideal.span {poly φ})).symm :
          (Ideal.span {poly φ}).ResidueField →* (Polynomial k ⧸ Ideal.span {poly φ}))
        (Units.map (residue (Localization.AtPrime (Ideal.span {poly φ}))).toMonoidHom w)) = m := by
  induction m with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons u m ih =>
      obtain ⟨l, hl1, hl2⟩ := ih
      obtain ⟨w, hw⟩ := isUnit_algebraMap_localizationAtPrime (p := poly φ)
        (polyRep_ne_zero (monic φ) (ne_one φ) u)
        (natDegree_polyRep_lt (monic φ) (ne_one φ) u)
      refine ⟨w :: l, ?_, ?_⟩
      · rw [List.map_cons, List.map_cons, hl1]
        refine congrArg (· :: _) (Units.ext ?_)
        show algebraMap (Localization.AtPrime (Ideal.span {poly φ})) (RatFunc k)
          (w : Localization.AtPrime (Ideal.span {poly φ})) = _
        rw [hw, ← IsScalarTower.algebraMap_apply, coe_polyUnit]
      · rw [List.map_cons, hl2]
        refine congrArg (· :: _) (Units.ext ?_)
        show (quotientRingEquivResidueField (Ideal.span {poly φ})).symm
          (residue (Localization.AtPrime (Ideal.span {poly φ}))
            (w : Localization.AtPrime (Ideal.span {poly φ}))) = _
        rw [hw, residue_algebraMap_eq_quotientRingEquivResidueField,
          RingEquiv.symm_apply_apply, mk_polyRep]

/-! ### The witness for a symbol -/

/-- **A symbol of `K^M_*(k[X] ⧸ φ)` is the residue at `φ` of `{rep ū_1, …, rep ū_m, φ}`, whose
residue vanishes at every other closed point of degree at least `deg φ`.** -/
theorem exists_monicIrreducibleResidue_eq_milnorKSymbolProd {e : ℕ}
    (φ : MonicIrreducibleOfDegree k (e + 1))
    (m : List (Polynomial k ⧸ Ideal.span {poly φ})ˣ) :
    ∃ y : MilnorKRing (RatFunc k),
      monicIrreducibleResidue φ y =
        milnorKSymbolProd (Polynomial k ⧸ Ideal.span {poly φ}) m ∧
      ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ → e + 1 ≤ d' →
        monicIrreducibleResidue ψ y = 0 := by
  obtain ⟨l, hl1, hl2⟩ := exists_unitList_of_polyRep φ m
  refine ⟨unitSymbolProd (RatFunc k) l *
    milnorKSymbol (RatFunc k) (dvrFracUniformizer (RatFunc k)
      (irreducible_algebraMap_self (p := poly φ))), ?_, ?_⟩
  · rw [monicIrreducibleResidue_unitSymbolProd_mul_uniformizer φ l, hl2]
  · intro d' ψ hne hle
    refine monicIrreducibleResidue_eq_zero_of_mem_milnorKNotDvdFiltration ψ ?_
    rw [unitSymbolProd, hl1, dvrFracUniformizer_irreducible_algebraMap_self (ne_zero φ),
      ← milnorKSymbolProd_singleton (polyUnit (ne_zero φ)), ← milnorKSymbolProd_append]
    refine milnorKSymbolProd_mem_milnorKNotDvdFiltration fun v hv ↦ ?_
    rcases List.mem_append.mp hv with hv' | hv'
    · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hv'
      refine ⟨polyRep (monic φ) (ne_one φ) u, polyRep_ne_zero (monic φ) (ne_one φ) u,
        fun hdvd ↦ ?_, rfl⟩
      have hle' := Polynomial.natDegree_le_of_dvd hdvd (polyRep_ne_zero (monic φ) (ne_one φ) u)
      have hlt := natDegree_polyRep_lt (monic φ) (ne_one φ) u
      have h1 := natDegree_eq ψ
      have h2 := natDegree_eq φ
      lia
    · rw [List.mem_singleton.mp hv']
      refine ⟨poly φ, ne_zero φ, fun hdvd ↦ hne ?_, rfl⟩
      exact Polynomial.eq_of_monic_of_associated (monic ψ) (monic φ)
        ((irreducible ψ).associated_of_dvd (irreducible φ) hdvd)

/-! ### The witness for an arbitrary class -/

/-- **The surjectivity half of Milnor's exact sequence, in its diagonal form: every class of
`K^M_*(k[X] ⧸ φ)` is the residue at `φ` of a class whose residue vanishes at every other closed
point of degree at least `deg φ`.** -/
theorem exists_monicIrreducibleResidue_eq {e : ℕ} (φ : MonicIrreducibleOfDegree k (e + 1))
    (α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})) :
    ∃ y : MilnorKRing (RatFunc k), monicIrreducibleResidue φ y = α ∧
      ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ → e + 1 ≤ d' →
        monicIrreducibleResidue ψ y = 0 :=
  mem_of_forall_milnorKSymbolProd_mem
    (H := { carrier := {β | ∃ y : MilnorKRing (RatFunc k), monicIrreducibleResidue φ y = β ∧
              ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ → e + 1 ≤ d' →
                monicIrreducibleResidue ψ y = 0}
            zero_mem' := ⟨0, map_zero _, fun _ _ _ _ ↦ map_zero _⟩
            add_mem' := by
              rintro β γ ⟨y, hy, hy0⟩ ⟨z, hz, hz0⟩
              exact ⟨y + z, by rw [map_add, hy, hz], fun d' ψ hne hle ↦ by
                rw [map_add, hy0 d' ψ hne hle, hz0 d' ψ hne hle, add_zero]⟩
            neg_mem' := by
              rintro β ⟨y, hy, hy0⟩
              exact ⟨-y, by rw [map_neg, hy], fun d' ψ hne hle ↦ by
                rw [map_neg, hy0 d' ψ hne hle, neg_zero]⟩ })
    (fun m ↦ exists_monicIrreducibleResidue_eq_milnorKSymbolProd φ m) α

end Stacks.Chow

end
