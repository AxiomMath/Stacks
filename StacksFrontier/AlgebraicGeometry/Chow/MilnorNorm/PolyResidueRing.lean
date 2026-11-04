module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueOnGenerators
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SectionMap

/-!
# The residue at a closed point of `A¹_k`, on the whole Milnor K-ring

Let `k` be a field. The residue maps of
`StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.AffineLineResidue` are stated one degree at a
time, on `K^M_{i+1}(RatFunc k)`. The inductive comparison of the steps of the degree filtration
needs them on the **whole** Milnor K-ring instead, because the steps `L_d` are subgroups of the
ring rather than of one graded piece, and every argument about them is a statement about a
subgroup. This file provides that reading of the residue, normalized at the uniformizer `ψ`
itself as in `StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueOnGenerators`, together with
its two vanishing properties.

Nothing new is proved: both vanishing statements are the ring-level lemmas already in the tree,
`Stacks.Chow.shift_dvrMilnorShiftMap_eq_zero_of_mem_milnorKPolyFiltration` and
`Stacks.Chow.shift_dvrMilnorShiftMap_eq_zero_of_mem_milnorKNotDvdFiltration`, read through the
identification of the residue field with `k[X] ⧸ ψ`.

## The index type

The closed points of `A¹_k` of a given degree are packaged as a subtype
`Stacks.Chow.MonicIrreducibleOfDegree`, so that the family of residues of a given degree is
indexed by a type and the sums over it need no `if`-then-else on a predicate. The maximality of
the ideal a point generates is registered as an instance on that subtype.

## Main definitions

* `Stacks.Chow.MonicIrreducibleOfDegree` — the monic irreducible polynomials of a given degree.
* `Stacks.Chow.monicIrreducibleResidue` — the residue `∂_ψ` on the whole Milnor K-ring, with
  values in `K^M_*(k[X] ⧸ ψ)`.

## Main results

* `Stacks.Chow.mem_polyUnitsOfDegreeLE_of_notMem_topDegreeUnits` — a generator entry which is not
  of top degree has degree one less.
* `Stacks.Chow.monicIrreducibleResidue_eq_zero_of_mem_milnorKPolyFiltration` — **`∂_ψ` kills
  `L_e`** for `ψ` of degree `e + 1`.
* `Stacks.Chow.monicIrreducibleResidue_eq_zero_of_mem_milnorKNotDvdFiltration` — **`∂_ψ` kills
  everything generated away from `ψ`.**
* `Stacks.Chow.monicIrreducibleResidue_unitSymbolProd_mul_uniformizer` — **`∂_ψ` of a symbol of
  units of the local ring followed by the uniformizer is the symbol of the residues.**
* `Stacks.Chow.monicIrreducibleResidue_eq_zero_of_poly_eq` — the residue depends only on the
  point.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u

namespace Stacks.Chow

/- The quotient of `k[X]` by a maximal ideal is a field, and the local ring of `A¹_k` at a closed
point is a discrete valuation ring. Both are definitions rather than global instances in
`Mathlib`, and the statements below name the Milnor K-theory of the first and the tame symbol of
the second. -/
attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

variable {k : Type u} [Field k]

/-! ### The closed points of a given degree -/

/-- **The closed points of `A¹_k` of degree `d`:** the monic irreducible polynomials of that
degree. -/
def MonicIrreducibleOfDegree (k : Type u) [Field k] (d : ℕ) : Type u :=
  {ψ : Polynomial k // ψ.Monic ∧ Irreducible ψ ∧ ψ.natDegree = d}

namespace MonicIrreducibleOfDegree

variable {d : ℕ}

/-- The underlying polynomial. -/
def poly (ψ : MonicIrreducibleOfDegree k d) : Polynomial k := ψ.1

/-- The polynomial of a closed point is monic. -/
theorem monic (ψ : MonicIrreducibleOfDegree k d) : (poly ψ).Monic := ψ.2.1

/-- The polynomial of a closed point is irreducible. -/
theorem irreducible (ψ : MonicIrreducibleOfDegree k d) : Irreducible (poly ψ) := ψ.2.2.1

/-- The polynomial of a closed point of degree `d` has degree `d`. -/
theorem natDegree_eq (ψ : MonicIrreducibleOfDegree k d) : (poly ψ).natDegree = d := ψ.2.2.2

/-- The polynomial of a closed point is nonzero. -/
theorem ne_zero (ψ : MonicIrreducibleOfDegree k d) : poly ψ ≠ 0 := (monic ψ).ne_zero

/-- The polynomial of a closed point of positive degree is not `1`. -/
theorem ne_one {e : ℕ} (ψ : MonicIrreducibleOfDegree k (e + 1)) : poly ψ ≠ 1 := fun hone ↦ by
  have h := natDegree_eq ψ
  rw [hone, Polynomial.natDegree_one] at h
  omega

/-- A closed point of a given degree is determined by its polynomial. -/
theorem poly_injective {ψ χ : MonicIrreducibleOfDegree k d} (h : poly ψ = poly χ) : ψ = χ :=
  Subtype.ext h

end MonicIrreducibleOfDegree

open MonicIrreducibleOfDegree

/-- A closed point generates a maximal ideal of `k[X]`. -/
instance isMaximal_span_singleton_poly {d : ℕ} (ψ : MonicIrreducibleOfDegree k d) :
    (Ideal.span {poly ψ}).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial (irreducible ψ)

/-! ### Generator entries which are not of top degree -/

/-- **An entry of a generator of `L_{e+1}` which is not a monic irreducible of degree `e + 1` has
degree at most `e`:** it is either a nonzero constant or a monic irreducible of degree at most
`e + 1`, and the second case of degree exactly `e + 1` is excluded. -/
theorem mem_polyUnitsOfDegreeLE_of_notMem_topDegreeUnits {e : ℕ} {u : (RatFunc k)ˣ}
    (hu : u ∈ polyFactorUnits k (e + 1)) (hnot : u ∉ topDegreeUnits k (e + 1)) :
    u ∈ polyUnitsOfDegreeLE k e := by
  obtain ⟨f, hf, hcase, rfl⟩ := hu
  rcases hcase with h0 | ⟨hm, hi, hle⟩
  · exact polyUnit_mem_polyUnitsOfDegreeLE hf (by omega)
  · refine polyUnit_mem_polyUnitsOfDegreeLE hf ?_
    by_contra hcon
    exact hnot ⟨f, hf, ⟨hm, hi, by omega⟩, rfl⟩

/-! ### The residue on the whole Milnor K-ring -/

/-- **The residue `∂_ψ : K^M_*(RatFunc k) ⟶ K^M_*(k[X] ⧸ ψ)` at a closed point, on the whole
Milnor K-ring.** It is the `ξ`-coefficient of `Stacks.Chow.dvrMilnorShiftMap` at the
uniformizer `ψ`, read in `k[X] ⧸ ψ` through `Stacks.Chow.quotientRingEquivResidueField`. The
uniformizer is named, as in `StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueOnGenerators`,
so that the value on a symbol ending in `ψ` can be computed. -/
def monicIrreducibleResidue {d : ℕ} (ψ : MonicIrreducibleOfDegree k d) :
    MilnorKRing (RatFunc k) →+ MilnorKRing (Polynomial k ⧸ Ideal.span {poly ψ}) :=
  (milnorKRingMap ((quotientRingEquivResidueField (Ideal.span {poly ψ})).symm :
        (Ideal.span {poly ψ}).ResidueField →+*
          (Polynomial k ⧸ Ideal.span {poly ψ}))).toAddMonoidHom.comp
    ((MilnorKShift.shiftHom (ResidueField
        (Localization.AtPrime (Ideal.span {poly ψ})))).comp
      (dvrMilnorShiftMap (F := RatFunc k)
        (irreducible_algebraMap_self (p := poly ψ))).toAddMonoidHom)

/-- The value of `∂_ψ` at `x` is the shifted `Stacks.Chow.dvrMilnorShiftMap` of `x` at the
uniformizer `ψ`, mapped to `K^M_*(k[X] ⧸ ψ)` along `Stacks.Chow.quotientRingEquivResidueField`. -/
theorem monicIrreducibleResidue_apply {d : ℕ} (ψ : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue ψ x =
      milnorKRingMap ((quotientRingEquivResidueField (Ideal.span {poly ψ})).symm :
          (Ideal.span {poly ψ}).ResidueField →+* (Polynomial k ⧸ Ideal.span {poly ψ}))
        (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
          (irreducible_algebraMap_self (p := poly ψ)) x)) :=
  rfl

/-- **`∂_ψ` kills `L_e` when `ψ` has degree `e + 1`:** a polynomial of degree at most `e` is a
unit of the local ring at `ψ`. -/
theorem monicIrreducibleResidue_eq_zero_of_mem_milnorKPolyFiltration {e : ℕ}
    (ψ : MonicIrreducibleOfDegree k (e + 1)) {x : MilnorKRing (RatFunc k)}
    (hx : x ∈ milnorKPolyFiltration k e) : monicIrreducibleResidue ψ x = 0 := by
  rw [monicIrreducibleResidue_apply,
    shift_dvrMilnorShiftMap_eq_zero_of_mem_milnorKPolyFiltration
      (irreducible_algebraMap_self (p := poly ψ)) (by rw [natDegree_eq ψ]; omega) hx,
    map_zero]

/-- **`∂_ψ` kills everything generated by polynomials not divisible by `ψ`.** -/
theorem monicIrreducibleResidue_eq_zero_of_mem_milnorKNotDvdFiltration {d : ℕ}
    (ψ : MonicIrreducibleOfDegree k d) {x : MilnorKRing (RatFunc k)}
    (hx : x ∈ milnorKNotDvdFiltration k (poly ψ)) : monicIrreducibleResidue ψ x = 0 := by
  rw [monicIrreducibleResidue_apply,
    shift_dvrMilnorShiftMap_eq_zero_of_mem_milnorKNotDvdFiltration
      (irreducible_algebraMap_self (p := poly ψ)) hx, map_zero]

/-- **`∂_ψ {u_1, …, u_r, ψ} = {ū_1, …, ū_r}`:** the residue, normalized at the uniformizer `ψ`,
of a symbol of units of the local ring at `ψ` followed by the uniformizer is the symbol of their
residues. This is `Stacks.Chow.dvrMilnorTameSymbol_uniformizer` read on the whole Milnor K-ring
and in `k[X] ⧸ ψ`; the symbol is homogeneous, which is what lets the graded statement be
applied. -/
theorem monicIrreducibleResidue_unitSymbolProd_mul_uniformizer {d : ℕ}
    (ψ : MonicIrreducibleOfDegree k d)
    (l : List (Localization.AtPrime (Ideal.span {poly ψ}))ˣ) :
    monicIrreducibleResidue ψ (unitSymbolProd (RatFunc k) l *
        milnorKSymbol (RatFunc k) (dvrFracUniformizer (RatFunc k)
          (irreducible_algebraMap_self (p := poly ψ)))) =
      milnorKSymbolProd (Polynomial k ⧸ Ideal.span {poly ψ})
        (l.map fun w ↦ Units.map
          ((quotientRingEquivResidueField (Ideal.span {poly ψ})).symm :
            (Ideal.span {poly ψ}).ResidueField →* (Polynomial k ⧸ Ideal.span {poly ψ}))
          (Units.map (residue (Localization.AtPrime (Ideal.span {poly ψ}))).toMonoidHom w)) := by
  have hgrade : unitSymbolProd (RatFunc k) l *
      milnorKSymbol (RatFunc k) (dvrFracUniformizer (RatFunc k)
        (irreducible_algebraMap_self (p := poly ψ))) ∈
      milnorKGrading (RatFunc k) (l.length + 1) := by
    refine SetLike.mul_mem_graded ?_ (milnorKSymbol_mem_milnorKGrading _)
    simpa only [unitSymbolProd, List.length_map] using
      milnorKSymbolProd_mem_milnorKGrading
        (l.map (Units.map (algebraMap (Localization.AtPrime (Ideal.span {poly ψ}))
          (RatFunc k) : Localization.AtPrime (Ideal.span {poly ψ}) →* RatFunc k)))
  rw [monicIrreducibleResidue_apply,
    show MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
        (irreducible_algebraMap_self (p := poly ψ)) (unitSymbolProd (RatFunc k) l *
          milnorKSymbol (RatFunc k) (dvrFracUniformizer (RatFunc k)
            (irreducible_algebraMap_self (p := poly ψ))))) =
      residueSymbolProd (Localization.AtPrime (Ideal.span {poly ψ})) l from
      dvrMilnorTameSymbol_uniformizer (irreducible_algebraMap_self (p := poly ψ))
        l.length (y := ⟨_, hgrade⟩) l rfl,
    residueSymbolProd, milnorKRingMap_milnorKSymbolProd, List.map_map]
  rfl

/-- **The residue depends only on the point, not on the degree it is indexed by.** -/
theorem monicIrreducibleResidue_eq_zero_of_poly_eq {d d' : ℕ}
    {ψ : MonicIrreducibleOfDegree k d} {ψ' : MonicIrreducibleOfDegree k d'}
    (h : poly ψ = poly ψ') {x : MilnorKRing (RatFunc k)}
    (hx : monicIrreducibleResidue ψ x = 0) : monicIrreducibleResidue ψ' x = 0 := by
  obtain rfl : d' = d := by rw [← natDegree_eq ψ', ← h, natDegree_eq ψ]
  obtain rfl : ψ' = ψ := poly_injective h.symm
  exact hx

/-- **`∂_ψ` kills a symbol in which `ψ` does not occur.** The entries of a generator of `L_d`
other than `ψ` are not divisible by `ψ`, by
`Stacks.Chow.notDvd_of_mem_polyFactorUnits_of_ne`. -/
theorem monicIrreducibleResidue_milnorKSymbolProd_eq_zero_of_forall_ne {d : ℕ}
    (ψ : MonicIrreducibleOfDegree k d) {l : List (RatFunc k)ˣ}
    (hl : ∀ u ∈ l, u ∈ polyFactorUnits k d)
    (hne : ∀ u ∈ l, u ≠ polyUnit (ne_zero ψ)) :
    monicIrreducibleResidue ψ (milnorKSymbolProd (RatFunc k) l) = 0 :=
  monicIrreducibleResidue_eq_zero_of_mem_milnorKNotDvdFiltration ψ
    (milnorKSymbolProd_mem_milnorKNotDvdFiltration fun u hu ↦
      notDvd_of_mem_polyFactorUnits_of_ne (monic ψ) (irreducible ψ) (ne_zero ψ)
        (natDegree_eq ψ) (hl u hu) (hne u hu))

end Stacks.Chow

end
