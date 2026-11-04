module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.BassTate
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ConstantRetraction

/-!
# The residue of `A¹_k` at a closed point, computed on the generators of the filtration

Let `k` be a field and `p ∈ k[X]` monic with `p ≠ 1`, generating a maximal ideal, so that
`k[X] ⧸ p` is a simple extension of `k`. Milnor's normalization of the residue at the closed
point `p` is the tame symbol of the local ring there *at the uniformizer `p`*, and it is pinned
down by

`∂_p {f_1, …, f_n, p} = {f̄_1, …, f̄_n}`

for `f_i ∈ k[X]` nonzero of degree below `deg p`, where `f̄` is the class of `f` in `k[X] ⧸ p`.
This file proves that identity, in the form that combines with the Bass–Tate generation statement
of `StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.BassTate`: **every symbol of `K^M_*(k[X] ⧸ p)`
is the residue of a class lying in `L_{deg p}`**
(`Stacks.Chow.exists_mem_milnorKPolyFiltration_dvrMilnorTameSymbol_eq`). Together with
`Stacks.Chow.affineLineResidue_eq_zero_of_mem_milnorKPolyFiltration` — the vanishing of the
residues at the closed points of larger degree — this is the generator-level form of the
surjectivity half of Milnor's exact sequence.

## Why the uniformizer is named

`Stacks.Chow.affineLineResidue` is the tame symbol at an *unspecified* uniformizer, so it cannot
be computed on a symbol ending in `p`: two uniformizers differ by a unit, and the independence of
the tame symbol from that choice is not proved in this development. The statements below are
therefore about `Stacks.Chow.dvrMilnorTameSymbol` at the uniformizer
`Stacks.Chow.irreducible_algebraMap_self`, that is at `p` itself, which is the normalization
Milnor's sequence uses. No new map is introduced for it.

## Main results

* `Stacks.Chow.dvrFracUniformizer_irreducible_algebraMap_self` — the uniformizer `p`, read as a
  unit of `RatFunc k`, is the polynomial `p`.
* `Stacks.Chow.exists_mem_milnorKPolyFiltration_dvrMilnorTameSymbol_eq` — **`∂_p` carries a
  symbol of `L_{deg p}` onto any prescribed symbol of `K^M_*(k[X] ⧸ p)`.**
* `Stacks.Chow.exists_mem_milnorKPolyFiltration_dvrMilnorTameSymbol_eq_of_monic` — the same with
  no hypothesis on the prescribed symbol, Bass-Tate having removed it.

## Implementation notes

What is **not** proved here is that *every* class of `K^M_n(k[X] ⧸ p)`, rather than every symbol,
is such a residue. Passing from the symbols to a class means taking the degree-`(n+1)` part of a
preimage, for which the homogeneity of the filtration
(`Stacks.Chow.milnorKPolyFiltration_eq_iSup_inf_milnorKGrading`) is available; what is still
missing is the graded bookkeeping that selects that part. Nothing below asserts it.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing Polynomial

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

/- The quotient of `k[X]` by a maximal ideal is a field, and the local ring of `A¹_k` at a closed
point is a discrete valuation ring. Both are definitions rather than global instances; the
statements below mention `Stacks.Chow.dvrMilnorTameSymbol` and the Milnor K-theory of
`k[X] ⧸ p`, so both are needed here as instances. -/
attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

/-! ### The uniformizer `p`, read in the rational function field -/

/-- The uniformizer `p` of the local ring at `p`, read as a unit of `RatFunc k`, is the
polynomial `p`. -/
theorem dvrFracUniformizer_irreducible_algebraMap_self {p : Polynomial k}
    [(Ideal.span {p}).IsMaximal] (hp0 : p ≠ 0) :
    dvrFracUniformizer (RatFunc k) (irreducible_algebraMap_self (p := p)) = polyUnit hp0 :=
  Units.ext (by
    rw [dvrFracUniformizer_val, coe_polyUnit, ← IsScalarTower.algebraMap_apply])

/-! ### A list of low-degree classes, lifted to units of the local ring -/

/-- **A list of classes of low-degree polynomials lifts to a list of units of the local ring at
`p`**, whose images in `RatFunc k` are polynomials of degree at most `deg p` and whose residues
are the given classes. -/
theorem exists_unitList_of_quotUnitsOfLowDegree {p : Polynomial k} [(Ideal.span {p}).IsMaximal]
    (l : List (Polynomial k ⧸ Ideal.span {p})ˣ) (hl : ∀ u ∈ l, u ∈ quotUnitsOfLowDegree p) :
    ∃ l' : List (Localization.AtPrime (Ideal.span {p}))ˣ,
      (∀ w ∈ l', Units.map (algebraMap (Localization.AtPrime (Ideal.span {p})) (RatFunc k) :
          Localization.AtPrime (Ideal.span {p}) →* RatFunc k) w ∈
          polyUnitsOfDegreeLE k p.natDegree) ∧
        l'.map (Units.map (residue (Localization.AtPrime (Ideal.span {p})) :
            Localization.AtPrime (Ideal.span {p}) →*
              ResidueField (Localization.AtPrime (Ideal.span {p})))) =
          l.map (Units.map ((quotientRingEquivResidueField (Ideal.span {p}) :
              (Polynomial k ⧸ Ideal.span {p}) →+* (Ideal.span {p}).ResidueField) :
              (Polynomial k ⧸ Ideal.span {p}) →* (Ideal.span {p}).ResidueField)) := by
  induction l with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons u l ih =>
      obtain ⟨f, hf0, hfd, hfu⟩ := hl u List.mem_cons_self
      obtain ⟨w, hw⟩ := isUnit_algebraMap_localizationAtPrime (p := p) hf0 hfd
      obtain ⟨l', hl'deg, hl'res⟩ := ih fun v hv ↦ hl v (List.mem_cons_of_mem u hv)
      refine ⟨w :: l', ?_, ?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hvw | hvl
        · rw [hvw]
          refine ⟨f, hf0, hfd.le, Units.ext ?_⟩
          show algebraMap (Polynomial k) (RatFunc k) f =
            algebraMap (Localization.AtPrime (Ideal.span {p})) (RatFunc k) (w : _)
          rw [hw, ← IsScalarTower.algebraMap_apply]
        · exact hl'deg v hvl
      · rw [List.map_cons, List.map_cons, hl'res]
        refine congrArg (· :: _) (Units.ext ?_)
        show residue (Localization.AtPrime (Ideal.span {p})) (w : _) =
          quotientRingEquivResidueField (Ideal.span {p}) (u : _)
        rw [hw, residue_algebraMap_eq_quotientRingEquivResidueField, hfu]

/-! ### The residue of a generator -/

/-- **`∂_p {f_1, …, f_n, p} = {f̄_1, …, f̄_n}`: the residue at `p`, normalized by the uniformizer
`p`, carries a symbol lying in `L_{deg p}` onto any prescribed symbol of `K^M_*(k[X] ⧸ p)`.**

The entries `f_i` are nonzero polynomials of degree below `deg p` representing the prescribed
classes, which exist by `Stacks.Chow.quotUnitsOfLowDegree_eq_univ`; they are units of the local
ring at `p`, and appending the uniformizer `p` turns their symbol into the symbol of their
residues, which is `Stacks.Chow.dvrMilnorTameSymbol_uniformizer`. The symbol lies in
`L_{deg p}` because every entry is a polynomial of degree at most `deg p`. -/
theorem exists_mem_milnorKPolyFiltration_dvrMilnorTameSymbol_eq {p : Polynomial k}
    (hp0 : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (l : List (Polynomial k ⧸ Ideal.span {p})ˣ) (hl : ∀ u ∈ l, u ∈ quotUnitsOfLowDegree p) :
    ∃ y : MilnorKTheory (RatFunc k) (l.length + 1),
      (y : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k p.natDegree ∧
      (dvrMilnorTameSymbol (F := RatFunc k) (irreducible_algebraMap_self (p := p))
            l.length y : MilnorKRing (Ideal.span {p}).ResidueField) =
        milnorKRingMap (quotientRingEquivResidueField (Ideal.span {p}) :
            (Polynomial k ⧸ Ideal.span {p}) →+* (Ideal.span {p}).ResidueField)
          (milnorKSymbolProd (Polynomial k ⧸ Ideal.span {p}) l) := by
  obtain ⟨l', hl'deg, hl'res⟩ := exists_unitList_of_quotUnitsOfLowDegree l hl
  have hlen : l'.length = l.length := by
    simpa only [List.length_map] using congrArg List.length hl'res
  set x := unitSymbolProd (RatFunc k) l' *
    milnorKSymbol (RatFunc k)
      (dvrFracUniformizer (RatFunc k) (irreducible_algebraMap_self (p := p))) with hxdef
  obtain ⟨L, hsymb, hLlen, hLdeg⟩ : ∃ L : List (RatFunc k)ˣ, x = milnorKSymbolProd (RatFunc k) L ∧
      L.length = l.length + 1 ∧ ∀ v ∈ L, v ∈ polyUnitsOfDegreeLE k p.natDegree := by
    refine ⟨l'.map (Units.map (algebraMap (Localization.AtPrime (Ideal.span {p})) (RatFunc k) :
      Localization.AtPrime (Ideal.span {p}) →* RatFunc k)) ++ [polyUnit hp0], ?_, by simp [hlen],
      fun v hv ↦ ?_⟩
    · rw [hxdef, milnorKSymbolProd_append, milnorKSymbolProd_singleton,
        dvrFracUniformizer_irreducible_algebraMap_self hp0]
      rfl
    · rcases List.mem_append.mp hv with hvl | hvp
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hvl
        exact hl'deg w hw
      · rw [List.mem_singleton.mp hvp]
        exact polyUnit_mem_polyUnitsOfDegreeLE hp0 le_rfl
  refine ⟨⟨x, by rw [hsymb, ← hLlen]; exact milnorKSymbolProd_mem_milnorKGrading L⟩, ?_, ?_⟩
  · change x ∈ milnorKPolyFiltration k p.natDegree
    rw [hsymb]
    exact milnorKSymbolProd_mem_milnorKPolyFiltration hLdeg
  · rw [dvrMilnorTameSymbol_uniformizer (irreducible_algebraMap_self (p := p)) l.length l' rfl,
      residueSymbolProd, milnorKRingMap_milnorKSymbolProd]
    exact congrArg (milnorKSymbolProd (ResidueField
      (Localization.AtPrime (Ideal.span {p})))) hl'res

/-- **Bass-Tate and the residue computation together: for `p` monic with `p ≠ 1`, EVERY symbol of
`K^M_*(k[X] ⧸ p)` is the residue at `p` of a class lying in `L_{deg p}`.** No hypothesis on the
entries of the symbol is needed: by `Stacks.Chow.quotUnitsOfLowDegree_eq_univ` every unit of
`k[X] ⧸ p` is already the class of a nonzero polynomial of degree below `deg p`. -/
theorem exists_mem_milnorKPolyFiltration_dvrMilnorTameSymbol_eq_of_monic {p : Polynomial k}
    (hp : p.Monic) (hp1 : p ≠ 1) [(Ideal.span {p}).IsMaximal]
    (l : List (Polynomial k ⧸ Ideal.span {p})ˣ) :
    ∃ y : MilnorKTheory (RatFunc k) (l.length + 1),
      (y : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k p.natDegree ∧
      (dvrMilnorTameSymbol (F := RatFunc k) (irreducible_algebraMap_self (p := p))
            l.length y : MilnorKRing (Ideal.span {p}).ResidueField) =
        milnorKRingMap (quotientRingEquivResidueField (Ideal.span {p}) :
            (Polynomial k ⧸ Ideal.span {p}) →+* (Ideal.span {p}).ResidueField)
          (milnorKSymbolProd (Polynomial k ⧸ Ideal.span {p}) l) :=
  exists_mem_milnorKPolyFiltration_dvrMilnorTameSymbol_eq hp.ne_zero l fun u _ ↦ by
    rw [quotUnitsOfLowDegree_eq_univ hp hp1]
    exact Set.mem_univ u

end Stacks.Chow

end
