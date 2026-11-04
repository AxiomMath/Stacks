module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.KeyFormulaRatioN

/-!
# The situation of Stacks 0AYB adapted to two sections at once

Let `Y` be integral and locally Noetherian, let `M` and `M'` be invertible `𝒪_Y`-modules with
nonzero global sections `t` and `t'`, and let `ℱ` be a situation of Stacks 0AYB for the pair of
meromorphic sections they define. Stacks 0B73, the commutativity of the two Gysin maps of
`(M, t)` and `(M', t')`, needs the chosen generators of the situation to be adapted to *both*
sections: at a member `Z_i` of the family lying off `Z(t)` the generator of `M_{ξ_i}` should be
the germ of `t`, and at a member lying off `Z(t')` the generator of `M'_{ξ_i}` should be the germ
of `t'`.

`Stacks.Chow.gysinGenerator`, from
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge`, already makes that
choice for one pair; this file applies it on both sides at once. The consequence the proof of
Stacks 0B73 uses is `Stacks.Chow.isRationallyEquivalentToZeroWithin_leftCoeff_gysinPair`: the
left hand side of the key formula is rationally equivalent to zero with witnesses inside the
intersection `Z(t) ∩ Z(t')` of the two zero schemes. A member off `Z(t)` has `f_i = 1`, a member
off `Z(t')` has `g_i = 1`, and either way its tame symbol is trivial, so only the members
contained in both divisors carry the rational equivalence.

## Main definitions

* `Stacks.Chow.withGysinGeneratorsPair` — the situation of Stacks 0AYB whose generators are
  prescribed on both sides.

## Main results

* `Stacks.Chow.withGysinGeneratorsPair_ratioL_eq_one`,
  `Stacks.Chow.withGysinGeneratorsPair_ratioN_eq_one` — the two ratios are `1` off the respective
  zero schemes.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_leftCoeff_of_zeroScheme_pair` — the left hand
  side of the key formula is rationally equivalent to zero, witnessed inside `Z(t) ∩ Z(t')`, for
  any situation whose ratios are trivial off the two zero schemes. The sections are allowed to be
  zero, which is the case the proof of Stacks 0B73 meets at a component contained in one of the
  two divisors.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_leftCoeff_gysinPair` — the same for the
  situation whose generators are prescribed on both sides.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (M M' : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M']
  (t : Γ(M, ⊤)) (t' : Γ(M', ⊤))

/-- **The situation of Stacks 0AYB with the generators the Gysin-Gysin comparison asks for**: at
each member of the family the generator of `M` is the germ of `t` wherever that generates, and
the generator of `M'` is the germ of `t'` wherever that generates.

This is `Stacks.Chow.withGysinGenerators` applied on both sides at once, rather than on the
first with the unit section of the structure sheaf on the second. -/
def withGysinGeneratorsPair (ℱ : KeyFormulaSituation M M') : KeyFormulaSituation M M' :=
  { ℱ with
    localGeneratorL := fun i ↦ gysinGenerator M t (ℱ.componentPoint i)
    localGeneratorN := fun i ↦ gysinGenerator M' t' (ℱ.componentPoint i)
    isStalkBasis_localGeneratorL := fun i ↦ isStalkBasis_gysinGenerator M t (ℱ.componentPoint i)
    isStalkBasis_localGeneratorN := fun i ↦
      isStalkBasis_gysinGenerator M' t' (ℱ.componentPoint i) }

variable (ℱ : KeyFormulaSituation M M')

omit [IsLocallyNoetherian Y] in
/-- `Stacks.Chow.withGysinGeneratorsPair` has the same meromorphic section of `M` as `ℱ`. -/
@[simp]
theorem withGysinGeneratorsPair_sectionL :
    (withGysinGeneratorsPair M M' t t' ℱ).sectionL = ℱ.sectionL := rfl

omit [IsLocallyNoetherian Y] in
/-- `Stacks.Chow.withGysinGeneratorsPair` has the same meromorphic section of `M'` as `ℱ`. -/
@[simp]
theorem withGysinGeneratorsPair_sectionN :
    (withGysinGeneratorsPair M M' t t' ℱ).sectionN = ℱ.sectionN := rfl

omit [IsLocallyNoetherian Y] in
/-- `Stacks.Chow.withGysinGeneratorsPair` has the same members of the family as `ℱ`. -/
@[simp]
theorem withGysinGeneratorsPair_component (i : ℱ.Index) :
    (withGysinGeneratorsPair M M' t t' ℱ).component i = ℱ.component i := rfl

omit [IsLocallyNoetherian Y] in
/-- In `Stacks.Chow.withGysinGeneratorsPair` the generator of `M` at the `i`-th member is
`Stacks.Chow.gysinGenerator M t` at its generic point. -/
@[simp]
theorem withGysinGeneratorsPair_localGeneratorL (i : ℱ.Index) :
    (withGysinGeneratorsPair M M' t t' ℱ).localGeneratorL i =
      gysinGenerator M t (ℱ.componentPoint i) := rfl

omit [IsLocallyNoetherian Y] in
/-- In `Stacks.Chow.withGysinGeneratorsPair` the generator of `M'` at the `i`-th member is
`Stacks.Chow.gysinGenerator M' t'` at its generic point. -/
@[simp]
theorem withGysinGeneratorsPair_localGeneratorN (i : ℱ.Index) :
    (withGysinGeneratorsPair M M' t t' ℱ).localGeneratorN i =
      gysinGenerator M' t' (ℱ.componentPoint i) := rfl

/-- Off `Z(s)`, the generic value of `gysinGenerator` at `ξ` is the generic germ of `s`. -/
private theorem toGenericStalk_gysinGenerator_eq_germ (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (ξ : Y)
    (hξ : ¬ Stacks.Divisors.zeroScheme Y L s ≤ integralComponentAt ξ) :
    toGenericStalk L ξ (gysinGenerator L s ξ) = L.presheaf.germ ⊤ (genericPoint Y) trivial s := by
  rw [gysinGenerator_eq_germ L s hs hξ,
    toGenericStalk_germ (Opens.mem_top ξ) (Opens.mem_top (genericPoint Y))]

/-- **The prescribed situation has `f_i = 1` at every member off `Z(t)`.** There the chosen
generator of `M` is the germ of `t`, whose generic value is the meromorphic section itself. -/
theorem withGysinGeneratorsPair_ratioL_eq_one (ht : t ≠ 0) (i : ℱ.Index)
    (hsection : ℱ.sectionL = M.presheaf.germ ⊤ (genericPoint Y) trivial t)
    (hξ : ¬ Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt (ℱ.componentPoint i)) :
    (withGysinGeneratorsPair M M' t t' ℱ).ratioL i = 1 := by
  exact ((withGysinGeneratorsPair M M' t t' ℱ).ratioL_eq_one_iff i).mpr
    ((toGenericStalk_gysinGenerator_eq_germ M t ht _ hξ).trans hsection.symm)

/-- **The prescribed situation has `g_i = 1` at every member off `Z(t')`.** There the chosen
generator of `M'` is the germ of `t'`, whose generic value is the meromorphic section itself. -/
theorem withGysinGeneratorsPair_ratioN_eq_one (ht' : t' ≠ 0) (i : ℱ.Index)
    (hsection : ℱ.sectionN = M'.presheaf.germ ⊤ (genericPoint Y) trivial t')
    (hξ : ¬ Stacks.Divisors.zeroScheme Y M' t' ≤ integralComponentAt (ℱ.componentPoint i)) :
    (withGysinGeneratorsPair M M' t t' ℱ).ratioN i = 1 := by
  exact ((withGysinGeneratorsPair M M' t t' ℱ).ratioN_eq_one_iff i).mpr
    ((toGenericStalk_gysinGenerator_eq_germ M' t' ht' _ hξ).trans hsection.symm)

/-- **The rational equivalence of the key formula is witnessed inside the intersection of the
zero schemes of two global sections**, for any situation whose ratios are trivial off them. A
member off `Z(t)` is asked to have `f_i = 1` and a member off `Z(t')` to have `g_i = 1`; either
way its tame symbol is trivial and it drops out of the right hand side of the key formula. The
surviving members are contained in both zero schemes, their supports being the closures of their
generic points.

This is the form in which the proof of Stacks 0B73 reads the key formula: the discrepancy between
the two iterated Gysin cycles is rationally equivalent to zero *on the intersection*
`Z(t) ∩ Z(t')`, which is the scheme its conclusion lives on.

Nothing is assumed about the sections themselves; in particular `t` or `t'` may be zero, in which
case its zero scheme is all of `Y` and the corresponding hypothesis is vacuous. That is the case
the proof of Stacks 0B73 meets at an integral `W` contained in one of the two divisors. -/
theorem isRationallyEquivalentToZeroWithin_leftCoeff_of_zeroScheme_pair (C : ChowSituation.{u})
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] {k : ℤ}
    (hratioL : ∀ i : ℱ.Index, ¬ Stacks.Divisors.zeroScheme Y M t ≤
      integralComponentAt (ℱ.componentPoint i) → ℱ.ratioL i = 1)
    (hratioN : ∀ i : ℱ.Index, ¬ Stacks.Divisors.zeroScheme Y M' t' ≤
      integralComponentAt (ℱ.componentPoint i) → ℱ.ratioN i = 1)
    (hdim : ∀ i : ℱ.Index,
      schemeDeltaDimension C (((ℱ.toKeyFormulaData C q).component i).subschemeι ≫ q) =
        ((k + 1 : ℤ) : EInt))
    (α : CycleGroup C q k)
    (hα : ∀ y : Y, α.1 y = (ℱ.toKeyFormulaData C q).leftCoeff C q y) :
    IsRationallyEquivalentToZeroWithin C q k α
      (((Stacks.Divisors.zeroScheme Y M t).support : Set Y) ∩
        ((Stacks.Divisors.zeroScheme Y M' t').support : Set Y)) := by
  refine (ℱ.isRationallyEquivalentToZeroWithin_leftCoeff_of_ratio_eq_one
    C q (fun i ↦ ℱ.componentPoint i ∈ ((Stacks.Divisors.zeroScheme Y M t).support : Set Y) ∧
      ℱ.componentPoint i ∈ ((Stacks.Divisors.zeroScheme Y M' t').support : Set Y))
    (fun i hi ↦ ?_) hdim α hα).mono ?_
  · by_cases h : ℱ.componentPoint i ∈ ((Stacks.Divisors.zeroScheme Y M t).support : Set Y)
    · exact Or.inr (hratioN i fun hle ↦
        hi ⟨h, (le_integralComponentAt_iff_mem_support _ _).1 hle⟩)
    · exact Or.inl (hratioL i fun hle ↦
        h ((le_integralComponentAt_iff_mem_support _ _).1 hle))
  · refine Set.iUnion_subset fun j ↦ ?_
    have hcl : (((ℱ.toKeyFormulaData C q).component j.1).support : Set Y) =
        closure {ℱ.componentPoint j.1} := coe_support_integralComponentAt _
    rw [hcl]
    refine Set.subset_inter ?_ ?_
    · exact ((Stacks.Divisors.zeroScheme Y M t).support.isClosed.closure_subset_iff).mpr
        (Set.singleton_subset_iff.mpr j.2.1)
    · exact ((Stacks.Divisors.zeroScheme Y M' t').support.isClosed.closure_subset_iff).mpr
        (Set.singleton_subset_iff.mpr j.2.2)

/-- **The rational equivalence of the key formula for two sections is witnessed inside the
intersection of their zero schemes.** This is
`Stacks.Chow.isRationallyEquivalentToZeroWithin_leftCoeff_of_zeroScheme_pair` for the situation
of `Stacks.Chow.withGysinGeneratorsPair`, whose two ratios are trivial off the respective zero
schemes by `Stacks.Chow.withGysinGeneratorsPair_ratioL_eq_one` and
`Stacks.Chow.withGysinGeneratorsPair_ratioN_eq_one`. -/
theorem isRationallyEquivalentToZeroWithin_leftCoeff_gysinPair (C : ChowSituation.{u})
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] {k : ℤ} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (hsectionL : ℱ.sectionL = M.presheaf.germ ⊤ (genericPoint Y) trivial t)
    (hsectionN : ℱ.sectionN = M'.presheaf.germ ⊤ (genericPoint Y) trivial t')
    (hdim : ∀ i : ℱ.Index,
      schemeDeltaDimension C
          ((((withGysinGeneratorsPair M M' t t' ℱ).toKeyFormulaData C q).component i).subschemeι
            ≫ q) = ((k + 1 : ℤ) : EInt))
    (α : CycleGroup C q k)
    (hα : ∀ y : Y, α.1 y =
      ((withGysinGeneratorsPair M M' t t' ℱ).toKeyFormulaData C q).leftCoeff C q y) :
    IsRationallyEquivalentToZeroWithin C q k α
      (((Stacks.Divisors.zeroScheme Y M t).support : Set Y) ∩
        ((Stacks.Divisors.zeroScheme Y M' t').support : Set Y)) :=
  isRationallyEquivalentToZeroWithin_leftCoeff_of_zeroScheme_pair M M' t t'
    (withGysinGeneratorsPair M M' t t' ℱ) C q
    (fun i ↦ withGysinGeneratorsPair_ratioL_eq_one M M' t t' ℱ ht i hsectionL)
    (fun i ↦ withGysinGeneratorsPair_ratioN_eq_one M M' t t' ℱ ht' i hsectionN) hdim α hα

end Stacks.Chow

end
