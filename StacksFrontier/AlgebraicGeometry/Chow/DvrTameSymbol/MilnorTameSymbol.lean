module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.FractionUnits
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKShift
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKSymbolProd
public import StacksCore.Tactic.StacksAttribute

/-!
# The tame symbol of a discrete valuation ring in every degree

Let `A` be a discrete valuation ring with fraction field `F` and residue field `κ`. Stacks 0EAY
records that there is a tame symbol

`∂_A : K^M_{i+1}(F) ⟶ K^M_i(κ)`

in every degree `i`, extending the symbol `Q(A)^* × Q(A)^* → κ^*` of Section 42.5. This file
constructs it.

The recipe is the one the source points at. Fix a uniformizer `ϖ`. Then `F^*` is `A^* × ℤ`
(`Stacks.Chow.dvrFracUnitsEquiv`), so a unit `f` of `F` has a valuation `v(f)` and a unit part
`f ϖ ^ -v(f)` whose residue is a unit of `κ`. Send `f` to

`{f ϖ ^ -v(f)} + v(f) ξ ∈ K^M_*(κ) ⊕ K^M_*(κ) ξ = MilnorKShift κ`,

a degree-one element of the ring of
`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKShift`. This kills the Steinberg relations,
so it extends to a ring homomorphism out of `K^M_*(F)`; the tame symbol is the coefficient of
`ξ`, which drops the degree by one.

The Steinberg verification is a four-way case analysis on `v(f)`, carried out in
`FractionUnits`:

* `v(f) > 0`: then `f ∈ 𝔪` and `1 - f` is a unit of `A` with residue `1`, so the image of `1 - f`
  is zero outright;
* `v(f) = 0` and `v(1 - f) > 0`: symmetrically the image of `f` is zero;
* `v(f) = v(1 - f) = 0`: both come from units of `A` whose residues add to `1`, and the Steinberg
  relation of `κ` applies;
* `v(f) = n < 0`: then `v(1 - f) = n` too and the unit parts differ by `-1`, and the `ξ`
  coefficient of the product comes out as `(n ^ 2 - n) {-1}`, which vanishes because `n ^ 2 - n`
  is even and `{-1}` is killed by `2`.

That last case is the whole reason the ring `MilnorKShift` has to be twisted; it is where
`ξ ^ 2 = {-1} ξ` and `ξ r = σ(r) ξ` are used.

In degree two the construction reproduces the formula of Stacks 02Q6 on the nose:
`∂_A(f, g) = (-1) ^ (v(f) v(g)) (f ϖ ^ -v(f)) ^ v(g) (g ϖ ^ -v(g)) ^ -v(f)`, which is
`Stacks.Chow.dvrMilnorTameSymbol_degree_two`. So this is an extension of the tame symbol of
Section 42.5 already in the tree (`Stacks.Chow.dvrTameSymbol`), not a second unrelated symbol.

Like the recipe of Section 42.5, which the source is explicit does not produce a *unique* map,
the construction uses a choice: here the uniformizer. `Stacks.Chow.dvrMilnorTameSymbol'` makes
that choice internally, giving the map `∂_A` of the source with no choice in its statement.

## Main definitions

* `Stacks.Chow.dvrMilnorThetaHom` — `f ↦ {f ϖ ^ -v(f)} + v(f) ξ`.
* `Stacks.Chow.dvrMilnorShiftMap` — the induced ring homomorphism `K^M_*(F) ⟶ MilnorKShift κ`.
* `Stacks.Chow.dvrMilnorTameSymbol` — the tame symbol `K^M_{i+1}(F) ⟶ K^M_i(κ)` of a uniformizer.
* `Stacks.Chow.dvrMilnorTameSymbol'` — the same for an unspecified uniformizer.

## Main results

* `Stacks.Chow.dvrMilnorThetaHom_mul_eq_zero` — the Steinberg relations are killed.
* `Stacks.Chow.dvrMilnorTameSymbol_eq_zero_of_units` — `∂_A` kills a symbol of units of `A`.
* `Stacks.Chow.dvrMilnorTameSymbol_uniformizer` —
  `∂_A {u_1, …, u_i, ϖ} = {ū_1, …, ū_i}`.
* `Stacks.Chow.dvrMilnorTameSymbol_degree_two` — in degree two it is the symbol of Stacks 02Q6.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

universe u v

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {F : Type v} [Field F] [Algebra A F] [IsFractionRing A F]
variable {ϖ : A}

/-! ### The degree-one map `f ↦ {f ϖ ^ -v(f)} + v(f) ξ` -/

/-- The degree-one element of `K^M_*(κ) ⊕ K^M_*(κ) ξ` attached to a unit `f` of the fraction
field: the symbol of the unit part of `f` plus `v(f)` times `ξ`. -/
def dvrMilnorThetaHom (hϖ : Irreducible ϖ) :
    Additive Fˣ →+ MilnorKShift (ResidueField A) where
  toFun x := MilnorKShift.mk
    (milnorKSymbol (ResidueField A) (dvrFracUnitPart hϖ (Additive.toMul x)))
    (dvrFracOrd hϖ (Additive.toMul x) • (1 : MilnorKRing (ResidueField A)))
  map_zero' := by
    refine MilnorKShift.ext ?_ ?_ <;>
      simp [dvrFracUnitPart_one, dvrFracOrd_one]
  map_add' x y := by
    refine MilnorKShift.ext ?_ ?_
    · change milnorKSymbol (ResidueField A) (dvrFracUnitPart hϖ
          (Additive.toMul x * Additive.toMul y)) = _
      rw [dvrFracUnitPart_mul, milnorKSymbol_mul]
      rfl
    · change dvrFracOrd hϖ (Additive.toMul x * Additive.toMul y) •
          (1 : MilnorKRing (ResidueField A)) = _
      rw [dvrFracOrd_mul, add_smul]
      rfl

/-- The `K^M_*(κ)`-component of the element attached to `f` is the symbol `{f ϖ ^ -v(f)}`. -/
@[simp]
theorem main_dvrMilnorThetaHom (hϖ : Irreducible ϖ) (f : Fˣ) :
    MilnorKShift.main (dvrMilnorThetaHom (F := F) hϖ (Additive.ofMul f)) =
      milnorKSymbol (ResidueField A) (dvrFracUnitPart hϖ f) := rfl

/-- The `ξ`-coefficient of the element attached to `f` is `v(f)`. -/
@[simp]
theorem shift_dvrMilnorThetaHom (hϖ : Irreducible ϖ) (f : Fˣ) :
    MilnorKShift.shift (dvrMilnorThetaHom (F := F) hϖ (Additive.ofMul f)) =
      dvrFracOrd hϖ f • (1 : MilnorKRing (ResidueField A)) := rfl

/-- The `ξ`-coefficient of a product of two degree-one elements:
`v(g) {f ϖ ^ -v(f)} - v(f) {g ϖ ^ -v(g)} + v(f) v(g) {-1}`. -/
theorem shift_dvrMilnorThetaHom_mul (hϖ : Irreducible ϖ) (f g : Fˣ) :
    MilnorKShift.shift (dvrMilnorThetaHom (F := F) hϖ (Additive.ofMul f) *
        dvrMilnorThetaHom (F := F) hϖ (Additive.ofMul g)) =
      dvrFracOrd hϖ g • milnorKSymbol (ResidueField A) (dvrFracUnitPart hϖ f) -
        dvrFracOrd hϖ f • milnorKSymbol (ResidueField A) (dvrFracUnitPart hϖ g) +
        (dvrFracOrd hϖ f * dvrFracOrd hϖ g) • milnorKNegOne (ResidueField A) := by
  simp only [MilnorKShift.shift_mul, main_dvrMilnorThetaHom, shift_dvrMilnorThetaHom,
    milnorKInvolution_milnorKSymbol, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, smul_neg]
  rw [mul_comm (dvrFracOrd hϖ f) (dvrFracOrd hϖ g)]
  abel

/-- The `K^M_*(κ)`-component of a product of two degree-one elements is
`{f ϖ ^ -v(f)} {g ϖ ^ -v(g)}`. -/
theorem main_dvrMilnorThetaHom_mul (hϖ : Irreducible ϖ) (f g : Fˣ) :
    MilnorKShift.main (dvrMilnorThetaHom (F := F) hϖ (Additive.ofMul f) *
        dvrMilnorThetaHom (F := F) hϖ (Additive.ofMul g)) =
      milnorKSymbol (ResidueField A) (dvrFracUnitPart hϖ f) *
        milnorKSymbol (ResidueField A) (dvrFracUnitPart hϖ g) := rfl

/-! ### The Steinberg relations are killed -/

/-- **The Steinberg relation holds in `K^M_*(κ) ⊕ K^M_*(κ) ξ`.** For units `f, g` of `F` with
`f + g = 1`, the product of the two degree-one elements attached to them is zero. -/
theorem dvrMilnorThetaHom_mul_eq_zero (hϖ : Irreducible ϖ) {f g : Fˣ}
    (hfg : (f : F) + (g : F) = 1) :
    dvrMilnorThetaHom (F := F) hϖ (Additive.ofMul f) *
      dvrMilnorThetaHom (F := F) hϖ (Additive.ofMul g) = 0 := by
  have hgf : (g : F) + (f : F) = 1 := by rw [add_comm]; exact hfg
  have hg_nonneg : dvrFracOrd hϖ f = 0 → 0 ≤ dvrFracOrd hϖ g := fun hf ↦ by
    by_contra hg
    obtain ⟨hord, -⟩ := dvrFracOrd_eq_and_dvrFracUnitPart_eq_neg_of_neg hϖ hgf (not_le.1 hg)
    omega
  refine MilnorKShift.ext ?_ ?_
  · rw [main_dvrMilnorThetaHom_mul, MilnorKShift.main_zero]
    rcases lt_trichotomy (dvrFracOrd hϖ f) 0 with hf | hf | hf
    · obtain ⟨-, hpart⟩ := dvrFracOrd_eq_and_dvrFracUnitPart_eq_neg_of_neg hϖ hfg hf
      rw [hpart]
      exact milnorKSymbol_mul_neg_self _
    · rcases (hg_nonneg hf).eq_or_lt with hg | hg
      · exact milnorKSymbol_mul_steinberg (dvrFracUnitPart_add_eq_one hϖ hfg hf hg.symm)
      · rw [dvrFracUnitPart_eq_one_of_pos hϖ hfg hg, milnorKSymbol_one, zero_mul]
    · obtain ⟨-, hpart⟩ :=
        dvrFracOrd_eq_zero_and_dvrFracUnitPart_eq_one_of_pos hϖ hfg hf
      rw [hpart, milnorKSymbol_one, mul_zero]
  · rw [shift_dvrMilnorThetaHom_mul, MilnorKShift.shift_zero]
    have htwo : (2 : ℤ) • milnorKNegOne (ResidueField A) = 0 := by
      rw [two_zsmul, milnorKNegOne_add_self]
    rcases lt_trichotomy (dvrFracOrd hϖ f) 0 with hf | hf | hf
    · obtain ⟨hord, hpart⟩ := dvrFracOrd_eq_and_dvrFracUnitPart_eq_neg_of_neg hϖ hfg hf
      set n := dvrFracOrd hϖ f with hn
      set S := milnorKSymbol (ResidueField A) (dvrFracUnitPart hϖ f) with hS
      have hneg : (-dvrFracUnitPart hϖ f : (ResidueField A)ˣ) =
          (-1 : (ResidueField A)ˣ) * dvrFracUnitPart hϖ f :=
        Units.ext (by simp)
      obtain ⟨j, hjeven⟩ := Int.even_mul_pred_self n
      have hj : n * n - n = 2 * j := by
        have h1 : n * n - n = n * (n - 1) := by ring
        rw [h1, hjeven]
        ring
      rw [hord, hpart, hneg, milnorKSymbol_mul, ← milnorKNegOne_eq, smul_add, ← hS]
      have hstep : n • S - (n • milnorKNegOne (ResidueField A) + n • S) +
          (n * n) • milnorKNegOne (ResidueField A) =
          (n * n - n) • milnorKNegOne (ResidueField A) := by
        rw [sub_smul]
        abel
      rw [hstep, hj, mul_comm 2 j, mul_smul, htwo, smul_zero]
    · rcases (hg_nonneg hf).eq_or_lt with hg | hg
      · rw [hf, ← hg]
        simp
      · rw [hf, dvrFracUnitPart_eq_one_of_pos hϖ hfg hg, milnorKSymbol_one]
        simp
    · obtain ⟨hord, hpart⟩ :=
        dvrFracOrd_eq_zero_and_dvrFracUnitPart_eq_one_of_pos hϖ hfg hf
      rw [hord, hpart, milnorKSymbol_one]
      simp

/-! ### The induced ring homomorphism -/

/-- The map of the Milnor tensor algebra of `F` into `K^M_*(κ) ⊕ K^M_*(κ) ξ`. -/
def dvrMilnorTensorMap (hϖ : Irreducible ϖ) :
    MilnorKTensorAlgebra F →ₐ[ℤ] MilnorKShift (ResidueField A) :=
  TensorAlgebra.lift ℤ (AddMonoidHom.toIntLinearMap (dvrMilnorThetaHom (F := F) hϖ))

/-- On a generator `a` of the tensor algebra, `Stacks.Chow.dvrMilnorTensorMap` is
`Stacks.Chow.dvrMilnorThetaHom`. -/
@[simp]
theorem dvrMilnorTensorMap_ι (hϖ : Irreducible ϖ) (a : Additive Fˣ) :
    dvrMilnorTensorMap (F := F) hϖ (TensorAlgebra.ι ℤ a) = dvrMilnorThetaHom hϖ a := by
  rw [dvrMilnorTensorMap, TensorAlgebra.lift_ι_apply]
  rfl

/-- `Stacks.Chow.dvrMilnorTensorMap` vanishes on the Steinberg relations of `F`. -/
theorem dvrMilnorTensorMap_of_mem_milnorKSteinbergRelations (hϖ : Irreducible ϖ)
    {x : MilnorKTensorAlgebra F} (hx : x ∈ milnorKSteinbergRelations F) :
    dvrMilnorTensorMap (F := F) hϖ x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [map_mul, dvrMilnorTensorMap_ι, dvrMilnorTensorMap_ι]
  refine dvrMilnorThetaHom_mul_eq_zero hϖ ?_
  simp

/-- `Stacks.Chow.dvrMilnorTensorMap` vanishes on the two-sided ideal generated by the Steinberg
relations of `F`. -/
theorem dvrMilnorTensorMap_eq_zero_of_mem_milnorKSteinbergIdeal (hϖ : Irreducible ϖ)
    {x : MilnorKTensorAlgebra F} (hx : x ∈ milnorKSteinbergIdeal F) :
    dvrMilnorTensorMap (F := F) hϖ x = 0 := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx => exact dvrMilnorTensorMap_of_mem_milnorKSteinbergRelations hϖ hx
  | zero => exact map_zero _
  | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x _ ihx => rw [map_neg, ihx, neg_zero]
  | left_absorb a x _ ihx => rw [map_mul, ihx, mul_zero]
  | right_absorb b x _ ihx => rw [map_mul, ihx, zero_mul]

/-- The ring homomorphism `K^M_*(F) ⟶ K^M_*(κ) ⊕ K^M_*(κ) ξ` whose `ξ`-coefficient is the tame
symbol. -/
def dvrMilnorShiftMap (hϖ : Irreducible ϖ) :
    MilnorKRing F →+* MilnorKShift (ResidueField A) :=
  (milnorKSteinbergIdeal F).ringCon.lift (dvrMilnorTensorMap (F := F) hϖ).toRingHom
    (by
      intro x y hxy
      rw [RingCon.ker_apply]
      have hmem : x - y ∈ milnorKSteinbergIdeal F :=
        ((milnorKSteinbergIdeal F).rel_iff x y).mp hxy
      have hzero := dvrMilnorTensorMap_eq_zero_of_mem_milnorKSteinbergIdeal hϖ hmem
      rw [map_sub, sub_eq_zero] at hzero
      exact hzero)

/-- `Stacks.Chow.dvrMilnorShiftMap` on the class of an element of the tensor algebra is
`Stacks.Chow.dvrMilnorTensorMap` of that element. -/
@[simp]
theorem dvrMilnorShiftMap_mk' (hϖ : Irreducible ϖ) (x : MilnorKTensorAlgebra F) :
    dvrMilnorShiftMap (F := F) hϖ ((milnorKSteinbergIdeal F).ringCon.mk' x) =
      dvrMilnorTensorMap hϖ x := rfl

/-- `Stacks.Chow.dvrMilnorShiftMap` sends the symbol `{f}` to `{f ϖ ^ -v(f)} + v(f) ξ`. -/
@[simp]
theorem dvrMilnorShiftMap_milnorKSymbol (hϖ : Irreducible ϖ) (f : Fˣ) :
    dvrMilnorShiftMap (F := F) hϖ (milnorKSymbol F f) =
      dvrMilnorThetaHom hϖ (Additive.ofMul f) := by
  rw [milnorKSymbol_eq_mk', dvrMilnorShiftMap_mk', dvrMilnorTensorMap_ι]

/-! ### The degree -/

/-- The element attached to a unit of `F` has degree one in `K^M_*(κ) ⊕ K^M_*(κ) ξ`. -/
theorem dvrMilnorThetaHom_mem_milnorKShiftGrading (hϖ : Irreducible ϖ) (a : Additive Fˣ) :
    dvrMilnorThetaHom (F := F) hϖ a ∈ milnorKShiftGrading (ResidueField A) 1 := by
  refine mem_milnorKShiftGrading.2 ⟨milnorKSymbol_mem_milnorKGrading _, ?_⟩
  rw [milnorKGradingPred_succ]
  exact zsmul_mem (SetLike.one_mem_graded (A := milnorKGrading (ResidueField A))) _

/-- `Stacks.Chow.dvrMilnorTensorMap` sends the degree-`n` part of the tensor algebra into the
degree-`n` part of `K^M_*(κ) ⊕ K^M_*(κ) ξ`. -/
theorem dvrMilnorTensorMap_mem_milnorKShiftGrading (hϖ : Irreducible ϖ) (n : ℕ)
    {x : MilnorKTensorAlgebra F} (hx : x ∈ milnorKTensorGrading F n) :
    dvrMilnorTensorMap (F := F) hϖ x ∈ milnorKShiftGrading (ResidueField A) n := by
  induction n generalizing x with
  | zero =>
      rw [milnorKTensorGrading, pow_zero, Submodule.one_eq_range] at hx
      obtain ⟨r, rfl⟩ := hx
      have hr : dvrMilnorTensorMap (F := F) hϖ ((Algebra.linearMap ℤ (MilnorKTensorAlgebra F)) r) =
          r • (1 : MilnorKShift (ResidueField A)) := by
        change dvrMilnorTensorMap (F := F) hϖ (algebraMap ℤ (MilnorKTensorAlgebra F) r) = _
        rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      rw [hr]
      exact zsmul_mem one_mem_milnorKShiftGrading _
  | succ n ih =>
      rw [milnorKTensorGrading, pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        obtain ⟨m, rfl⟩ := hb
        exact milnorKShiftGrading_mul (ih ha)
          (by rw [dvrMilnorTensorMap_ι]; exact dvrMilnorThetaHom_mem_milnorKShiftGrading hϖ m)
      · intro a b ha hb
        rw [map_add]
        exact add_mem ha hb

/-- The `ξ`-coefficient of the image of an element of `K^M_{i+1}(F)` lies in `K^M_i(κ)`. -/
theorem dvrMilnorShiftMap_shift_mem (hϖ : Irreducible ϖ) (i : ℕ) {x : MilnorKRing F}
    (hx : x ∈ milnorKGrading F (i + 1)) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ x) ∈ milnorKGrading (ResidueField A) i := by
  obtain ⟨t, ht, rfl⟩ := hx
  simp only [SetLike.mem_coe, Submodule.mem_toAddSubgroup] at ht
  have hmem := dvrMilnorTensorMap_mem_milnorKShiftGrading hϖ (i + 1) ht
  have hval : dvrMilnorShiftMap (F := F) hϖ
      ((milnorKSteinbergIdeal F).ringCon.mk'.toAddMonoidHom t) =
      dvrMilnorTensorMap hϖ t := rfl
  rw [hval]
  simpa using (mem_milnorKShiftGrading.1 hmem).2

/-! ### The tame symbol -/

/-- **The tame symbol of a discrete valuation ring in every degree.** For a discrete
valuation ring `A` with fraction field `F` and residue field `κ`, and a uniformizer `ϖ`, the
homomorphism

`∂_A : K^M_{i+1}(F) ⟶ K^M_i(κ)`

of the remark. It is the coefficient of `ξ` in the image of the ring homomorphism
`Stacks.Chow.dvrMilnorShiftMap`, which sends a unit `f` of `F` to `{f ϖ ^ -v(f)} + v(f) ξ`; that
coefficient drops the degree by one. In degree two it is the tame symbol of Section 42.5
(`Stacks.Chow.dvrMilnorTameSymbol_degree_two`, the formula of Stacks 02Q6; and
`Stacks.Chow.dvrMilnorTameSymbol_milnorKTwoPureSymbol`, the comparison with
`Stacks.Chow.dvrRegularTameSymbol` itself), and it is characterized in general by
`Stacks.Chow.dvrMilnorTameSymbol_eq_zero_of_units` and
`Stacks.Chow.dvrMilnorTameSymbol_uniformizer`.

Only the discrete valuation ring case is proved here. The source's extension of `∂_A` to an
excellent local domain of dimension one is a citation to [Kato-Milnor-K], and its extension to an
arbitrary Noetherian local domain of dimension one is flagged in the source itself as a
conjecture ("presumably"); neither is formalized. -/
@[stacks 0EAY "the tame symbol ∂_A : K^M_{i+1}(F) → K^M_i(κ) of a discrete valuation ring A with \
fraction field F and residue field κ, constructed as in Section 42.5"]
def dvrMilnorTameSymbol (hϖ : Irreducible ϖ) (i : ℕ) :
    MilnorKTheory F (i + 1) →+ MilnorKTheory (ResidueField A) i where
  toFun y := ⟨MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ (y : MilnorKRing F)),
    dvrMilnorShiftMap_shift_mem hϖ i y.2⟩
  map_zero' := Subtype.ext (by
    change MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ 0) = 0
    rw [map_zero, MilnorKShift.shift_zero])
  map_add' y z := Subtype.ext (by
    change MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ
        ((y : MilnorKRing F) + (z : MilnorKRing F))) = _
    rw [map_add, MilnorKShift.shift_add]
    rfl)

/-- The tame symbol of `y` is the `ξ`-coefficient of `Stacks.Chow.dvrMilnorShiftMap` of `y`. -/
@[simp]
theorem dvrMilnorTameSymbol_coe (hϖ : Irreducible ϖ) (i : ℕ) (y : MilnorKTheory F (i + 1)) :
    (dvrMilnorTameSymbol hϖ i y : MilnorKRing (ResidueField A)) =
      MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ (y : MilnorKRing F)) := rfl

/-- **The tame symbol `∂_A` of a discrete valuation ring, in every degree.** The map
of `Stacks.Chow.dvrMilnorTameSymbol` for an unspecified uniformizer, so that the statement names
no choice — as in the source, which asserts that a tame symbol exists rather than that it is
unique (Section 42.5: "We do not claim there is a unique map with these properties"). -/
@[stacks 0EAY "the existence of the tame symbol ∂_A : K^M_{i+1}(F) → K^M_i(κ) for A a discrete \
valuation ring, with no choice of uniformizer in the statement"]
def dvrMilnorTameSymbol' (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (F : Type v) [Field F] [Algebra A F] [IsFractionRing A F] (i : ℕ) :
    MilnorKTheory F (i + 1) →+ MilnorKTheory (ResidueField A) i :=
  dvrMilnorTameSymbol (F := F) (exists_irreducible A).choose_spec i

/-- `Stacks.Chow.dvrMilnorTameSymbol'` of `y` is the `ξ`-coefficient of
`Stacks.Chow.dvrMilnorShiftMap` of `y` for the chosen uniformizer. -/
@[simp]
theorem dvrMilnorTameSymbol'_coe (i : ℕ) (y : MilnorKTheory F (i + 1)) :
    (dvrMilnorTameSymbol' A F i y : MilnorKRing (ResidueField A)) =
      MilnorKShift.shift (dvrMilnorShiftMap (F := F) (exists_irreducible A).choose_spec
        (y : MilnorKRing F)) := rfl

/-! ### Values on symbols -/

/-- The symbol `{u_1, …, u_r}` in `K^M_*(F)` of a list of units of `A`, read in `F`. -/
def unitSymbolProd (F : Type v) [Field F] [Algebra A F] [IsFractionRing A F] (l : List Aˣ) :
    MilnorKRing F :=
  milnorKSymbolProd F (l.map (Units.map (algebraMap A F : A →* F)))

/-- The symbol `{ū_1, …, ū_r}` in `K^M_*(κ)` of the residues of a list of units of `A`. -/
def residueSymbolProd (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (l : List Aˣ) : MilnorKRing (ResidueField A) :=
  milnorKSymbolProd (ResidueField A) (l.map (Units.map (residue A).toMonoidHom))

/-- A unit of `A`, read in `F`, has valuation zero. -/
theorem dvrFracOrd_unitsMap (hϖ : Irreducible ϖ) (w : Aˣ) :
    dvrFracOrd (F := F) hϖ (Units.map (algebraMap A F : A →* F) w) = 0 :=
  dvrFracOrd_eq_of_eq (u := w) (n := 0) hϖ (by simp)

/-- The unit part of a unit `w` of `A`, read in `F`, is the residue of `w`. -/
theorem dvrFracUnitPart_unitsMap (hϖ : Irreducible ϖ) (w : Aˣ) :
    dvrFracUnitPart (F := F) hϖ (Units.map (algebraMap A F : A →* F) w) =
      Units.map (residue A).toMonoidHom w :=
  dvrFracUnitPart_eq_of_eq (u := w) (n := 0) hϖ (by simp)

/-- A symbol of units of `A` has no `ξ`-coefficient: its image is `{ū_1, …, ū_r}` with no `ξ`
part at all. -/
theorem dvrMilnorShiftMap_unitSymbolProd (hϖ : Irreducible ϖ) (l : List Aˣ) :
    dvrMilnorShiftMap (F := F) hϖ (unitSymbolProd F l) =
      MilnorKShift.mk (residueSymbolProd A l) 0 := by
  induction l with
  | nil =>
      change dvrMilnorShiftMap (F := F) hϖ 1 = _
      rw [map_one]
      rfl
  | cons w l ih =>
      have hcons : unitSymbolProd F (w :: l) =
          milnorKSymbol F (Units.map (algebraMap A F : A →* F) w) * unitSymbolProd F l := rfl
      have hcons' : residueSymbolProd A (w :: l) =
          milnorKSymbol (ResidueField A) (Units.map (residue A).toMonoidHom w) *
            residueSymbolProd A l := rfl
      rw [hcons, map_mul, ih, dvrMilnorShiftMap_milnorKSymbol, hcons']
      refine MilnorKShift.ext ?_ ?_
      · simp [dvrFracUnitPart_unitsMap]
      · simp [dvrFracOrd_unitsMap]

/-- **`∂_A` kills a symbol of units of `A`.** This is one half of the characterization of the
tame symbol. -/
theorem dvrMilnorTameSymbol_eq_zero_of_units (hϖ : Irreducible ϖ) (i : ℕ)
    {y : MilnorKTheory F (i + 1)} (l : List Aˣ) (hy : (y : MilnorKRing F) = unitSymbolProd F l) :
    dvrMilnorTameSymbol hϖ i y = 0 := by
  refine Subtype.ext ?_
  rw [dvrMilnorTameSymbol_coe, hy, dvrMilnorShiftMap_unitSymbolProd]
  rfl

/-- **`∂_A {u_1, …, u_i, ϖ} = {ū_1, …, ū_i}`.** This is the other half of the characterization of
the tame symbol: appending the uniformizer to a symbol of units of `A` turns it into the symbol
of the residues. -/
theorem dvrMilnorTameSymbol_uniformizer (hϖ : Irreducible ϖ) (i : ℕ)
    {y : MilnorKTheory F (i + 1)} (l : List Aˣ)
    (hy : (y : MilnorKRing F) =
      unitSymbolProd F l * milnorKSymbol F (dvrFracUniformizer F hϖ)) :
    (dvrMilnorTameSymbol hϖ i y : MilnorKRing (ResidueField A)) = residueSymbolProd A l := by
  have hord : dvrFracOrd (F := F) hϖ (dvrFracUniformizer F hϖ) = 1 :=
    dvrFracOrd_eq_of_eq (u := 1) (n := 1) hϖ (by simp)
  have hpart : dvrFracUnitPart (F := F) hϖ (dvrFracUniformizer F hϖ) = 1 :=
    (dvrFracUnitPart_eq_of_eq (u := 1) (n := 1) hϖ (by simp)).trans (Units.ext (by simp))
  rw [dvrMilnorTameSymbol_coe, hy, map_mul, dvrMilnorShiftMap_unitSymbolProd,
    dvrMilnorShiftMap_milnorKSymbol, MilnorKShift.shift_mul, MilnorKShift.main_mk,
    MilnorKShift.shift_mk, main_dvrMilnorThetaHom, shift_dvrMilnorThetaHom, hord, hpart,
    milnorKSymbol_one]
  simp

/-- A unit of `F` coming from a unit of `A` has valuation zero. -/
theorem dvrFracOrd_eq_zero_of_eq_algebraMap_unit (hϖ : Irreducible ϖ) {f : Fˣ} {u : Aˣ}
    (hu : algebraMap A F (u : A) = (f : F)) : dvrFracOrd hϖ f = 0 :=
  dvrFracOrd_eq_of_eq (u := u) (n := 0) hϖ (by rw [← hu]; simp)

/-- **`∂_A` kills a symbol all of whose entries have valuation zero.** Such entries are units of
`A`, so no factor contributes a `ξ`, and the coefficient of `ξ` in the product is zero. This is
the general-degree form of Stacks 02Q2, and is what makes the tame-symbol boundary of a class
vanish at all but finitely many points of a scheme. -/
theorem dvrMilnorShiftMap_shift_milnorKSymbolProd_eq_zero (hϖ : Irreducible ϖ) {l : List Fˣ}
    (hl : ∀ f ∈ l, dvrFracOrd hϖ f = 0) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ (milnorKSymbolProd F l)) = 0 := by
  induction l with
  | nil =>
      rw [milnorKSymbolProd_nil, map_one]
      rfl
  | cons f l ih =>
      have hf : dvrFracOrd hϖ f = 0 := hl f (by simp)
      have hrest := ih fun g hg ↦ hl g (by simp [hg])
      rw [milnorKSymbolProd_cons, map_mul, dvrMilnorShiftMap_milnorKSymbol,
        MilnorKShift.shift_mul, shift_dvrMilnorThetaHom, hf, hrest]
      simp

/-- **`∂_A` kills a symbol of units of `A` in every degree**, for the symbol with no choice of
uniformizer in its statement. -/
theorem dvrMilnorTameSymbol'_eq_zero_of_milnorKSymbolProd (i : ℕ)
    {y : MilnorKTheory F (i + 1)} (l : List Fˣ) (hy : (y : MilnorKRing F) = milnorKSymbolProd F l)
    (hl : ∀ f ∈ l, ∃ u : Aˣ, algebraMap A F (u : A) = (f : F)) :
    dvrMilnorTameSymbol' A F i y = 0 := by
  refine Subtype.ext ?_
  rw [dvrMilnorTameSymbol'_coe, hy]
  refine dvrMilnorShiftMap_shift_milnorKSymbolProd_eq_zero _ fun f hf ↦ ?_
  obtain ⟨u, hu⟩ := hl f hf
  exact dvrFracOrd_eq_zero_of_eq_algebraMap_unit _ hu

/-- **In degree two the construction is the tame symbol of Section 42.5.** With `v` the valuation
and `ū` the unit part, `∂_A {f, g} = (-1) ^ (v(f) v(g)) ū_f ^ v(g) (ū_g ^ v(f))⁻¹`, which is the
formula of Stacks 02Q6 and so of `Stacks.Chow.dvrTameSymbolFormula`. -/
theorem dvrMilnorTameSymbol_degree_two (hϖ : Irreducible ϖ) (f g : Fˣ) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ
        (milnorKSymbol F f * milnorKSymbol F g)) =
      milnorKSymbol (ResidueField A)
        ((-1 : (ResidueField A)ˣ) ^ (dvrFracOrd hϖ f * dvrFracOrd hϖ g) *
          dvrFracUnitPart hϖ f ^ dvrFracOrd hϖ g *
          (dvrFracUnitPart hϖ g ^ dvrFracOrd hϖ f)⁻¹) := by
  rw [map_mul, dvrMilnorShiftMap_milnorKSymbol, dvrMilnorShiftMap_milnorKSymbol,
    shift_dvrMilnorThetaHom_mul, milnorKSymbol_mul, milnorKSymbol_mul, milnorKSymbol_inv,
    milnorKSymbol_zpow, milnorKSymbol_zpow, milnorKSymbol_zpow, ← milnorKNegOne_eq]
  abel

end Stacks.Chow
