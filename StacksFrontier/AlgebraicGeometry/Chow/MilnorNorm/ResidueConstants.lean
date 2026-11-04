module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SingleResidue

/-!
# The residues of `K^M_*(RatFunc k)` are linear over `K^M_*(k)`

Let `k` be a field. The residues `∂_ψ` at the closed points of `A¹_k` and the residue `∂_∞` at
infinity are homomorphisms of `K^M_*(k)`-modules, up to the grading involution `σ` on the right:

* `∂_ψ (c(z) y) = ι_ψ(z) ∂_ψ(y)` and `∂_ψ (y c(z)) = ∂_ψ(y) σ(ι_ψ(z))`
  (`Stacks.Chow.monicIrreducibleResidue_constants_mul`,
  `Stacks.Chow.monicIrreducibleResidue_mul_constants`);
* `∂_∞ (c(z) y) = z ∂_∞(y)` and `∂_∞ (y c(z)) = ∂_∞(y) σ(z)`
  (`Stacks.Chow.infinityResidueRing_constants_mul`,
  `Stacks.Chow.infinityResidueRing_mul_constants`),

where `c : K^M_*(k) → K^M_*(RatFunc k)` and `ι_ψ : K^M_*(k) → K^M_*(k[X] ⧸ ψ)` are induced by the
inclusions of the constants.

The reason is the same at every point: a nonzero constant is a unit of the local ring, so the
ring homomorphism `K^M_*(F) ⟶ K^M_*(κ) ⊕ K^M_*(κ) ξ` computing the tame symbol sends the image
of `K^M_*(k)` into the `ξ`-free part (`Stacks.Chow.dvrMilnorShiftMap_milnorKRingMap_units`), and
the `ξ`-coefficient of a product with a `ξ`-free element is computed by the multiplication rule of
the shifted ring (`MilnorKShift.shift_ofMilnorK_mul`, `MilnorKShift.shift_mul_ofMilnorK`).

The homomorphisms of rings out of a Milnor K-ring are determined by their values on the symbols
(`Stacks.Chow.milnorKRing_ringHom_ext`); this gives the functoriality of `milnorKRingMap`
(`Stacks.Chow.milnorKRingMap_comp`, `Stacks.Chow.milnorKRingMap_id`).

## Main results

* `Stacks.Chow.milnorKRing_ringHom_ext` — ring homomorphisms agreeing on symbols are equal.
* `Stacks.Chow.milnorKRingMap_comp`, `Stacks.Chow.milnorKRingMap_id` — functoriality.
* `Stacks.Chow.milnorKInvolution_milnorKRingMap` — `σ` commutes with the induced maps.
* `Stacks.Chow.dvrMilnorShiftMap_milnorKRingMap_units` — the image of the constants is `ξ`-free.
* `Stacks.Chow.monicIrreducibleResidue_constants_mul`,
  `Stacks.Chow.monicIrreducibleResidue_mul_constants` — linearity of `∂_ψ`.
* `Stacks.Chow.infinityResidueRing_constants_mul`, `Stacks.Chow.infinityResidueRing_mul_constants`
  — linearity of `∂_∞`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u v

/-! ### Products with a `ξ`-free element in the shifted ring -/

namespace MilnorKShift

variable {k : Type u} [Field k]

/-- The `ξ`-coefficient of `a · y` for `a` without `ξ`-part is `a` times that of `y`. -/
theorem shift_ofMilnorK_mul (a : MilnorKRing k) (y : MilnorKShift k) :
    shift (ofMilnorK k a * y) = a * shift y := by
  rw [shift_mul, main_ofMilnorK, shift_ofMilnorK]
  simp

/-- The `ξ`-coefficient of `y · a` for `a` without `ξ`-part is that of `y` times `σ(a)`. -/
theorem shift_mul_ofMilnorK (y : MilnorKShift k) (a : MilnorKRing k) :
    shift (y * ofMilnorK k a) = shift y * milnorKInvolution k a := by
  rw [shift_mul, main_ofMilnorK, shift_ofMilnorK]
  simp

end MilnorKShift

namespace Stacks.Chow

/-! ### Ring homomorphisms out of a Milnor K-ring -/

section Functoriality

variable {k k' k'' : Type u} [Field k] [Field k'] [Field k'']

/-- **A ring homomorphism out of `K^M_*(k)` is determined by its values on the symbols.** -/
theorem milnorKRing_ringHom_ext {R : Type v} [Ring R] {f g : MilnorKRing k →+* R}
    (h : ∀ u : kˣ, f (milnorKSymbol k u) = g (milnorKSymbol k u)) : f = g := by
  refine RingHom.ext fun x ↦ ?_
  refine mem_of_forall_milnorKSymbolProd_mem
    (H := AddMonoidHom.eqLocus f.toAddMonoidHom g.toAddMonoidHom) (fun l ↦ ?_) x
  induction l with
  | nil => exact (map_one f).trans (map_one g).symm
  | cons u l ih =>
      change f (milnorKSymbolProd k (u :: l)) = g (milnorKSymbolProd k (u :: l))
      rw [milnorKSymbolProd_cons, map_mul, map_mul, h u]
      exact congrArg _ ih

/-- The map induced by a composite of field homomorphisms is the composite of the induced maps. -/
theorem milnorKRingMap_comp (f : k →+* k') (g : k' →+* k'') :
    milnorKRingMap (g.comp f) = (milnorKRingMap g).comp (milnorKRingMap f) :=
  milnorKRing_ringHom_ext fun u ↦ by
    simp only [RingHom.comp_apply, milnorKRingMap_milnorKSymbol]
    rfl

/-- `milnorKRingMap g (milnorKRingMap f x) = milnorKRingMap (g.comp f) x`. -/
theorem milnorKRingMap_comp_apply (f : k →+* k') (g : k' →+* k'') (x : MilnorKRing k) :
    milnorKRingMap g (milnorKRingMap f x) = milnorKRingMap (g.comp f) x := by
  rw [milnorKRingMap_comp, RingHom.comp_apply]

/-- The map induced by the identity of `k` is the identity of `K^M_*(k)`. -/
theorem milnorKRingMap_id : milnorKRingMap (RingHom.id k) = RingHom.id (MilnorKRing k) :=
  milnorKRing_ringHom_ext fun u ↦ by
    rw [milnorKRingMap_milnorKSymbol, RingHom.id_apply]
    rfl

/-- The map induced by the identity of `k` fixes every element of `K^M_*(k)`. -/
theorem milnorKRingMap_id_apply (x : MilnorKRing k) : milnorKRingMap (RingHom.id k) x = x := by
  rw [milnorKRingMap_id, RingHom.id_apply]

/-- **The grading involution commutes with the maps induced by field homomorphisms.** -/
theorem milnorKInvolution_milnorKRingMap (f : k →+* k') (x : MilnorKRing k) :
    milnorKInvolution k' (milnorKRingMap f x) = milnorKRingMap f (milnorKInvolution k x) := by
  have h : (milnorKInvolution k').comp (milnorKRingMap f) =
      (milnorKRingMap f).comp (milnorKInvolution k) :=
    milnorKRing_ringHom_ext fun u ↦ by
      simp only [RingHom.comp_apply, milnorKRingMap_milnorKSymbol,
        milnorKInvolution_milnorKSymbol, map_neg]
  exact congrArg (· x) h

end Functoriality

/-! ### The image of the constants is `ξ`-free -/

section Dvr

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {F : Type u} [Field F] [Algebra A F] [IsFractionRing A F]
variable {ϖ : A} {k : Type u} [Field k]

/-- **The image of `K^M_*(k)` under a homomorphism `k → A` into a discrete valuation ring has no
`ξ`-part**: the units of `k` go to units of `A`, of valuation zero. -/
theorem dvrMilnorShiftMap_milnorKRingMap_units (hϖ : Irreducible ϖ) (j : k →+* A)
    (z : MilnorKRing k) :
    dvrMilnorShiftMap (F := F) hϖ (milnorKRingMap ((algebraMap A F).comp j) z) =
      MilnorKShift.ofMilnorK (ResidueField A) (milnorKRingMap ((residue A).comp j) z) := by
  have h : (dvrMilnorShiftMap (F := F) hϖ).comp (milnorKRingMap ((algebraMap A F).comp j)) =
      (MilnorKShift.ofMilnorK (ResidueField A)).comp (milnorKRingMap ((residue A).comp j)) := by
    refine milnorKRing_ringHom_ext fun u ↦ ?_
    simp only [RingHom.comp_apply, milnorKRingMap_milnorKSymbol, dvrMilnorShiftMap_milnorKSymbol]
    have hx : ((Units.map (((algebraMap A F).comp j : k →+* F) : k →* F) u : Fˣ) : F) =
        algebraMap A F ((Units.map (j : k →* A) u : Aˣ) : A) * (algebraMap A F ϖ) ^ (0 : ℤ) := by
      simp
    refine MilnorKShift.ext ?_ ?_
    · rw [main_dvrMilnorThetaHom, dvrFracUnitPart_eq_of_eq hϖ hx, MilnorKShift.main_ofMilnorK]
      rfl
    · rw [shift_dvrMilnorThetaHom, dvrFracOrd_eq_of_eq hϖ hx, MilnorKShift.shift_ofMilnorK,
        zero_smul]
  exact congrArg (· z) h

end Dvr

variable {k : Type u} [Field k]

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] isDiscreteValuationRing_localizationAtPrime_polynomial

/-! ### Linearity of the residues at the closed points -/

/-- The constants, read in the local ring of `A¹_k` at a point. -/
def constantsToLocalization (P : Ideal (Polynomial k)) [P.IsPrime] :
    k →+* Localization.AtPrime P :=
  (algebraMap (Polynomial k) (Localization.AtPrime P)).comp (C : k →+* Polynomial k)

/-- The inclusion of the constants `k → RatFunc k` factors through the local ring of `A¹_k` at any
prime `P`. -/
theorem constantsHom_eq_comp (P : Ideal (Polynomial k)) [P.IsPrime] :
    constantsHom k = (algebraMap (Localization.AtPrime P) (RatFunc k)).comp
      (constantsToLocalization P) := by
  rw [constantsToLocalization, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  rfl

/-- The residue of a constant at `ψ` is its class in `k[X] ⧸ ψ`. -/
theorem quotientRingEquivResidueField_symm_residue_constants {d : ℕ}
    (ψ : MonicIrreducibleOfDegree k d) :
    ((quotientRingEquivResidueField (Ideal.span {poly ψ})).symm :
        (Ideal.span {poly ψ}).ResidueField →+* (Polynomial k ⧸ Ideal.span {poly ψ})).comp
      ((residue (Localization.AtPrime (Ideal.span {poly ψ}))).comp
        (constantsToLocalization (Ideal.span {poly ψ}))) =
      algebraMap k (Polynomial k ⧸ Ideal.span {poly ψ}) := by
  refine RingHom.ext fun c ↦ ?_
  simp only [RingHom.comp_apply, constantsToLocalization, RingEquiv.coe_toRingHom]
  rw [residue_algebraMap_eq_quotientRingEquivResidueField, RingEquiv.symm_apply_apply]
  rfl

/-- **`∂_ψ (c(z) y) = ι_ψ(z) ∂_ψ(y)`.** -/
theorem monicIrreducibleResidue_constants_mul {d : ℕ} (ψ : MonicIrreducibleOfDegree k d)
    (z : MilnorKRing k) (y : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue ψ (milnorKRingMap (constantsHom k) z * y) =
      milnorKRingMap (algebraMap k (Polynomial k ⧸ Ideal.span {poly ψ})) z *
        monicIrreducibleResidue ψ y := by
  rw [monicIrreducibleResidue_apply, monicIrreducibleResidue_apply, map_mul,
    constantsHom_eq_comp (Ideal.span {poly ψ}), dvrMilnorShiftMap_milnorKRingMap_units,
    MilnorKShift.shift_ofMilnorK_mul, map_mul, milnorKRingMap_comp_apply,
    ← quotientRingEquivResidueField_symm_residue_constants ψ]

/-- **`∂_ψ (y c(z)) = ∂_ψ(y) σ(ι_ψ(z))`.** -/
theorem monicIrreducibleResidue_mul_constants {d : ℕ} (ψ : MonicIrreducibleOfDegree k d)
    (y : MilnorKRing (RatFunc k)) (z : MilnorKRing k) :
    monicIrreducibleResidue ψ (y * milnorKRingMap (constantsHom k) z) =
      monicIrreducibleResidue ψ y *
        milnorKInvolution _
          (milnorKRingMap (algebraMap k (Polynomial k ⧸ Ideal.span {poly ψ})) z) := by
  rw [monicIrreducibleResidue_apply, monicIrreducibleResidue_apply, map_mul,
    constantsHom_eq_comp (Ideal.span {poly ψ}), dvrMilnorShiftMap_milnorKRingMap_units,
    MilnorKShift.shift_mul_ofMilnorK, map_mul, milnorKInvolution_milnorKRingMap,
    milnorKInvolution_milnorKRingMap, milnorKRingMap_comp_apply,
    ← quotientRingEquivResidueField_symm_residue_constants ψ]

/-! ### Linearity of the residue at infinity -/

/-- The involution `X ↦ 1/X` fixes the constants. -/
theorem projectiveLineChartInversion_comp_constantsHom :
    (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom.comp (constantsHom k) =
      constantsHom k :=
  RingHom.ext fun c ↦ projectiveLineChartInversion_constantsHom c

/-- The residue at the origin of a constant, read back in `k`, is that constant. -/
theorem residueFieldAtOriginEquiv_symm_comp :
    ((residueFieldAtOriginEquiv k).symm : ResidueField (localRingAtOrigin k) →+* k).comp
      ((residue (localRingAtOrigin k)).comp
        (constantsToLocalization (Ideal.span {(X : Polynomial k)}))) = RingHom.id k :=
  RingHom.ext fun c ↦ (residueFieldAtOriginEquiv k).symm_apply_apply c

/-- The residue `∂_∞` at infinity is the residue at the origin, read back in `k`, of the pullback
along the involution `X ↦ 1/X`. -/
theorem infinityResidueRing_apply (y : MilnorKRing (RatFunc k)) :
    infinityResidueRing k y =
      milnorKRingMap ((residueFieldAtOriginEquiv k).symm :
          ResidueField (localRingAtOrigin k) →+* k)
        (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
          (irreducible_algebraMap_X (k := k))
          (milnorKRingMap (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom y))) :=
  rfl

/-- **`∂_∞ (c(z) y) = z ∂_∞(y)`.** -/
theorem infinityResidueRing_constants_mul (z : MilnorKRing k) (y : MilnorKRing (RatFunc k)) :
    infinityResidueRing k (milnorKRingMap (constantsHom k) z * y) =
      z * infinityResidueRing k y := by
  rw [infinityResidueRing_apply, infinityResidueRing_apply, map_mul, milnorKRingMap_comp_apply,
    projectiveLineChartInversion_comp_constantsHom, map_mul,
    constantsHom_eq_comp (Ideal.span {(X : Polynomial k)}),
    dvrMilnorShiftMap_milnorKRingMap_units, MilnorKShift.shift_ofMilnorK_mul, map_mul,
    milnorKRingMap_comp_apply, residueFieldAtOriginEquiv_symm_comp, milnorKRingMap_id_apply]

/-- **`∂_∞ (y c(z)) = ∂_∞(y) σ(z)`.** -/
theorem infinityResidueRing_mul_constants (y : MilnorKRing (RatFunc k)) (z : MilnorKRing k) :
    infinityResidueRing k (y * milnorKRingMap (constantsHom k) z) =
      infinityResidueRing k y * milnorKInvolution k z := by
  rw [infinityResidueRing_apply, infinityResidueRing_apply, map_mul, milnorKRingMap_comp_apply,
    projectiveLineChartInversion_comp_constantsHom, map_mul,
    constantsHom_eq_comp (Ideal.span {(X : Polynomial k)}),
    dvrMilnorShiftMap_milnorKRingMap_units, MilnorKShift.shift_mul_ofMilnorK, map_mul,
    milnorKInvolution_milnorKRingMap, milnorKRingMap_comp_apply,
    residueFieldAtOriginEquiv_symm_comp, milnorKRingMap_id_apply]

end Stacks.Chow

end
