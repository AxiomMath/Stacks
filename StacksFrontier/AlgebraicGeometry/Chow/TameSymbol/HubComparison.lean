module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.ModuleSymbolFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.UnitCorrection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing

/-!
# Comparing two tame symbols inside a common unramified flat extension

Let `B` and `C` be one-dimensional Noetherian local rings and `R` a one-dimensional Noetherian
local ring receiving flat local homomorphisms `B → R` and `C → R` with `𝔪_B R = 𝔪_R = 𝔪_C R`.
If `f, g ∈ Q(B)^*` and `a, b ∈ Q(C)^*` differ in `Q(R)` by units `λ, μ ∈ R^*`,

`f = a λ`,  `g = b μ`,

then their orders agree, `ord_B(f) = ord_C(a)`, and their tame symbols compare in `κ(R)` as

`∂_B(f, g) = ∂_C(a, b) · μ̄^{-ord_C(a)} · λ̄^{ord_C(b)}`.

This is the local identity behind the key formula, Stacks 0EQV: `B` is the henselian local ring
of an algebraic space at the generic point of a prime divisor, `C` the local ring of an étale
chart at a point above it, and `R` the étale local ring at a geometric point above both; `f`,
`g` are the ratios of the sections against the chosen generators, `a`, `b` their ratios against
generators over the chart, and `λ`, `μ` the ratios of the two generators.

## Main results

* `Stacks.Chow.ordTotalFracInt_map_of_flat`: the order of vanishing is unchanged by a flat local
  homomorphism with `𝔪 A' = 𝔪'`.
* `Stacks.Chow.tameSymbol_hub_comparison`: the comparison above.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 0EAN](https://stacks.math.columbia.edu/tag/0EAN)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v w

namespace Stacks.Chow

section OrderFlat

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {A' : Type v} [CommRing A'] [IsNoetherianRing A'] [IsLocalRing A'] [Ring.KrullDimLE 1 A']
  [Algebra A A'] [Module.Flat A A'] [IsLocalHom (algebraMap A A')]
  (Q : Type*) [CommRing Q] [Algebra A Q] [IsFractionRing A Q]
  (Q' : Type*) [CommRing Q'] [Algebra A' Q'] [IsFractionRing A' Q']

/-- **The order of vanishing is unchanged by a flat local homomorphism with `𝔪 A' = 𝔪'`**
(Stacks 02M1 with multiplier one), on units of the total rings of fractions. -/
theorem ordTotalFracInt_map_of_flat
    (hmax : Ideal.map (algebraMap A A') (maximalIdeal A) = maximalIdeal A') (f : Qˣ) :
    Ring.ordTotalFracInt A'
        (IsLocalization.map Q' (algebraMap A A')
          (nonZeroDivisors_le_comap_of_flat (A := A) (A' := A')) (f : Q))
        (f.isUnit.map _) =
      Ring.ordTotalFracInt A (f : Q) f.isUnit := by
  obtain ⟨a, b, hab'⟩ := exists_regularFractionUnit_div (A := A) (Q := Q) f
  have hab : IsLocalization.mk' Q (a : A) b = (f : Q) := by
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    have hmul : f * regularFractionUnit (Q := Q) b = regularFractionUnit a := by
      rw [hab', inv_mul_cancel_right]
    exact (congrArg Units.val hmul).symm
  have hm : Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A)) =
      ((1 : ℕ) : ℕ∞) := by
    rw [hmax, Nat.cast_one]
    exact Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal A').out)
  have hflat : (algebraMap A A').Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hmap : IsLocalization.map Q' (algebraMap A A')
      (nonZeroDivisors_le_comap_of_flat (A := A) (A' := A')) (f : Q) =
      IsLocalization.mk' Q' (algebraMap A A' a)
        (⟨algebraMap A A' b, Ring.map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ :
          nonZeroDivisors A') := by
    rw [← hab, IsLocalization.map_mk']
  rw [Ring.ordTotalFracInt_congr A' _ (hmap ▸ f.isUnit.map _) hmap,
    Ring.ordTotalFracInt_congr A f.isUnit (hab ▸ f.isUnit) hab.symm,
    Ring.ordTotalFracInt_map_mk'_of_flatHom (KA := Q) (KB := Q') (φ := algebraMap A A')
      inferInstance hflat hm a b,
    Nat.cast_one, one_mul]

end OrderFlat

section Hub

variable {B : Type u} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
  {C : Type v} [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
  {R : Type w} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [Algebra B R] [Module.Flat B R] [IsLocalHom (algebraMap B R)]
  [Algebra C R] [Module.Flat C R] [IsLocalHom (algebraMap C R)]
  (hmB : Ideal.map (algebraMap B R) (maximalIdeal B) = maximalIdeal R)
  (hmC : Ideal.map (algebraMap C R) (maximalIdeal C) = maximalIdeal R)
  (hB : ringKrullDim B = 1) (hC : ringKrullDim C = 1) (hR : ringKrullDim R = 1)
  (QB : Type*) [CommRing QB] [Algebra B QB] [IsFractionRing B QB]
  (QC : Type*) [CommRing QC] [Algebra C QC] [IsFractionRing C QC]
  (QR : Type*) [CommRing QR] [Algebra R QR] [IsFractionRing R QR]

include hmB hmC hR in
/-- **The tame symbols of `B` and of `C`, compared in a common unramified flat extension `R`.**
If `f = a λ` and `g = b μ` in `Q(R)` with `λ, μ ∈ R^*`, then `ord_B(f) = ord_C(a)` and
`∂_B(f, g) = ∂_C(a, b) · μ̄^{-ord_C(a)} · λ̄^{ord_C(b)}` in `κ(R)`. -/
theorem tameSymbol_hub_comparison (f g : QBˣ) (a b : QCˣ) (l m : Rˣ)
    (hf : IsLocalization.map QR (algebraMap B R)
        (nonZeroDivisors_le_comap_of_flat (A := B) (A' := R)) (f : QB) =
      IsLocalization.map QR (algebraMap C R)
        (nonZeroDivisors_le_comap_of_flat (A := C) (A' := R)) (a : QC) * algebraMap R QR l)
    (hg : IsLocalization.map QR (algebraMap B R)
        (nonZeroDivisors_le_comap_of_flat (A := B) (A' := R)) (g : QB) =
      IsLocalization.map QR (algebraMap C R)
        (nonZeroDivisors_le_comap_of_flat (A := C) (A' := R)) (b : QC) * algebraMap R QR m) :
    haveI := krullDimLE_one_of_ringKrullDim_eq_one hB
    haveI := krullDimLE_one_of_ringKrullDim_eq_one hC
    Ring.ordTotalFracInt B (f : QB) f.isUnit = Ring.ordTotalFracInt C (a : QC) a.isUnit ∧
      Units.map (ResidueField.map (algebraMap B R)).toMonoidHom
          (tameSymbolOfKrullDimOne hB QB f g) =
        Units.map (ResidueField.map (algebraMap C R)).toMonoidHom
            (tameSymbolOfKrullDimOne hC QC a b) *
          (Units.map (residue R).toMonoidHom m ^ Ring.ordTotalFracInt C (a : QC) a.isUnit)⁻¹ *
          Units.map (residue R).toMonoidHom l ^ Ring.ordTotalFracInt C (b : QC) b.isUnit := by
  have := krullDimLE_one_of_ringKrullDim_eq_one hB
  have := krullDimLE_one_of_ringKrullDim_eq_one hC
  have := krullDimLE_one_of_ringKrullDim_eq_one hR
  set ιB : QB →+* QR := IsLocalization.map QR (algebraMap B R)
    (nonZeroDivisors_le_comap_of_flat (A := B) (A' := R))
  set ιC : QC →+* QR := IsLocalization.map QR (algebraMap C R)
    (nonZeroDivisors_le_comap_of_flat (A := C) (A' := R))
  have hfU : Units.map ιB.toMonoidHom f =
      Units.map ιC.toMonoidHom a * Units.map (algebraMap R QR).toMonoidHom l :=
    Units.ext hf
  have hgU : Units.map ιB.toMonoidHom g =
      Units.map ιC.toMonoidHom b * Units.map (algebraMap R QR).toMonoidHom m :=
    Units.ext hg
  have hlord : ∀ (x : Rˣ) (h : IsUnit (algebraMap R QR x)),
      Ring.ordTotalFracInt R (algebraMap R QR x) h = 0 := by
    intro x h
    have hx : (x : R) ∈ nonZeroDivisors R := x.isUnit.mem_nonZeroDivisors
    rw [Ring.ordTotalFracInt_algebraMap R (x : R) hx]
    have : Ring.ord R (x : R) = 0 := by
      rw [Ring.ord, Ideal.span_singleton_eq_top.mpr x.isUnit]
      exact Module.length_eq_zero
    simp
  have hordB := ordTotalFracInt_map_of_flat QB QR hmB f
  have e : ∀ x : QCˣ, Ring.ordTotalFracInt R ((Units.map ιC.toMonoidHom x : QRˣ) : QR)
      (Units.isUnit _) = Ring.ordTotalFracInt C (x : QC) x.isUnit := fun x =>
    (Ring.ordTotalFracInt_congr R _ _ rfl).trans (ordTotalFracInt_map_of_flat QC QR hmC x)
  refine ⟨?_, ?_⟩
  · rw [← hordB, ← e a]
    rw [Ring.ordTotalFracInt_congr R (f.isUnit.map ιB)
        ((a.isUnit.map ιC).mul (l.isUnit.map (algebraMap R QR))) hf,
      Ring.ordTotalFracInt_mul R _ _ (a.isUnit.map ιC) (l.isUnit.map (algebraMap R QR)),
      hlord, add_zero]
    rfl
  · rw [map_tameSymbolOfKrullDimOne_of_flat QB QR hmB hB hR, hfU, hgU,
      tameSymbolOfKrullDimOne,
      (regularTameSymbolOfKrullDimOne hR).extend_mul_units QR, ← tameSymbolOfKrullDimOne,
      ← map_tameSymbolOfKrullDimOne_of_flat QC QR hmC hC hR]
    rw [e a, e b]

end Hub

end Stacks.Chow

end
