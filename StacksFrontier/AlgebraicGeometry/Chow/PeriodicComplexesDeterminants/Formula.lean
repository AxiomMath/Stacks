module

public import Mathlib.RingTheory.Flat.Domain
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.DeterminantLine

/-!
# An elementary formula for the periodic determinant

For an exact two-periodic complex of finite length over a local ring, the periodic determinant
compares the determinant symbols obtained by adjoining lifts of admissible sequences in the two
images. The comparison includes the sign given by the product of the lengths of the images.

## Main results

* `AlgebraicGeometry.periodicDeterminant_symbol_eq` gives the signed comparison of the two
  concatenated determinant symbols.
* `AlgebraicGeometry.eq_periodicDeterminant_of_symbol_eq` says this comparison determines the
  residue-field unit uniquely.

## Implementation notes

The two differentials are endomorphisms with exactness expressed by `Function.Exact`. The
lengths and admissibility of the concatenated sequences are included in the conclusion, since
these are needed to form their determinant symbols and follow from the stated exactness and
finite-length hypotheses. A symbol generating its determinant line is expressed by the span of
that symbol being the top submodule.

## References

* [Stacks Project, Tag 02PK](https://stacks.math.columbia.edu/tag/02PK)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- The determinant map of an exact periodic complex sends the tensor of the symbols of `y` and
of lifts of `x` to the symbol of their concatenation. -/
private theorem periodicGamma_tmul_symbol_append
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M)
    (x : AdmissibleSequence R (LinearMap.range φ))
    (y : AdmissibleSequence R (LinearMap.range ψ))
    (hx0 : symbol x ≠ 0) (hy0 : symbol y ≠ 0)
    (xLift : Fin (moduleLength R (LinearMap.range φ)) → M)
    (hxLift : ∀ i, φ (xLift i) = (x.1 i : M)) :
    ∃ hlen : moduleLength R M =
        moduleLength R (LinearMap.range ψ) + moduleLength R (LinearMap.range φ),
      ∃ hadm : IsAdmissibleSequence (R := R)
          (fun i ↦ Fin.append (fun j ↦ (y.1 j : M)) xLift (Fin.cast hlen i)),
        periodicGamma φ ψ hψφ hM
            (symbol y ⊗ₜ[IsLocalRing.ResidueField R] symbol x) =
          symbol ⟨fun i ↦ Fin.append (fun j ↦ (y.1 j : M)) xLift (Fin.cast hlen i), hadm⟩ :=
  determinantExactSequenceMap_spec
    (LinearMap.range ψ).subtype φ.rangeRestrict
    (Submodule.injective_subtype (LinearMap.range ψ))
    (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict φ))
    (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      exact hψφ.linearMap_ker_eq)
    (hM.of_injective (LinearMap.range ψ).subtype_injective) hM
    (hM.of_surjective (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict φ)))
    y x hy0 hx0 xLift fun i ↦ Subtype.ext (hxLift i)

/-- **Stacks Project, Tag 02PK.** For an exact two-periodic complex, the determinant symbol
formed from an admissible sequence in the image of the first differential and lifts from the
second image differs from the opposite symbol by the signed periodic determinant. -/
@[stacks 02PK "formula"]
theorem periodicDeterminant_symbol_eq
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M)
    (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hM : IsFiniteLength R M)
    (x : AdmissibleSequence R (LinearMap.range φ))
    (y : AdmissibleSequence R (LinearMap.range ψ))
    (hx : (IsLocalRing.ResidueField R) ∙ symbol x = ⊤)
    (hy : (IsLocalRing.ResidueField R) ∙ symbol y = ⊤)
    (xLift : Fin (moduleLength R (LinearMap.range φ)) → M)
    (yLift : Fin (moduleLength R (LinearMap.range ψ)) → M)
    (hxLift : ∀ i, φ (xLift i) = (x.1 i : M))
    (hyLift : ∀ j, ψ (yLift j) = (y.1 j : M)) :
    ∃ hleftLength : moduleLength R M =
        moduleLength R (LinearMap.range φ) + moduleLength R (LinearMap.range ψ),
      ∃ hrightLength : moduleLength R M =
          moduleLength R (LinearMap.range ψ) + moduleLength R (LinearMap.range φ),
        ∃ hleft : IsAdmissibleSequence (R := R)
            (fun i ↦ Fin.append (fun j ↦ (x.1 j : M)) yLift (Fin.cast hleftLength i)),
          ∃ hright : IsAdmissibleSequence (R := R)
              (fun i ↦ Fin.append (fun j ↦ (y.1 j : M)) xLift
                (Fin.cast hrightLength i)),
            symbol ⟨fun i ↦ Fin.append (fun j ↦ (x.1 j : M)) yLift
                (Fin.cast hleftLength i), hleft⟩ =
              (((-1 : IsLocalRing.ResidueField R) ^
                (moduleLength R (LinearMap.range φ) *
                  moduleLength R (LinearMap.range ψ))) *
                (periodicDeterminant φ ψ hφψ hψφ hM : IsLocalRing.ResidueField R)) •
                symbol ⟨fun i ↦ Fin.append (fun j ↦ (y.1 j : M)) xLift
                (Fin.cast hrightLength i), hright⟩ := by
  have hφrange : IsFiniteLength R (LinearMap.range φ) :=
    hM.of_injective (LinearMap.range φ).subtype_injective
  have hψrange : IsFiniteLength R (LinearMap.range ψ) :=
    hM.of_injective (LinearMap.range ψ).subtype_injective
  have hx0 := symbol_ne_zero_of_span_eq_top hφrange x hx
  have hy0 := symbol_ne_zero_of_span_eq_top hψrange y hy
  obtain ⟨hleftLength, hleft, hleftEq⟩ :=
    periodicGamma_tmul_symbol_append ψ φ hφψ hM y x hy0 hx0 yLift hyLift
  obtain ⟨hrightLength, hright, hrightEq⟩ :=
    periodicGamma_tmul_symbol_append φ ψ hψφ hM x y hx0 hy0 xLift hxLift
  have hdet := periodicDeterminant_spec φ ψ hφψ hψφ hM
  change periodicGamma ψ φ hφψ hM ∘ₗ
      (TensorProduct.comm (IsLocalRing.ResidueField R)
        (determinant R (LinearMap.range ψ))
        (determinant R (LinearMap.range φ))).toLinearMap =
    (((-1 : IsLocalRing.ResidueField R) ^
      (moduleLength R (LinearMap.range φ) * moduleLength R (LinearMap.range ψ))) *
      (periodicDeterminant φ ψ hφψ hψφ hM : IsLocalRing.ResidueField R)) •
      periodicGamma φ ψ hψφ hM at hdet
  have hval := congrArg
    (fun f : _ →ₗ[IsLocalRing.ResidueField R] _ =>
      f (symbol y ⊗ₜ[IsLocalRing.ResidueField R] symbol x)) hdet
  simp only [LinearMap.comp_apply] at hval
  have hcomm :
      (TensorProduct.comm (IsLocalRing.ResidueField R)
        (determinant R (LinearMap.range ψ))
        (determinant R (LinearMap.range φ))).toLinearMap
          (symbol y ⊗ₜ[IsLocalRing.ResidueField R] symbol x) =
        symbol x ⊗ₜ[IsLocalRing.ResidueField R] symbol y := by
    change TensorProduct.comm (IsLocalRing.ResidueField R)
      (determinant R (LinearMap.range ψ)) (determinant R (LinearMap.range φ))
      (symbol y ⊗ₜ[IsLocalRing.ResidueField R] symbol x) = _
    exact TensorProduct.comm_tmul (IsLocalRing.ResidueField R)
      (determinant R (LinearMap.range ψ)) (determinant R (LinearMap.range φ))
      (symbol y) (symbol x)
  rw [hcomm, hleftEq] at hval
  simp only [LinearMap.smul_apply, hrightEq] at hval
  exact ⟨hleftLength, hrightLength, hleft, hright, hval⟩

/-- The right concatenation of two nonzero symbols has nonzero symbol. -/
private theorem right_concat_symbol_ne_zero
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M)
    (hψφ : Function.Exact ψ φ)
    (hM : IsFiniteLength R M)
    (x : AdmissibleSequence R (LinearMap.range φ))
    (y : AdmissibleSequence R (LinearMap.range ψ))
    (hx0 : symbol x ≠ 0) (hy0 : symbol y ≠ 0)
    (xLift : Fin (moduleLength R (LinearMap.range φ)) → M)
    (hxLift : ∀ i, φ (xLift i) = (x.1 i : M))
    (hrightLength : moduleLength R M =
      moduleLength R (LinearMap.range ψ) + moduleLength R (LinearMap.range φ))
    (hright : IsAdmissibleSequence
      (fun i ↦ Fin.append (fun j ↦ (y.1 j : M)) xLift (Fin.cast hrightLength i))) :
    symbol ⟨fun i ↦ Fin.append (fun j ↦ (y.1 j : M)) xLift
      (Fin.cast hrightLength i), hright⟩ ≠ 0 := by
  obtain ⟨hlen, hadm, heq⟩ :=
    periodicGamma_tmul_symbol_append φ ψ hψφ hM x y hx0 hy0 xLift hxLift
  cases Subsingleton.elim hlen hrightLength
  cases Subsingleton.elim hadm hright
  have hbij : Function.Bijective (periodicGamma φ ψ hψφ hM) := by
    unfold periodicGamma
    exact determinantExactSequenceMap_bijective _ _ _ _ _ _ _ _
  have htensor := LinearIndependent.tmul_of_isDomain
    (LinearIndependent.of_subsingleton () hy0 :
      LinearIndependent (IsLocalRing.ResidueField R) fun _ : Unit ↦ symbol y)
    (LinearIndependent.of_subsingleton () hx0 :
      LinearIndependent (IsLocalRing.ResidueField R) fun _ : Unit ↦ symbol x)
  intro hz
  exact htensor.ne_zero ((), ()) (hbij.1 (by rw [heq, hz, map_zero]))

/-- **Stacks Project, Tag 02PK.** The signed comparison of symbols of generating admissible
sequences uniquely determines the determinant of an exact two-periodic complex. -/
@[stacks 02PK "uniqueness"]
theorem eq_periodicDeterminant_of_symbol_eq
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M)
    (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hM : IsFiniteLength R M)
    (x : AdmissibleSequence R (LinearMap.range φ))
    (y : AdmissibleSequence R (LinearMap.range ψ))
    (hx : (IsLocalRing.ResidueField R) ∙ symbol x = ⊤)
    (hy : (IsLocalRing.ResidueField R) ∙ symbol y = ⊤)
    (xLift : Fin (moduleLength R (LinearMap.range φ)) → M)
    (yLift : Fin (moduleLength R (LinearMap.range ψ)) → M)
    (hxLift : ∀ i, φ (xLift i) = (x.1 i : M))
    (hyLift : ∀ j, ψ (yLift j) = (y.1 j : M))
    (hleftLength : moduleLength R M =
      moduleLength R (LinearMap.range φ) + moduleLength R (LinearMap.range ψ))
    (hrightLength : moduleLength R M =
      moduleLength R (LinearMap.range ψ) + moduleLength R (LinearMap.range φ))
    (hleft : IsAdmissibleSequence (R := R)
      (fun i ↦ Fin.append (fun j ↦ (x.1 j : M)) yLift (Fin.cast hleftLength i)))
    (hright : IsAdmissibleSequence (R := R)
      (fun i ↦ Fin.append (fun j ↦ (y.1 j : M)) xLift (Fin.cast hrightLength i)))
    (d : (IsLocalRing.ResidueField R)ˣ)
    (hd : symbol ⟨fun i ↦ Fin.append (fun j ↦ (x.1 j : M)) yLift
        (Fin.cast hleftLength i), hleft⟩ =
      (((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R (LinearMap.range φ) *
          moduleLength R (LinearMap.range ψ))) *
        (d : IsLocalRing.ResidueField R)) •
        symbol ⟨fun i ↦ Fin.append (fun j ↦ (y.1 j : M)) xLift
          (Fin.cast hrightLength i), hright⟩) :
    d = periodicDeterminant φ ψ hφψ hψφ hM := by
  have hx0 := symbol_ne_zero_of_span_eq_top
    (hM.of_injective (LinearMap.range φ).subtype_injective) x hx
  have hy0 := symbol_ne_zero_of_span_eq_top
    (hM.of_injective (LinearMap.range ψ).subtype_injective) y hy
  have hrightNe := right_concat_symbol_ne_zero φ ψ hψφ hM x y hx0 hy0
    xLift hxLift hrightLength hright
  obtain ⟨hl, hr, ha, hb, heq⟩ :=
    periodicDeterminant_symbol_eq φ ψ hφψ hψφ hM x y hx hy xLift yLift hxLift hyLift
  have hcomp := hd.symm.trans heq
  have hl' : hl = hleftLength := Subsingleton.elim _ _
  have hr' : hr = hrightLength := Subsingleton.elim _ _
  cases hl'
  cases hr'
  have hcoeff := (smul_left_inj hrightNe).mp
    (show _ • symbol ⟨_, hright⟩ = _ • symbol ⟨_, hright⟩ from by
      simpa only [Subsingleton.elim ha hleft, Subsingleton.elim hb hright] using hcomp)
  have hs : (-1 : IsLocalRing.ResidueField R) ^
      (moduleLength R (LinearMap.range φ) * moduleLength R (LinearMap.range ψ)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : IsLocalRing.ResidueField R) ≠ 0))
  have hunitval : (d : IsLocalRing.ResidueField R) =
      (periodicDeterminant φ ψ hφψ hψφ hM : IsLocalRing.ResidueField R) := by
    apply mul_left_cancel₀ hs
    simpa [mul_assoc] using hcoeff
  exact Units.ext hunitval

end AlgebraicGeometry
