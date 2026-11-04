module

public import StacksFrontier.AlgebraicGeometry.Blowup.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Affine
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGrading

/-!
# The projectivized normal cone inside the blowup of an affine scheme

Let `I` be an ideal of a commutative ring `R`. The blowup of `Spec R` in `I` is
`Proj (⨁ₙ Iⁿ)`, the homogeneous spectrum of the Rees algebra
(`Stacks.Blowup.blowUpSpec`), and the associated graded ring
`Gr_I(R) = ⨁ₙ Iⁿ/Iⁿ⁺¹` is the conormal algebra of `I` in `R`, so that `Proj (Gr_I(R))` is the
projectivized normal cone of `V(I)` in `Spec R`. Reducing a coefficient modulo the next power of
`I` is a surjection of graded rings

  `⨁ₙ Iⁿ ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹`,

and this file builds it and draws the geometric consequence: the projectivized normal cone is a
closed subscheme of the blowup, lying over the closed subscheme `V(I) = Spec (R/I)` of `Spec R`.

## Main definitions

* `Stacks.Blowup.reesToAssociatedGraded` — the reduction `⨁ₙ Iⁿ ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹`, as a ring
  homomorphism out of `reesAlgebra I`.
* `Stacks.Blowup.reesGradedToAssociatedGraded` — the same homomorphism, graded for
  `Stacks.Blowup.reesGrading` and `AssociatedGraded.grading`.
* `Stacks.Blowup.projectivizedNormalConeToBlowUpSpec` — the induced morphism
  `Proj (Gr_I(R)) ⟶ Bl_I (Spec R)`.

## Main results

* `Stacks.Blowup.reesToAssociatedGraded_apply_of_mem` — the reduction on a homogeneous element:
  the degree-`n` part of the Rees algebra is `Iⁿ`, and its image is the class of its coefficient
  in `Iⁿ/Iⁿ⁺¹`.
* `Stacks.Blowup.reesToAssociatedGraded_eq_zero_iff_of_mem` — the kernel in degree `n` is
  `Iⁿ⁺¹`: a homogeneous element of degree `n` dies exactly when its coefficient lies in `Iⁿ⁺¹`.
* `Stacks.Blowup.reesToAssociatedGraded_surjective` — the reduction is surjective, because
  `Iⁿ ⟶ Iⁿ/Iⁿ⁺¹` is.
* `Stacks.Blowup.isClosedImmersion_projectivizedNormalConeToBlowUpSpec` — **the projectivized
  normal cone is a closed subscheme of the blowup**, by [Stacks, Tag 01N0] part (2) for a
  surjection of graded rings.
* `Stacks.Blowup.projectivizedNormalConeToBlowUpSpec_toSpec` — **it lies over `V(I)`**: the
  composite with the structure morphism `Bl_I (Spec R) ⟶ Spec R` is the structure morphism
  `Proj (Gr_I(R)) ⟶ Spec (R/I)` followed by `Spec (R/I) ⟶ Spec R`.

## Implementation notes

The reduction is assembled degreewise. `Stacks.Blowup.reesGradingEquivPow` identifies the
degree-`n` part of the Rees algebra with `Iⁿ` and `Stacks.Conormal.toPiece` is the quotient map
`Iⁿ ⟶ Iⁿ/Iⁿ⁺¹`, so each degree supplies an additive map into the degree-`n` summand of
`Gr_I(R)`; `DirectSum.toSemiring` glues them, after `DirectSum.decomposeRingEquiv` has presented
the Rees algebra as the direct sum of its homogeneous parts. The two hypotheses of
`DirectSum.toSemiring` are `Stacks.Conormal.toPiece_one` and `Stacks.Conormal.toPiece_mul`, which
are the multiplicativity of the quotient presentation of the conormal algebra.

`AssociatedGraded.gradedRing I` is an *external* direct sum, and `AlgebraicGeometry.Proj` needs
an internal grading; `AssociatedGraded.grading` is the internal grading, by the images of the
structure maps of the direct sum, and `AssociatedGraded.gradeZeroEquiv` identifies its
degree-zero part with `R/I`, which is what puts the morphism over `Spec (R/I)`.

### What is not proved here

The source's identification is sharper: clause (6) of [Stacks, Tag 0FBG] says that the
projectivized normal cone **is** the exceptional divisor, that is the closed immersion below cuts
out exactly the ideal `I · 𝒪` of the exceptional divisor rather than merely some closed
subscheme over `V(I)`. Equivalently the square formed by the closed immersion, the two structure
morphisms and `Spec (R/I) ⟶ Spec R` is cartesian. That is not proved here but in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivizedNormalConeExceptional.lean`, as
`Stacks.Blowup.ker_projectivizedNormalConeToBlowUpSpec` and
`Stacks.Blowup.isPullback_projectivizedNormalConeToBlowUpSpec`. What is proved nowhere is the
globalisation of clause (6) over an arbitrary base scheme, which needs the relative `Proj` of the
conormal algebra. No `@[stacks]` attribute is attached: clause (6) of [Stacks, Tag 0FBG] is
stated for an arbitrary scheme `X` and identifies the subscheme, and the statements below do
neither.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CommRingCat DirectSum Polynomial

universe u

namespace Stacks.Blowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The reduction of the Rees algebra to the associated graded ring -/

/-- The degree-`n` part of the reduction: the degree-`n` part of the Rees algebra is `Iⁿ`, whose
class in `Iⁿ/Iⁿ⁺¹` is placed in the degree-`n` summand of `Gr_I(R)`. -/
def reesPieceToAssociatedGraded (n : ℕ) :
    reesGrading I n →+ AssociatedGraded.gradedRing I :=
  (DirectSum.of (fun k => AssociatedGraded.piece (M := R) I k) n).comp
    (((Stacks.Conormal.toPiece I n).comp
      (reesGradingEquivPow I n).symm.toLinearMap).toAddMonoidHom)

/-- The degree-`n` part of the reduction sends `x` to the class in `Iⁿ/Iⁿ⁺¹` of the element of
`Iⁿ` corresponding to it, placed in the degree-`n` summand of `Gr_I(R)`. -/
theorem reesPieceToAssociatedGraded_apply (n : ℕ) (x : reesGrading I n) :
    reesPieceToAssociatedGraded I n x =
      DirectSum.of (fun k => AssociatedGraded.piece (M := R) I k) n
        (Stacks.Conormal.toPiece I n ((reesGradingEquivPow I n).symm x)) := rfl

/-- The degree-zero part of the reduction sends a homogeneous element with `0`-th coefficient `1`
to the unit of `Gr_I(R)`; this is the unit law of `DirectSum.toSemiring`. -/
theorem reesPieceToAssociatedGraded_one (x : reesGrading I 0)
    (hx : ((x : reesAlgebra I) : R[X]).coeff 0 = 1) :
    reesPieceToAssociatedGraded I 0 x = 1 := by
  rw [reesPieceToAssociatedGraded_apply, show (1 : AssociatedGraded.gradedRing I)
      = DirectSum.of (fun k => AssociatedGraded.piece (M := R) I k) 0
        GradedMonoid.GOne.one from rfl]
  exact congrArg _ (Stacks.Conormal.toPiece_one I _
    ((coe_reesGradingEquivPow_symm I x).trans hx))

/-- The reduction is multiplicative on homogeneous elements; this is the multiplication law of
`DirectSum.toSemiring`. A homogeneous element is a monomial, so the `(i + j)`-th coefficient of a
product of homogeneous elements of degrees `i` and `j` is the product of their coefficients, and
`Stacks.Conormal.toPiece_mul` turns that into the graded multiplication of `Gr_I(R)`. -/
theorem reesPieceToAssociatedGraded_mul {i j : ℕ} (ai : reesGrading I i) (aj : reesGrading I j)
    (c : reesGrading I (i + j))
    (hc : ((c : reesAlgebra I) : R[X])
      = ((ai : reesAlgebra I) : R[X]) * ((aj : reesAlgebra I) : R[X])) :
    reesPieceToAssociatedGraded I (i + j) c
      = reesPieceToAssociatedGraded I i ai * reesPieceToAssociatedGraded I j aj := by
  have key : (((c : reesAlgebra I) : R[X])).coeff (i + j)
      = (((ai : reesAlgebra I) : R[X])).coeff i * (((aj : reesAlgebra I) : R[X])).coeff j := by
    conv_lhs => rw [hc, coe_eq_monomial I ai.2, coe_eq_monomial I aj.2]
    rw [monomial_mul_monomial, coeff_monomial, if_pos rfl]
  rw [reesPieceToAssociatedGraded_apply, reesPieceToAssociatedGraded_apply,
    reesPieceToAssociatedGraded_apply, AssociatedGraded.of_mul_of]
  exact congrArg _ (Stacks.Conormal.toPiece_mul I i j _ _ _
    ((coe_reesGradingEquivPow_symm I c).trans (key.trans (by
      rw [coe_reesGradingEquivPow_symm I ai, coe_reesGradingEquivPow_symm I aj]))))

/-- The reduction, as a homomorphism out of the direct sum of the homogeneous parts of the Rees
algebra. -/
def reesSumToAssociatedGraded :
    (⨁ n, reesGrading I n) →+* AssociatedGraded.gradedRing I :=
  DirectSum.toSemiring (reesPieceToAssociatedGraded I)
    (reesPieceToAssociatedGraded_one I _ (by simp))
    (fun {i j} ai aj => reesPieceToAssociatedGraded_mul I ai aj _ rfl)

/-- On the summand of degree `n`, the reduction out of the direct sum is its degree-`n` part
`Stacks.Blowup.reesPieceToAssociatedGraded`. -/
theorem reesSumToAssociatedGraded_of (n : ℕ) (a : reesGrading I n) :
    reesSumToAssociatedGraded I (DirectSum.of (fun k => reesGrading I k) n a)
      = reesPieceToAssociatedGraded I n a :=
  DirectSum.toAddMonoid_of _ n _

/-- **The reduction `⨁ₙ Iⁿ ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹`.** On the degree-`n` part of the Rees algebra, a copy
of `Iⁿ`, it is the quotient map to `Iⁿ/Iⁿ⁺¹`. -/
def reesToAssociatedGraded : reesAlgebra I →+* AssociatedGraded.gradedRing I :=
  (reesSumToAssociatedGraded I).comp
    (DirectSum.decomposeRingEquiv (reesGrading I)).toRingHom

/-- The reduction on a homogeneous element. -/
theorem reesToAssociatedGraded_apply_of_mem {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ reesGrading I n) :
    reesToAssociatedGraded I x = reesPieceToAssociatedGraded I n ⟨x, hx⟩ := by
  show reesSumToAssociatedGraded I (DirectSum.decompose (reesGrading I) x) = _
  rw [DirectSum.decompose_of_mem (reesGrading I) hx, reesSumToAssociatedGraded_of]

/-- **A homogeneous element of the Rees algebra dies in `Gr_I(R)` exactly when its coefficient
lies in the next power of `I`.** The degree-`n` part of the Rees algebra is `Iⁿ`, carried to
`Iⁿ/Iⁿ⁺¹`, so the kernel in degree `n` is `Iⁿ⁺¹`. This is the degreewise description of the
kernel of the reduction, which is the ideal `I · ⨁ₙ Iⁿ`. -/
theorem reesToAssociatedGraded_eq_zero_iff_of_mem {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ reesGrading I n) :
    reesToAssociatedGraded I x = 0 ↔ ((x : R[X])).coeff n ∈ I ^ (n + 1) := by
  have hcoe : (((reesGradingEquivPow I n).symm ⟨x, hx⟩ : (I ^ n : Ideal R)) : R)
      = ((x : R[X])).coeff n := coe_reesGradingEquivPow_symm I ⟨x, hx⟩
  rw [reesToAssociatedGraded_apply_of_mem I hx, reesPieceToAssociatedGraded_apply, ← hcoe,
    ← Stacks.Conormal.toPiece_eq_zero_iff I n ((reesGradingEquivPow I n).symm ⟨x, hx⟩)]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have h0 := congrArg (fun z : AssociatedGraded.gradedRing I => z n) h
  simpa using h0

/-- The reduction carries the degree-`n` part of the Rees algebra into the degree-`n` part of
`Gr_I(R)`. -/
theorem reesToAssociatedGraded_mem_grading {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ reesGrading I n) :
    reesToAssociatedGraded I x ∈ AssociatedGraded.grading I n := by
  rw [reesToAssociatedGraded_apply_of_mem I hx, reesPieceToAssociatedGraded_apply]
  exact AssociatedGraded.of_mem_grading I _

/-- **The reduction `⨁ₙ Iⁿ ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` as a homomorphism of graded rings**, for the grading
`Stacks.Blowup.reesGrading` of the Rees algebra and the internal grading
`AssociatedGraded.grading` of the associated graded ring. -/
def reesGradedToAssociatedGraded : reesGrading I →+*ᵍ AssociatedGraded.grading I where
  __ := reesToAssociatedGraded I
  map_mem hx := reesToAssociatedGraded_mem_grading I hx

/-- The graded reduction is `Stacks.Blowup.reesToAssociatedGraded` as a function. -/
@[simp]
theorem reesGradedToAssociatedGraded_apply (x : reesAlgebra I) :
    reesGradedToAssociatedGraded I x = reesToAssociatedGraded I x := rfl

/-- **The reduction is surjective.** Each `Iⁿ ⟶ Iⁿ/Iⁿ⁺¹` is, and the target is generated by its
homogeneous parts. -/
theorem reesToAssociatedGraded_surjective :
    Function.Surjective (reesToAssociatedGraded I) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n a =>
      obtain ⟨r, hr⟩ := Stacks.Conormal.toPiece_surjective I n a
      refine ⟨((reesGradingEquivPow I n r : reesAlgebra I)), ?_⟩
      rw [reesToAssociatedGraded_apply_of_mem I (reesGradingEquivPow I n r).2,
        reesPieceToAssociatedGraded_apply,
        show (⟨(reesGradingEquivPow I n r : reesAlgebra I), (reesGradingEquivPow I n r).2⟩ :
            reesGrading I n) = reesGradingEquivPow I n r from rfl,
        (reesGradingEquivPow I n).symm_apply_apply, hr]
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩

/-- The irrelevant ideal of `Gr_I(R)` is contained in the image, under the graded reduction, of
the irrelevant ideal of the Rees algebra. -/
theorem irrelevant_le_map_reesGradedToAssociatedGraded :
    HomogeneousIdeal.irrelevant (AssociatedGraded.grading I) ≤
      (HomogeneousIdeal.irrelevant (reesGrading I)).map (reesGradedToAssociatedGraded I) :=
  AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
    (reesToAssociatedGraded_surjective I)

/-! ### The projectivized normal cone as a closed subscheme of the blowup -/

/-- **The projectivized normal cone of `V(I)` in `Spec R` inside the blowup.** The morphism
`Proj (⨁ₙ Iⁿ/Iⁿ⁺¹) ⟶ Proj (⨁ₙ Iⁿ) = Bl_I (Spec R)` induced by the reduction of the Rees algebra
to the associated graded ring. -/
def projectivizedNormalConeToBlowUpSpec :
    AlgebraicGeometry.Proj (AssociatedGraded.grading I) ⟶ blowUpSpec I :=
  AlgebraicGeometry.Proj.map (reesGradedToAssociatedGraded I)
    (irrelevant_le_map_reesGradedToAssociatedGraded I)

/-- **The projectivized normal cone is a closed subscheme of the blowup.** This is
[Stacks, Tag 01N0] part (2) applied to the surjection
`Stacks.Blowup.reesGradedToAssociatedGraded`. -/
instance isClosedImmersion_projectivizedNormalConeToBlowUpSpec :
    IsClosedImmersion (projectivizedNormalConeToBlowUpSpec I) :=
  AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective' _
    (reesToAssociatedGraded_surjective I)

/-- The degree-zero part of the reduction, read through the identifications of the two
degree-zero parts, is the quotient map `R ⟶ R/I`: the degree-zero part of the Rees algebra is a
copy of `R`, that of `Gr_I(R)` is `R/I`, and the reduction sends the class of `a` to the class of
`a` in `R/I`. -/
theorem reesGradedToAssociatedGraded_gradedZeroRingHom_comp :
    ((reesGradedToAssociatedGraded I).gradedZeroRingHom.comp
        (reesGradingZeroEquiv I).toRingHom) = AssociatedGraded.gradeZeroHom I := by
  refine RingHom.ext fun a => Subtype.ext ?_
  have hmem : ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I)
      ∈ reesGrading I 0 := (reesGradingZeroEquiv I a).2
  have hcoeff : ((((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I) : R[X])).coeff 0
      = a := by
    rw [show ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I)
        = algebraMap R (reesGrading I 0) a from rfl, SetLike.GradeZero.coe_algebraMap]
    simp
  show reesToAssociatedGraded I
      ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I) = _
  rw [reesToAssociatedGraded_apply_of_mem I hmem, reesPieceToAssociatedGraded_apply,
    AssociatedGraded.coe_gradeZeroHom]
  refine congrArg _ ?_
  refine (Stacks.Conormal.toPiece_apply I 0 _).trans (congrArg (AssociatedGraded.mk I 0) ?_)
  exact Subtype.ext ((coe_reesGradingEquivPow_symm I _).trans hcoeff)

/-- The identification `R/I ≅ (Gr_I(R))₀` of `AssociatedGraded.gradeZeroEquiv`, precomposed with
the quotient map, is the canonical ring map `R ⟶ (Gr_I(R))₀`. -/
theorem gradeZeroEquiv_comp_mk :
    (AssociatedGraded.gradeZeroEquiv I).toRingHom.comp (Ideal.Quotient.mk I)
      = AssociatedGraded.gradeZeroHom I :=
  RingHom.ext fun _ => rfl

/-- **The projectivized normal cone lies over `V(I)`.** The composite of
`Proj (Gr_I(R)) ⟶ Bl_I (Spec R)` with the structure morphism of the blowup is the structure
morphism `Proj (Gr_I(R)) ⟶ Spec ((Gr_I(R))₀) = Spec (R/I)` followed by the closed immersion
`Spec (R/I) ⟶ Spec R`. -/
theorem projectivizedNormalConeToBlowUpSpec_toSpec :
    projectivizedNormalConeToBlowUpSpec I ≫ toSpec I =
      AlgebraicGeometry.Proj.toSpecZero (AssociatedGraded.grading I) ≫
        Spec.map (ofHom (AssociatedGraded.gradeZeroEquiv I).toRingHom) ≫
          Spec.map (ofHom (Ideal.Quotient.mk I)) := by
  refine (AlgebraicGeometry.Proj.map_toSpecZero_assoc (reesGradedToAssociatedGraded I)
    (irrelevant_le_map_reesGradedToAssociatedGraded I) _).trans ?_
  rw [← Spec.map_comp, ← Spec.map_comp, ← ofHom_comp, ← ofHom_comp,
    reesGradedToAssociatedGraded_gradedZeroRingHom_comp I, gradeZeroEquiv_comp_mk I]

end Stacks.Blowup

end
