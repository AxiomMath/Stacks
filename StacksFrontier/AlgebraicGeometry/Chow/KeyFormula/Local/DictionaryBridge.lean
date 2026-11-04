module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SymbolComparison
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocityNormal

/-!
# The codimension-one dictionary and the intermediate-point correspondence are the same

Two bijections of this development describe one correspondence. At a point `x''` of a scheme `W`
the dictionary `Stacks.Chow.heightOnePrimeEquivCoheightOneGenerization` matches the height-one
primes of `A = 𝒪_{W, x''}` with the points of `W` of coheight one specializing to `x''`, while
for `W` integral with `dim A = 2` the correspondence
`Stacks.Chow.heightOnePrimeEquivIntermediatePoint` matches the height-one primes of `A`, spelled
as prime ideals, with the points `x'` for which `genericPoint W ⇝ x' ⇝ x''` with both steps
immediate specializations. This file identifies the two: the index types agree with no hypothesis
on `A`, the two descriptions of the target agree whenever `W` is integral and `dim A = 2`, and
the composite of those two identifications with the dictionary is the correspondence.

## Main definitions

* `Stacks.Chow.coheightOneGenerizationEquivIntermediatePoint` — the two descriptions of the
  codimension-one points of `W` through `x''`.

## Main results

* `Stacks.Chow.coheight_eq_two_of_ringKrullDim_stalk_eq_two` — a two-dimensional local ring sits
  at a point of coheight two.
* `Stacks.Chow.specializes_and_coheight_eq_one_iff_isImmediateSpecialization` — on an integral
  `W` with `dim 𝒪_{W, x''} = 2`, a point is a coheight-one generization of `x''` exactly when it
  is an intermediate point of `genericPoint W ⇝ x''`.
* `Stacks.Chow.heightOnePrimeEquivIntermediatePoint_eq` — the two bijections agree.

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The two spellings of the target -/

variable {X : Scheme.{u}}

/-- **A two-dimensional local ring sits at a point of coheight two.** This is Stacks 02IZ, the
converse of `Stacks.Chow.ringKrullDim_stalk_eq_two_of_coheight_eq_two`. -/
theorem coheight_eq_two_of_ringKrullDim_stalk_eq_two {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2) : coheight x = 2 := by
  have h : ((coheight x : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
    rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x, hdim]
    norm_num
  exact WithBot.coe_inj.mp h

variable {W : Scheme.{u}}

/-- **The two descriptions of the codimension-one points through `x''` agree.** On an integral
scheme `W` whose local ring at `x''` is two-dimensional, a point `z` is a coheight-one
generization of `x''` exactly when `genericPoint W ⇝ z ⇝ x''` with both steps immediate. -/
theorem specializes_and_coheight_eq_one_iff_isImmediateSpecialization [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2) (z : W) :
    z ⤳ x'' ∧ coheight z = 1 ↔
      IsImmediateSpecialization (genericPoint W) z ∧ IsImmediateSpecialization z x'' := by
  refine ⟨fun ⟨hzx, hz⟩ => ⟨?_, ?_⟩, fun ⟨hgen, himm⟩ => ⟨himm.1, ?_⟩⟩
  · exact (coheight_eq_one_iff_isImmediateSpecialization_genericPoint z).mp hz
  · exact isImmediateSpecialization_of_coheight_eq_one_of_coheight_eq_two
      (coheight_eq_two_of_ringKrullDim_stalk_eq_two hdim) hz
      (Scheme.le_iff_specializes.mpr hzx)
  · exact (coheight_eq_one_iff_isImmediateSpecialization_genericPoint z).mpr hgen

/-- The coheight-one generizations of `x''` and the intermediate points of
`genericPoint W ⇝ x''`, identified by
`Stacks.Chow.specializes_and_coheight_eq_one_iff_isImmediateSpecialization`. -/
def coheightOneGenerizationEquivIntermediatePoint [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2) :
    {z : W // z ⤳ x'' ∧ coheight z = 1} ≃
      {x' : W // IsImmediateSpecialization (genericPoint W) x' ∧
        IsImmediateSpecialization x' x''} :=
  Equiv.subtypeEquivRight (specializes_and_coheight_eq_one_iff_isImmediateSpecialization hdim)

/-- The equivalence `coheightOneGenerizationEquivIntermediatePoint` sends a point `z` to `z`
itself. -/
@[simp] theorem coheightOneGenerizationEquivIntermediatePoint_apply [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2) (z : {z : W // z ⤳ x'' ∧ coheight z = 1}) :
    (coheightOneGenerizationEquivIntermediatePoint hdim z : W) = (z : W) :=
  rfl

/-! ### The bridge -/

/-- The point the correspondence attaches to a height-one prime of `𝒪_{W, x''}` is the point the
dictionary attaches to it. -/
@[simp] theorem heightOnePrimeEquivIntermediatePoint_heightOnePrimeIdeal [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2)
    (𝔮 : HeightOnePrime (W.presheaf.stalk x'')) :
    (heightOnePrimeEquivIntermediatePoint hdim (heightOnePrimeIdeal 𝔮) : W) =
      pointOfHeightOnePrime 𝔮 :=
  rfl

/-- The point the correspondence attaches to a height-one prime ideal of `𝒪_{W, x''}` is the
point the dictionary attaches to the corresponding point of the prime spectrum. -/
theorem heightOnePrimeEquivIntermediatePoint_apply_eq_pointOfHeightOnePrime [IsIntegral W]
    {x'' : W} (hdim : ringKrullDim (W.presheaf.stalk x'') = 2)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    (heightOnePrimeEquivIntermediatePoint hdim q : W) =
      pointOfHeightOnePrime (heightOnePrimeEquivIdeal.symm q) :=
  rfl

/-- **The dictionary and the correspondence are one bijection.** Transporting the dictionary
`Stacks.Chow.heightOnePrimeEquivCoheightOneGenerization` along the identification of the index
types and the identification of the targets gives
`Stacks.Chow.heightOnePrimeEquivIntermediatePoint`. -/
theorem heightOnePrimeEquivIntermediatePoint_eq [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2) :
    heightOnePrimeEquivIntermediatePoint hdim =
      (heightOnePrimeEquivIdeal (A := W.presheaf.stalk x'')).symm.trans
        ((heightOnePrimeEquivCoheightOneGenerization x'').trans
          (coheightOneGenerizationEquivIntermediatePoint hdim)) :=
  Equiv.ext fun _ => Subtype.ext rfl

end Stacks.Chow

end
