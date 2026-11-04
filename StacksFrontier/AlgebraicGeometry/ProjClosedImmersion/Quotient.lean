module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded quotient of a graded ring, and `V_+` of a homogeneous ideal

Let `𝒜 : ι → σ` be an internal grading of a commutative ring `A` by a family of additive
subgroups and let `I : HomogeneousIdeal 𝒜`. The quotient `A ⧸ I` is again graded, by the images
of the graded pieces, and the quotient map is a homomorphism of graded rings. Without this,
`Proj (𝒜 ⧸ I)` cannot even be written: Mathlib grades no quotient of a graded ring.

With it, `AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective` applies, and gives the
closed subscheme `V_+(I) = Proj (𝒜 ⧸ I) ⟶ Proj 𝒜`.

## Main definitions

* `Stacks.HomogeneousIdeal.quotientGrading`: the grading of `A ⧸ I` by the images of `𝒜 i`.
* `Stacks.HomogeneousIdeal.quotientGradingMk`: the quotient map in a single degree.
* `Stacks.HomogeneousIdeal.quotientMk`: the quotient map as a homomorphism of graded rings.

## Main results

* `Stacks.HomogeneousIdeal.instGradedRingQuotientGrading`: `A ⧸ I` is a graded ring.
* `AlgebraicGeometry.Proj.isClosedImmersion_map_quotientMk`: **`V_+(I) ⟶ Proj 𝒜` is a closed
  immersion**, with no side condition.

## Implementation notes

The grading is a family of `AddSubgroup (A ⧸ I.toIdeal)`, for a grading `𝒜 : ι → σ` of `A` by an
arbitrary `AddSubgroupClass`. `AlgebraicGeometry.Proj`, `Ideal.IsHomogeneous`,
`HomogeneousIdeal` and the twisting sheaves are all stated for a general `σ` with
`[SetLike σ A] [AddSubgroupClass σ A]`, and a family of `R`-submodules is a special case of that,
so grading the quotient by `R`-submodules would restrict the input for no gain while leaving the
output in a shape that a statement for general `σ` must transport.

The direct-sum decomposition is built here: it is `DirectSum.map` of the degreewise quotient maps
composed with the decomposition of `A`, descended through `QuotientAddGroup.lift`. Its two inverse
properties follow from `DirectSum.coeAddMonoidHom` commuting with `DirectSum.map` and from the
degreewise surjectivity, so no linear independence or spanning argument is needed; the homogeneity
of `I` enters only in checking that the lifted map kills `I`.

The `mul_mem` field of `SetLike.GradedMonoid` (`SetLike.GradedMul.mul_mem`) is proved through
`mem_quotientGrading_iff` at the ascribed type rather than by destructuring the membership
directly, which keeps the `Monoid (A ⧸ I.toIdeal)` instance visible.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public section

open DirectSum HomogeneousIdeal

namespace Stacks.HomogeneousIdeal

variable {ι σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [DecidableEq ι]
  [AddMonoid ι] {𝒜 : ι → σ} [GradedRing 𝒜] (I : _root_.HomogeneousIdeal 𝒜)

/-- **The grading of the quotient of a graded ring by a homogeneous ideal**: the degree-`i` piece
of `A ⧸ I` is the image of `𝒜 i`. -/
def quotientGrading (i : ι) : AddSubgroup (A ⧸ I.toIdeal) :=
  (AddSubgroup.ofClass (𝒜 i)).map (Ideal.Quotient.mk I.toIdeal).toAddMonoidHom

/-- Membership in the quotient grading: being the class of an element of `𝒜 i`. -/
theorem mem_quotientGrading_iff {i : ι} (x : A ⧸ I.toIdeal) :
    x ∈ quotientGrading I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I.toIdeal a = x :=
  Iff.rfl

/-- The class of an element of `𝒜 i` lies in the degree-`i` piece of the quotient grading. -/
theorem mk_mem_quotientGrading {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I.toIdeal a ∈ quotientGrading I i :=
  ⟨a, ha, rfl⟩

/-- The quotient grading is multiplicative: the product of the images of `𝒜 i` and `𝒜 j` lands in
the image of `𝒜 (i + j)`. -/
instance instGradedMonoidQuotientGrading : SetLike.GradedMonoid (quotientGrading I) where
  one_mem := mk_mem_quotientGrading I SetLike.GradedOne.one_mem
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := (mem_quotientGrading_iff I x).mp hx
    obtain ⟨b, hb, rfl⟩ := (mem_quotientGrading_iff I y).mp hy
    have h := mk_mem_quotientGrading I (SetLike.GradedMul.mul_mem ha hb)
    rwa [map_mul] at h

/-- The quotient map restricted to a single degree, from `𝒜 i` onto the degree-`i` piece of the
quotient grading. -/
def quotientGradingMk (i : ι) : 𝒜 i →+ quotientGrading I i where
  toFun a := ⟨Ideal.Quotient.mk I.toIdeal a, mk_mem_quotientGrading I a.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add (Ideal.Quotient.mk I.toIdeal) (a : A) (b : A))

/-- The quotient map in a single degree is surjective. -/
theorem surjective_quotientGradingMk (i : ι) : Function.Surjective (quotientGradingMk I i) := by
  rintro ⟨b, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

private theorem coe_map_quotientGradingMk (z : ⨁ i, 𝒜 i) :
    DirectSum.coeAddMonoidHom (quotientGrading I) (DirectSum.map (quotientGradingMk I) z) =
      Ideal.Quotient.mk I.toIdeal (DirectSum.coeAddMonoidHom 𝒜 z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of n a => simp only [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **The homogeneous decomposition of the quotient of a graded ring by a homogeneous ideal.**
The decomposition map is the one of `A` followed by the degreewise quotient maps, which kills `I`
precisely because `I` is homogeneous. -/
noncomputable instance instDecompositionQuotientGrading :
    DirectSum.Decomposition (quotientGrading I) where
  decompose' := QuotientAddGroup.lift I.toIdeal.toAddSubgroup
    ((DirectSum.map (quotientGradingMk I)).comp
      (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom) <| by
        intro a ha
        ext n
        change ((DirectSum.map (quotientGradingMk I) (DirectSum.decompose 𝒜 a)) n :
          A ⧸ I.toIdeal) = 0
        rw [DirectSum.map_apply]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.IsHomogeneous.mem_iff 𝒜 I.2).mp ha n)
  left_inv := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change DirectSum.coeAddMonoidHom (quotientGrading I)
      (DirectSum.map (quotientGradingMk I) (DirectSum.decompose 𝒜 a)) = _
    rw [coe_map_quotientGradingMk]
    exact congrArg (Ideal.Quotient.mk I.toIdeal) ((DirectSum.decompose 𝒜).left_inv a)
  right_inv := by
    intro z
    obtain ⟨w, rfl⟩ := (DirectSum.map_surjective (quotientGradingMk I)).mpr
      (surjective_quotientGradingMk I) z
    rw [coe_map_quotientGradingMk]
    change DirectSum.map (quotientGradingMk I)
      (DirectSum.decompose 𝒜 (DirectSum.coeAddMonoidHom 𝒜 w)) = _
    exact congrArg (DirectSum.map (quotientGradingMk I)) ((DirectSum.decompose 𝒜).right_inv w)

/-- **The quotient of a graded ring by a homogeneous ideal is a graded ring.** -/
noncomputable instance instGradedRingQuotientGrading : GradedRing (quotientGrading I) where
  __ := instGradedMonoidQuotientGrading I
  __ := instDecompositionQuotientGrading I

/-- **The quotient map of a graded ring by a homogeneous ideal, as a homomorphism of graded
rings.** -/
def quotientMk : 𝒜 →+*ᵍ quotientGrading I where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem ha := mk_mem_quotientGrading I ha

/-- The graded quotient map acts as `Ideal.Quotient.mk`. -/
@[simp]
theorem quotientMk_apply (a : A) : quotientMk I a = Ideal.Quotient.mk I.toIdeal a := rfl

/-- The graded quotient map is surjective. -/
theorem surjective_quotientMk : Function.Surjective (quotientMk I) :=
  Ideal.Quotient.mk_surjective

end Stacks.HomogeneousIdeal

namespace AlgebraicGeometry.Proj

open Stacks.HomogeneousIdeal

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)

/-- **`V_+(I) = Proj (𝒜 ⧸ I)` is a closed subscheme of `Proj 𝒜`.** This is Stacks tag 01N0
parts (1) and (2) for the quotient of a graded ring by a homogeneous ideal, and the first step of
the proof of Tag 0801. -/
@[ega "II 2.9.2" "(i), special case", ega "II 3.6.2" "(i), special case"]
theorem isClosedImmersion_map_quotientMk :
    IsClosedImmersion (Proj.map (quotientMk I)
      (irrelevant_le_map_of_surjective (quotientMk I) (surjective_quotientMk I))) :=
  isClosedImmersion_map_of_surjective _ (surjective_quotientMk I)

end AlgebraicGeometry.Proj

end
