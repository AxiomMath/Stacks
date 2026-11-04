module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralDivisorMultiplicity
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegree
public import StacksFrontier.AlgebraicGeometry.Picard.DegreeAtLeastGenus
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of the invertible sheaf of an effective Cartier divisor

Let `X` be a proper integral scheme of dimension at most one over a field `k` and `D` an
effective Cartier divisor on it. The degree of `𝒪_X(D)` is the dimension over `k` of the ring of
functions on `D`:

`deg 𝒪_X(D) = dim_k Γ(D, 𝒪_D)`.

In particular the degree of `𝒪_X(D)` for a `k`-rational point `D` is `1`, and the degree
homomorphism `AlgebraicGeometry.picardDegree` is onto `𝐙`.

## Main definitions

* `AlgebraicGeometry.divisorSchemePicardClass`: the class of `𝒪_X(D)` in `Pic(X)`.
* `AlgebraicGeometry.picardDegreeTranslate`: the bijection from the classes of degree `d` onto
  the classes of degree zero given by subtracting a class of degree `d`.

## Main results

* `AlgebraicGeometry.invertibleCurveDegree_divisorSheaf_eq_finrank_globalSections`:
  `deg 𝒪_X(D) = dim_k Γ(D, 𝒪_D)`.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree`:
  the degree of `𝒪_X(D)` is the rank of the finite locally free morphism `D ⟶ Spec k`.
* `AlgebraicGeometry.invertibleCurveDegree_divisorSheaf_eq_one` and
  `AlgebraicGeometry.picardDegree_divisorSchemePicardClass_eq_one`: the degree of `𝒪_X(D)` is
  one when the ring of functions on `D` is `k`.
* `AlgebraicGeometry.surjective_picardDegree_of_eq_one`: if a class of degree one exists, the
  degree homomorphism is onto `𝐙`.
* `AlgebraicGeometry.exists_sub_eq_of_forall_exists_eq_of_picardDegree_eq`: if a family of
  classes hits every class of the degree of one of its members, then its differences with that
  member hit every class of degree zero.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)
open Stacks.Divisors (divisorSheaf divisorSheafGlobalSection canonicalSection' zeroScheme
  IsEffectiveCartierDivisor)

universe u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-! ### The degree of `𝒪_X(D)` -/

/-- **The canonical section `1_D` of `𝒪_X(D)` is nonzero** when `X` is integral. -/
theorem divisorSheafGlobalSection_ne_zero {X : Scheme.{u}} [IsIntegral X]
    (D : X.IdealSheafData) [hD : IsEffectiveCartierDivisor D] :
    divisorSheafGlobalSection D ≠ 0 := by
  intro h
  refine ne_bot_of_isEffectiveCartierDivisor hD ?_
  rw [← Stacks.Divisors.zeroScheme_canonicalSection D, h]
  exact Stacks.Divisors.zeroScheme_zero_eq_bot (divisorSheaf D)

/-- **The degree of `𝒪_X(D)` is the dimension over `k` of the ring of functions on `D`.** For an
effective Cartier divisor `D` on a proper integral scheme of dimension at most one over a field,

`deg 𝒪_X(D) = dim_k Γ(D, 𝒪_D)`.

The degree is `AlgebraicGeometry.invertibleCurveDegree`, [Stacks, Tag 0AYR]; the right-hand side
is the degree of `D` over `k` in the sense of [Stacks, Tag 0AYY], which
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_divisorSubscheme` exhibits as the rank of the finite
locally free morphism `D ⟶ Spec k`. -/
theorem invertibleCurveDegree_divisorSheaf_eq_finrank_globalSections (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    @invertibleCurveDegree k _ X f _ hdim (divisorSheaf D)
        (Stacks.Divisors.isInvertible_divisorSheaf D) =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) :=
  @invertibleCurveDegree_eq_finrank_globalSections_zeroScheme k _ X f _ hdim _
    (divisorSheaf D) (Stacks.Divisors.isInvertible_divisorSheaf D) (canonicalSection' D)
    (divisorSheafGlobalSection_ne_zero D) D (Stacks.Divisors.zeroScheme_canonicalSection D)

/-- **The degree of `𝒪_X(D)` is the rank of `D` over `k`.** The degree of a divisor in the sense
of [Stacks, Tag 0AYY] — the rank of the finite locally free morphism `D ⟶ Spec k` — equals the
degree of its invertible sheaf. -/
theorem exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D] :
    ∃ d : ℕ, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) d ∧
      (d : ℤ) = @invertibleCurveDegree k _ X f _ hdim (divisorSheaf D)
        (Stacks.Divisors.isInvertible_divisorSheaf D) :=
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  ⟨Module.finrank k Γ(D.subscheme, ⊤),
    isFiniteLocallyFreeOfRank_divisorSubscheme k f hdim D,
    (invertibleCurveDegree_divisorSheaf_eq_finrank_globalSections k f hdim D).symm⟩

/-! ### A divisor of degree one -/

/-- **A divisor whose only functions are the constants has degree one over `k`.** The hypothesis
is that `k ⟶ Γ(D, 𝒪_D)` is an isomorphism, which for a reduced one-point divisor is the
`k`-rationality of that point. -/
theorem finrank_globalSections_divisorSubscheme_eq_one (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop)] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank k Γ(D.subscheme, ⊤) = 1 := by
  rw [← finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k (D.subschemeι ≫ f)]
  exact finrank_cohomologyOverField_unit_zero_eq_one (D.subschemeι ≫ f)

/-- **The degree of `𝒪_X(D)` is one** for an effective Cartier divisor `D` whose ring of
functions is `k`, such as a `k`-rational point. -/
theorem invertibleCurveDegree_divisorSheaf_eq_one (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop)] :
    @invertibleCurveDegree k _ X f _ hdim (divisorSheaf D)
        (Stacks.Divisors.isInvertible_divisorSheaf D) = 1 := by
  rw [invertibleCurveDegree_divisorSheaf_eq_finrank_globalSections k f hdim D,
    finrank_globalSections_divisorSubscheme_eq_one k f D, Nat.cast_one]

/-! ### The class of `𝒪_X(D)` in `Pic(X)` and its degree -/

/-- `𝒪_X(D)` is invertible at the index `AlgebraicGeometry.schemePicard` is written over. -/
public theorem stacksIsInvertible_divisorSheaf {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) (divisorSheaf D) :=
  Stacks.Divisors.isTensorInvertible_invertibleSheaf D

/-- **The class of `𝒪_X(D)` in `Pic(X)`**, for `Pic(X)` the group
`AlgebraicGeometry.schemePicard` that `AlgebraicGeometry.picardDegree` is defined on. -/
@[ega "IV 21.3.2" "partial"]
def divisorSchemePicardClass {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] : schemePicard X :=
  schemePicardClassOf X (divisorSheaf D) (stacksIsInvertible_divisorSheaf D)

/-- **The degree of the class of `𝒪_X(D)` is the dimension over `k` of the ring of functions on
`D`.** -/
theorem picardDegree_divisorSchemePicardClass (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X] [IsCurve k f]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    picardDegree k f hdim (divisorSchemePicardClass D) =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) :=
  (picardDegree_classOf k f hdim (divisorSheaf D)
    (stacksIsInvertible_divisorSheaf D)).trans
      (invertibleCurveDegree_divisorSheaf_eq_finrank_globalSections k f hdim D)

/-- **A class of degree one in `Pic(X)`**, from a `k`-rational point of the curve. -/
theorem picardDegree_divisorSchemePicardClass_eq_one (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X] [IsCurve k f]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop)] :
    picardDegree k f hdim (divisorSchemePicardClass D) = 1 :=
  by rw [picardDegree_divisorSchemePicardClass k f hdim D,
    finrank_globalSections_divisorSubscheme_eq_one k f D, Nat.cast_one]

/-! ### The degree homomorphism is onto `𝐙`, and the degree-`d` to degree-`0` translation -/

/-- **The degree homomorphism `deg : Pic(X) ⟶ 𝐙` is surjective** as soon as one class of degree
one exists. -/
theorem surjective_picardDegree_of_eq_one (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
    (hdim : topologicalKrullDim X ≤ 1) (M : schemePicard X)
    (hM : picardDegree k f hdim M = 1) :
    Function.Surjective (picardDegree k f hdim) := fun n =>
  ⟨n • M, by simp [map_zsmul, hM]⟩

/-- **The translation `Pic^d(X) ≅ Pic⁰(X)` by a class of degree `d`.** Subtracting a class `M`
is a bijection from the classes of the same degree as `M` onto the degree-zero subgroup
`AlgebraicGeometry.picardDegreeZero`, with inverse the addition of `M`. -/
def picardDegreeTranslate (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [IsCurve k f] (hdim : topologicalKrullDim X ≤ 1) (M : schemePicard X) :
    {x : schemePicard X // picardDegree k f hdim x = picardDegree k f hdim M} ≃
      picardDegreeZero k f hdim where
  toFun x := ⟨x.1 - M, by
    rw [mem_picardDegreeZero_iff, map_sub, x.2, sub_self]⟩
  invFun z := ⟨z.1 + M, by
    rw [map_add, (mem_picardDegreeZero_iff k f hdim _).1 z.2, zero_add]⟩
  left_inv x := Subtype.ext (sub_add_cancel x.1 M)
  right_inv z := Subtype.ext (add_sub_cancel_right z.1 M)

/-- **The degree-`d` to degree-`0` translation, in the shape a surjectivity hypothesis consumes.**
If a family `abel` of Picard classes hits every class of the same degree as one of its own
values `abel a₀`, then `a ↦ abel a - abel a₀` hits every class of degree zero. -/
theorem exists_sub_eq_of_forall_exists_eq_of_picardDegree_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
    (hdim : topologicalKrullDim X ≤ 1) {A : Type*} (abel : A → schemePicard X) (a₀ : A)
    (hsurj : ∀ x : schemePicard X,
      picardDegree k f hdim x = picardDegree k f hdim (abel a₀) → ∃ a, abel a = x)
    (z : schemePicard X) (hz : z ∈ picardDegreeZero k f hdim) :
    ∃ a, abel a - abel a₀ = z := by
  obtain ⟨a, ha⟩ := hsurj _ ((picardDegreeTranslate k f hdim (abel a₀)).symm ⟨z, hz⟩).2
  exact ⟨a, by rw [ha]; exact add_sub_cancel_right z _⟩

end AlgebraicGeometry

end
