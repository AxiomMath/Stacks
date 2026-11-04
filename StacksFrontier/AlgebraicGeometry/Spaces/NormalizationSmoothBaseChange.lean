module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty

/-!
# Normalization commutes with smooth base change

Let
```
Y₂ ⟶ Y₁
 |     | f
 v     v
X₂ ⟶ X₁
   φ
```
be a fibre square of algebraic spaces over a scheme `S`, and let `Yᵢ ⟶ Xᵢ' ⟶ Xᵢ` be the
normalization of `Xᵢ` in `Yᵢ`.  Stacks 082F asserts that `X₂' ≅ X₂ ×_{X₁} X₁'`.

This file follows the source's proof.  The base change `X₂ ×_{X₁} X₁' ⟶ X₂` of `ν₁` is
integral by Stacks 03ZS, the square produces a canonical morphism `Y₂ ⟶ X₂ ×_{X₁} X₁'`
factoring `f₂` through it, and the universal property of Stacks 0823 therefore supplies a
unique comparison morphism `h : X₂' ⟶ X₂ ×_{X₁} X₁'`; that morphism in turn exhibits `X₂'` as
the normalization of `X₂ ×_{X₁} X₁'` in `Y₂`.  The isomorphism itself is not proved here: it is
`AlgebraicGeometry.Space.IsRelativeNormalization.existsUnique_iso_baseChange_of_isSmooth`, in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInSmoothBaseChange`; see the implementation
notes.

## Main definitions

* `AlgebraicGeometry.Space.IsRelativeNormalization.baseChangeFactorization` is the canonical
  morphism `Y₂ ⟶ X₂ ×_{X₁} X₁'` through which the base change of the factorization
  `Y₁ ⟶ X₁' ⟶ X₁` factors `f₂`.

## Main results

* `AlgebraicGeometry.Space.IsRelativeNormalization.isIntegralHom_baseChange`: the base change
  `X₂ ×_{X₁} X₁' ⟶ X₂` of the normalization `ν₁` is integral.
* `AlgebraicGeometry.Space.IsRelativeNormalization.existsUnique_baseChangeComparison`: the
  morphism `h : X₂' ⟶ X₂ ×_{X₁} X₁'` of the source's proof exists and is unique.
* `AlgebraicGeometry.Space.IsRelativeNormalization.isRelativeNormalization_baseChangeComparison`:
  that comparison morphism exhibits `X₂'` as the normalization of `X₂ ×_{X₁} X₁'` in `Y₂`; in
  particular it is itself integral.
* `AlgebraicGeometry.Space.IsRelativeNormalization.isRelativeNormalization_baseChange`: the
  base-changed factorization `Y₂ ⟶ X₂ ×_{X₁} X₁' ⟶ X₂` is a relative normalization as soon as
  it has the universal property.

## Implementation notes

**The meaning of "the normalization of `Xᵢ` in `Yᵢ`".**  It is
`AlgebraicGeometry.Space.IsRelativeNormalization`, the two properties of Stacks 0823:
the morphism `νᵢ : Xᵢ' ⟶ Xᵢ` is integral, and every factorization of `fᵢ` through an integral
morphism of algebraic spaces to `Xᵢ` receives a unique compatible morphism from `Xᵢ'`.  Those
properties characterize the factorization, and
`AlgebraicGeometry.Space.isRelativeNormalization_toNormalizationIn` proves that the relative
spectrum of the integral closure of `𝒪_{Xᵢ}` in `f_{i,*}𝒪_{Yᵢ}` has them, so working with the
two properties rather than with that construction loses nothing and keeps the inputs of that
construction out of the statements below.

**What is proved outright, and what is assumed.**  Of the three clauses of
`AlgebraicGeometry.Space.IsRelativeNormalization` for the base change
`X₂ ×_{X₁} X₁' ⟶ X₂`, two are proved here: the factorization, which is the defining property
of `baseChangeFactorization`, and the integrality, which is Stacks 03ZS.  The third, the
universal property, is the hypothesis `huniv` of `isRelativeNormalization_baseChange`.  It is
the tail of the source's argument, which compares the two integral closures: `X₂'` is the
relative spectrum of the integral closure of `𝒪_{X₂}` in
`f_{2,*}𝒪_{Y₂}`, while `X₂ ×_{X₁} X₁'` is the relative spectrum of `φ^*𝒜'` for `𝒜'` the
integral closure of `𝒪_{X₁}` in `f_{1,*}𝒪_{Y₁}`, because the relative spectrum commutes with
arbitrary base change; the two algebras agree because `f_{2,*}𝒪_{Y₂} = φ^*f_{1,*}𝒪_{Y₁}`,
which is Stacks 073K, and because the integral closure commutes with smooth pullback, which is
Stacks 082E.  Of those two inputs the library proves the second and not the first: the file
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean` constructs the base change
map of Stacks 0736 for a cartesian square with flat lower edge and characterizes it, but
proves neither part of Stacks 073K, so the identification `f_{2,*}𝒪_{Y₂} = φ^*f_{1,*}𝒪_{Y₁}`
is not available in any form.

**Why neither the smoothness of `φ` nor the quasi-compactness and quasi-separatedness of `f`
is carried.**  Those hypotheses enter the source in exactly two places, and neither is a step
performed here: they make the two normalizations exist, which is Stacks 0822 and is a
hypothesis below in the shape `IsRelativeNormalization`, and the smoothness of `φ` is the
hypothesis of Stacks 082E inside the tail of the proof, which is the hypothesis `huniv`.  The
results below are correspondingly more general than the source, in the same way and for the
same reason as those of
`StacksFrontier/AlgebraicGeometry/Spaces/NormalizationInUniversalProperty.lean`.

**The fibre product.**  Both fibre squares are arbitrary cartesian squares rather than the
chosen limits, so no compatibility between a choice of fibre product and the square of the
source has to be transported; the algebraicity of `X₂ ×_{X₁} X₁'` is then Stacks 04T9 and is
proved rather than assumed.

## References

* [Stacks Project, Tag 082F](https://stacks.math.columbia.edu/tag/082F)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 082E](https://stacks.math.columbia.edu/tag/082E)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 04T9](https://stacks.math.columbia.edu/tag/04T9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X₁ X₂ Y₁ Y₂ X₁' X₂' P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : Y₁ ⟶ X₁} {φ : X₂ ⟶ X₁} {g : Y₂ ⟶ Y₁} {f₂ : Y₂ ⟶ X₂}
    {ν₁ : X₁' ⟶ X₁} {f₁' : Y₁ ⟶ X₁'} {ν₂ : X₂' ⟶ X₂} {f₂' : Y₂ ⟶ X₂'}
    {p : P ⟶ X₂} {q : P ⟶ X₁'}

/-- The fibre product `X₂ ×_{X₁} X₁'` of two algebraic spaces over an algebraic space is an
algebraic space, by Stacks 04T9. -/
private theorem isAlgebraicSpace_of_isPullback_fst (hX₁ : IsAlgebraicSpace B S hS X₁)
    (hX₂ : IsAlgebraicSpace B S hS X₂) (hX₁' : IsAlgebraicSpace B S hS X₁')
    (sqP : IsPullback p q φ ν₁) : IsAlgebraicSpace B S hS P :=
  isAlgebraicSpace_of_isPullback hX₂ hX₁' hX₁.isSheaf hX₁.diagonal_representable sqP

namespace IsRelativeNormalization

/-! ### The base change of the normalization -/

/-- The base change `X₂ ×_{X₁} X₁' ⟶ X₂` of the normalization `ν₁ : X₁' ⟶ X₁` of `X₁` in `Y₁`
is integral, by Stacks 03ZS. -/
theorem isIntegralHom_baseChange (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (sqP : IsPullback p q φ ν₁) : IsIntegralHom B S hS p :=
  isIntegralHom_of_isPullback B S hS sqP.flip hnorm₁.isIntegralHom

/-- The canonical morphism `Y₂ ⟶ X₂ ×_{X₁} X₁'`: the base change to `X₂` of the factorization
`Y₁ ⟶ X₁' ⟶ X₁` of `f`, which is the morphism with components `f₂ : Y₂ ⟶ X₂` and
`Y₂ ⟶ Y₁ ⟶ X₁'`. -/
def baseChangeFactorization (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (sq : IsPullback g f₂ f φ) (sqP : IsPullback p q φ ν₁) : Y₂ ⟶ P :=
  sqP.lift f₂ (g ≫ f₁') (by rw [Category.assoc, hnorm₁.fac]; exact sq.w.symm)

/-- The canonical morphism `Y₂ ⟶ X₂ ×_{X₁} X₁'` factors `f₂` through the base change of the
normalization of `X₁` in `Y₁`. -/
@[simp]
theorem baseChangeFactorization_fst (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (sq : IsPullback g f₂ f φ) (sqP : IsPullback p q φ ν₁) :
    hnorm₁.baseChangeFactorization sq sqP ≫ p = f₂ :=
  sqP.lift_fst _ _ _

/-- The second component of the canonical morphism `Y₂ ⟶ X₂ ×_{X₁} X₁'` is the morphism
`Y₂ ⟶ Y₁ ⟶ X₁'` to the normalization of `X₁` in `Y₁`. -/
@[simp]
theorem baseChangeFactorization_snd (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (sq : IsPullback g f₂ f φ) (sqP : IsPullback p q φ ν₁) :
    hnorm₁.baseChangeFactorization sq sqP ≫ q = g ≫ f₁' :=
  sqP.lift_snd _ _ _

/-! ### The comparison morphism -/

/-- **Stacks 082F, the morphism `h`.**  The base change `X₂ ×_{X₁} X₁' ⟶ X₂` is an integral
morphism through which `f₂` factors, so the universal property of the normalization `X₂'` of
`X₂` in `Y₂` supplies a unique morphism `h : X₂' ⟶ X₂ ×_{X₁} X₁'` compatible with the two
factorizations of `f₂` and with the two morphisms to `X₂`. -/
@[stacks 082F "the morphism h of the proof: the base change X₂ ×_{X₁} X₁' ⟶ X₂ is integral \
and f₂ factors through it, so the universal property of Tag 0823 supplies a unique h"]
theorem existsUnique_baseChangeComparison
    (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (hnorm₂ : IsRelativeNormalization B S hS f₂ ν₂ f₂')
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX₂ : IsAlgebraicSpace B S hS X₂)
    (hX₁' : IsAlgebraicSpace B S hS X₁')
    (sq : IsPullback g f₂ f φ) (sqP : IsPullback p q φ ν₁) :
    ∃! h : X₂' ⟶ P, f₂' ≫ h = hnorm₁.baseChangeFactorization sq sqP ∧ h ≫ p = ν₂ :=
  hnorm₂.existsUnique_lift (isAlgebraicSpace_of_isPullback_fst hX₁ hX₂ hX₁' sqP) p
    (hnorm₁.isIntegralHom_baseChange sqP) (hnorm₁.baseChangeFactorization sq sqP)
    (hnorm₁.baseChangeFactorization_fst sq sqP)

/-- **Stacks 0823 for the morphism `h` of Stacks 082F.**  The comparison morphism
`h : X₂' ⟶ X₂ ×_{X₁} X₁'` exhibits `X₂'` as the normalization of `X₂ ×_{X₁} X₁'` in `Y₂`; in
particular `h` is integral. -/
theorem isRelativeNormalization_baseChangeComparison
    (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (hnorm₂ : IsRelativeNormalization B S hS f₂ ν₂ f₂')
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX₂ : IsAlgebraicSpace B S hS X₂)
    (hX₁' : IsAlgebraicSpace B S hS X₁')
    (sq : IsPullback g f₂ f φ) (sqP : IsPullback p q φ ν₁) {h : X₂' ⟶ P}
    (hh : f₂' ≫ h = hnorm₁.baseChangeFactorization sq sqP) (hhp : h ≫ p = ν₂) :
    IsRelativeNormalization B S hS (hnorm₁.baseChangeFactorization sq sqP) h f₂' :=
  hnorm₂.comparison hX₂ (isAlgebraicSpace_of_isPullback_fst hX₁ hX₂ hX₁' sqP)
    (hnorm₁.isIntegralHom_baseChange sqP) hh hhp

/-! ### The isomorphism -/

/-- The base-changed factorization `Y₂ ⟶ X₂ ×_{X₁} X₁' ⟶ X₂` exhibits `X₂ ×_{X₁} X₁'` as the
normalization of `X₂` in `Y₂` as soon as it has the universal property `huniv`.  Its other two
clauses, the factorization and the integrality of `X₂ ×_{X₁} X₁' ⟶ X₂`, hold with no further
hypothesis. -/
theorem isRelativeNormalization_baseChange
    (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (sq : IsPullback g f₂ f φ) (sqP : IsPullback p q φ ν₁)
    (huniv : ∀ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Z →
      ∀ π : Z ⟶ X₂, IsIntegralHom B S hS π → ∀ u : Y₂ ⟶ Z, u ≫ π = f₂ →
        ∃! k : P ⟶ Z, hnorm₁.baseChangeFactorization sq sqP ≫ k = u ∧ k ≫ π = p) :
    IsRelativeNormalization B S hS f₂ p (hnorm₁.baseChangeFactorization sq sqP) :=
  ⟨hnorm₁.baseChangeFactorization_fst sq sqP, hnorm₁.isIntegralHom_baseChange sqP, huniv⟩

end IsRelativeNormalization

end AlgebraicGeometry.Space

end
