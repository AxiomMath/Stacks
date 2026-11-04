module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedTensorChernTwo

/-!
# Localized Chern classes of a derived tensor product

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`. Let `Z₁, Z₂ ⊆ X` be closed subschemes and let `F₁, F₂ ∈ D(𝒪_X)` be perfect
objects such that `F_i|_{X ∖ Z_i}` is zero and `F_i` satisfies condition (3) of Situation 0GUJ.
Write `r_i = P_0(Z_i ⟶ X, F_i) ∈ A^0(Z_i ⟶ X)`. Lemma 0FBF states

  `P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(Z₁ ⟶ X, F₁) P_{p₂}(Z₂ ⟶ X, F₂)`,

  `c_1(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ c_1(Z₂ ⟶ X, F₂) + r₂ c_1(Z₁ ⟶ X, F₁)`,

  `c_2(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ c_2(Z₂ ⟶ X, F₂) + r₂ c_2(Z₁ ⟶ X, F₁) +
    C(r₁, 2) c_1(Z₂ ⟶ X, F₂)² + (r₁ r₂ - 1) c_1(Z₂ ⟶ X, F₂) c_1(Z₁ ⟶ X, F₁) +
    C(r₂, 2) c_1(Z₁ ⟶ X, F₁)²`,

and `ch(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = ch(Z₁ ⟶ X, F₁) ch(Z₂ ⟶ X, F₂)`, in `A^*(Z₁ ∩ Z₂ ⟶ X)`, resp.
`∏_p A^p(Z₁ ∩ Z₂ ⟶ X) ⊗ 𝐐`. This file states the four formulas with the factors `F_i` in
Situation 0GUJ.

## Main definitions

* `Stacks.Chow.LocalizedSituation.ofIsZero` — Situation 0GUJ for `F` perfect with `F|_{X ∖ Z}`
  zero satisfying condition (3), in a given degree.

## Main results

* `Stacks.Chow.LocalizedSituation.localizedPowerSum_derivedTensor` — the formula for `P_p`.
* `Stacks.Chow.LocalizedSituation.localizedChern_one_derivedTensor` — the formula for `c_1`.
* `Stacks.Chow.LocalizedSituation.localizedChern_two_derivedTensor` — the formula for `c_2`.
* `Stacks.Chow.LocalizedSituation.localizedChernChar_derivedTensor` — the formula for `ch`, in
  each degree.

## Implementation notes

The source does not say in which sense `F₁ ⊗^L F₂` satisfies condition (3) of Situation 0GUJ: under
alternatives (c) and (d) for both factors it does, but in the mixed cases, say (c) for `F₁` and (d)
for `F₂`, or (d) for both with different schemes `X'`, the source leaves it implicit. The classes
of `F₁ ⊗^L F₂` here are those of Remark 0GUK (`Stacks.Chow.LocalizedChernData.localizedPowerSum`,
`Stacks.Chow.LocalizedChernData.localizedChern`), defined for every perfect object whose Chern
classes are defined; those of `F₁ ⊗^L F₂` are, by Stacks 0GUE, whatever alternatives `F₁` and `F₂`
satisfy, and in Situation 0GUJ the classes of Remark 0GUK are those of Stacks 0FB2
(`Stacks.Chow.LocalizedSituation.localizedPowerSum_toLocalizedChernData`). This covers the
mixed cases.

`Z₁ ∩ Z₂` is the scheme theoretic intersection `Z₁ ×_X Z₂`, mapping to `X` through `Z₂`; the
products are those of Stacks 0FE5 (`Stacks.Chow.supportedIntersectionMul`), and the second summand
`r₂ c_1(Z₁ ⟶ X, F₁)` is taken for `Z₁ ∩ Z₂` presented as `Z₂ ×_X Z₁` through the flipped square.
The Chern character is compared degree by degree: the component of degree `p` of the product of
`ch₁ = ∑_n P_{1,n}/n!` and `ch₂` is `∑_{p₁ + p₂ = p} (P_{1,p₁}/p₁!) (P_{2,p₂}/p₂!)`.

In the formula for `c_2`, the squares `c_1(Z_i ⟶ X, F_i)²` are the products
`res(c) ∘ c` of Stacks 0FA0 (`Stacks.Chow.supportedMul`), the binomial coefficient `C(r_i, 2)` is
the class in `A^0(Z_i ⟶ X)` of the locally constant function `x ↦ C(χ_{F_i}(x), 2)`
(`Stacks.Chow.LocalizedChernData.rankChoose`), whose analogue for `C(r_i, 1)` is `r_i`, and
`(r₁ r₂ - 1) c_1(Z₂ ⟶ X, F₂) c_1(Z₁ ⟶ X, F₁)` is read as
`(r₁ r₂) (c_1(Z₂ ⟶ X, F₂) c_1(Z₁ ⟶ X, F₁)) - c_1(Z₂ ⟶ X, F₂) c_1(Z₁ ⟶ X, F₁)`, there being no
unit `1` in `A^0(Z₁ ∩ Z₂ ⟶ X)` when `Z₁ ∩ Z₂ ≠ X`. The source's "and so on for higher Chern
classes" is not a precise assertion and is not formalized.

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Finset

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

namespace LocalizedSituation

variable (C : ChowSituation.{u}) {X Z₁ Z₂ : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]

/-- **Situation 0GUJ for an object zero away from a closed subscheme**: the data
`Stacks.Chow.LocalizedChernData.ofIsZero` of `(X, Z, F)` in degree `p`, with condition (3). -/
abbrev ofIsZero {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (F : DerivedCategory X.Modules)
    (hF : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F)
    (h : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i.base)ᶜ,
        i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F))
    (hfin : CompactSpace X ∨ (∀ c ∈ irreducibleComponents X, IsCompact c) ∨
      (∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ F)) ∨
      (∃ (X' : Scheme.{u}) (a' : X' ⟶ C.S) (g : X ⟶ X')
          (F' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
        LocallyOfFiniteType a' ∧ g ≫ a' = a ∧
          Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) F' ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            g.toLRSHom.toShHom).obj F' ≅ F) ∧
          ∀ c ∈ irreducibleComponents X', IsCompact c))
    (p : ℕ) : LocalizedSituation.{u} where
  toLocalizedChernData := LocalizedChernData.ofIsZero C a i F hF h p
  finiteness := hfin

variable (i₁ : Z₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₂]
  {F₁ F₂ : DerivedCategory X.Modules}
  (hF₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F₁)
  (hF₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F₂)
  (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i₁.base)ᶜ,
        i₁.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F₁))
  (h₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i₂.base)ᶜ,
        i₂.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F₂))
  (hfin₁ : CompactSpace X ∨ (∀ c ∈ irreducibleComponents X, IsCompact c) ∨
      (∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ F₁)) ∨
      (∃ (X' : Scheme.{u}) (a' : X' ⟶ C.S) (g : X ⟶ X')
          (F' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
        LocallyOfFiniteType a' ∧ g ≫ a' = a ∧
          Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) F' ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            g.toLRSHom.toShHom).obj F' ≅ F₁) ∧
          ∀ c ∈ irreducibleComponents X', IsCompact c))
  (hfin₂ : CompactSpace X ∨ (∀ c ∈ irreducibleComponents X, IsCompact c) ∨
      (∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ F₂)) ∨
      (∃ (X' : Scheme.{u}) (a' : X' ⟶ C.S) (g : X ⟶ X')
          (F' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
        LocallyOfFiniteType a' ∧ g ≫ a' = a ∧
          Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) F' ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            g.toLRSHom.toShHom).obj F' ≅ F₂) ∧
          ∀ c ∈ irreducibleComponents X', IsCompact c))

/-- **The localized power sums of a derived tensor product.** In Situation 02QL let `X` be locally
of finite type over `S`, let `Z₁, Z₂ ⊆ X` be closed subschemes and let `F₁, F₂ ∈ D(𝒪_X)` be perfect
with `F_i|_{X ∖ Z_i}` zero and satisfying condition (3) of Situation 0GUJ. Then

  `P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(Z₁ ⟶ X, F₁) P_{p₂}(Z₂ ⟶ X, F₂)`

in `A^p(Z₁ ∩ Z₂ ⟶ X)`, the class of `F₁ ⊗^L F₂` being that of Remark 0GUK; the source leaves
implicit in which sense `F₁ ⊗^L F₂` satisfies condition (3) in the mixed cases of alternatives
(c) and (d), which the classes of Remark 0GUK cover. -/
@[stacks 0FBF "the formula for P_p(Z_1 cap Z_2 -> X, F_1 tensor^L F_2), with Z_1 cap Z_2 = Z_1 \
x_X Z_2 and the products those of 0FE5 (supportedIntersectionMul).  The source leaves implicit in \
which sense F_1 tensor^L F_2 satisfies (3) of 0GUJ in the mixed cases ((c) for one factor and (d) \
for the other, or (d) for both with different X'); the classes of F_1 tensor^L F_2 are those of \
Remark 0GUK, defined for every perfect object with defined Chern classes, which covers them."]
theorem localizedPowerSum_derivedTensor (p : ℕ) :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0).localizedPowerSum
        (hasDefinedChernClasses_derivedTensor
          (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).hasDefinedChernClasses_E
          (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).hasDefinedChernClasses_E)
        (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) p =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).localizedPowerSum h₁ q.1.1)
            ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).localizedPowerSum h₂ q.1.2)) := by
  refine (LocalizedChernData.localizedPowerSum_derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂
    (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).hasDefinedChernClasses_E
    (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).hasDefinedChernClasses_E _ p).trans ?_
  simp only [← localizedPowerSum_toLocalizedChernData (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0) h₁,
    ← localizedPowerSum_toLocalizedChernData (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0) h₂]

/-- **The first localized Chern class of a derived tensor product.** In the situation of
`Stacks.Chow.LocalizedSituation.localizedPowerSum_derivedTensor`, with
`r_i = P_0(Z_i ⟶ X, F_i)`,

  `c_1(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ c_1(Z₂ ⟶ X, F₂) + r₂ c_1(Z₁ ⟶ X, F₁)`

in `A^1(Z₁ ∩ Z₂ ⟶ X)`, the class of `F₁ ⊗^L F₂` being that of Remark 0GUK. -/
@[stacks 0FBF "the formula for c_1(Z_1 cap Z_2 -> X, F_1 tensor^L F_2), r_i = P_0(Z_i -> X, F_i); \
the product r_2 c_1(Z_1 -> X, F_1) is taken for Z_1 cap Z_2 presented as Z_2 x_X Z_1 through the \
flipped square.  The source leaves implicit in which sense F_1 tensor^L F_2 satisfies (3) of 0GUJ \
in the mixed cases ((c) for one factor and (d) for the other, or (d) for both with different X'); \
the classes of F_1 tensor^L F_2 are those of Remark 0GUK, defined for every perfect object with \
defined Chern classes, which covers them."]
theorem localizedChern_one_derivedTensor :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 1).localizedChern
        (hasDefinedChernClasses_derivedTensor
          (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).hasDefinedChernClasses_E
          (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).hasDefinedChernClasses_E)
        (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _
          (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) one_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).localizedPowerSum h₁ 0)
            ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).localizedPowerSum h₂ 0)
            ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos))) := by
  have e₁ := localizedPowerSum_toLocalizedChernData (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0) h₁ 0
  have e₂ := localizedPowerSum_toLocalizedChernData (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0) h₂ 0
  have e₁' := localizedChern_toLocalizedChernData (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 1)
    (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁ one_pos)
  have e₂' := localizedChern_toLocalizedChernData (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 1)
    (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂ one_pos)
  refine (LocalizedChernData.localizedChern_one_derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂
    (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).hasDefinedChernClasses_E
    (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).hasDefinedChernClasses_E _).trans ?_
  simp only [← e₁, ← e₂, ← e₁', ← e₂']

/-- **The second localized Chern class of a derived tensor product.** In the situation of
`Stacks.Chow.LocalizedSituation.localizedPowerSum_derivedTensor`, with
`r_i = P_0(Z_i ⟶ X, F_i)`, `γ_{i,p} = c_p(Z_i ⟶ X, F_i)` and `C(r_i, 2)` the class
`Stacks.Chow.LocalizedChernData.rankChoose`,

  `c_2(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ γ_{2,2} + r₂ γ_{1,2} + C(r₁, 2) γ_{2,1}² +
    ((r₁ r₂) (γ_{2,1} γ_{1,1}) - γ_{2,1} γ_{1,1}) + C(r₂, 2) γ_{1,1}²`

in `A^2(Z₁ ∩ Z₂ ⟶ X)`, the class of `F₁ ⊗^L F₂` being that of Remark 0GUK. The products of a
class supported on `Z₂` with one supported on `Z₁` are taken for `Z₁ ∩ Z₂` presented as
`Z₂ ×_X Z₁` through the flipped square, and the squares are the products of
`Stacks.Chow.supportedMul`. -/
@[stacks 0FBF "the formula for c_2(Z_1 cap Z_2 -> X, F_1 tensor^L F_2); the squares are the \
products res(c) o c of 0FA0 (supportedMul), C(r_i, 2) is the class of x |-> C(chi_{F_i}(x), 2) \
(LocalizedChernData.rankChoose), and (r_1 r_2 - 1) c c' is read as (r_1 r_2)(c c') - c c'.  The \
source's 'and so on for higher Chern classes' is not formalized.  The source leaves implicit in \
which sense F_1 tensor^L F_2 satisfies (3) of 0GUJ in the mixed cases ((c) for one factor and (d) \
for the other, or (d) for both with different X'); the classes of F_1 tensor^L F_2 are those of \
Remark 0GUK, defined for every perfect object with defined Chern classes, which covers them."]
theorem localizedChern_two_derivedTensor :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 2).localizedChern
        (hasDefinedChernClasses_derivedTensor
          (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).hasDefinedChernClasses_E
          (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).hasDefinedChernClasses_E)
        (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _
          (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) two_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).localizedPowerSum h₁ 0)
            ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 2).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).localizedPowerSum h₂ 0)
            ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 2).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).rankChoose h₁ 2 two_pos)
            (supportedMul C (i₂ ≫ a) a i₂ rfl ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
              ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos)))) +
        (bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedMul C ((pullback.snd i₁ i₂ ≫ i₂) ≫ a) a (pullback.snd i₁ i₂ ≫ i₂) rfl
              (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
                ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).localizedPowerSum h₁ 0)
                ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).localizedPowerSum h₂ 0))
              (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
                ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
                ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))) -
          bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
              ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
              ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).rankChoose h₂ 2 two_pos)
            (supportedMul C (i₁ ≫ a) a i₁ rfl ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos))
              ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 1).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))) := by
  have e₁ := localizedPowerSum_toLocalizedChernData (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0) h₁ 0
  have e₂ := localizedPowerSum_toLocalizedChernData (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0) h₂ 0
  have e₁' := localizedChern_toLocalizedChernData (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 1)
    (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁ one_pos)
  have e₂' := localizedChern_toLocalizedChernData (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 1)
    (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂ one_pos)
  have e₁'' := localizedChern_toLocalizedChernData (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 2)
    (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁ two_pos)
  have e₂'' := localizedChern_toLocalizedChernData (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 2)
    (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂ two_pos)
  refine (LocalizedChernData.localizedChern_two_derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂
    (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).hasDefinedChernClasses_E
    (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).hasDefinedChernClasses_E _).trans ?_
  simp only [← e₁, ← e₂, ← e₁', ← e₂', ← e₁'', ← e₂'']

/-- **The localized Chern character of a derived tensor product.** In the situation of
`Stacks.Chow.LocalizedSituation.localizedPowerSum_derivedTensor`,

  `ch(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = ch(Z₁ ⟶ X, F₁) ch(Z₂ ⟶ X, F₂)`

in `∏_p A^p(Z₁ ∩ Z₂ ⟶ X) ⊗ 𝐐`, read in each degree `p`: the component of degree `p` of the left
side is `∑_{p₁ + p₂ = p} ch_{p₁}(Z₁ ⟶ X, F₁) ch_{p₂}(Z₂ ⟶ X, F₂)`, the degree `p` component of the
product, with the products of `Stacks.Chow.rationalSupportedIntersectionMul`. The Chern character
of `F₁ ⊗^L F₂` is that of Remark 0GUK. -/
@[stacks 0FBF "the formula ch(Z_1 cap Z_2 -> X, F_1 tensor^L F_2) = ch(Z_1 -> X, F_1) ch(Z_2 -> \
X, F_2), read degree by degree in prod_p A^p(Z_1 cap Z_2 -> X) tensor Q.  The source leaves \
implicit in which sense F_1 tensor^L F_2 satisfies (3) of 0GUJ in the mixed cases ((c) for one \
factor and (d) for the other, or (d) for both with different X'); the classes of F_1 tensor^L F_2 \
are those of Remark 0GUK, defined for every perfect object with defined Chern classes, which \
covers them."]
theorem localizedChernChar_derivedTensor (p : ℕ) :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0).localizedChernChar
        (hasDefinedChernClasses_derivedTensor
          (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).hasDefinedChernClasses_E
          (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).hasDefinedChernClasses_E)
        (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) p =
      ∑ q ∈ (antidiagonal p).attach,
        rationalBivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (rationalSupportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).localizedChernChar h₁ q.1.1)
            ((ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).localizedChernChar h₂ q.1.2)) :=
  tmul_eq_sum_rationalSupportedIntersectionMul_of_eq_sum_choose C a i₁ i₂ _ _ rfl
    (fun n ↦ (ofIsZero C a i₁ F₁ hF₁ h₁ hfin₁ 0).localizedPowerSum h₁ n)
    (fun n ↦ (ofIsZero C a i₂ F₂ hF₂ h₂ hfin₂ 0).localizedPowerSum h₂ n) _ p
    (localizedPowerSum_derivedTensor C a i₁ i₂ hF₁ hF₂ h₁ h₂ hfin₁ hfin₂ p)

end LocalizedSituation

end Stacks.Chow

end
