module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralFiniteMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningUniversallyInjective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IdentityCospan

/-!
# Affineness and integrality in a morphism of thickenings of algebraic stacks

Stacks 0CJ9 reads, at the two items treated here:

> Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks. Then
> (1) `f` is an affine morphism if and only if `f'` is an affine morphism,
> (5) `f` is integral if and only if `f'` is integral.

An affine (**Stacks 0CHQ**), respectively integral (**Stacks 0CHU**), 1-morphism of algebraic
stacks is one representable by algebraic spaces which is affine, respectively integral, in the
sense of Stacks 04XB. Representability by algebraic spaces passes between `f` and `f'` by part
(12) of the tag (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inner_iff_outer`).
The source then reduces to the corresponding statement for a morphism of thickenings of
algebraic spaces (**Stacks 09ZY**) after a smooth base change; here the same geometric input — a
surjective closed immersion of algebraic spaces cancels off the front of an affine, respectively
integral, composite
(`AlgebraicGeometry.Space.isAffineHom_of_comp_of_isClosedImmersion_of_isSurjective`,
`AlgebraicGeometry.Space.isIntegralHom_of_comp_of_isClosedImmersion_of_isSurjective`, which rest on
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`) —
is used directly at the level of the conditions of Stacks 04XB, along the restriction
2-isomorphism `f ≫ j ≅ i ≫ f'`:

* from `f` to `f'`: `f ≫ j` has the property because `f` and the closed immersion `j` do
  (**Stacks 045B**), so `i ≫ f'` has it (**Stacks 0457**), and the cancellation against the
  surjective closed immersion `i` gives `f'`
  (`AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_spaceCancelFirst`);
* from `f'` to `f`: `i ≫ f'`, hence `f ≫ j`, has the property, and a 1-morphism `f` has a
  condition of Stacks 04XB as soon as `f ≫ j` does, when `j` is fully faithful
  (`AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_fullyFaithful`): `f` is a base
  change of `f ≫ j` along `j` up to equivalences, namely `𝒳 ≃ 𝒴 ×_𝒴 𝒳 ≃ 𝒴 ×_{𝒴'} 𝒳`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_fullyFaithful`: a condition of
  Stacks 04XB descends from `f ≫ j` to `f` when `j` is fully faithful.
* `AlgebraicGeometry.Stack.isAffineHom_inner_iff_outer`: **Stacks 0CJ9**, part (1).
* `AlgebraicGeometry.Stack.isIntegralHom_inner_iff_outer`: **Stacks 0CJ9**, part (5).

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0CHU](https://stacks.math.columbia.edu/tag/0CHU)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Cancel

variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- **A condition of Stacks 04XB descends along a fully faithful 1-morphism of the target.** Let
`f : 𝒳 ⟶ 𝒴` and `j : 𝒴 ⟶ 𝒴'` be 1-morphisms of algebraic stacks over `S` with `j` fully
faithful. If `f ≫ j` satisfies the condition of Stacks 04XB for a property `P` of morphisms of
algebraic spaces, so does `f`.

The projection `𝒴 ×_{𝒴'} 𝒳 ⟶ 𝒴` of the canonical 2-fibre product of `(𝟙 ≫ j, f ≫ j)` has the
condition by **Stacks 045C** (`AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct`,
which asks nothing of `P`). Enlarging the target of the cospan `(𝟙, f)` along `j` is an
equivalence `𝒴 ×_𝒴 𝒳 ≃ 𝒴 ×_{𝒴'} 𝒳` strictly over `𝒴`, and `𝒳` is a 2-fibre product of `(𝟙, f)`
with first projection `f` (`CategoryTheory.Bicategory.TwoCommSq.idCospan`), so the condition moves
to `f` by **Stacks 0457** (`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`), twice. -/
theorem hasRelativeProperty_of_comp_of_fullyFaithful
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (j : 𝒴 ⟶ 𝒴')
    (hj : (CatFiberedInGroupoids.homFunctor j.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor j.hom).Faithful)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hfj : IsRepresentableByAlgebraicSpaces B S hS (f ≫ j).hom.hom)
    (h : HasRelativeProperty.{u, u, u + 1, u} B S hS P (f ≫ j).hom hfj) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P f.hom hf := by
  set C' := AlgebraicStacks.twoFibreProductSquare B S hS (𝟙 𝒴 ≫ j) (f ≫ j)
  -- Stacks 045C: the base change of `f ≫ j` along `𝟙 ≫ j`
  have h₁ := prop_baseChange_of_isTwoFibreProduct.{u, u, u} B S hS P 𝒳.val 𝒴'.val 𝒴.val
    (f ≫ j).hom (𝟙 𝒴 ≫ j).hom (AlgebraicStacks.toCatFiberedInGroupoids B S hS C')
    (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS C'
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (𝟙 𝒴 ≫ j) (f ≫ j))) h
  -- enlarging the target of `(𝟙, f)` along `j` is an equivalence strictly over `𝒴`
  set C := AlgebraicStacks.twoFibreProductSquare B S hS (𝟙 𝒴) f
  have hC := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (𝟙 𝒴) f
  have : (enlargeTargetComparison B S hS (𝟙 𝒴) f j).hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_enlargeTargetComparison B S hS (𝟙 𝒴) f hj
  have : (BasedFunctor.id 𝒴.val.val).toFunctor.IsEquivalence :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒴.val.val.obj))
  have h₂ := relativeProperty_of_equivalences B S hS P C.fst.hom.hom C'.fst.hom.hom
    (enlargeTargetComparison B S hS (𝟙 𝒴) f j).hom.hom (BasedFunctor.id 𝒴.val.val)
    (Iso.refl _) h₁
  -- `𝒳` is a 2-fibre product of `(𝟙, f)` with first projection `f`
  let e := Bicategory.twoFibreProductPreHom hC (Bicategory.TwoCommSq.idCospan f)
  have : e.hom.hom.hom.toFunctor.IsEquivalence := isEquivalence_homFunctor_preHom B S hS
    (Bicategory.isTwoFibreProduct_idCospan f) hC e
  exact relativeProperty_of_equivalences B S hS P f.hom.hom C.fst.hom.hom e.hom.hom.hom
    (BasedFunctor.id 𝒴.val.val)
    (twoIsoHomIso B S hS (algebraicStacksTwoIsoHom B S hS e.isoFst.symm)) h₂

end Cancel

section Thickenings

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}

/-- **A condition of Stacks 04XB passes from the restricted 1-morphism of a morphism of
thickenings to the ambient one**, for a property `P` of morphisms of algebraic spaces enjoyed by
thickenings and cancelling against a surjective closed immersion. `f ≫ j` has `P` by **Stacks
045B**, so `i ≫ f'` has it by **Stacks 0457**, and the thickening `i` is cancelled off the front
by `AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_spaceCancelFirst`. -/
theorem hasRelativeProperty_outer_of_inner (m : ThickeningMorphism i j hi hj)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsStableUnderComposition]
    (hcancel : ∀ {A C D : AlgebraicSpaces B S hS} (a : A ⟶ C) (b : C ⟶ D),
      P (a ≫ b) → Space.closedImmersionProperty B S hS a →
        Space.surjectiveMorphismProperty B S hS a → P b)
    (hPj : HasRelativeProperty.{u, u, u + 1, u} B S hS P j.hom hj.1.1)
    (hf : IsRepresentableByAlgebraicSpaces B S hS m.inner.hom.hom)
    (hf' : IsRepresentableByAlgebraicSpaces B S hS m.outer.hom.hom)
    (h : HasRelativeProperty.{u, u, u + 1, u} B S hS P m.inner.hom hf) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P m.outer.hom hf' := by
  have hmoved := hasRelativeProperty_congr_twoIso.{u, u, u + 1, u} B S hS P
    (algebraicStacksTwoIsoHom B S hS m.comm)
    (isRepresentableByAlgebraicSpaces_comp B S hS m.inner.hom j.hom hf hj.1.1)
    (isRepresentableByAlgebraicSpaces_comp B S hS i.hom m.outer.hom hi.1.1 hf')
    (hasRelativeProperty_comp.{u, u, u + 1, u} B S hS P m.inner.hom j.hom hf hj.1.1 h hPj)
  exact hasRelativeProperty_of_comp_of_spaceCancelFirst.{u, u} B S hS P
    (Space.closedImmersionProperty B S hS) (Space.surjectiveMorphismProperty B S hS) hcancel
    i.hom m.outer.hom hi.1.1 hf' _
    (hasRelativeProperty_closedImmersion_of_isThickening B S hS hi)
    (hasRelativeProperty_surjective_of_isThickening B S hS hi) hmoved

/-- **A condition of Stacks 04XB passes from the ambient 1-morphism of a morphism of thickenings
to the restricted one**, for a property `P` of morphisms of algebraic spaces enjoyed by
thickenings. `i ≫ f'` has `P` by **Stacks 045B**, so `f ≫ j` has it by **Stacks 0457**, and `j`,
a closed immersion, is fully faithful (**Stacks 04ZZ**), so
`AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_fullyFaithful` gives `f`. -/
theorem hasRelativeProperty_inner_of_outer (m : ThickeningMorphism i j hi hj)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsStableUnderComposition]
    (hPi : HasRelativeProperty.{u, u, u + 1, u} B S hS P i.hom hi.1.1)
    (hf : IsRepresentableByAlgebraicSpaces B S hS m.inner.hom.hom)
    (hf' : IsRepresentableByAlgebraicSpaces B S hS m.outer.hom.hom)
    (h : HasRelativeProperty.{u, u, u + 1, u} B S hS P m.outer.hom hf') :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P m.inner.hom hf := by
  have hfj := isRepresentableByAlgebraicSpaces_comp B S hS m.inner.hom j.hom hf hj.1.1
  have hmoved := hasRelativeProperty_congr_twoIso.{u, u, u + 1, u} B S hS P
    (algebraicStacksTwoIsoHom B S hS m.comm.symm)
    (isRepresentableByAlgebraicSpaces_comp B S hS i.hom m.outer.hom hi.1.1 hf') hfj
    (hasRelativeProperty_comp.{u, u, u + 1, u} B S hS P i.hom m.outer.hom hi.1.1 hf' hPi h)
  exact hasRelativeProperty_of_comp_of_fullyFaithful B S hS P m.inner j
    (AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS j hj.1) hf hfj
    hmoved

/-- A condition of Stacks 04XB holds for `f` if and only if it holds for `f'` in a morphism of
thickenings, given the cancellation and that thickenings enjoy the property. -/
private theorem exists_hasRelativeProperty_inner_iff_outer (m : ThickeningMorphism i j hi hj)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsStableUnderComposition]
    (hcancel : ∀ {A C D : AlgebraicSpaces B S hS} (a : A ⟶ C) (b : C ⟶ D),
      P (a ≫ b) → Space.closedImmersionProperty B S hS a →
        Space.surjectiveMorphismProperty B S hS a → P b)
    (hPi : HasRelativeProperty.{u, u, u + 1, u} B S hS P i.hom hi.1.1)
    (hPj : HasRelativeProperty.{u, u, u + 1, u} B S hS P j.hom hj.1.1) :
    (∃ hf, HasRelativeProperty.{u, u, u + 1, u} B S hS P m.inner.hom hf) ↔
      ∃ hf', HasRelativeProperty.{u, u, u + 1, u} B S hS P m.outer.hom hf' := by
  have hrep := isRepresentableByAlgebraicSpaces_inner_iff_outer B S hS m
  exact ⟨fun ⟨hf, h⟩ => ⟨hrep.1 hf, hasRelativeProperty_outer_of_inner B S hS m P hcancel hPj hf
      (hrep.1 hf) h⟩,
    fun ⟨hf', h⟩ => ⟨hrep.2 hf', hasRelativeProperty_inner_of_outer B S hS m P hPi
      (hrep.2 hf') hf' h⟩⟩

/-- **Stacks 0CJ9, part (1).** In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of
algebraic stacks over `S`, the restricted 1-morphism `f` is affine (**Stacks 0CHQ**) if and only
if the ambient 1-morphism `f'` is.

Representability by algebraic spaces is part (12) of the tag; affineness in the sense of Stacks
04XB is `AlgebraicGeometry.Stack.hasRelativeProperty_outer_of_inner` and
`AlgebraicGeometry.Stack.hasRelativeProperty_inner_of_outer` at
`AlgebraicGeometry.Space.affineMorphismProperty`, with the cancellation
`AlgebraicGeometry.Space.isAffineHom_of_comp_of_isClosedImmersion_of_isSurjective`. -/
@[stacks 0CJ9 "part (1): affine"]
theorem isAffineHom_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    AlgebraicStacks.IsAffineHom B S hS m.inner ↔ AlgebraicStacks.IsAffineHom B S hS m.outer := by
  have _haffBC : (Space.affineMorphismProperty B S hS).IsStableUnderBaseChange :=
    ⟨fun sq hg => Space.isAffineHom_hom_of_isPullback sq hg⟩
  have _haffLoc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isLocalAtTarget_isAffineHom_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hcancel : ∀ {A C D : AlgebraicSpaces B S hS} (a : A ⟶ C) (b : C ⟶ D),
      Space.affineMorphismProperty B S hS (a ≫ b) → Space.closedImmersionProperty B S hS a →
        Space.surjectiveMorphismProperty B S hS a → Space.affineMorphismProperty B S hS b :=
    fun {A C D} a b hab hci hsurj =>
      Space.isAffineHom_of_comp_of_isClosedImmersion_of_isSurjective B S hS C.2 D.2
        a.hom b.hom hci hsurj hab
  simpa only [exists_prop] using exists_hasRelativeProperty_inner_iff_outer B S hS m
    (Space.affineMorphismProperty B S hS) hcancel (isAffineHom_of_isThickening B S hS hi)
    (isAffineHom_of_isThickening B S hS hj)

/-- **Stacks 0CJ9, part (5).** In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of
algebraic stacks over `S`, the restricted 1-morphism `f` is integral (**Stacks 0CHU**) if and
only if the ambient 1-morphism `f'` is.

The argument is that of part (1) at `AlgebraicGeometry.Space.integralMorphismProperty`, with the
cancellation `AlgebraicGeometry.Space.isIntegralHom_of_comp_of_isClosedImmersion_of_isSurjective`
(Stacks 0415 splits integrality into affineness and universal closedness, which both cancel). -/
@[stacks 0CJ9 "part (5): integral"]
theorem isIntegralHom_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    AlgebraicStacks.IsIntegralHom B S hS m.inner ↔
      AlgebraicStacks.IsIntegralHom B S hS m.outer := by
  have hcancel : ∀ {A C D : AlgebraicSpaces B S hS} (a : A ⟶ C) (b : C ⟶ D),
      Space.integralMorphismProperty B S hS (a ≫ b) → Space.closedImmersionProperty B S hS a →
        Space.surjectiveMorphismProperty B S hS a → Space.integralMorphismProperty B S hS b :=
    fun {A C D} a b hab hci hsurj =>
      Space.isIntegralHom_of_comp_of_isClosedImmersion_of_isSurjective B S hS A.2 C.2 D.2
        a.hom b.hom hci hsurj hab
  exact exists_hasRelativeProperty_inner_iff_outer B S hS m
    (Space.integralMorphismProperty B S hS) hcancel
    (hasRelativeProperty_integral_of_isThickening B S hS hi)
    (hasRelativeProperty_integral_of_isThickening B S hS hj)

end Thickenings

end AlgebraicGeometry.Stack

end
