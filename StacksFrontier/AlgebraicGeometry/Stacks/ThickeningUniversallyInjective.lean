module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveComp
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDescent
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Universal injectivity in a morphism of thickenings of algebraic stacks (Stacks 0CJ9, part (6))

Stacks 0CJ9 part (6) reads, verbatim:

> Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks. Then
> (6) `f` is universally injective if and only if `f'` is universally injective.

Universal injectivity (**Stacks 0CI2**) is injectivity on points of *every* base change, so
unlike surjectivity it is not a condition on one map of sets and the bijectivity on points of the
two thickenings is not by itself enough. What replaces it is that the two notions of base change
are compared by the *enlargement of the target of a cospan* along `j : 𝒴 ⟶ 𝒴'`, which is an
equivalence because `j`, being a closed immersion, is fully faithful (**Stacks 04ZZ** (1) ⟹ (2),
`AlgebraicGeometry.Stack.AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion`):

`𝒵 ×_𝒴 𝒳 ≃ 𝒵 ×_{𝒴'} 𝒳`,

which is the source's step "since `𝒳 → 𝒴'` factors through the closed substack `𝒴` we see that
`𝒳 ×_𝒴 𝒳 = 𝒳 ×_{𝒴'} 𝒳`" of Stacks 0BPU, here at a general first factor.

## Main definitions

* `AlgebraicGeometry.Stack.enlargeTargetComparison`: the comparison
  `𝒵 ×_𝒴 𝒳 ⟶ 𝒵 ×_{𝒴'} 𝒳` of canonical 2-fibre products given by enlarging the target of the
  cospan along `j`, i.e. `CategoryTheory.TwoFibreProductOver.mapBase` read in the 2-category of
  algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.bijective_pointsMap_enlargeTargetComparison`: that comparison is
  bijective on points when `j` is fully faithful.
* `AlgebraicGeometry.Stack.injective_pointsMap_fst_of_enlargeTarget` and
  `AlgebraicGeometry.Stack.injective_pointsMap_fst_enlargeTarget`: hence injectivity on points of
  the first projection may be checked after enlarging the target, and survives it. The first uses
  injectivity of the comparison on points, the second surjectivity.
* `AlgebraicGeometry.Stack.universallyInjective_inner_of_outer` and
  `AlgebraicGeometry.Stack.universallyInjective_outer_of_inner`: the two implications.
* `AlgebraicGeometry.Stack.universallyInjective_inner_iff_outer`: **Stacks 0CJ9**, part (6).

## Implementation notes

The two implications are not symmetric, because `AlgebraicGeometry.Stack.UniversallyInjective`
quantifies over test 1-morphisms into the *target*, and the targets `𝒴`, `𝒴'` of the two
morphisms are different.

For `f'` universally injective ⟹ `f` universally injective, a test `d : 𝒵 ⟶ 𝒴` is pushed to
`d ≫ j : 𝒵 ⟶ 𝒴'`, where the hypothesis applies. The resulting base change `𝒵 ×_{𝒴'} 𝒳'` is then
cut down to `𝒵 ×_{𝒴'} 𝒳` by a further base change along `i`, which is a thickening by
**Stacks 0BPR** and therefore injective on points; pasting
(`CategoryTheory.Bicategory.isTwoFibreProduct_pasteSnd`) presents the composite as the first
projection of a 2-fibre product of the cospan `(d ≫ j, i ≫ f')`, and reindexing
(`CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd`) along the restriction
2-isomorphism of the morphism of thickenings moves that to the cospan `(d ≫ j, f ≫ j)`, which is
where `enlargeTargetComparison` connects it to `𝒵 ×_𝒴 𝒳`.

For `f` universally injective ⟹ `f'` universally injective the test 1-morphisms go the wrong
way, and the route is instead descent along the cover `j` itself: `j` is surjective because it is
a thickening, so **Stacks 0DTP**
(`AlgebraicGeometry.Stack.universallyInjective_of_isSurjective_baseChange`) reduces the claim to
universal injectivity of `𝒴 ×_{𝒴'} 𝒳' ⟶ 𝒴`. There a test `t : 𝒯 ⟶ 𝒴` produces `𝒯 ×_{𝒴'} 𝒳'`,
and the comparison with `𝒯 ×_𝒴 𝒳` — on which the hypothesis bites — runs through a base change
of `i`, which is a thickening and hence **bijective** on points. Bijectivity, not merely
injectivity, is what is needed: the comparison points the wrong way for injectivity to transport
along it, and it is surjectivity that lets two points upstairs be found over two points
downstairs.

Both directions transport between models of one cospan with
`AlgebraicGeometry.Stack.injective_pointsMap_fst_of_isTwoFibreProduct`, so every step may be
taken at the canonical models of Stacks 04T2 and no model-independence bookkeeping is needed.

`AlgebraicGeometry.Stack.enlargeTargetComparison` is strictly over the first projection — the
identity `enlargeTargetComparison ≫ fst = fst` holds on the nose, since
`CategoryTheory.TwoFibreProductOver.mapBase` changes nothing but the comparison isomorphism of an
object — so the factorisation of the map on points needs no 2-morphism.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0CI2](https://stacks.math.columbia.edu/tag/0CI2)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
* [Stacks Project, Tag 0DTP](https://stacks.math.columbia.edu/tag/0DTP)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparison

variable {𝒳 𝒴 𝒴' 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- **Enlarging the target of a cospan of algebraic stacks**, as a comparison of the canonical
2-fibre products of Stacks 04T2:

`𝒵 ×_{d, 𝒴, f} 𝒳 ⟶ 𝒵 ×_{d ≫ j, 𝒴', f ≫ j} 𝒳`.

It keeps the base object and both components of an object of the 2-fibre product and applies `j`
to its comparison isomorphism, which stays vertical because `j` is a 1-morphism over the site.
This is `CategoryTheory.TwoFibreProductOver.mapBase` read in the 2-category of algebraic
stacks. -/
def enlargeTargetComparison (d : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (j : 𝒴 ⟶ 𝒴') :
    (AlgebraicStacks.twoFibreProductSquare B S hS d f).pt ⟶
      (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) (f ≫ j)).pt :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.mapBase
        (pT := 𝒵.val.val.p) (p𝒜 := 𝒳.val.val.p)
        (CatFiberedInGroupoids.homFunctor d.hom) (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor j.hom) (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
      w := rfl })

/-- The comparison of `AlgebraicGeometry.Stack.enlargeTargetComparison` is strictly over the
first projection. -/
theorem enlargeTargetComparison_comp_fst (d : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (j : 𝒴 ⟶ 𝒴') :
    enlargeTargetComparison B S hS d f j ≫
        (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) (f ≫ j)).fst =
      (AlgebraicStacks.twoFibreProductSquare B S hS d f).fst :=
  rfl

/-- **Enlarging the target of a cospan along a fully faithful 1-morphism does not change the
2-fibre product.** The comparison is an equivalence of the underlying categories, by
`CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase`. -/
theorem isEquivalence_enlargeTargetComparison (d : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) {j : 𝒴 ⟶ 𝒴'}
    (hj : (CatFiberedInGroupoids.homFunctor j.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor j.hom).Faithful) :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (enlargeTargetComparison B S hS d f j).hom) :=
  have _ := hj.1
  have _ := hj.2
  TwoFibreProductOver.isEquivalence_mapBase (CatFiberedInGroupoids.homFunctor_comp_p j.hom)

/-- **Enlarging the target of a cospan along a fully faithful 1-morphism is bijective on
points.** -/
theorem bijective_pointsMap_enlargeTargetComparison (d : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) {j : 𝒴 ⟶ 𝒴'}
    (hj : (CatFiberedInGroupoids.homFunctor j.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor j.hom).Faithful) :
    Function.Bijective
      (AlgebraicStacks.pointsMap B S hS (enlargeTargetComparison B S hS d f j)) :=
  have _ := isEquivalence_enlargeTargetComparison B S hS d f hj
  AlgebraicStacks.bijective_pointsMap_of_isEquivalence B S hS _

/-- **Injectivity on points of a base change may be checked after enlarging the target of the
cospan along a fully faithful 1-morphism**: the comparison is bijective on points and is strictly
over the first projection. -/
theorem injective_pointsMap_fst_of_enlargeTarget (d : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) {j : 𝒴 ⟶ 𝒴'}
    (hj : (CatFiberedInGroupoids.homFunctor j.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor j.hom).Faithful)
    (h : Function.Injective (AlgebraicStacks.pointsMap B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) (f ≫ j)).fst)) :
    Function.Injective
      (AlgebraicStacks.pointsMap B S hS
        (AlgebraicStacks.twoFibreProductSquare B S hS d f).fst) := by
  rw [← enlargeTargetComparison_comp_fst B S hS d f j, AlgebraicStacks.pointsMap_comp]
  exact h.comp (bijective_pointsMap_enlargeTargetComparison B S hS d f hj).1

/-- **Injectivity on points of a base change survives enlarging the target of the cospan along a
fully faithful 1-morphism.** The converse of
`AlgebraicGeometry.Stack.injective_pointsMap_fst_of_enlargeTarget`: here it is *surjectivity* of
the comparison on points that is used, to find preimages of two points of the enlarged base
change. -/
theorem injective_pointsMap_fst_enlargeTarget (d : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) {j : 𝒴 ⟶ 𝒴'}
    (hj : (CatFiberedInGroupoids.homFunctor j.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor j.hom).Faithful)
    (h : Function.Injective (AlgebraicStacks.pointsMap B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS d f).fst)) :
    Function.Injective (AlgebraicStacks.pointsMap B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) (f ≫ j)).fst) := by
  rw [← enlargeTargetComparison_comp_fst B S hS d f j, AlgebraicStacks.pointsMap_comp] at h
  exact h.of_comp_right (bijective_pointsMap_enlargeTargetComparison B S hS d f hj).2

end Comparison

section Thickenings

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}

/-- **In a morphism of thickenings of algebraic stacks, if the ambient 1-morphism is universally
injective then so is the restricted one.**

A test `d : 𝒵 ⟶ 𝒴` for the restricted 1-morphism is pushed along `j` to a test for the ambient
one, whose base change `𝒵 ×_{𝒴'} 𝒳'` is injective on points by hypothesis. Cutting that down
along `i` — a base change of a thickening, hence a thickening (**Stacks 0BPR**) and so injective
on points — gives, after pasting and reindexing along the restriction 2-isomorphism, a 2-fibre
product of the cospan `(d ≫ j, f ≫ j)` whose first projection is injective on points. Enlarging
the target is an equivalence because `j` is fully faithful, so that is the same as injectivity for
the cospan `(d, f)`. -/
theorem universallyInjective_inner_of_outer (m : ThickeningMorphism i j hi hj)
    (h : UniversallyInjective B S hS m.outer) :
    UniversallyInjective B S hS m.inner := by
  have hjff := AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS j hj.1
  intro 𝒵 d P hP
  set Fc := AlgebraicStacks.twoFibreProductSquare B S hS d m.inner with hFcdef
  have hFc := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS d m.inner
  set E := AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer with hEdef
  have hE := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (d ≫ j) m.outer
  set T := AlgebraicStacks.twoFibreProductSquare B S hS E.snd i with hTdef
  have hT := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS E.snd i
  -- the hypothesis, at the pushed test `d ≫ j`
  have hEinj : Function.Injective (AlgebraicStacks.pointsMap B S hS E.fst) := h 𝒵 (d ≫ j) E hE
  -- `T.fst` is a base change of the thickening `i`, hence a thickening, hence injective on points
  have hTinj : Function.Injective (AlgebraicStacks.pointsMap B S hS T.fst) :=
    injective_pointsMap_of_isThickening (isThickening_fst_of_isTwoFibreProduct B S hS hi T hT)
  -- paste, then reindex the second leg along the restriction 2-isomorphism
  have hA := Bicategory.isTwoFibreProduct_reindexSnd (P := E.pasteSnd T) m.comm.symm
    (Bicategory.isTwoFibreProduct_pasteSnd E hE T hT)
  -- pasting leaves the first projection the composite of the two, and reindexing does not touch it
  have hAinj : Function.Injective
      (AlgebraicStacks.pointsMap B S hS ((E.pasteSnd T).reindexSnd m.comm.symm).fst) := by
    exact AlgebraicStacks.pointsMap_comp B S hS T.fst E.fst ▸ hEinj.comp hTinj
  -- transport to the canonical model of the same cospan, then shrink the target back
  refine injective_pointsMap_fst_of_isTwoFibreProduct B S hS hP hFc ?_
  exact injective_pointsMap_fst_of_enlargeTarget B S hS d m.inner hjff
    (injective_pointsMap_fst_of_isTwoFibreProduct B S hS
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (d ≫ j) (m.inner ≫ j))
      hA hAinj)

/-- **In a morphism of thickenings of algebraic stacks, if the restricted 1-morphism is
universally injective then so is the ambient one.**

The test 1-morphisms of the two statements go the wrong way round for the previous argument, so
the route is descent: `j` is surjective because it is a thickening, so **Stacks 0DTP** reduces
the claim to universal injectivity of `𝒴 ×_{𝒴'} 𝒳' ⟶ 𝒴`. A test `t : 𝒯 ⟶ 𝒴` for that pastes
down to `𝒯 ×_{𝒴'} 𝒳' ⟶ 𝒯`, the middle `𝒴` cancelling, and a further base change along `i` — a
thickening by **Stacks 0BPR** and hence *bijective* on points — presents `𝒯 ×_{𝒴'} 𝒳 ⟶ 𝒯` as the
composite. The hypothesis, enlarged along `j`, is exactly injectivity of that composite, and
surjectivity of the base change along `i` cancels it. -/
theorem universallyInjective_outer_of_inner (m : ThickeningMorphism i j hi hj)
    (h : UniversallyInjective B S hS m.inner) :
    UniversallyInjective B S hS m.outer := by
  have hjff := AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS j hj.1
  refine universallyInjective_of_isSurjective_baseChange B S hS m.outer j hj.2 ?_
  intro 𝒯 t Q hQ
  set W := AlgebraicStacks.twoFibreProductSquare B S hS j m.outer with hWdef
  have hW := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS j m.outer
  set Qc := AlgebraicStacks.twoFibreProductSquare B S hS t W.fst with hQcdef
  have hQc := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS t W.fst
  -- pasting cancels the middle `𝒴`: `Qc.pt` is a 2-fibre product of `(t ≫ j, outer)`
  have hPout := Bicategory.isTwoFibreProduct_pasteFst W hW Qc hQc
  set R := AlgebraicStacks.twoFibreProductSquare B S hS (W.pasteFst Qc).snd i with hRdef
  have hR := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (W.pasteFst Qc).snd i
  -- a further base change along `i` is a thickening, hence bijective on points
  have hRbij : Function.Bijective (AlgebraicStacks.pointsMap B S hS R.fst) :=
    bijective_pointsMap_of_isThickening (isThickening_fst_of_isTwoFibreProduct B S hS hi R hR)
  -- the hypothesis at `t`, enlarged along `j`, then reindexed to the cospan `(t ≫ j, i ≫ outer)`
  have hGcinj := injective_pointsMap_fst_enlargeTarget B S hS t m.inner hjff
    (h 𝒯 t (AlgebraicStacks.twoFibreProductSquare B S hS t m.inner)
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS t m.inner))
  have hPin := Bicategory.isTwoFibreProduct_reindexSnd
    (P := AlgebraicStacks.twoFibreProductSquare B S hS (t ≫ j) (m.inner ≫ j)) m.comm
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (t ≫ j) (m.inner ≫ j))
  -- transport to the pasted model of that cospan, whose first projection is `R.fst ≫ Qc.fst`
  have hpasteinj := injective_pointsMap_fst_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_pasteSnd (W.pasteFst Qc) hPout R hR) hPin hGcinj
  -- cancel the surjection `R.fst`
  refine injective_pointsMap_fst_of_isTwoFibreProduct B S hS hQ hQc ?_
  exact (AlgebraicStacks.pointsMap_comp B S hS R.fst Qc.fst ▸ hpasteinj).of_comp_right hRbij.2

/-- **Stacks 0CJ9, part (6).** In a morphism of thickenings of algebraic stacks over `S`, the
restricted 1-morphism is universally injective if and only if the ambient 1-morphism is
universally injective. -/
@[stacks 0CJ9 "part (6): universally injective"]
theorem universallyInjective_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    UniversallyInjective B S hS m.inner ↔ UniversallyInjective B S hS m.outer :=
  ⟨universallyInjective_outer_of_inner B S hS m, universallyInjective_inner_of_outer B S hS m⟩

end Thickenings

end AlgebraicGeometry.Stack

end
