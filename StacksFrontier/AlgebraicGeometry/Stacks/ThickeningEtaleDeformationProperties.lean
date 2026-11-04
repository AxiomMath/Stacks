module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatDeformation
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDeformationPropertiesPointTest
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningEtaleChartTower
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedEtaleDiagram

/-!
# Unramifiedness and étaleness along a thickening of algebraic stacks

Consider a commutative diagram of thickenings of algebraic stacks over `S`
`(𝒳 ⊂ 𝒳') ⟶ (𝒴 ⊂ 𝒴')` over a thickening `iB : ℬ ⟶ ℬ'` with `𝒴' ⟶ ℬ'` locally of finite type,
`𝒳' ⟶ ℬ'` flat and locally of finite presentation and the two restricted stacks the base changes
of the ambient ones, as in Stacks 0CJC. If the restricted 1-morphism `f` is unramified, resp.
étale, then so is the ambient one `f'`. Conversely, `f` is unramified, resp. étale, when `f'` is
Deligne–Mumford and satisfies the corresponding étale-diagram test of Stacks 0CIY.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_ambient_of_flatDeformation`: for
  a property of morphisms of algebraic spaces which is étale-smooth local on the source-and-target
  and invariant along a flat deformation of algebraic spaces, the universal étale-smooth diagram
  test passes from the restricted 1-morphism to the ambient one.
* `AlgebraicGeometry.Stack.isDM_restricted_iff_ambient`: the restricted 1-morphism is
  Deligne–Mumford exactly when the ambient one is.
* `AlgebraicGeometry.Stack.isUnramified_ambient_of_isUnramified` and
  `AlgebraicGeometry.Stack.isEtale_ambient_of_isEtale`: items (8) and (9) of Stacks 0CJC, the
  implication from the restricted 1-morphism to the ambient one.
* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_restricted_of_etaleDiagram`:
  the universal étale-smooth diagram test for the restricted 1-morphism, from the étale-diagram
  test of Stacks 0CIY for the ambient one.
* `AlgebraicGeometry.Stack.isUnramified_restricted_of_isUnramifiedOnEveryEtaleDiagram` and
  `AlgebraicGeometry.Stack.isEtale_restricted_of_etaleDiagram`: items (8) and (9) of
  Stacks 0CJC, the implication from the ambient 1-morphism to the restricted one, with condition
  (2) of Stacks 0CIY on the ambient 1-morphism in place of its unramifiedness, resp. the
  corresponding étale-diagram test in place of its étaleness.

## References

* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CG1](https://stacks.math.columbia.edu/tag/0CG1)
* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CII](https://stacks.math.columbia.edu/tag/0CII)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIU](https://stacks.math.columbia.edu/tag/0CIU)
* [Stacks Project, Tag 0CIV](https://stacks.math.columbia.edu/tag/0CIV)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
* [Stacks Project, Tag 0CJB](https://stacks.math.columbia.edu/tag/0CJB)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {ℬ ℬ' 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-! ### The universal étale-smooth test passes to the ambient 1-morphism -/

/-- Let `P` be a property of morphisms of algebraic spaces which is étale-smooth local on the
source-and-target and such that in every flat deformation diagram of algebraic spaces the morphism
of special fibres has `P` exactly when its ambient deformation does. In a commutative diagram of
thickenings of algebraic stacks satisfying the hypotheses of Stacks 0CJC, if the restricted
1-morphism satisfies the universal étale-smooth diagram test for `P`, then so does the ambient
one. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_ambient_of_flatDeformation
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    (hPdef : ∀ D : Space.FlatDeformationDiagram B S hS, P D.f ↔ P D.f')
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX')
    (hfP : HasPropertyOnEveryEtaleSmoothDiagram B S hS P f) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f' := by
  intro U'₀ V'₀ hU'₀ hV'₀ a'₀ b'₀ h'₀ η'₀ hb'₀ hcomp'₀
  obtain ⟨T, β, α, hcomm, hβsm, hαsu, hliftiso⟩ :=
    exists_etaleChartTower_of_etaleSmoothDiagram B S hS houter hYft hXflat hXfp U'₀ V'₀
      hU'₀ hV'₀ a'₀.hom b'₀.hom h'₀ η'₀ hb'₀ hcomp'₀
  obtain ⟨C, hCT⟩ := exists_thickenedEtaleChartTower B S hS hiB T
  subst hCT
  have hfwv : P (ObjectProperty.homMk C.fWV :
      (⟨C.W, C.algW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C.V, C.algV⟩) :=
    prop_fWV_of_thickenedEtaleChartTower B S hS P hcartX hcartY houter hrestrict hinner hcoh
      hfP C
  have hh' : P (ObjectProperty.homMk C.tower.h' :
      (⟨C.tower.W', C.tower.algebraicW⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨C.tower.V', C.tower.algebraicV⟩) :=
    (hPdef (C.flatDeformationDiagram hiB)).1 hfwv
  have _hiso := hliftiso
  exact Space.prop_of_etale_smooth_surjective_square B S hS hP hU'₀ hV'₀
    C.tower.algebraicW C.tower.algebraicV h'₀ β α C.tower.h' hcomm hβsm hαsu
    (Space.isEtale_of_isIso B S hS _) hh'

/-! ### The universal étale-smooth test passes to the restricted 1-morphism -/

/-- In a commutative diagram of thickenings of algebraic stacks whose restricted stacks are the
base changes of the ambient ones, if the ambient 1-morphism satisfies the étale-diagram test of
Stacks 0CIY for `P`, then the restricted 1-morphism satisfies the universal étale-smooth diagram
test for `P`. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_restricted_of_etaleDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hf'P : HasPropertyOnEveryEtaleDiagram B S hS P f') :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f :=
  hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleDiagram B S hS P
    (hasPropertyOnEveryEtaleDiagram_baseChange B S hS P f' PY.fst
      (restrictedSourceSq B S hS PX PY hrestrict)
      (isTwoFibreProduct_restrictedSourceSq B S hS hcartX hcartY houter hrestrict hinner hcoh)
      hf'P)

/-! ### Unramifiedness and étaleness -/

/-- In a commutative diagram of thickenings of algebraic stacks over `S` with the two restricted
stacks the base changes of the ambient ones along `iB`, the restricted 1-morphism is
Deligne–Mumford exactly when the ambient one is. -/
theorem isDM_restricted_iff_ambient
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f') :
    IsDM B S hS f ↔ IsDM B S hS f' :=
  isDM_inner_iff_outer B S hS
    ({ outer := f', inner := f, comm := hrestrict } :
      ThickeningMorphism PX.fst PY.fst
        (isThickening_baseChange B S hS iB pX' PX.swap
          (Bicategory.isTwoFibreProduct_swap hcartX) hiB)
        (isThickening_baseChange B S hS iB pY' PY.swap
          (Bicategory.isTwoFibreProduct_swap hcartY) hiB))

/-- Under the hypotheses of `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`,
an unramified restricted 1-morphism has an unramified ambient 1-morphism. -/
theorem isUnramified_ambient_of_isUnramified
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX')
    (hf : IsUnramified B S hS f) :
    IsUnramified B S hS f' :=
  ⟨(isDM_restricted_iff_ambient B S hS hiB hcartX hcartY hrestrict).1 hf.1,
    hasPropertyOnEveryEtaleSmoothDiagram_ambient_of_flatDeformation B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsUnramified B S hS g.hom)
      (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS)
      (fun D => Space.isUnramified_iff_isUnramified_deformation B S hS D)
      hiB hcartX hcartY houter hrestrict hinner hcoh hYft hXflat hXfp hf.2⟩

/-- Under the hypotheses of `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`,
an étale restricted 1-morphism has an étale ambient 1-morphism. -/
theorem isEtale_ambient_of_isEtale
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX')
    (hf : IsEtale B S hS f) :
    IsEtale B S hS f' :=
  ⟨(isDM_restricted_iff_ambient B S hS hiB hcartX hcartY hrestrict).1 hf.1,
    hasPropertyOnEveryEtaleSmoothDiagram_ambient_of_flatDeformation B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsEtale B S hS g.hom)
      (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS)
      (fun D => Space.isEtale_iff_of_flatDeformationDiagram B S hS D)
      hiB hcartX hcartY houter hrestrict hinner hcoh hYft hXflat hXfp hf.2⟩

/-- In a commutative diagram of thickenings of algebraic stacks over `S` whose restricted source is
the base change of the ambient one, if the ambient 1-morphism is Deligne–Mumford and every étale
diagram of algebraic spaces over it has unramified top horizontal morphism, then the restricted
1-morphism is unramified. -/
theorem isUnramified_restricted_of_isUnramifiedOnEveryEtaleDiagram
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hf' : IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f') :
    IsUnramified B S hS f :=
  isUnramified_fst_of_isUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f' PY.fst
    (restrictedSourceSq B S hS PX PY hrestrict)
    (isTwoFibreProduct_restrictedSourceSq B S hS hcartX hcartY houter hrestrict hinner hcoh) hf'

/-- In a commutative diagram of thickenings of algebraic stacks over `S` whose restricted source is
the base change of the ambient one, if the ambient 1-morphism is Deligne–Mumford and every étale
diagram of algebraic spaces over it has étale top horizontal morphism, then the restricted
1-morphism is étale. -/
theorem isEtale_restricted_of_etaleDiagram
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hdm' : IsDM B S hS f')
    (hf' : HasPropertyOnEveryEtaleDiagram B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsEtale B S hS g.hom) f') :
    IsEtale B S hS f :=
  ⟨(isDM_restricted_iff_ambient B S hS hiB hcartX hcartY hrestrict).2 hdm',
    hasPropertyOnEveryEtaleSmoothDiagram_restricted_of_etaleDiagram B S hS _
      hcartX hcartY houter hrestrict hinner hcoh hf'⟩

end AlgebraicGeometry.Stack

end
