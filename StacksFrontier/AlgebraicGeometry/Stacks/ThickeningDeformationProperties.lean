module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Properties of a 1-morphism of algebraic stacks invariant along a thickening (Stacks 0CJC)

Consider a commutative diagram of thickenings of algebraic stacks over `S`,
`(𝒳 ⊂ 𝒳') ⟶ (𝒴 ⊂ 𝒴')`, both over a thickening `iB : ℬ ⟶ ℬ'`, with `𝒴' ⟶ ℬ'` locally of finite
type, `𝒳' ⟶ ℬ'` flat and locally of finite presentation, and the two restricted stacks the base
changes of the ambient ones along `iB`. For several properties the restricted 1-morphism
`f : 𝒳 ⟶ 𝒴` has the property exactly when the ambient one `f' : 𝒳' ⟶ 𝒴'` does.

## Main definitions

* `AlgebraicGeometry.Stack.restrictedSourceSq`: the restricted source read as a 2-commutative
  square over the cospan of the ambient 1-morphism and the thickening of the restricted target.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_restrictedSourceSq`: that square is a 2-fibre
  product, so the restricted 1-morphism is a base change of the ambient one.
* `AlgebraicGeometry.Stack.prop_fWV_of_thickenedChartTower`: a property smooth local on the
  source-and-target, stable under base change, closed under composition and holding for
  identities passes from the restricted 1-morphism to the morphism of charts of a thickened
  chart tower.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_of_flatDeformation`: for such a
  property, invariant along flat deformations of algebraic spaces, the existential smooth-diagram
  criterion holds for the restricted 1-morphism exactly when it holds for the ambient one.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`: the restricted 1-morphism
  is flat if and only if the ambient one is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_iff_isSmooth_ambient`: the restricted
  1-morphism is smooth if and only if the ambient one is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSyntomic_iff_isSyntomic_ambient`: the restricted
  1-morphism passes the existential smooth-diagram test at syntomicity if and only if the ambient
  one does, assuming source locality of syntomicity for the syntomic precoverage and target
  locality for the fpqc precoverage.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FN](https://stacks.math.columbia.edu/tag/06FN)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
* [Stacks Project, Tag 0CJB](https://stacks.math.columbia.edu/tag/0CJB)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CatFiberedInGroupoids
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {ℬ ℬ' 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-! ### The restricted 1-morphism as a base change of the ambient one -/

/-- The restricted source of a commutative diagram of thickenings, as a 2-commutative square
over the cospan of the ambient 1-morphism and the thickening of the restricted target. Its
first projection is the restricted 1-morphism, its second projection the thickening of the
restricted source, and its filler the 2-cell of the diagram identifying the two routes from the
restricted source to the ambient target. -/
def restrictedSourceSq
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    (PX : Bicategory.TwoCommSq pX' iB) (PY : Bicategory.TwoCommSq pY' iB)
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f') :
    Bicategory.TwoCommSq PY.fst f' where
  pt := PX.pt
  fst := f
  snd := PX.fst
  iso := hrestrict

/-- Under the two cartesian hypotheses, the restricted source of a commutative diagram of
thickenings is a 2-fibre product of the cospan of the ambient 1-morphism and the thickening of the
restricted target; that is, the restricted 1-morphism is a base change of the ambient one. -/
noncomputable def isTwoFibreProduct_restrictedSourceSq
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom) :
    Bicategory.IsTwoFibreProduct (restrictedSourceSq B S hS PX PY hrestrict) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_pasteInnerSq B S hS PY.underlying
        (isTwoFibreProduct_underlying_algebraicStacks B S hS PY hcartY)
        (Bicategory.isTwoFibreProduct_reindexFst _
          (isTwoFibreProduct_underlying_algebraicStacks B S hS PX hcartX))
        (restrictionPreHom B S hS PX PY houter hrestrict hinner hcoh)))

/-! ### A property invariant along a flat deformation is invariant along a thickening -/

/-- A property of morphisms of algebraic spaces which is smooth local on the source-and-target,
stable under base change, closed under composition and satisfied by identities passes from the
restricted 1-morphism to the morphism of charts of a thickened chart tower. -/
theorem prop_fWV_of_thickenedChartTower
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hPloc : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    (hPcomp : ∀ {X₀ Y₀ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hZ : IsAlgebraicSpace B S hS Z₀) (p : X₀ ⟶ Y₀) (q : Y₀ ⟶ Z₀),
      P p → P q → P (p ≫ q))
    (hPid : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F → P (𝟙 F))
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
    (hfP : HasPropertyOnSomeSmoothDiagram B S hS P f.hom)
    (C : ThickenedChartTower B S hS iB pY' f') :
    P C.fWV := by
  classical
  have hPYu : Bicategory.IsTwoFibreProduct PY.underlying :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS PY hcartY
  have hPXu : Bicategory.IsTwoFibreProduct PX.underlying :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS PX hcartX
  have hSx : Bicategory.IsTwoFibreProduct
      (PX.underlying.reindexFst (algebraicStacksTwoIsoHom B S hS houter).symm) :=
    Bicategory.isTwoFibreProduct_reindexFst _ hPXu
  set XX := Bicategory.pasteInnerSq PY.underlying
    (restrictionPreHom B S hS PX PY houter hrestrict hinner hcoh)
  have hXX : Bicategory.IsTwoFibreProduct XX :=
    isTwoFibreProduct_pasteInnerSq B S hS PY.underlying hPYu hSx _
  have hGV : Bicategory.IsTwoFibreProduct
      ((C.AU.pasteFst C.Qv).reindexFst C.tower.targetComm) :=
    Bicategory.isTwoFibreProduct_reindexFst _
      (Bicategory.isTwoFibreProduct_pasteFst C.AU C.cartAU C.Qv C.cartQv)
  set cV := Bicategory.twoFibreProductPreHom hPYu
    (Bicategory.pasteOuterSq C.tower.b' ((C.AU.pasteFst C.Qv).reindexFst C.tower.targetComm))
   
  have hMV : Bicategory.IsTwoFibreProduct (Bicategory.pasteInnerSq PY.underlying cV) :=
    isTwoFibreProduct_pasteInnerSq B S hS PY.underlying hPYu hGV cV
  have hcVsm : IsRelativelySmooth B S hS cV.hom :=
    (isRelativelySmooth_isSurjectiveOnObjects_snd B S hS C.tower.b' PY.underlying.fst
      (Bicategory.pasteInnerSq PY.underlying cV) hMV C.tower.smoothB C.tower.surjectiveB).1
  set Dsq := twoFibreProductSquare.{u, u, u + 1, u + 1} C.tower.b' f'.hom
  have hDsq : Bicategory.IsTwoFibreProduct Dsq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} C.tower.b' f'.hom
  set cc := Bicategory.twoFibreProductPreHom hDsq
    (diagramCone B S hS f'.hom C.tower.c' C.tower.b' C.tower.h' C.tower.sourceComm)
  have hccsm : IsRelativelySmooth B S hS cc.hom :=
    C.tower.smoothSourceComparison Dsq hDsq cc
  set Ev := twoFibreProductSquare.{u, u, u + 1, u + 1} C.Qv.fst Dsq.fst
  have hEv : Bicategory.IsTwoFibreProduct Ev :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} C.Qv.fst Dsq.fst
  set Pc := twoFibreProductSquare.{u, u, u + 1, u + 1} Ev.snd cc.hom
  have hPc : Bicategory.IsTwoFibreProduct Pc :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Ev.snd cc.hom
  have hPcfst : IsRelativelySmooth B S hS Pc.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS C.tower.W') Dsq.pt Ev.pt cc.hom Ev.snd Pc hPc hccsm
  have hRc : Bicategory.IsTwoFibreProduct (Ev.swap.pasteFst Pc.swap) :=
    Bicategory.isTwoFibreProduct_pasteFst Ev.swap (Bicategory.isTwoFibreProduct_swap hEv)
      Pc.swap (Bicategory.isTwoFibreProduct_swap hPc)
  have hQwr : Bicategory.IsTwoFibreProduct (C.Qw.reindexFst cc.isoFst) :=
    Bicategory.isTwoFibreProduct_reindexFst _ C.cartQw
  set e₀ := Bicategory.twoFibreProductPreHom hRc (C.Qw.reindexFst cc.isoFst)
  have he₀eq : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e₀.hom) :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hQwr hRc e₀
  have hcompsm : IsRelativelySmooth B S hS (e₀.hom ≫ Pc.fst) :=
    isRelativelySmooth_of_isEquivalence_comp B S hS e₀.hom Pc.fst he₀eq hPcfst
  have hGv : Bicategory.IsTwoFibreProduct ((Dsq.pasteFst Ev).reindexFst cV.isoFst) :=
    Bicategory.isTwoFibreProduct_reindexFst _
      (Bicategory.isTwoFibreProduct_pasteFst Dsq hDsq Ev hEv)
  set pv := Bicategory.twoFibreProductPreHom (Bicategory.isTwoFibreProduct_swap hXX)
    (Bicategory.pasteOuterSq cV.hom ((Dsq.pasteFst Ev).reindexFst cV.isoFst))
  have hNV : Bicategory.IsTwoFibreProduct (Bicategory.pasteInnerSq XX.swap pv) :=
    isTwoFibreProduct_pasteInnerSq B S hS XX.swap (Bicategory.isTwoFibreProduct_swap hXX) hGv pv
  have hbc : HasPropertyOnSomeSmoothDiagram B S hS P
      (twoFibreProductSquare.{u, u, u + 1, u + 1} cV.hom f.hom).fst :=
    hasPropertyOnSomeSmoothDiagram_baseChange_of_isRepresentableByAlgebraicSpace B S hS P
      f.hom cV.hom ⟨C.V, C.algV, ⟨C.eV⟩⟩ hfP
  have hEvfst : HasPropertyOnSomeSmoothDiagram B S hS P Ev.fst :=
    hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS P
      (twoFibreProductSquare.{u, u, u + 1, u + 1} cV.hom f.hom)
      (Bicategory.pasteInnerSq XX.swap pv)
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} cV.hom f.hom) hNV hbc
  have hsmoothP : HasPropertyOnSomeSmoothDiagram B S hS P (e₀.hom ≫ Pc.fst) :=
    hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS P (e₀.hom ≫ Pc.fst)
      C.W C.algW C.eW hcompsm (hPid C.algW)
  have hchain : HasPropertyOnSomeSmoothDiagram B S hS P ((e₀.hom ≫ Pc.fst) ≫ Ev.fst) :=
    hasPropertyOnSomeSmoothDiagram_comp_of_precomp B S hS P
      (fun hX hY hZ p q hp hq => hPloc.precomp hX hY hZ p q hp hq)
      (fun hX hY hZ p q hp hq => hPcomp hX hY hZ p q hp hq)
      (e₀.hom ≫ Pc.fst) Ev.fst hsmoothP hEvfst
  have hQwsnd : HasPropertyOnSomeSmoothDiagram B S hS P C.Qw.snd :=
    hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS P e₀.isoSnd.symm hchain
  exact prop_representingMap_of_hasPropertyOnSomeSmoothDiagram B S hS P hPloc
    C.W C.V C.algW C.algV C.eW C.eV C.Qw.snd hQwsnd

/-- For `P` smooth local on the source-and-target, stable under base change, closed under
composition, satisfied by identities, and such that in every flat deformation diagram of algebraic
spaces the morphism of special fibres has `P` exactly when its ambient deformation does, the
existential smooth-diagram criterion at `P` holds for the restricted 1-morphism of a commutative
diagram of thickenings exactly when it holds for the ambient one. -/
theorem hasPropertyOnSomeSmoothDiagram_iff_of_flatDeformation
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hPloc : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    (hPcomp : ∀ {X₀ Y₀ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hZ : IsAlgebraicSpace B S hS Z₀) (p : X₀ ⟶ Y₀) (q : Y₀ ⟶ Z₀),
      P p → P q → P (p ≫ q))
    (hPid : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F → P (𝟙 F))
    (hPdef : ∀ D : Space.FlatDeformationDiagram B S hS, P D.f.hom ↔ P D.f'.hom)
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
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX') :
    HasPropertyOnSomeSmoothDiagram B S hS P f.hom ↔
      HasPropertyOnSomeSmoothDiagram B S hS P f'.hom := by
  classical
  refine ⟨fun hfP => ?_, fun hf'P => ?_⟩
  · obtain ⟨T⟩ := exists_smoothChartTower B S hS pX' pY' f' houter hYft hXflat hXfp
    obtain ⟨C⟩ := exists_thickenedChartTower B S hS hiB T
    have hfwv : P C.fWV :=
      prop_fWV_of_thickenedChartTower B S hS P hPloc hPcomp hPid hcartX hcartY houter
        hrestrict hinner hcoh hfP C
    have hh' : P C.tower.h' := (hPdef (C.flatDeformationDiagram hiB)).1 hfwv
    exact ⟨C.tower.W', C.tower.V', C.tower.algebraicW, C.tower.algebraicV, C.tower.c',
      C.tower.b', C.tower.h', ⟨C.tower.sourceComm⟩, C.tower.smoothC, C.tower.surjectiveC,
      C.tower.smoothB, hh'⟩
  · exact hasPropertyOnSomeSmoothDiagram_baseChange_of_isStableUnderBaseChange B S hS P f'
      PY.fst (restrictedSourceSq B S hS PX PY hrestrict)
      (isTwoFibreProduct_restrictedSourceSq B S hS hcartX hcartY houter hrestrict hinner hcoh)
      hf'P

namespace AlgebraicStacks

/-! ### The clauses of Stacks 0CJC -/

/-- For a commutative diagram of thickenings of algebraic stacks over `S` over a thickening
`iB : ℬ ⟶ ℬ'` of bases, with `𝒴' ⟶ ℬ'` locally of finite type, `𝒳' ⟶ ℬ'` flat and locally of
finite presentation and the two restricted stacks the base changes of the ambient ones along `iB`,
the restricted 1-morphism `f` is flat if and only if the ambient 1-morphism `f'` is flat. -/
@[stacks 0CJC "flat"]
theorem isFlat_iff_isFlat_ambient
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
    (hYft : IsLocallyOfFiniteType B S hS pY')
    (hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    IsFlat B S hS f ↔ IsFlat B S hS f' := by
  exact ⟨isFlat_ambient_of_flatDeformation B S hS hiB hcartX hcartY houter hrestrict hinner hcoh
    hYft hXflat hXfp, isFlat_baseChange B S hS f' PY.fst (restrictedSourceSq B S hS PX PY hrestrict)
    (isTwoFibreProduct_restrictedSourceSq B S hS hcartX hcartY houter hrestrict hinner hcoh)⟩

/-- Under the hypotheses of `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`,
the restricted 1-morphism `f` is smooth if and only if the ambient 1-morphism `f'` is smooth. -/
@[stacks 0CJC "smooth"]
theorem isSmooth_iff_isSmooth_ambient
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
    (hYft : IsLocallyOfFiniteType B S hS pY')
    (hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    IsSmooth B S hS f ↔ IsSmooth B S hS f' :=
  let : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  Stack.hasPropertyOnSomeSmoothDiagram_iff_of_flatDeformation B S hS
    (fun _ _ k => Space.IsSmooth B S hS k)
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (fun hX hY hZ p q hp hq => Space.isSmooth_comp B S hS hX hY hZ p q hp hq)
    (fun hF => Space.isSmooth_id B S hS hF)
    (fun D => Space.isSmooth_iff_of_flatDeformationDiagram B S hS D)
    hiB hcartX hcartY houter hrestrict hinner hcoh hYft hXflat hXfp

/-- Under the hypotheses of `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`,
and assuming that syntomicity of morphisms of algebraic spaces is local on the source for the
syntomic precoverage and local on the target for the fpqc precoverage, the restricted 1-morphism
`f` passes the existential smooth-diagram test at syntomicity of morphisms of algebraic spaces if
and only if the ambient 1-morphism `f'` does. -/
@[stacks 0CJC "syntomic"]
theorem isSyntomic_iff_isSyntomic_ambient
    [MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => Space.IsSyntomic B S hS k.hom)
      (Space.Topology.precoverage.{u, u + 1} .syntomic B S hS)]
    [MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => Space.IsSyntomic B S hS k.hom)
      (Space.Topology.precoverage.{u, u + 1} .fpqc B S hS)]
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
    (hYft : IsLocallyOfFiniteType B S hS pY')
    (hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS
        (fun _ _ k => Space.IsSyntomic B S hS k) f.hom ↔
      Stack.HasPropertyOnSomeSmoothDiagram B S hS
        (fun _ _ k => Space.IsSyntomic B S hS k) f'.hom :=
  let : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsSyntomic B S hS k)).IsStableUnderBaseChange :=
    Space.isSyntomic_isStableUnderBaseChange B S hS
  Stack.hasPropertyOnSomeSmoothDiagram_iff_of_flatDeformation B S hS
    (fun _ _ k => Space.IsSyntomic B S hS k)
    (Space.isSyntomic_isSmoothLocalOnSourceAndTarget B S hS)
    (fun hX hY hZ p q hp hq => Space.isSyntomic_comp B S hS hX hY hZ p q hp hq)
    (fun hF => Space.isSyntomic_of_isSmooth B S hS _ (Space.isSmooth_id B S hS hF))
    (fun D => Space.isSyntomic_iff_of_flatDeformationDiagram B S hS D)
    hiB hcartX hcartY houter hrestrict hinner hcoh hYft hXflat hXfp

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
