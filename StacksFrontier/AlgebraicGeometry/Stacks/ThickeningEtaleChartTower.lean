module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation

/-!
# The étale chart tower of a thickening of algebraic stacks

An étale chart tower is a tower of three compatible charts of `ℬ'`, `𝒴'` and `𝒳'` carrying the
hypotheses of Stacks 0CJB, in which the comparison of the chart of `𝒳'` with the 2-fibre product
`V' ×_{𝒴'} 𝒳'` is étale, as in the étale-smooth diagrams of Stacks 0CIF. Its base change along a
thickening `iB : ℬ ⟶ ℬ'` of the base is a flat deformation diagram of algebraic spaces in the
sense of Stacks 0CGW, and its morphism of charts sits in an étale-smooth diagram over the
restricted 1-morphism.

## Main definitions

* `AlgebraicGeometry.Stack.EtaleChartTower`: three compatible charts of `ℬ'`, `𝒴'` and `𝒳'` with
  the hypotheses of Stacks 0CJB read on them, the chart of `𝒴'` smooth and the comparison of the
  chart of `𝒳'` with the 2-fibre product `V' ×_{𝒴'} 𝒳'` **étale**.
* `AlgebraicGeometry.Stack.ThickenedEtaleChartTower`: such a tower together with the three
  iterated 2-fibre products base-changing it along the thickening of the base.
* `AlgebraicGeometry.Stack.ThickenedEtaleChartTower.flatDeformationDiagram`: the flat deformation
  diagram of algebraic spaces it carries.

## Main results

* `AlgebraicGeometry.Stack.ThickenedEtaleChartTower.isPullback_targetSq`,
  `.isPullback_sourceSq` and `.isPullback_sourceBaseSq`: the three base-change squares, read on
  representing presheaves, are pullback squares of algebraic spaces.
* `AlgebraicGeometry.Stack.ThickenedEtaleChartTower.mono_isThickening_iU`, `.mono_isThickening_iV`
  and `.mono_isThickening_iW`: the three thickenings of charts are monomorphisms whose ranges are
  thickenings.
* `AlgebraicGeometry.Stack.exists_thickenedEtaleChartTower`: an étale chart tower can be base
  changed along a thickening of the ambient base.
* `AlgebraicGeometry.Stack.exists_etaleChartTower_of_etaleSmoothDiagram`: an étale-smooth
  diagram of Stacks 0CIF over the ambient 1-morphism yields an étale chart tower, whose top
  morphism of charts is the diagram's top morphism base-changed along a smooth morphism of
  targets.
* `AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_comp_equivalenceOverInvMap`: a
  1-morphism between represented categories fibred in groupoids and the morphism of representing
  presheaves it induces agree up to the two representing equivalences.
* `AlgebraicGeometry.Stack.exists_etaleChart_twoFibreProduct_of_thickenedEtaleChartTower` and
  `AlgebraicGeometry.Stack.exists_etaleDiagram_fWV_of_thickenedEtaleChartTower`: the base change
  of the tower exhibits its morphism of charts in an étale-smooth diagram of Stacks 0CIF over
  the restricted 1-morphism.
* `AlgebraicGeometry.Stack.prop_fWV_of_thickenedEtaleChartTower`: a property tested on every
  étale-smooth diagram over the restricted 1-morphism holds for that morphism of charts.

## References

* [Stacks Project, Tag 0CGW](https://stacks.math.columbia.edu/tag/0CGW)
* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CJB](https://stacks.math.columbia.edu/tag/0CJB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {ℬ ℬ' 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ThickeningEtaleChartTower :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ThickeningEtaleChartTower
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_ThickeningEtaleChartTower B S hS).has_limit _

/-- A tower of charts of a 1-morphism over a base whose top comparison is étale. For
1-morphisms `f' : 𝒳' ⟶ 𝒴'` and `pY' : 𝒴' ⟶ ℬ'` of algebraic stacks over `S`: algebraic spaces
`U'`, `V'`, `W'` with 1-morphisms to `ℬ'`, `𝒴'`, `𝒳'`, morphisms `g' : V' ⟶ U'` and
`h' : W' ⟶ V'` making the two squares 2-commute, the chart of `𝒴'` smooth, every comparison
1-morphism from the cone of the upper square to a 2-fibre product of `(b', f')` étale, and the
hypotheses of Stacks 0CJB on the ambient stacks read on `g'` and `h' ≫ g'`. -/
structure EtaleChartTower (pY' : 𝒴' ⟶ ℬ') (f' : 𝒳' ⟶ 𝒴') where
  /-- the chart of the ambient base -/
  U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the chart of the ambient target -/
  V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the chart of the ambient source -/
  W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `U'` is an algebraic space over `S` -/
  algebraicU : IsAlgebraicSpace B S hS U'
  /-- `V'` is an algebraic space over `S` -/
  algebraicV : IsAlgebraicSpace B S hS V'
  /-- `W'` is an algebraic space over `S` -/
  algebraicW : IsAlgebraicSpace B S hS W'
  /-- the chart 1-morphism of the ambient base -/
  a' : fibredCategory B S hS U' ⟶ ℬ'.val
  /-- the chart 1-morphism of the ambient target -/
  b' : fibredCategory B S hS V' ⟶ 𝒴'.val
  /-- the chart 1-morphism of the ambient source -/
  c' : fibredCategory B S hS W' ⟶ 𝒳'.val
  /-- the morphism of charts of the structure 1-morphism of the ambient target -/
  g' : V' ⟶ U'
  /-- the morphism of charts of the ambient 1-morphism -/
  h' : W' ⟶ V'
  /-- the chart of the ambient target is smooth -/
  smoothB : IsRelativelySmooth B S hS b'
  /-- the square of charts of the structure 1-morphism of the ambient target 2-commutes -/
  targetComm : (associatedMap B S hS g').1 ≫ a' ≅ b' ≫ pY'.hom
  /-- the square of charts of the ambient 1-morphism 2-commutes -/
  sourceComm : (associatedMap B S hS h').1 ≫ b' ≅ c' ≫ f'.hom
  /-- every comparison 1-morphism from the square of charts of the ambient 1-morphism to a
  2-fibre product of the cospan `(b', f')` is étale: the chart of the ambient source is an étale
  chart of that 2-fibre product -/
  etaleSourceComparison : ∀ (Q : Bicategory.TwoCommSq b' f'.hom)
    (_hQ : Bicategory.IsTwoFibreProduct Q)
    (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f'.hom c' b' h' sourceComm) Q),
      IsRelativelyEtale B S hS k.hom
  /-- the chart of the ambient target is locally of finite type over the chart of the base -/
  finiteType : Space.IsLocallyOfFiniteType B S hS g'
  /-- the chart of the ambient source is flat over the chart of the base -/
  flat : Space.IsFlat B S hS (h' ≫ g')
  /-- the chart of the ambient source is locally of finite presentation over the chart of the
  base -/
  finitePresentation : Space.IsLocallyOfFinitePresentation B S hS (h' ≫ g')

/-- An étale chart tower together with its base change along a thickening `iB` of the ambient
base: three 2-fibre product squares, base-changing the chart of the ambient base along `iB`, then
the chart of the ambient target along that, then the chart of the ambient source along that, and
algebraic spaces `U`, `V`, `W` representing their apexes. -/
structure ThickenedEtaleChartTower (iB : ℬ ⟶ ℬ') (pY' : 𝒴' ⟶ ℬ') (f' : 𝒳' ⟶ 𝒴') where
  /-- the étale chart tower of the ambient stacks -/
  tower : EtaleChartTower B S hS pY' f'
  /-- the base change of the chart of the ambient base along the base thickening -/
  AU : Bicategory.TwoCommSq tower.a' iB.hom
  /-- that square is a 2-fibre product -/
  cartAU : Bicategory.IsTwoFibreProduct AU
  /-- the base change of the chart of the ambient target -/
  Qv : Bicategory.TwoCommSq (associatedMap B S hS tower.g').1 AU.fst
  /-- that square is a 2-fibre product -/
  cartQv : Bicategory.IsTwoFibreProduct Qv
  /-- the base change of the chart of the ambient source -/
  Qw : Bicategory.TwoCommSq (associatedMap B S hS tower.h').1 Qv.fst
  /-- that square is a 2-fibre product -/
  cartQw : Bicategory.IsTwoFibreProduct Qw
  /-- the chart of the base of the thickening -/
  U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the chart of the target of the thickening -/
  V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the chart of the source of the thickening -/
  W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `U` is an algebraic space over `S` -/
  algU : IsAlgebraicSpace B S hS U
  /-- `V` is an algebraic space over `S` -/
  algV : IsAlgebraicSpace B S hS V
  /-- `W` is an algebraic space over `S` -/
  algW : IsAlgebraicSpace B S hS W
  /-- `U` represents the apex of the first square -/
  eU : StacksRepresentableCFG.EquivalenceOver AU.pt.val.p
    (presheafOfCategories (U ⋙ typeToCat)).p
  /-- `V` represents the apex of the second square -/
  eV : StacksRepresentableCFG.EquivalenceOver Qv.pt.val.p
    (presheafOfCategories (V ⋙ typeToCat)).p
  /-- `W` represents the apex of the third square -/
  eW : StacksRepresentableCFG.EquivalenceOver Qw.pt.val.p
    (presheafOfCategories (W ⋙ typeToCat)).p

/-- The apex of the canonical 2-fibre product of a 1-morphism from a represented category with a
1-morphism representable by algebraic spaces is represented by an algebraic space. -/
private theorem isRepresentableByAlgebraicSpace_twoFibreProductSquare
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ g f _
    (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g) hg h𝒳

/-- A 2-fibre product of a 1-morphism `k` between represented categories with a 1-morphism `g`
representable by algebraic spaces gives a cartesian square of the representing morphisms. -/
private theorem isPullback_representingMap_fibredCategory_of_isTwoFibreProduct
    {V' U' G T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algV : IsAlgebraicSpace B S hS V')
    {Y : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {k : fibredCategory B S hS V' ⟶ fibredCategory B S hS U'}
    {g : Y ⟶ fibredCategory B S hS U'} (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    {P : Bicategory.TwoCommSq k g} (hP : Bicategory.IsTwoFibreProduct P)
    (eG : StacksRepresentableCFG.EquivalenceOver Y.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver P.pt.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    IsPullback
      (representingMap B S hS P.pt (fibredCategory B S hS V') T V' eT
        (StacksRepresentableCFG.EquivalenceOver.refl _) P.fst)
      (representingMap B S hS P.pt Y T G eT eG P.snd)
      (representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S hS U') V' U'
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) k)
      (representingMap B S hS Y (fibredCategory B S hS U') G U' eG
        (StacksRepresentableCFG.EquivalenceOver.refl _) g) := by
  classical
  obtain ⟨K, -, ⟨eK⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProductSquare B S hS k g hg
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS V' algV)
  exact isPullback_representingMap_of_isTwoFibreProduct B S hS hP V' G U' T K
    (StacksRepresentableCFG.EquivalenceOver.refl _) eG
    (StacksRepresentableCFG.EquivalenceOver.refl _) eT eK

namespace ThickenedEtaleChartTower

variable {B S hS} {iB : ℬ ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'} {f' : 𝒳' ⟶ 𝒴'}

/-- The thickening of the chart of the ambient base of an étale chart tower. -/
noncomputable def iU (C : ThickenedEtaleChartTower B S hS iB pY' f') : C.U ⟶ C.tower.U' :=
  representingMap B S hS C.AU.pt (fibredCategory B S hS C.tower.U') C.U C.tower.U' C.eU
    (StacksRepresentableCFG.EquivalenceOver.refl _) C.AU.fst

/-- The thickening of the chart of the ambient target of an étale chart tower. -/
noncomputable def iV (C : ThickenedEtaleChartTower B S hS iB pY' f') : C.V ⟶ C.tower.V' :=
  representingMap B S hS C.Qv.pt (fibredCategory B S hS C.tower.V') C.V C.tower.V' C.eV
    (StacksRepresentableCFG.EquivalenceOver.refl _) C.Qv.fst

/-- The thickening of the chart of the ambient source of an étale chart tower. -/
noncomputable def iW (C : ThickenedEtaleChartTower B S hS iB pY' f') : C.W ⟶ C.tower.W' :=
  representingMap B S hS C.Qw.pt (fibredCategory B S hS C.tower.W') C.W C.tower.W' C.eW
    (StacksRepresentableCFG.EquivalenceOver.refl _) C.Qw.fst

/-- The structure morphism of the chart of the target over the chart of the base, for an étale
chart tower. -/
noncomputable def gVU (C : ThickenedEtaleChartTower B S hS iB pY' f') : C.V ⟶ C.U :=
  representingMap B S hS C.Qv.pt C.AU.pt C.V C.U C.eV C.eU C.Qv.snd

/-- The morphism of charts of the restricted 1-morphism, for an étale chart tower. -/
noncomputable def fWV (C : ThickenedEtaleChartTower B S hS iB pY' f') : C.W ⟶ C.V :=
  representingMap B S hS C.Qw.pt C.Qv.pt C.W C.V C.eW C.eV C.Qw.snd

/-- The base change of the base thickening to the chart of the ambient base of an étale chart
tower is a relative thickening. -/
theorem isRelativeThickening_AUfst (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) : IsRelativeThickening B S hS C.AU.fst :=
  isRelativeThickening_baseChange B S hS iB.hom C.tower.a'
    (isRelativeThickening_of_isThickening B S hS hiB) C.AU C.cartAU

/-- The base change of the base thickening to the chart of the ambient target of an étale chart
tower is a relative thickening. -/
theorem isRelativeThickening_Qvfst (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) : IsRelativeThickening B S hS C.Qv.fst :=
  isRelativeThickening_baseChange B S hS C.AU.fst _ (C.isRelativeThickening_AUfst hiB)
    C.Qv C.cartQv

/-- The base change of the base thickening to the chart of the ambient source of an étale chart
tower is a relative thickening. -/
theorem isRelativeThickening_Qwfst (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) : IsRelativeThickening B S hS C.Qw.fst :=
  isRelativeThickening_baseChange B S hS C.Qv.fst _ (C.isRelativeThickening_Qvfst hiB)
    C.Qw C.cartQw

/-- The chart of the target is the base change of the chart of the ambient target, for a
thickened étale chart tower. -/
theorem isPullback_targetSq (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) : IsPullback C.iV C.gVU C.tower.g' C.iU := by
  have h := isPullback_representingMap_fibredCategory_of_isTwoFibreProduct B S hS
    C.tower.algebraicV (C.isRelativeThickening_AUfst hiB).1 C.cartQv C.eU C.eV
  rwa [representingMap_associatedMap] at h

/-- The chart of the source is the base change of the chart of the ambient source, for a
thickened étale chart tower. -/
theorem isPullback_sourceSq (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) : IsPullback C.iW C.fWV C.tower.h' C.iV := by
  have h := isPullback_representingMap_fibredCategory_of_isTwoFibreProduct B S hS
    C.tower.algebraicW (C.isRelativeThickening_Qvfst hiB).1 C.cartQw C.eV C.eW
  rwa [representingMap_associatedMap] at h

/-- The chart of the source is the base change of the chart of the ambient source over the chart
of the ambient base, for a thickened étale chart tower. -/
theorem isPullback_sourceBaseSq (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) :
    IsPullback C.iW (C.fWV ≫ C.gVU) (C.tower.h' ≫ C.tower.g') C.iU := by
  have h := isPullback_representingMap_fibredCategory_of_isTwoFibreProduct B S hS
    C.tower.algebraicW (C.isRelativeThickening_AUfst hiB).1
    (Bicategory.isTwoFibreProduct_pasteFst C.Qv C.cartQv C.Qw C.cartQw) C.eU C.eW
  have h2 : IsPullback C.iW
      (representingMap B S hS C.Qw.pt C.AU.pt C.W C.U C.eW C.eU (C.Qw.snd ≫ C.Qv.snd))
      (representingMap B S hS (fibredCategory B S hS C.tower.W')
        (fibredCategory B S hS C.tower.U') C.tower.W' C.tower.U'
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        ((associatedMap B S hS C.tower.h').1 ≫ (associatedMap B S hS C.tower.g').1))
      C.iU := h
  rwa [representingMap_comp B S hS C.W C.V C.U C.eW C.eV C.eU C.Qw.snd C.Qv.snd,
    representingMap_comp B S hS C.tower.W' C.tower.V' C.tower.U'
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (associatedMap B S hS C.tower.h').1 (associatedMap B S hS C.tower.g').1,
    representingMap_associatedMap, representingMap_associatedMap] at h2

/-- The thickening of the chart of the ambient base of an étale chart tower is a monomorphism
whose range is a thickening. -/
theorem mono_isThickening_iU (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) : Mono C.iU ∧
    Space.IsThickening B S hS (⟨C.tower.U', C.tower.algebraicU⟩ : AlgebraicSpaces B S hS)
      (Subfunctor.range C.iU) :=
  mono_and_isThickening_range_representingMap_fst B S hS iB.hom C.tower.a'
    (isRelativeThickening_of_isThickening B S hS hiB) C.AU C.cartAU C.U C.tower.U'
    C.algU C.tower.algebraicU C.eU (StacksRepresentableCFG.EquivalenceOver.refl _)

/-- The thickening of the chart of the ambient target of an étale chart tower is a monomorphism
whose range is a thickening. -/
theorem mono_isThickening_iV (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) : Mono C.iV ∧
    Space.IsThickening B S hS (⟨C.tower.V', C.tower.algebraicV⟩ : AlgebraicSpaces B S hS)
      (Subfunctor.range C.iV) :=
  mono_and_isThickening_range_representingMap_fst B S hS C.AU.fst _
    (C.isRelativeThickening_AUfst hiB) C.Qv C.cartQv C.V C.tower.V'
    C.algV C.tower.algebraicV C.eV (StacksRepresentableCFG.EquivalenceOver.refl _)

/-- The thickening of the chart of the ambient source of an étale chart tower is a monomorphism
whose range is a thickening. -/
theorem mono_isThickening_iW (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) : Mono C.iW ∧
    Space.IsThickening B S hS (⟨C.tower.W', C.tower.algebraicW⟩ : AlgebraicSpaces B S hS)
      (Subfunctor.range C.iW) :=
  mono_and_isThickening_range_representingMap_fst B S hS C.Qv.fst _
    (C.isRelativeThickening_Qvfst hiB) C.Qw C.cartQw C.W C.tower.W'
    C.algW C.tower.algebraicW C.eW (StacksRepresentableCFG.EquivalenceOver.refl _)

/-- The flat deformation diagram of algebraic spaces carried by a thickened étale chart tower:
its ambient row is the tower of charts of the ambient stacks, its restricted row is their base
change along the thickening of the base, and its two cartesian squares are the base-change
squares read on representing presheaves. -/
noncomputable def flatDeformationDiagram (C : ThickenedEtaleChartTower B S hS iB pY' f')
    (hiB : IsThickening iB) :
    Space.FlatDeformationDiagram B S hS where
  X := ⟨C.W, C.algW⟩
  X' := ⟨C.tower.W', C.tower.algebraicW⟩
  Y := ⟨C.V, C.algV⟩
  Y' := ⟨C.tower.V', C.tower.algebraicV⟩
  B := ⟨C.U, C.algU⟩
  B' := ⟨C.tower.U', C.tower.algebraicU⟩
  iX := ObjectProperty.homMk C.iW
  iY := ObjectProperty.homMk C.iV
  iB := ObjectProperty.homMk C.iU
  f := ObjectProperty.homMk C.fWV
  f' := ObjectProperty.homMk C.tower.h'
  g := ObjectProperty.homMk C.gVU
  g' := ObjectProperty.homMk C.tower.g'
  iX_mono := (C.mono_isThickening_iW hiB).1
  iY_mono := (C.mono_isThickening_iV hiB).1
  iB_mono := (C.mono_isThickening_iU hiB).1
  iX_thickening := (C.mono_isThickening_iW hiB).2
  iY_thickening := (C.mono_isThickening_iV hiB).2
  iB_thickening := (C.mono_isThickening_iU hiB).2
  comm_f := ObjectProperty.hom_ext _ (C.isPullback_sourceSq hiB).w
  comm_g := ObjectProperty.hom_ext _ (C.isPullback_targetSq hiB).w
  isPullback_X :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (C.isPullback_sourceBaseSq hiB)
  isPullback_Y := IsPullback.of_map_of_faithful (ObjectProperty.ι _) (C.isPullback_targetSq hiB)
  finiteType_Y' := C.tower.finiteType
  flat_X' := C.tower.flat
  finitePresentation_X' := C.tower.finitePresentation

end ThickenedEtaleChartTower

/-- An étale chart tower can be base-changed along a thickening of the ambient base: there is a
thickened étale chart tower whose `tower` field is the given tower. -/
theorem exists_thickenedEtaleChartTower {iB : ℬ ⟶ ℬ'} (hiB : IsThickening iB)
    {pY' : 𝒴' ⟶ ℬ'} {f' : 𝒳' ⟶ 𝒴'} (T : EtaleChartTower B S hS pY' f') :
    ∃ C : ThickenedEtaleChartTower B S hS iB pY' f', C.tower = T := by
  classical
  set AU : Bicategory.TwoCommSq T.a' iB.hom :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} T.a' iB.hom with hAU
  have cartAU : Bicategory.IsTwoFibreProduct AU :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} T.a' iB.hom
  obtain ⟨U, hU, ⟨eU⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProductSquare B S hS
    T.a' iB.hom hiB.1.1 (isRepresentableByAlgebraicSpace_fibredCategory B S hS T.U' T.algebraicU)
  have hAUfst : IsRelativeThickening B S hS AU.fst :=
    isRelativeThickening_baseChange B S hS iB.hom T.a'
      (isRelativeThickening_of_isThickening B S hS hiB) AU cartAU
  set Qv : Bicategory.TwoCommSq (associatedMap B S hS T.g').1 AU.fst :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} (associatedMap B S hS T.g').1 AU.fst with hQv
  have cartQv : Bicategory.IsTwoFibreProduct Qv :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS T.g').1 AU.fst
  obtain ⟨V, hV, ⟨eV⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProductSquare B S hS
    (associatedMap B S hS T.g').1 AU.fst hAUfst.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS T.V' T.algebraicV)
  have hQvfst : IsRelativeThickening B S hS Qv.fst :=
    isRelativeThickening_baseChange B S hS AU.fst _ hAUfst Qv cartQv
  set Qw : Bicategory.TwoCommSq (associatedMap B S hS T.h').1 Qv.fst :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} (associatedMap B S hS T.h').1 Qv.fst with hQw
  have cartQw : Bicategory.IsTwoFibreProduct Qw :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS T.h').1 Qv.fst
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProductSquare B S hS
    (associatedMap B S hS T.h').1 Qv.fst hQvfst.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS T.W' T.algebraicW)
  exact ⟨{ tower := T, AU := AU, cartAU := cartAU, Qv := Qv, cartQv := cartQv, Qw := Qw
           cartQw := cartQw, U := U, V := V, W := W, algU := hU, algV := hV, algW := hW
           eU := eU, eV := eV, eW := eW }, rfl⟩

/-! ### Reading a 1-morphism of represented categories through the representing equivalences -/

/-- A 1-morphism between categories fibred in groupoids represented by algebraic spaces and the
morphism of representing presheaves it induces agree up to the two representing equivalences:
for `g : 𝒬₁ ⟶ 𝒬₂` with `𝒬₁` represented by `W` and `𝒬₂` by `U`, the 1-morphism of Stacks 0458
attached to the induced morphism `W ⟶ U`, followed by the backward 1-morphism of the equivalence
representing `𝒬₂`, is 2-isomorphic to the backward 1-morphism of the equivalence representing
`𝒬₁` followed by `g`. -/
theorem nonempty_twoIso_associatedMap_comp_equivalenceOverInvMap
    {𝒬₁ 𝒬₂ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {W U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e₁ : StacksRepresentableCFG.EquivalenceOver 𝒬₁.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (e₂ : StacksRepresentableCFG.EquivalenceOver 𝒬₂.val.p
      (presheafOfCategories (U ⋙ typeToCat)).p)
    (g : 𝒬₁ ⟶ 𝒬₂) :
    Nonempty ((associatedMap B S hS
          (representingMap B S hS 𝒬₁ 𝒬₂ W U e₁ e₂ g)).1 ≫ equivalenceOverInvMap B S hS U e₂ ≅
      equivalenceOverInvMap B S hS W e₁ ≫ g) := by
  refine (nonempty_unique_twoIso_of_representingMap_eq B S hS (fibredCategory B S hS W) 𝒬₂ W U
    (StacksRepresentableCFG.EquivalenceOver.refl _) e₂ ?_).map (fun h => h.default)
  rw [representingMap_comp B S hS W U U (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) e₂
      (associatedMap B S hS (representingMap B S hS 𝒬₁ 𝒬₂ W U e₁ e₂ g)).1
      (equivalenceOverInvMap B S hS U e₂),
    representingMap_associatedMap, representingMap_equivalenceOverInvMap, Category.comp_id,
    representingMap_comp B S hS W W U (StacksRepresentableCFG.EquivalenceOver.refl _) e₁ e₂
      (equivalenceOverInvMap B S hS W e₁) g,
    representingMap_equivalenceOverInvMap, Category.id_comp]

/-! ### Building an étale chart tower from an étale-smooth diagram -/

/-- An étale-smooth diagram of Stacks 0CIF over the ambient 1-morphism yields an étale chart
tower. Let the hypotheses of Stacks 0CJB hold for `pY'`, `pX'` and `f'`, and let
`(U'₀, V'₀, a'₀, b'₀, h'₀)` be a 2-commutative square of algebraic spaces over `f'` whose
right-hand vertical 1-morphism is smooth and whose every comparison 1-morphism to a 2-fibre
product of `(b'₀, f')` is étale. Then there are an étale chart tower `T` for `(pY', f')`, a smooth
morphism `β : T.V' ⟶ V'₀` and a surjective morphism `α : T.W' ⟶ U'₀` with
`α ≫ h'₀ = T.h' ≫ β`, such that the induced morphism from `T.W'` to the fibre product of `h'₀`
and `β` is an isomorphism. -/
theorem exists_etaleChartTower_of_etaleSmoothDiagram
    {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'} {f' : 𝒳' ⟶ 𝒴'}
    (houter : f' ≫ pY' ≅ pX')
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX')
    (U'₀ V'₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU'₀ : IsAlgebraicSpace B S hS U'₀) (hV'₀ : IsAlgebraicSpace B S hS V'₀)
    (a'₀ : fibredCategory B S hS U'₀ ⟶ 𝒳'.val)
    (b'₀ : fibredCategory B S hS V'₀ ⟶ 𝒴'.val)
    (h'₀ : U'₀ ⟶ V'₀)
    (η'₀ : (associatedMap B S hS h'₀).1 ≫ b'₀ ≅ a'₀ ≫ f'.hom)
    (hb'₀ : IsRelativelySmooth B S hS b'₀)
    (hcomp'₀ : ∀ (Q : Bicategory.TwoCommSq b'₀ f'.hom)
      (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f'.hom a'₀ b'₀ h'₀ η'₀) Q),
        IsRelativelyEtale B S hS k.hom) :
    ∃ (T : EtaleChartTower B S hS pY' f') (β : T.V' ⟶ V'₀) (α : T.W' ⟶ U'₀)
      (hcomm : α ≫ h'₀ = T.h' ≫ β),
      Space.IsSmooth B S hS β ∧ Space.IsSurjective B S hS α ∧
        IsIso (pullback.lift α T.h' hcomm) := by
  classical
  obtain ⟨U', hU', a', hasm, hasu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS ℬ'.property
  set QY : Bicategory.TwoCommSq a' pY'.hom :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} a' pY'.hom with hQYdef
  have hQY : Bicategory.IsTwoFibreProduct QY :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} a' pY'.hom
  obtain ⟨hQYsndsm, hQYsndsu⟩ := isRelativelySmooth_isSurjectiveOnObjects_snd B S hS
    a' pY'.hom QY hQY hasm hasu
  set Vsq : Bicategory.TwoCommSq b'₀ QY.snd :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} b'₀ QY.snd with hVsqdef
  have hVsq : Bicategory.IsTwoFibreProduct Vsq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b'₀ QY.snd
  obtain ⟨hVsqfstsm, hVsqfstsu⟩ := isRelativelySmooth_isSurjectiveOnObjects_snd B S hS
    QY.snd b'₀ Vsq.swap (Bicategory.isTwoFibreProduct_swap hVsq) hQYsndsm hQYsndsu
  have hVsqsndsm : IsRelativelySmooth B S hS Vsq.snd :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V'₀) 𝒴'.val
      QY.pt b'₀ QY.snd Vsq.swap (Bicategory.isTwoFibreProduct_swap hVsq) hb'₀
  obtain ⟨V'₁, hV'₁, ⟨eV₁⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProductSquare B S hS
    b'₀ QY.snd hQYsndsm.1 (isRepresentableByAlgebraicSpace_fibredCategory B S hS V'₀ hV'₀)
  set κV := equivalenceOverInvMap B S hS V'₁ eV₁ with hκVdef
  have hκVet : IsRelativelyEtale B S hS κV :=
    isRelativelyEtale_equivalenceOverInvMap B S hS V'₁ hV'₁ eV₁
  have hκVsm : IsRelativelySmooth B S hS κV :=
    isRelativelySmooth_of_isRelativelyEtale B S hS κV hκVet
  have hκVeq : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor κV) := by
    show Functor.IsEquivalence eV₁.inv.functor
    exact eV₁.toEquivalence.symm.isEquivalence_functor
  have hκVsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V'₁).val.p Vsq.pt.val.p
      (CatFiberedInGroupoids.homFunctor κV) :=
    isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := Vsq.pt) B S hS V'₁ eV₁
  set ccV := κV ≫ Vsq.snd with hccVdef
  have hccVsm : IsRelativelySmooth B S hS ccV :=
    isRelativelySmooth_comp B S hS κV Vsq.snd hκVsm hVsqsndsm
  set bT := ccV ≫ QY.snd with hbTdef
  have hbTsm : IsRelativelySmooth B S hS bT :=
    isRelativelySmooth_comp B S hS ccV QY.snd hccVsm hQYsndsm
  obtain ⟨eG⟩ := nonempty_twoIso_associatedMap_representingMap B S hS V'₁ U' (ccV ≫ QY.fst)
  set gT := representingMap B S hS (fibredCategory B S hS V'₁) (fibredCategory B S hS U')
    V'₁ U' (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (ccV ≫ QY.fst) with hgTdef
  set δ := κV ≫ Vsq.fst with hδdef
  have hδsm : IsRelativelySmooth B S hS δ :=
    isRelativelySmooth_comp B S hS κV Vsq.fst hκVsm hVsqfstsm
  have hδsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V'₁).val.p
      (fibredCategory B S hS V'₀).val.p (CatFiberedInGroupoids.homFunctor δ) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS V'₁).val.p Vsq.pt.val.p
      (fibredCategory B S hS V'₀).val.p (CatFiberedInGroupoids.homFunctor κV)
      (CatFiberedInGroupoids.homFunctor Vsq.fst)
      (CatFiberedInGroupoids.homFunctor_comp_p Vsq.fst) hκVsu hVsqfstsu
  set Dsq : Bicategory.TwoCommSq b'₀ f'.hom :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} b'₀ f'.hom with hDsqdef
  have hDsq : Bicategory.IsTwoFibreProduct Dsq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b'₀ f'.hom
  set cc₀ := Bicategory.twoFibreProductPreHom hDsq
    (diagramCone B S hS f'.hom a'₀ b'₀ h'₀ η'₀) with hcc₀def
  have hcc₀et : IsRelativelyEtale B S hS cc₀.hom := hcomp'₀ Dsq hDsq cc₀
  set Esq : Bicategory.TwoCommSq δ Dsq.fst :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} δ Dsq.fst with hEsqdef
  have hEsq : Bicategory.IsTwoFibreProduct Esq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} δ Dsq.fst
  obtain ⟨hEsqsndsm, hEsqsndsu⟩ := isRelativelySmooth_isSurjectiveOnObjects_snd B S hS
    δ Dsq.fst Esq hEsq hδsm hδsu
  have hSX : Bicategory.IsTwoFibreProduct (Dsq.pasteFst Esq) :=
    Bicategory.isTwoFibreProduct_pasteFst Dsq hDsq Esq hEsq
  set θV : δ ≫ b'₀ ≅ bT := Bicategory.whiskerLeftIso κV Vsq.iso with hθVdef
  set R : Bicategory.TwoCommSq bT f'.hom := (Dsq.pasteFst Esq).reindexFst θV with hRdef
  have hR : Bicategory.IsTwoFibreProduct R := Bicategory.isTwoFibreProduct_reindexFst θV hSX
  set Psq : Bicategory.TwoCommSq cc₀.hom Esq.snd :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} cc₀.hom Esq.snd with hPsqdef
  have hPsq : Bicategory.IsTwoFibreProduct Psq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} cc₀.hom Esq.snd
  obtain ⟨W'₁, hW'₁, ⟨eW₁⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProductSquare B S hS
    cc₀.hom Esq.snd hEsqsndsm.1 (isRepresentableByAlgebraicSpace_fibredCategory B S hS U'₀ hU'₀)
  have hPsqsndet : IsRelativelyEtale B S hS Psq.snd :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS U'₀) Dsq.pt Esq.pt
      cc₀.hom Esq.snd Psq.swap (Bicategory.isTwoFibreProduct_swap hPsq) hcc₀et
  obtain ⟨hPsqfstsm, hPsqfstsu⟩ := isRelativelySmooth_isSurjectiveOnObjects_snd B S hS
    Esq.snd cc₀.hom Psq.swap (Bicategory.isTwoFibreProduct_swap hPsq) hEsqsndsm hEsqsndsu
  set κW := equivalenceOverInvMap B S hS W'₁ eW₁ with hκWdef
  have hκWeq : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor κW) := by
    show Functor.IsEquivalence eW₁.inv.functor
    exact eW₁.toEquivalence.symm.isEquivalence_functor
  have hκWsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS W'₁).val.p Psq.pt.val.p
      (CatFiberedInGroupoids.homFunctor κW) :=
    isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := Psq.pt) B S hS W'₁ eW₁
  set ccW := κW ≫ Psq.snd with hccWdef
  have hccWet : IsRelativelyEtale B S hS ccW :=
    isRelativelyEtale_of_isEquivalence_comp B S hS κW Psq.snd hκWeq hPsqsndet
  obtain ⟨eH⟩ := nonempty_twoIso_associatedMap_representingMap B S hS W'₁ V'₁ (ccW ≫ R.fst)
  set hT := representingMap B S hS (fibredCategory B S hS W'₁) (fibredCategory B S hS V'₁)
    W'₁ V'₁ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (ccW ≫ R.fst) with hhTdef
  set TX : Bicategory.TwoCommSq QY.snd f'.hom :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} QY.snd f'.hom with hTXdef
  have hTX : Bicategory.IsTwoFibreProduct TX :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} QY.snd f'.hom
  set Gq : Bicategory.TwoCommSq ccV TX.fst :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} ccV TX.fst with hGqdef
  have hGq : Bicategory.IsTwoFibreProduct Gq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} ccV TX.fst
  have hGqsndsm : IsRelativelySmooth B S hS Gq.snd :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V'₁) QY.pt
      TX.pt ccV TX.fst Gq.swap (Bicategory.isTwoFibreProduct_swap hGq) hccVsm
  set e₁ := Bicategory.twoFibreProductPreHom
    (Bicategory.isTwoFibreProduct_pasteFst TX hTX Gq hGq) R with he₁def
  have he₁eq : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e₁.hom) :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hR
      (Bicategory.isTwoFibreProduct_pasteFst TX hTX Gq hGq) e₁
  set ccX := ccW ≫ e₁.hom ≫ Gq.snd with hccXdef
  have hccXsm : IsRelativelySmooth B S hS ccX :=
    isRelativelySmooth_comp B S hS ccW (e₁.hom ≫ Gq.snd)
      (isRelativelySmooth_of_isRelativelyEtale B S hS ccW hccWet)
      (isRelativelySmooth_of_isEquivalence_comp B S hS e₁.hom Gq.snd he₁eq hGqsndsm)
  have hQX : Bicategory.IsTwoFibreProduct
      ((QY.pasteSnd TX).reindexSnd (algebraicStacksTwoIsoHom B S hS houter)) :=
    Bicategory.isTwoFibreProduct_reindexSnd _
      (Bicategory.isTwoFibreProduct_pasteSnd QY hQY TX hTX)
  have hiso : ccX ≫ ((QY.pasteSnd TX).reindexSnd
      (algebraicStacksTwoIsoHom B S hS houter)).fst ≅ (ccW ≫ R.fst) ≫ (ccV ≫ QY.fst) :=
    (Bicategory.whiskerLeftIso ccW (Bicategory.whiskerLeftIso e₁.hom
        (Bicategory.whiskerRightIso Gq.iso QY.fst))).symm ≪≫
      Bicategory.whiskerLeftIso ccW
        (Bicategory.whiskerRightIso e₁.isoFst.symm (ccV ≫ QY.fst))
  have hflatEvery : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ k => Space.IsFlat B S hS k) pX'.hom :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsFlat B S hS k) (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      𝒳'.property ℬ'.property pX'.hom).2
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS pX').1 hXflat)
  have hchart : ∀ P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      HasPropertyOnEverySmoothDiagram B S hS P pX'.hom → P (hT ≫ gT) := by
    intro P hP
    rw [hhTdef, hgTdef, ← representingMap_comp B S hS W'₁ V'₁ U'
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (ccW ≫ R.fst) (ccV ≫ QY.fst),
      representingMap_congr_twoIso B S hS W'₁ U'
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) hiso.symm]
    exact prop_representingMap_fst_of_smooth_comparison B S hS P pX'.hom hP U' W'₁ hU' hW'₁
      a' hasm _ hQX _ hccXsm
  have hZsq : Bicategory.IsTwoFibreProduct
      ((Esq.swap.pasteFst Psq).reindexFst cc₀.isoFst.symm) :=
    Bicategory.isTwoFibreProduct_reindexFst _
      (Bicategory.isTwoFibreProduct_pasteFst Esq.swap
        (Bicategory.isTwoFibreProduct_swap hEsq) Psq hPsq)
  set β := representingMap B S hS (fibredCategory B S hS V'₁) (fibredCategory B S hS V'₀)
    V'₁ V'₀ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) δ with hβdef
  set α := representingMap B S hS (fibredCategory B S hS W'₁) (fibredCategory B S hS U'₀)
    W'₁ U'₀ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (κW ≫ Psq.fst) with hαdef
  have hinvW : representingMap B S hS (fibredCategory B S hS W'₁) Psq.pt W'₁ W'₁
      (StacksRepresentableCFG.EquivalenceOver.refl _) eW₁ κW = 𝟙 W'₁ := by
    rw [hκWdef]
    exact representingMap_equivalenceOverInvMap B S hS W'₁ eW₁
  have hαeq : α = representingMap B S hS Psq.pt (fibredCategory B S hS U'₀) W'₁ U'₀ eW₁
      (StacksRepresentableCFG.EquivalenceOver.refl _) Psq.fst := by
    have h1 := representingMap_comp B S hS W'₁ W'₁ U'₀
      (StacksRepresentableCFG.EquivalenceOver.refl _) eW₁
      (StacksRepresentableCFG.EquivalenceOver.refl _) κW Psq.fst
    rwa [hinvW, Category.id_comp] at h1
  have hhTeq : hT = representingMap B S hS Psq.pt (fibredCategory B S hS V'₁) W'₁ V'₁ eW₁
      (StacksRepresentableCFG.EquivalenceOver.refl _) (Psq.snd ≫ Esq.fst) := by
    have h1 := representingMap_comp B S hS W'₁ W'₁ V'₁
      (StacksRepresentableCFG.EquivalenceOver.refl _) eW₁
      (StacksRepresentableCFG.EquivalenceOver.refl _) κW (Psq.snd ≫ Esq.fst)
    rwa [hinvW, Category.id_comp] at h1
  have hsq : IsPullback α hT h'₀ β := by
    have h := isPullback_representingMap_fibredCategory_of_isTwoFibreProduct B S hS hU'₀
      hδsm.1 hZsq (StacksRepresentableCFG.EquivalenceOver.refl _) eW₁
    rw [representingMap_associatedMap] at h
    rwa [hαeq, hhTeq]
  have hcomm : α ≫ h'₀ = hT ≫ β := hsq.w
  have hβsm : Space.IsSmooth B S hS β :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS δ hδsm.1 V'₁ V'₀ hV'₁ hV'₀
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).1 hδsm
  have hαsu : Space.IsSurjective B S hS α :=
    isSurjective_representingMap_of_isSurjectiveOnObjects B S hS (κW ≫ Psq.fst) W'₁ U'₀
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS W'₁).val.p Psq.pt.val.p
        (fibredCategory B S hS U'₀).val.p (CatFiberedInGroupoids.homFunctor κW)
        (CatFiberedInGroupoids.homFunctor Psq.fst)
        (CatFiberedInGroupoids.homFunctor_comp_p Psq.fst) hκWsu hPsqfstsu)
  have hliftiso : IsIso (pullback.lift α hT hcomm) := by
    have hle : pullback.lift α hT hcomm = hsq.isoPullback.hom := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, hsq.isoPullback_hom_fst]
      · rw [pullback.lift_snd, hsq.isoPullback_hom_snd]
    rw [hle]
    infer_instance
  refine ⟨{ U' := U', V' := V'₁, W' := W'₁
            algebraicU := hU', algebraicV := hV'₁, algebraicW := hW'₁
            a' := a', b' := bT, c' := ccW ≫ R.snd
            g' := gT, h' := hT
            smoothB := hbTsm
            targetComm := Bicategory.whiskerRightIso eG a' ≪≫ Bicategory.whiskerLeftIso ccV QY.iso
            sourceComm := Bicategory.whiskerRightIso eH bT ≪≫ Bicategory.whiskerLeftIso ccW R.iso
            etaleSourceComparison := isRelativelyEtale_preHom_diagramCone_of_chart B S hS
              f'.hom bT R hR ccW hccWet hT eH
            finiteType := prop_representingMap_fst_of_smooth_comparison B S hS
              (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k) pY'.hom hYft U' V'₁ hU' hV'₁
              a' hasm QY hQY ccV hccVsm
            flat := hchart _ hflatEvery
            finitePresentation := hchart _ hXfp },
    β, α, hcomm, hβsm, hαsu, hliftiso⟩

/-! ### The universal étale-smooth test on the morphism of charts -/

/-- For a thickened étale chart tower `C` and the 1-morphism `f : PX.pt ⟶ PY.pt` that `f'`
induces between the base changes of `pX'` and `pY'` along `iB`, there are a smooth 1-morphism
`bq` from the apex of the second base-change square of `C` to `PY.pt`, a 2-fibre product `Q` of
the cospan `(bq, f)`, and an étale 1-morphism `ν` from the apex of the third base-change square to
the apex of `Q`, such that `C.Qw.snd` is 2-isomorphic to `ν ≫ Q.fst`. -/
theorem exists_etaleChart_twoFibreProduct_of_thickenedEtaleChartTower
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
    (C : ThickenedEtaleChartTower B S hS iB pY' f') :
    ∃ (bq : C.Qv.pt ⟶ PY.pt.val) (Q : Bicategory.TwoCommSq bq f.hom)
      (_hQ : Bicategory.IsTwoFibreProduct Q) (ν : C.Qw.pt ⟶ Q.pt),
      IsRelativelySmooth B S hS bq ∧ IsRelativelyEtale B S hS ν ∧
        Nonempty (C.Qw.snd ≅ ν ≫ Q.fst) := by
  classical
  have hPYu : Bicategory.IsTwoFibreProduct PY.underlying :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS PY hcartY
  have hPXu : Bicategory.IsTwoFibreProduct PX.underlying :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS PX hcartX
  have hSx : Bicategory.IsTwoFibreProduct
      (PX.underlying.reindexFst (algebraicStacksTwoIsoHom B S hS houter).symm) :=
    Bicategory.isTwoFibreProduct_reindexFst _ hPXu
  set XX := Bicategory.pasteInnerSq PY.underlying
    (restrictionPreHom B S hS PX PY houter hrestrict hinner hcoh) with hXXdef
  have hXX : Bicategory.IsTwoFibreProduct XX :=
    isTwoFibreProduct_pasteInnerSq B S hS PY.underlying hPYu hSx _
  have hGV : Bicategory.IsTwoFibreProduct
      ((C.AU.pasteFst C.Qv).reindexFst C.tower.targetComm) :=
    Bicategory.isTwoFibreProduct_reindexFst _
      (Bicategory.isTwoFibreProduct_pasteFst C.AU C.cartAU C.Qv C.cartQv)
  set cV := Bicategory.twoFibreProductPreHom hPYu
    (Bicategory.pasteOuterSq C.tower.b' ((C.AU.pasteFst C.Qv).reindexFst C.tower.targetComm))
    with hcVdef
  have hMV : Bicategory.IsTwoFibreProduct (Bicategory.pasteInnerSq PY.underlying cV) :=
    isTwoFibreProduct_pasteInnerSq B S hS PY.underlying hPYu hGV cV
  have hcVsm : IsRelativelySmooth B S hS cV.hom :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS C.tower.V') 𝒴'.val PY.pt.val C.tower.b' PY.underlying.fst
      (Bicategory.pasteInnerSq PY.underlying cV).swap
      (Bicategory.isTwoFibreProduct_swap hMV) C.tower.smoothB
  set Dsq := twoFibreProductSquare.{u, u, u + 1, u + 1} C.tower.b' f'.hom with hDsqdef
  have hDsq : Bicategory.IsTwoFibreProduct Dsq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} C.tower.b' f'.hom
  set cc := Bicategory.twoFibreProductPreHom hDsq
    (diagramCone B S hS f'.hom C.tower.c' C.tower.b' C.tower.h' C.tower.sourceComm) with hccdef
  have hccet : IsRelativelyEtale B S hS cc.hom := C.tower.etaleSourceComparison Dsq hDsq cc
  set Ev := twoFibreProductSquare.{u, u, u + 1, u + 1} C.Qv.fst Dsq.fst with hEvdef
  have hEv : Bicategory.IsTwoFibreProduct Ev :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} C.Qv.fst Dsq.fst
  set Pc := twoFibreProductSquare.{u, u, u + 1, u + 1} Ev.snd cc.hom with hPcdef
  have hPc : Bicategory.IsTwoFibreProduct Pc :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Ev.snd cc.hom
  have hPcfstet : IsRelativelyEtale B S hS Pc.fst :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS C.tower.W') Dsq.pt Ev.pt
      cc.hom Ev.snd Pc hPc hccet
  have hRc : Bicategory.IsTwoFibreProduct (Ev.swap.pasteFst Pc.swap) :=
    Bicategory.isTwoFibreProduct_pasteFst Ev.swap (Bicategory.isTwoFibreProduct_swap hEv)
      Pc.swap (Bicategory.isTwoFibreProduct_swap hPc)
  have hQwr : Bicategory.IsTwoFibreProduct (C.Qw.reindexFst cc.isoFst) :=
    Bicategory.isTwoFibreProduct_reindexFst _ C.cartQw
  set e₀ := Bicategory.twoFibreProductPreHom hRc (C.Qw.reindexFst cc.isoFst) with he₀def
  have he₀eq : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e₀.hom) :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hQwr hRc e₀
  have hGv : Bicategory.IsTwoFibreProduct ((Dsq.pasteFst Ev).reindexFst cV.isoFst) :=
    Bicategory.isTwoFibreProduct_reindexFst _
      (Bicategory.isTwoFibreProduct_pasteFst Dsq hDsq Ev hEv)
  set pv := Bicategory.twoFibreProductPreHom (Bicategory.isTwoFibreProduct_swap hXX)
    (Bicategory.pasteOuterSq cV.hom ((Dsq.pasteFst Ev).reindexFst cV.isoFst)) with hpvdef
  set Q₁ := Bicategory.pasteInnerSq XX.swap pv with hQ₁def
  have hQ₁ : Bicategory.IsTwoFibreProduct Q₁ :=
    isTwoFibreProduct_pasteInnerSq B S hS XX.swap (Bicategory.isTwoFibreProduct_swap hXX) hGv pv
  exact ⟨cV.hom, Q₁, hQ₁, e₀.hom ≫ Pc.fst, hcVsm,
    isRelativelyEtale_of_isEquivalence_comp B S hS e₀.hom Pc.fst he₀eq hPcfstet,
    ⟨e₀.isoSnd⟩⟩

/-- The morphism of charts of a thickened étale chart tower sits in an étale-smooth diagram of
Stacks 0CIF over the restricted 1-morphism `f`: there are 1-morphisms `b` and `a` from the
algebraic spaces `C.V` and `C.W` to `PY.pt` and `PX.pt`, and a 2-isomorphism `η` making the
square over `C.fWV` and `f` 2-commute, such that `b` is smooth and every comparison 1-morphism
from that square to a 2-fibre product of `(b, f)` is étale. -/
theorem exists_etaleDiagram_fWV_of_thickenedEtaleChartTower
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
    (C : ThickenedEtaleChartTower B S hS iB pY' f') :
    ∃ (b : algebraicSpaceStack.{u, w} B S hS C.V C.algV ⟶ PY.pt)
      (a : algebraicSpaceStack.{u, w} B S hS C.W C.algW ⟶ PX.pt)
      (η : (associatedMap B S hS C.fWV).1 ≫ b.hom ≅ a.hom ≫ f.hom),
      IsRelativelySmooth B S hS b.hom ∧
        ∀ (Q : Bicategory.TwoCommSq b.hom f.hom) (_hQ : Bicategory.IsTwoFibreProduct Q)
          (k : Bicategory.TwoCommSq.PreHom
            (diagramCone B S hS f.hom a.hom b.hom C.fWV η) Q),
            IsRelativelyEtale B S hS k.hom := by
  classical
  obtain ⟨bq, Q₁, hQ₁, ν, hbqsm, hνet, ⟨ε⟩⟩ :=
    exists_etaleChart_twoFibreProduct_of_thickenedEtaleChartTower B S hS hcartX hcartY houter
      hrestrict hinner hcoh C
  set κV := equivalenceOverInvMap B S hS C.V C.eV with hκVdef
  set κW := equivalenceOverInvMap B S hS C.W C.eW with hκWdef
  have hκVet : IsRelativelyEtale B S hS κV :=
    isRelativelyEtale_equivalenceOverInvMap B S hS C.V C.algV C.eV
  have hκWeq : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor κW) := by
    show Functor.IsEquivalence C.eW.inv.functor
    exact C.eW.toEquivalence.symm.isEquivalence_functor
  set bhom := κV ≫ bq with hbhomdef
  have hbsm : IsRelativelySmooth B S hS bhom :=
    isRelativelySmooth_comp B S hS κV bq
      (isRelativelySmooth_of_isRelativelyEtale B S hS κV hκVet) hbqsm
  have hωet : IsRelativelyEtale B S hS (κW ≫ ν) :=
    isRelativelyEtale_of_isEquivalence_comp B S hS κW ν hκWeq hνet
  obtain ⟨θ⟩ :=
    nonempty_twoIso_associatedMap_comp_equivalenceOverInvMap B S hS C.eW C.eV C.Qw.snd
  set Tsq : Bicategory.TwoCommSq κV Q₁.fst :=
    { pt := fibredCategory B S hS C.W
      fst := (associatedMap B S hS C.fWV).1
      snd := κW ≫ ν
      iso := θ ≪≫ Bicategory.whiskerLeftIso κW ε } with hTsqdef
  set Lq := twoFibreProductSquare.{u, u, u + 1, u + 1} κV Q₁.fst with hLqdef
  have hLq : Bicategory.IsTwoFibreProduct Lq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} κV Q₁.fst
  have hLqsndet : IsRelativelyEtale B S hS Lq.snd :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS C.V) C.Qv.pt Q₁.pt
      κV Q₁.fst Lq.swap (Bicategory.isTwoFibreProduct_swap hLq) hκVet
  set m := Bicategory.twoFibreProductPreHom hLq Tsq with hmdef
  have hmet : IsRelativelyEtale B S hS m.hom :=
    isRelativelyEtale_of_comp B S hS m.hom Lq.snd
      (isRelativelyEtale_congr_twoIso B S hS m.isoSnd hωet) hLqsndet
  have hQ₂ : Bicategory.IsTwoFibreProduct (Q₁.pasteFst Lq) :=
    Bicategory.isTwoFibreProduct_pasteFst Q₁ hQ₁ Lq hLq
  exact ⟨Bicategory.InducedBicategory.mkHom bhom,
    Bicategory.InducedBicategory.mkHom (m.hom ≫ (Q₁.pasteFst Lq).snd),
    Bicategory.whiskerRightIso m.isoFst bhom ≪≫
      Bicategory.whiskerLeftIso m.hom (Q₁.pasteFst Lq).iso,
    hbsm,
    fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom bhom
      (Q₁.pasteFst Lq) hQ₂ m.hom hmet C.fWV m.isoFst Q hQ k⟩

/-- A property tested on every étale-smooth diagram over the restricted 1-morphism holds for the
morphism of charts of a thickened étale chart tower. -/
theorem prop_fWV_of_thickenedEtaleChartTower
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
    (hfP : HasPropertyOnEveryEtaleSmoothDiagram B S hS P f)
    (C : ThickenedEtaleChartTower B S hS iB pY' f') :
    P (ObjectProperty.homMk C.fWV :
      (⟨C.W, C.algW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C.V, C.algV⟩) := by
  obtain ⟨b, a, η, hbsm, hcompar⟩ := exists_etaleDiagram_fWV_of_thickenedEtaleChartTower
    B S hS hcartX hcartY houter hrestrict hinner hcoh C
  exact hfP C.W C.V C.algW C.algV a b C.fWV η hbsm hcompar

end AlgebraicGeometry.Stack

end
