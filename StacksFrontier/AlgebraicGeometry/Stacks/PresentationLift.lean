module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Lifting a smooth surjective scheme presentation along a morphism of algebraic stacks

Let `S` be a scheme contained in a big fppf site, let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S`, and let `y : (Sch/V)_fppf ⟶ 𝒴` be surjective and smooth. **Stacks 04T1** says
that there are a scheme `U` over `S` and a 2-commutative square

```
  (Sch/U)_fppf  --a-->  (Sch/V)_fppf
       |                     |
       x                     y
       v                     v
       𝒳        --f-->       𝒴
```

with `x` surjective and smooth.

The proof takes a smooth surjective presentation `z : (Sch/W)_fppf ⟶ 𝒳` of `𝒳`, forms the
algebraic space `F` representing the base change of `y` along the point `z ≫ f` of `𝒴` over `W`
(**Stacks 0402**), and takes a scheme atlas `T ⟶ F`. A section of `F` over `T` is a factorization
of `T ⟶ W` through a scheme `U` over `W` together with a point of the 2-fibre product there; `U`
is the scheme sought, `x` is the composite `(Sch/U)_fppf ⟶ (Sch/W)_fppf ⟶ 𝒳`, and `a` is produced
from the second projection of the 2-fibre product by the 2-Yoneda lemma. Surjectivity and
smoothness of `x` come from those of `U ⟶ W` — a composite of the atlas with the structure
morphism `F ⟶ W`, which is surjective and smooth because `y` is — and of `z`.

## Main definitions

* `CategoryTheory.Functor.TwoYoneda.basedIsoOfEvaluationIso`: a 2-isomorphism of 1-morphisms out
  of a represented category, produced from an isomorphism of their values in a fibre.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_yoneda_map`: a morphism of schemes over
  `S` is representable by algebraic spaces as a morphism of representable presheaves.
* `AlgebraicGeometry.Stack.associatedMapSliceComparisonIso`: the square identifying the
  1-morphism of represented categories induced by a morphism of schemes with the 1-morphism of
  Stacks 0458 attached to the corresponding morphism of representable presheaves.
* `AlgebraicGeometry.Stack.exists_smoothSurjectivePresentation_lift`: **Stacks 04T1**.

## Implementation notes

The relative property of the 1-morphism `(Sch/U)_fppf ⟶ (Sch/V)_fppf` induced by a morphism of
schemes is `AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap`, and is used here
as a black box. The comparison apparatus it was first obtained from is kept here: the slice over
`U` is the category of elements of the presheaf `h_U` it represents
(`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`), and
`AlgebraicGeometry.Stack.associatedMapSliceComparisonIso` is the resulting 2-commutative square
with the 1-morphism of Stacks 0458 attached to `h_q`. That comparison costs a single object
equality in a fibre, whereas identifying the two composite functors on the nose is a defeq the
kernel cannot check in reasonable time.

The hypothesis that `𝒴` is an algebraic stack is the one the source makes; the proof does not use
it, since representability and the relative properties of `y` are hypotheses of their own.

The 2-commutativity of the square is produced in the fibre of `𝒴` over `U` and transported back
along the 2-Yoneda evaluation functor, which is full and faithful. Both composites evaluate to
objects of that fibre: `x ≫ f` to the image under `z ≫ f` of the chosen section, and `a ≫ y` to
the image under `y` of the second projection; the comparison isomorphism of the 2-fibre product
point is exactly an isomorphism between them.

## References

* [Stacks Project, Tag 0402](https://stacks.math.columbia.edu/tag/0402)
* [Stacks Project, Tag 04T1](https://stacks.math.columbia.edu/tag/04T1)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory

universe u

/-- A 2-isomorphism of 1-morphisms out of the category over `C` represented by `U` may be given by
an isomorphism of their values in the fibre of the target over `U`: the 2-Yoneda evaluation functor
of **Stacks 004B** is full and faithful. -/
noncomputable def Functor.TwoYoneda.basedIsoOfEvaluationIso {C : Type (u + 1)} [Category.{u} C]
    {D : Type (u + 1)} [Category.{u} D] (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (e : (Functor.twoYonedaEvaluation p U).obj F ≅
      (Functor.twoYonedaEvaluation p U).obj G) : F ≅ G :=
  have : (Functor.twoYonedaEvaluation p U).Faithful :=
    Functor.twoYonedaEvaluation_faithful p hp U
  have : (Functor.twoYonedaEvaluation p U).Full := Functor.twoYonedaEvaluation_full p hp U
  (Functor.twoYonedaEvaluation p U).preimageIso e

end CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The 1-morphism of represented categories fibred in groupoids induced by a morphism of schemes
over `S` is representable by algebraic spaces: its target is representable by an algebraic space,
so this is condition (3) of Stacks 045G for that target. -/
theorem isRepresentableByAlgebraicSpaces_overMapBased {U V : BigFppfOver B S hS} (q : U ⟶ V) :
    IsRepresentableByAlgebraicSpaces B S hS (overMapBased B S hS q) :=
  isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS
    (schemeFibredCategory B S hS V)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) U (overMapBased B S hS q)

/-- The comparison 1-morphism from the category represented by a scheme `U` over `S` to the
category of elements of the presheaf `h_U` it represents, as a based functor: it is the forward
half of `CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, hence an equivalence
over the site. -/
def sliceElementsComparison (U : BigFppfOver B S hS) :
    (schemeFibredCategory B S hS U).val ⥤ᵇ (fibredCategory B S hS (yoneda.obj U)).val :=
  ⟨(PresheafOfCategories.sliceElementsEquivalenceOver U).hom.functor,
    (PresheafOfCategories.sliceElementsEquivalenceOver U).hom.w⟩

/-- The comparison functor `sliceElementsComparison` from the category represented by `U` to the
category of elements of `h_U` is an equivalence of categories. -/
instance isEquivalence_sliceElementsComparison (U : BigFppfOver B S hS) :
    Functor.IsEquivalence (sliceElementsComparison B S hS U).toFunctor :=
  (PresheafOfCategories.sliceElementsEquivalenceOver U).isEquivalence_hom_functor

/-- A morphism `q : U ⟶ V` of schemes over `S` is representable by algebraic spaces as a morphism
`h_U ⟶ h_V` of presheaves: the fibre product of two representable algebraic spaces over a
representable algebraic space is an algebraic space, by Stacks 02X2. -/
theorem isRepresentableByAlgebraicSpaces_yoneda_map {U V : BigFppfOver B S hS} (q : U ⟶ V) :
    Space.IsRepresentableByAlgebraicSpaces B S hS (yoneda.map q) := fun T ξ =>
  isAlgebraicSpace_pullback B S hS ξ (yoneda.map q) (isAlgebraicSpace_yoneda B S hS T)
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)

/-- The square identifying the 1-morphism of represented categories induced by `q : U ⟶ V` with
the 1-morphism of Stacks 0458 attached to `h_q : h_U ⟶ h_V`, read through the identification of
each slice with the category of elements of the presheaf it represents.

Both composites send the terminal object `𝟙 U` of the slice over `U` to the element `𝟙 U ≫ q` of
`h_V`, which is `AlgebraicGeometry.Stack.associatedMap_obj`; the 2-Yoneda lemma turns that single
object equality into the 2-isomorphism. -/
noncomputable def associatedMapSliceComparisonIso {U V : BigFppfOver B S hS} (q : U ⟶ V) :
    BasedFunctor.comp (sliceElementsComparison B S hS U)
        (associatedMap B S hS (yoneda.map q)).1.hom ≅
      BasedFunctor.comp (overMapBased B S hS q) (sliceElementsComparison B S hS V) :=
  Functor.TwoYoneda.basedIsoOfEvaluationIso (fibredCategory B S hS (yoneda.obj V)).val.p
    (fibredCategory B S hS (yoneda.obj V)).isFiberedInGroupoids U
    (eqToIso (Subtype.ext (associatedMap_obj B S hS (yoneda.map q) ⟨U, Discrete.mk (𝟙 U)⟩)))

variable {B S hS}

/-- A relative property `P` of the composite `(Sch/U)_fppf ⟶ (Sch/W)_fppf ⟶ 𝒳` follows from `P`
for `q : U ⟶ W` as a map of representable presheaves and for the second map. -/
private theorem hasRelativeProperty_schemeFibredCategoryMap_comp
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsStableUnderComposition]
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {U W : BigFppfOver B S hS} (q : U ⟶ W) (z : schemeFibredCategory B S hS W ⟶ 𝒳)
    (hz : IsRepresentableByAlgebraicSpaces B S hS z.hom)
    (hq : P (ObjectProperty.homMk (yoneda.map q) :
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩))
    (hPz : HasRelativeProperty.{u, u, u + 1, u} B S hS P z hz) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P (schemeFibredCategoryMap B S hS q ≫ z)
      (isRepresentableByAlgebraicSpaces_comp B S hS _ z
        (isRepresentableByAlgebraicSpaces_overMapBased B S hS q) hz) :=
  hasRelativeProperty_comp.{u, u, u + 1, u} B S hS P (schemeFibredCategoryMap B S hS q) z
    (isRepresentableByAlgebraicSpaces_overMapBased B S hS q) hz
    (hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS P q hq) hPz

/-- **Stacks 04T1.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`y : (Sch/V)_fppf ⟶ 𝒴` be surjective and smooth. Then there are a scheme `U` over `S`, a
1-morphism `x : (Sch/U)_fppf ⟶ 𝒳` which is surjective and smooth, and a 1-morphism
`a : (Sch/U)_fppf ⟶ (Sch/V)_fppf` making the square `x ≫ f ≅ a ≫ y` 2-commute.

Surjectivity and smoothness are the relative properties of Stacks 03YK for
`AlgebraicGeometry.Space.surjectiveMorphismProperty` and
`AlgebraicGeometry.Space.smoothMorphismProperty`. -/
@[stacks 04T1]
theorem exists_smoothSurjectivePresentation_lift
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (_h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴) (V : BigFppfOver B S hS) (y : schemeFibredCategory B S hS V ⟶ 𝒴)
    (hy : IsRepresentableByAlgebraicSpaces B S hS y.hom)
    (hysurj : HasRelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS) y hy)
    (hysmooth : HasRelativeProperty B S hS (Space.smoothMorphismProperty B S hS) y hy) :
    ∃ (U : BigFppfOver B S hS) (x : schemeFibredCategory B S hS U ⟶ 𝒳)
      (a : schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V)
      (hx : IsRepresentableByAlgebraicSpaces B S hS x.hom),
      Nonempty (x ≫ f ≅ a ≫ y) ∧
        HasRelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS) x hx ∧
          HasRelativeProperty B S hS (Space.smoothMorphismProperty B S hS) x hx := by
  classical
  obtain ⟨h𝒳fib, -, h𝒳diag, W, z, hzrep, hzproperties⟩ := h𝒳
  -- the composite point `z ≫ f` of `𝒴` over `W`, read on the big fppf site of `W`
  let zf : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒴.val := BasedFunctor.comp z f.hom
  let G : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒴.val.obj :=
    Over.iteratedSliceBackward W ⋙ zf.toFunctor
  have hG : G ⋙ 𝒴.val.p = Over.map W.hom :=
    (Functor.assoc _ _ _).trans
      ((congrArg (Over.iteratedSliceBackward W ⋙ ·) zf.w).trans
        (Over.iteratedSliceBackward_forget W))
  -- Stacks 0402: the algebraic space `F` representing the base change of `y` along that point
  let F := baseChangeSpace B S hS y.hom hy W G hG
  let Fy := baseChangeSpaceOverBase B S hS y.hom hy W G hG
  obtain ⟨e⟩ := nonempty_equivalenceOver_baseChangeSpace B S hS y.hom hy W G hG
  have hFySurj : Space.IsSurjective B S hS
      (baseChangeStructureMap B S hS y.hom hy W G hG).hom :=
    prop_baseChangeStructureMap B S hS (Space.surjectiveMorphismProperty B S hS) y hy hysurj
      W G hG
  have hFySmooth : Space.IsSmooth B S hS
      (baseChangeStructureMap B S hS y.hom hy W G hG).hom :=
    prop_baseChangeStructureMap B S hS (Space.smoothMorphismProperty B S hS) y hy hysmooth
      W G hG
  -- a scheme atlas of `F`, read over `S`
  obtain ⟨T, b, hbSurj, hbEtale⟩ := Fy.property.exists_atlas
  let ι := (spacesOverSmallerBaseFunctorForgetIso B W.left.1 S W.left.2 hS W.hom).app F
  let t : Fy.1.left.obj (op T) := yonedaEquiv b
  let r := ι.hom.app (op T) t
  have hr : r.1.1 ≫ W.hom = T.hom := r.2
  -- the section of `F` named by the atlas point, and the factorization of `T ⟶ W` it carries
  let W₁ : BigFppfOver B W.left.1 W.left.2 := Over.mk r.1.1
  let s : F.1.obj (op W₁) := r.1.2
  let C := presheafOfCategories (F.1 ⋙ typeToCat)
  let w : C.obj := (PresheafOfCategories.objEquiv (F.1 ⋙ typeToCat)).symm ⟨W₁, Discrete.mk s⟩
  let z₀ : TwoFibreProductOver (Over.map W.hom) (schemeFibredCategory B S hS V).val.p 𝒴.val.p
      G y.hom.toFunctor := e.inv.functor.obj w
  have hxbase : z₀.x = W₁ := congrArg (fun H => H.obj w) e.inv.w
  -- the scheme `U` over `S`: the object `W₁` of the slice over `W`, read over `S`
  let Wslice := (Over.iteratedSliceBackward W).obj W₁
  have hWbase : Wslice.left = z₀.base :=
    (congrArg (Over.map W.hom).obj hxbase.symm).trans z₀.hx
  set U := Wslice.left
  have hTbase : Wslice.left = T := by
    apply congrArg Over.mk
    dsimp [Wslice, W₁]
    simpa using hr
  let k : Wslice.left ⟶ T := eqToHom hTbase
  let b' : yoneda.obj Wslice.left ⟶ Fy.1.left := yoneda.map k ≫ b
  -- the composite `U ⟶ F ⟶ W` is the structure morphism of `W₁`
  have hschemeComp : b' ≫ Fy.1.hom = yoneda.map Wslice.hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simp only [yonedaEquiv_yoneda_map]
    apply Over.OverMorphism.ext
    rw [← map_yonedaEquiv b k]
    rw [congrArg Over.Hom.left (NatTrans.naturality_apply Fy.1.hom k.op t)]
    have hkleft : k.left = 𝟙 T.left := Over.eqToHom_left hTbase
    show k.left ≫ (Fy.1.hom.app (op T) t).left = Wslice.hom.left
    refine (congrArg (fun l : T.left ⟶ T.left =>
      l ≫ (Fy.1.hom.app (op T) t).left) hkleft).trans ((Category.id_comp _).trans ?_)
    exact spacesOverSmallerBaseFunctor_hom_app_left B W.left.1 S W.left.2 hS W.hom F (op T) t
  -- the second projection of the 2-fibre product point, as an object of the fibre of `(Sch/V)`
  let ypt : (schemeFibredCategory B S hS V).val.p.Fiber U :=
    Functor.Fiber.mk (z₀.hy.trans hWbase.symm)
  let evV := Functor.twoYonedaEvaluation (schemeFibredCategory B S hS V).val.p U
  have : evV.IsEquivalence :=
    Functor.twoYonedaEvaluation_isEquivalence (schemeFibredCategory B S hS V).val.p
      (schemeFibredCategory B S hS V).isFiberedInGroupoids U
  obtain ⟨aBase, ⟨ηa⟩⟩ := Functor.EssSurj.mem_essImage (F := evV) ypt
  let qBase : (schemeFibredCategory B S hS U).val ⥤ᵇ (schemeFibredCategory B S hS W).val :=
    overMapBased B S hS Wslice.hom
  let xBase := BasedFunctor.comp qBase z
  let x : schemeFibredCategory B S hS U ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom xBase
  let a : schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V :=
    Bicategory.InducedBicategory.mkHom aBase
  have hxrep : IsRepresentableByAlgebraicSpaces B S hS x.hom :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp h𝒳diag) U xBase
  -- the scheme map `U ⟶ W` is surjective and smooth, being the atlas followed by `F ⟶ W`
  have hb'Surj : Space.IsSurjective B S hS b' :=
    (Space.surjective_iff_surjective_pointsMap B S hS Fy.1.left Fy.property U b').mp
      (MorphismProperty.RespectsIso.precomp _ (yoneda.map k) b hbSurj)
  have hb'Etale : Space.IsEtale B S hS b' :=
    (Space.isEtale_iff_presheaf_of_yoneda B S hS b').2
      (MorphismProperty.RespectsIso.precomp _ (yoneda.map k) b hbEtale)
  have hb'Smooth := Space.isSmooth_of_isEtale B S hS Fy.property hb'Etale
  have hqSurj : Space.IsSurjective B S hS (yoneda.map Wslice.hom) := by
    rw [← hschemeComp]
    exact Space.isSurjective_comp B S hS hb'Surj hFySurj
  have hqSmooth : Space.IsSmooth B S hS (yoneda.map Wslice.hom) := by
    rw [← hschemeComp]
    exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS U) Fy.property
      (isAlgebraicSpace_yoneda B S hS W) b' Fy.1.hom hb'Smooth hFySmooth
  let z' : schemeFibredCategory B S hS W ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom z
  have hzs : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) z' hzrep :=
    fun T z hz F hF he => (hzproperties T z hz F hF he).1
  have hzm : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) z' hzrep :=
    fun T z hz F hF he => (hzproperties T z hz F hF he).2
  refine ⟨U, x, a, hxrep, ?_,
    hasRelativeProperty_schemeFibredCategoryMap_comp _ Wslice.hom z' hzrep hqSurj hzs,
    hasRelativeProperty_schemeFibredCategoryMap_comp _ Wslice.hom z' hzrep hqSmooth hzm⟩
  · -- 2-commutativity, produced in the fibre of `𝒴` over `U`
    let H := BasedFunctor.comp xBase f.hom
    let K := BasedFunctor.comp aBase y.hom
    let evY := Functor.twoYonedaEvaluation 𝒴.val.p U
    let VF := (schemeFibredCategory B S hS V).val.p
    let yFun := y.hom.toFunctor
    have hYcomp : (Functor.Fiber.fiberInclusion (p := VF) (S := U) ⋙ yFun) ⋙ 𝒴.val.p =
        (Functor.const (VF.Fiber U)).obj U := by
      calc
        _ = Functor.Fiber.fiberInclusion (p := VF) (S := U) ⋙ (yFun ⋙ 𝒴.val.p) :=
          Functor.assoc _ _ _
        _ = Functor.Fiber.fiberInclusion (p := VF) (S := U) ⋙ VF :=
          congrArg (Functor.comp (Functor.Fiber.fiberInclusion (p := VF) (S := U))) y.hom.w
        _ = (Functor.const (VF.Fiber U)).obj U := Functor.Fiber.fiberInclusion_comp_eq_const
    let yFiberMap := Functor.Fiber.inducedFunctor hYcomp
    have hGbase : 𝒴.val.p.obj (G.obj z₀.x) = U :=
      (congrArg (fun K => K.obj z₀.x) hG).trans (congrArg (Over.map W.hom).obj hxbase)
    have hyYbase : 𝒴.val.p.obj (yFun.obj z₀.y) = U :=
      (congrArg (fun K => K.obj z₀.y) y.hom.w).trans (z₀.hy.trans hWbase.symm)
    have hvertical : 𝒴.val.p.IsHomLift (𝟙 U) z₀.iso.hom := by
      refine IsHomLift.of_fac' 𝒴.val.p (𝟙 U) z₀.iso.hom hGbase hyYbase ?_
      have : 𝒴.val.p.IsHomLift (𝟙 z₀.base) z₀.iso.hom := z₀.vertical
      simpa [hWbase] using IsHomLift.fac' 𝒴.val.p (𝟙 z₀.base) z₀.iso.hom
    let zIso : Functor.Fiber.mk hGbase ≅ Functor.Fiber.mk hyYbase :=
      { hom := Functor.Fiber.homMk 𝒴.val.p U z₀.iso.hom
        inv := Functor.Fiber.homMk 𝒴.val.p U z₀.iso.inv
        hom_inv_id := Functor.Fiber.hom_ext (by simp [yFun])
        inv_hom_id := Functor.Fiber.hom_ext (by simp [yFun]) }
    have hHval : evY.obj H = Functor.Fiber.mk hGbase := by
      apply Subtype.ext
      show zf.toFunctor.obj ((Over.map Wslice.hom).obj (Over.mk (𝟙 U))) =
        zf.toFunctor.obj ((Over.iteratedSliceBackward W).obj z₀.x)
      rw [hxbase]
      exact congrArg zf.toFunctor.obj (show Over.mk (𝟙 U ≫ Wslice.hom) = Wslice from rfl)
    have hKval : evY.obj K = yFiberMap.obj (evV.obj aBase) := Subtype.ext rfl
    have hyFiberVal : yFiberMap.obj ypt = Functor.Fiber.mk hyYbase := Subtype.ext rfl
    let eEval : evY.obj H ≅ evY.obj K :=
      eqToIso hHval ≪≫ zIso ≪≫ eqToIso hyFiberVal.symm ≪≫
        (Functor.mapIso yFiberMap ηa).symm ≪≫ eqToIso hKval.symm
    exact ⟨Bicategory.InducedBicategory.isoMk
      (Functor.TwoYoneda.basedIsoOfEvaluationIso 𝒴.val.p 𝒴.isFiberedInGroupoids U eEval)⟩
end AlgebraicGeometry.Stack

end
