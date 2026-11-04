module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Locally quasi-finite representable 1-morphisms of algebraic stacks (Stacks 06UA)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is representable by algebraic
spaces. Then `f` is locally quasi-finite in the sense of **Stacks 04XB** — every algebraic space
representing a base change of `f` along a scheme-valued point of `𝒴` has locally quasi-finite
structural morphism — exactly when `f` is locally of finite type (**Stacks 06FS**, part (1)) and
for every field-valued point `Spec(k) ⟶ 𝒴` the fibre `𝒳_k` has discrete space of points.

The two conditions of the right-hand side are the second and third conjuncts of local
quasi-finiteness of an arbitrary 1-morphism of algebraic stacks (**Stacks 06PU**), so this is the
comparison of the two notions sharing that name for a representable 1-morphism.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_isLocallyQuasiFinite`: a representable
  locally quasi-finite 1-morphism is locally of finite type.
* `AlgebraicGeometry.Stack.discreteTopology_points_fibre_of_isLocallyQuasiFinite`: its fibre over
  a point of the site whose scheme has at most one point has discrete space of points.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_and_discreteTopology_of_isLocallyQuasiFinite`:
  **Stacks 06UA**, the implication (1) ⟹ (2).
* `AlgebraicGeometry.Stack.discreteTopology_points_pullback_representingMap`: the fibre of the
  morphism of representing presheaves of a base change of `f` over a field-valued point of the
  base is, up to isomorphism, a representing presheaf of a fibre of `f` over a field-valued point
  of `𝒴`, so it has discrete space of points.
* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology`:
  **Stacks 06UA**, the implication (2) ⟹ (1).
* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_iff_isLocallyOfFiniteType_and_discreteTopology`:
  **Stacks 06UA**.

## Implementation notes

Clause (1) is the Stacks 04XB notion written out, `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`;
it is the relative property of **Stacks 03YK** at
`AlgebraicGeometry.Space.locallyQuasiFiniteProperty` and is related to
`AlgebraicGeometry.Stack.HasRelativeProperty` there by `Iff.rfl`, which is how the
relative-property machinery is applied to it below. Clause (2) is phrased exactly as the second
and third conjuncts of `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite`.

For (1) ⟹ (2) the local finite type half is **Stacks 06FM** for a representable 1-morphism,
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty`, applied at local
finite type of morphisms of algebraic spaces — which, unlike local quasi-finiteness, is smooth
local on the source and target. The fibre half is **Stacks 04XC** at the field-valued point
itself: the apex of the fibre square is representable by an algebraic space by **Stacks 04ZP**, the
induced morphism of representing presheaves to the represented point is locally quasi-finite, so
that presheaf has discrete space of points by **Stacks 0ACA**, and the point space of a stack
represented by an algebraic space is that of the space.

For (2) ⟹ (1) one scheme atlas `U ⟶ 𝒴` suffices, by **Stacks 04XD** in the form
`AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_localEssSurj` with the
local essential surjectivity taken from the presentation clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`. What has to be checked is that the morphism of
representing presheaves of `U ×_𝒴 𝒳 ⟶ U` is locally quasi-finite, and by **Stacks 06RW** that is
local finite type together with discreteness of all of its field-valued fibres. A field-valued
point of `U` gives, through `AlgebraicGeometry.Stack.schemeFibredCategoryMap`, a field-valued
point of `𝒴`; the fibre of the morphism of representing presheaves over it is a representing
presheaf of the 2-fibre product `(U ×_𝒴 𝒳) ×_U Spec(k)` by **Stacks 04SD**, and that 2-fibre
product is one of the cospan `(f, Spec(k) ⟶ 𝒴)` by **Stacks 02XD**, whose space of points the
hypothesis says is discrete.

`AlgebraicGeometry.Space.pointTopology` and `AlgebraicGeometry.Stack.pointTopology` are `def`s and
not instances; they are supplied here as local instances, as
`StacksFrontier.AlgebraicGeometry.Stacks.SpecializationSmoothChart` does.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06RW](https://stacks.math.columbia.edu/tag/06RW)
* [Stacks Project, Tag 06UA](https://stacks.math.columbia.edu/tag/06UA)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] AlgebraicGeometry.Space.pointTopology
  AlgebraicGeometry.Stack.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A locally quasi-finite representable 1-morphism is locally of finite type.** Local
quasi-finiteness of a morphism of algebraic spaces is local finite type together with a
fibre condition, so the relative property of **Stacks 03YK** at local quasi-finiteness implies the
one at local finite type; and for local finite type, which is smooth local on the source and
target, the relative property is the universal smooth-diagram test of **Stacks 06FM**. -/
theorem isLocallyOfFiniteType_of_isLocallyQuasiFinite
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h : IsLocallyQuasiFinite B S hS f.hom) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS f := by
  have hP : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ q => Space.IsLocallyOfFiniteType B S hS q) :=
    Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS
  have : (spaceProperty B S hS
      (fun _ _ q => Space.IsLocallyOfFiniteType B S hS q)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  exact hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty.{u, u + 1, w} B S hS _ hP
    𝒳.property 𝒴.property f.hom hf
    (fun U y hy F hF he U' V a b m ha hb hc => (h U y hy F hF he U' V a b m ha hb hc).1)

/-- **The fibre of a locally quasi-finite representable 1-morphism over a one-point base is
discrete.** For a 1-morphism `g : U ⟶ 𝒴` out of an object of the site whose scheme has at most one
point, the apex of the fibre square of `f` and `g` has discrete space of points for the topology
of **Stacks 04XL**.

The apex is representable by an algebraic space by **Stacks 04ZP**; by **Stacks 04XC** the induced
morphism of representing presheaves to the presheaf of `U` is locally quasi-finite, hence the
representing presheaf has discrete space of points by **Stacks 0ACA**; and the point space of a
stack represented by an algebraic space is the point space of that space. -/
theorem discreteTopology_points_fibre_of_isLocallyQuasiFinite
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h : IsLocallyQuasiFinite B S hS f.hom)
    (K : BigFppfOver B S hS)
    (hK : Subsingleton ((BigFppfOver.toScheme B S hS).obj K))
    (g : schemeStack.{u, w} B S hS K ⟶ 𝒴) :
    DiscreteTopology
      (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.property) := by
  have hQ : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquareAlgebraicStacks B S hS f g).underlying.swap :=
    Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_underlying_algebraicStacks B S hS _
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g))
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      𝒳.val 𝒴.val (schemeFibredCategory B S hS K) f.hom g.hom
      (twoFibreProductSquareAlgebraicStacks B S hS f g).underlying.swap hQ hf
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS K)
  have hm := prop_representingMap_of_hasRelativeProperty.{u, u + 1} B S hS
    (Space.locallyQuasiFiniteProperty B S hS) f.hom hf h
    (schemeFibredCategory B S hS K) g.hom
    (twoFibreProductSquareAlgebraicStacks B S hS f g).underlying.swap hQ F (yoneda.obj K) hF
    (isAlgebraicSpace_yoneda B S hS K) eF (PresheafOfCategories.sliceElementsEquivalenceOver K)
  have hdF : DiscreteTopology (Space.points B S hS F) :=
    Space.discreteTopology_points_of_isLocallyQuasiFinite B S hS hF hK _ hm
  exact ((isHomeomorph_spacePointMap_representing B S hS F hF
    (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val eF).homeomorph _).discreteTopology

/-- **Stacks 06UA, the implication (1) ⟹ (2).** A 1-morphism of algebraic stacks over `S` which is
representable by algebraic spaces and locally quasi-finite in the sense of **Stacks 04XB** is
locally of finite type, and the fibre of it over every field-valued point of the target has
discrete space of points. -/
@[stacks 06UA "(1) implies (2)"]
theorem isLocallyOfFiniteType_and_discreteTopology_of_isLocallyQuasiFinite
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h : IsLocallyQuasiFinite B S hS f.hom) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS f ∧
      ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
        (toBase : Spec (.of k) ⟶ S)
        (g : schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒴),
        DiscreteTopology
          (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val
            (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.property) :=
  ⟨isLocallyOfFiniteType_of_isLocallyQuasiFinite B S hS f hf h,
    fun k _ _hk _toBase g =>
      discreteTopology_points_fibre_of_isLocallyQuasiFinite B S hS f hf h _
        (inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))) g⟩

/-- **The field-valued fibres of a base change along a scheme atlas are fibres of `f`.** Let
`a : U ⟶ 𝒴` be a 1-morphism out of an object of the site, let `V` represent the apex of the
canonical fibre square of `f` and `a`, and let `p` be a field-valued point of the presheaf of `U`.
If every fibre of `f` over a field-valued point of `𝒴` has discrete space of points, then so does
the fibre of the induced morphism `V ⟶ U` of representing presheaves over `p`.

The point `p` names a morphism `Spec(k) ⟶ U` of the site, hence a field-valued point of `𝒴`; the
2-fibre product of the projection `U ×_𝒴 𝒳 ⟶ U` with it is a 2-fibre product of the cospan
`(f, Spec(k) ⟶ 𝒴)` by **Stacks 02XD**, so its space of points is discrete, and the fibre in
question is a representing presheaf of it by **Stacks 04SD**. -/
theorem discreteTopology_points_pullback_representingMap
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hfib : ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (toBase : Spec (.of k) ⟶ S)
      (g : schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒴),
      DiscreteTopology
        (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val
          (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.property))
    (U : BigFppfOver B S hS) (a : schemeFibredCategory B S hS U ⟶ 𝒴.val)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).pt.val.p
      (presheafOfCategories (V ⋙ typeToCat)).p)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    DiscreteTopology (Space.points B S hS
      (Limits.pullback (yonedaEquiv.symm p.value)
        (representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).pt
          (schemeFibredCategory B S hS U) V (yoneda.obj U) eV
          (PresheafOfCategories.sliceElementsEquivalenceOver U)
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).snd))) := by
  classical
  let _ := p.field
  set K : BigFppfOver B S hS :=
    Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS) with hKdef
  set b : K ⟶ U := p.value with hbdef
  set c := schemeFibredCategoryMap B S hS b with hcdef
  set gK : schemeStack.{u, w} B S hS K ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom (c ≫ a) with hgKdef
  have hD := CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1}
    f.hom a c (c ≫ a) (Iso.refl _)
  have hdD := discreteTopology_points_congr B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f gK).underlying
    (CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} f.hom a c (c ≫ a) (Iso.refl _))
    (isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f gK))
    hD (hfib p.carrier p.contained p.toBase gK)
  have hdD' : DiscreteTopology (points B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).snd c).pt.val
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom a).snd c).pt.property) := hdD
  obtain ⟨T, hT, ⟨eT⟩⟩ :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (schemeFibredCategory B S hS K) (schemeFibredCategory B S hS U)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).pt
      c (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).snd
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).snd c)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS b) ⟨V, hV, ⟨eV⟩⟩
  have hdT : DiscreteTopology (Space.points B S hS T) :=
    ((isHomeomorph_spacePointMap_representing B S hS T hT
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).snd c).pt
      eT).homeomorph _).symm.discreteTopology
  let _ : (twoFibreProductStructureFunctor B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).pt
      (schemeFibredCategory B S hS K) (schemeFibredCategory B S hS U)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).snd
      c).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom a).snd c).pt.property.isFibered
  have eT' : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).pt
        (schemeFibredCategory B S hS K) (schemeFibredCategory B S hS U)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).snd c)
      (presheafOfCategories (T ⋙ typeToCat)).p := eT
  have hiso := fibreProductIsoRepresenting B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).pt
    (schemeFibredCategory B S hS K) (schemeFibredCategory B S hS U)
    V (yoneda.obj K) (yoneda.obj U) eV
    (PresheafOfCategories.sliceElementsEquivalenceOver K)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).snd c T eT'
  rw [hcdef, representingMap_schemeFibredCategoryMap] at hiso
  have hyb : (yonedaEquiv.symm b : yoneda.obj K ⟶ yoneda.obj U) = yoneda.map b := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
  rw [hyb]
  exact Space.discreteTopology_points_of_isIso B S hS (Limits.pullbackSymmetry _ _).hom
    (Space.discreteTopology_points_of_isIso B S hS (Presheaf.fibreProductIsoPullback _ _).hom
      (Space.discreteTopology_points_of_isIso B S hS hiso.inv hdT))

/-- **Stacks 06UA, the implication (2) ⟹ (1).** A 1-morphism of algebraic stacks over `S` which is
representable by algebraic spaces, locally of finite type, and whose fibre over every field-valued
point of the target has discrete space of points, is locally quasi-finite in the sense of
**Stacks 04XB**.

One scheme atlas of `𝒴` suffices by **Stacks 04XD**, and for the base change of `f` along it the
criterion of **Stacks 06RW** applies: it is locally of finite type by **Stacks 04XC** and its
field-valued fibres are fibres of `f`. -/
@[stacks 06UA "(2) implies (1)"]
theorem isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hfib : ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (toBase : Spec (.of k) ⟶ S)
      (g : schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒴),
      DiscreteTopology
        (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val
          (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.property)) :
    IsLocallyQuasiFinite B S hS f.hom := by
  classical
  obtain ⟨U, a, harep, hess⟩ := exists_atlas_localEssSurj.{u, w} B S hS 𝒴
  have hCswap : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).swap :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a)
  obtain ⟨V, hV, ⟨eV⟩⟩ :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      𝒳.val 𝒴.val (schemeFibredCategory B S hS U) f.hom a
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).swap
      hCswap hf (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  refine hasRelativeProperty_of_prop_representingMap_of_localEssSurj B S hS
    (Space.locallyQuasiFiniteProperty B S hS) 𝒳.val 𝒴.val (schemeFibredCategory B S hS U)
    f.hom a hf hess
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).swap hCswap
    V (yoneda.obj U) hV (isAlgebraicSpace_yoneda B S hS U) eV
    (PresheafOfCategories.sliceElementsEquivalenceOver U) ?_
  have hP : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ q => Space.IsLocallyOfFiniteType B S hS q) :=
    Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS
  have hlt : (spaceProperty B S hS
      (fun _ _ q => Space.IsLocallyOfFiniteType B S hS q)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  have hrel := (hasPropertyOnEverySmoothDiagram_iff_relative.{u, u + 1, w} B S hS _ hP
    𝒳.property 𝒴.property f.hom hf).1 hft
  have hmft := prop_representingMap_of_hasRelativeProperty.{u, u + 1} B S hS _ f.hom hf hrel
    (schemeFibredCategory B S hS U) a
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a).swap hCswap
    V (yoneda.obj U) hV (isAlgebraicSpace_yoneda B S hS U) eV
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
  exact (Space.isLocallyQuasiFinite_iff_forall_discreteTopology_fibre B S hS hV
    (isAlgebraicSpace_yoneda B S hS U) _ hmft).2
    (fun p => discreteTopology_points_pullback_representingMap B S hS f hfib U a V hV eV p)

/-- **Stacks 06UA.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is representable
by algebraic spaces is locally quasi-finite in the sense of **Stacks 04XB** exactly when it is
locally of finite type and for every field-valued point of `𝒴` the fibre of `f` over it has
discrete space of points.

The right-hand side is the conjunction of the second and third clauses of **Stacks 06PU**. -/
@[stacks 06UA]
theorem isLocallyQuasiFinite_iff_isLocallyOfFiniteType_and_discreteTopology
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    IsLocallyQuasiFinite B S hS f.hom ↔
      (AlgebraicStacks.IsLocallyOfFiniteType B S hS f ∧
        ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
          (toBase : Spec (.of k) ⟶ S)
          (g : schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒴),
          DiscreteTopology
            (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val
              (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.property)) :=
  ⟨isLocallyOfFiniteType_and_discreteTopology_of_isLocallyQuasiFinite B S hS f hf,
    fun h => isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology B S hS f hf
      h.1 h.2⟩

end AlgebraicGeometry.Stack

end
