module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski
public import StacksFrontier.AlgebraicGeometry.Stacks.CoproductPointPropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionOpenSourceRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCoverGeneral
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# Descent of a chart's properties to the coproduct (Stacks 06MF)

Let `W` be an object of the big fppf site over `S` which is, in schemes, the coproduct of a
family `Z i` of objects of the site, and let `g : schemeStack W ⟶ 𝒳` be a 1-morphism into an
algebraic stack whose restriction along each summand inclusion is 2-isomorphic to a given
`f i : schemeStack (Z i) ⟶ 𝒳`. Any relative property of **Stacks 03YK** which is local on the
source for the étale topology descends from the `f i` to `g`; in particular so do local
quasi-finiteness in the sense of **Stacks 04XB**, flatness (**Stacks 06PW**), local finite
presentation (**Stacks 06Q2**, part (1)) and relative étaleness.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap_chartBaseChange`: the
  relative property of **Stacks 03YK** of a 1-morphism out of a stack representable by an
  algebraic space is the property of the morphism of representing algebraic spaces obtained from
  *any* 2-fibre product square of the 1-morphism with *any* smooth surjective chart of the
  target.
* `AlgebraicGeometry.Stack.relativeProperty_of_isColimit_of_forall_relativeProperty`: the
  descent itself, for an arbitrary property of morphisms of algebraic spaces over `S` which is
  stable under base change, fppf local on the target and étale local on the source.
* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_of_isColimit_of_forall_isLocallyQuasiFinite`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isColimit_of_forall_isFlat` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isColimit_of_forall`:
  the descent of local quasi-finiteness, of flatness in the sense of **Stacks 06PW** and of local
  finite presentation in the sense of **Stacks 06Q2**.
* `AlgebraicGeometry.Stack.isRelativelyEtale_of_isColimit_of_forall_isRelativelyEtale`: the
  descent at relative étaleness.
* `AlgebraicGeometry.Space.Topology.precoverage_etale_le_fppf` and
  `AlgebraicGeometry.Space.Topology.precoverage_etale_le_fpqc`: the étale precoverage of
  algebraic spaces is contained in the fppf and in the fpqc one.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0501](https://stacks.math.columbia.edu/tag/0501)
* [Stacks Project, Tag 06ET](https://stacks.math.columbia.edu/tag/06ET)
* [Stacks Project, Tag 06EV](https://stacks.math.columbia.edu/tag/06EV)
* [Stacks Project, Tag 06F5](https://stacks.math.columbia.edu/tag/06F5)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0CPP](https://stacks.math.columbia.edu/tag/0CPP)
* [Stacks Project, Tag 0DF1](https://stacks.math.columbia.edu/tag/0DF1)
* [Stacks Project, Tag 0DFC](https://stacks.math.columbia.edu/tag/0DFC)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

/-! ### The étale precoverage inside the fppf and the fpqc one -/

namespace Space.Topology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The étale precoverage of algebraic spaces over `S` is contained in the fppf one. -/
@[stacks 0DFC "étale coverings, at the precoverages"]
theorem precoverage_etale_le_fppf :
    Topology.precoverage.{u, v} .etale B S hS ≤ Topology.precoverage.{u, v} .fppf B S hS :=
  Topology.precoverage_le_of_isCovering B S hS fun _ _ hcover ↦
    ⟨hcover.1, hcover.2.1, isFppfCovering_of_isEtaleCovering B S hS hcover.2.2⟩

/-- The étale precoverage of algebraic spaces over `S` is contained in the fpqc one. -/
@[stacks 0DFQ "étale coverings, at the precoverages"]
theorem precoverage_etale_le_fpqc :
    Topology.precoverage.{u, v} .etale B S hS ≤ Topology.precoverage.{u, v} .fpqc B S hS :=
  Topology.precoverage_le_of_isCovering B S hS fun Yi g hcover ↦
    ⟨hcover.1, hcover.2.1, isFpqcCovering_of_isEtaleCovering B S hS Yi g hcover.2.2⟩

end Space.Topology

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The relative property read on an arbitrary smooth surjective chart -/

/-- **The relative property of Stacks 03YK of a 1-morphism out of a stack representable by an
algebraic space, read on an arbitrary smooth surjective chart of the target.** Let `c : 𝒯 ⟶ 𝒳`
be a 1-morphism of algebraic stacks over `S` whose source is representable by an algebraic space,
let `a : V₀ ⟶ 𝒳` be a smooth surjective chart by a scheme of the site, and let `Sq` be any
2-fibre product square of the cospan `(a, c)` whose apex is represented by the algebraic space
`F`. Then `c` has the relative property `P` exactly when the projection `F ⟶ V₀` of representing
algebraic spaces has `P`. -/
theorem hasRelativeProperty_iff_prop_representingMap_chartBaseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS) (c : 𝒯 ⟶ 𝒳)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    (haSm : AlgebraicStacks.IsSmooth B S hS a) (haSurj : IsSurjective B S hS a)
    {Sq : Bicategory.TwoCommSq a c} (hSq : Bicategory.IsTwoFibreProduct Sq)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eF : StacksRepresentableCFG.EquivalenceOver Sq.pt.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    HasRelativeProperty B S hS P c.hom
        (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒯 c.hom) ↔
      P (ObjectProperty.homMk (representingMap B S hS Sq.pt.val
          (schemeStack.{u, w} B S hS V₀).val F (yoneda.obj V₀) eF
          (PresheafOfCategories.sliceElementsEquivalenceOver V₀) Sq.fst.hom) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace V₀) := by
  have hcrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒯 c.hom
  refine Iff.trans (hasRelativeProperty_iff_of_fppfCoverStack B S hS P c a hcrep haSurj
    (AlgebraicStacks.isFlat_of_isSmooth B S hS a haSm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a haSm) Sq hSq) ?_
  have key := fun hc ↦ hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P Sq.fst.hom hc
    F (yoneda.obj V₀) hF (isAlgebraicSpace_yoneda B S hS V₀) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
  exact ⟨fun h ↦ (key h.1).mp h.2,
    fun h ↦ ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ c.hom a.hom _
    (Bicategory.isTwoFibreProduct_underlying (P := Sq)
      (twoFibreProductSquareAlgebraicStacks B S hS a c) hSq
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        a.hom c.hom)) hcrep, (key _).mpr h⟩⟩

/-! ### Transport of a relative property along a 2-isomorphism -/

/-- **Two 2-isomorphic 1-morphisms have a relative property together.** -/
theorem relativeProperty_congr_twoIso (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {p q : 𝒜 ⟶ 𝒞} (e : p ≅ q) (h : RelativeProperty B S hS P p) :
    RelativeProperty B S hS P q := by
  have ha : Functor.IsEquivalence (BasedFunctor.id 𝒜.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒜.val.obj))
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒞.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒞.val.obj))
  exact relativeProperty_of_equivalences B S hS P q.hom p.hom (BasedFunctor.id 𝒜.val)
    (BasedFunctor.id 𝒞.val) (twoIsoHomIso B S hS e) h

/-! ### The descent -/

/-- **A 1-morphism out of a coproduct of objects of the site has a source-local relative
property as soon as its restriction to every summand has it.** Let `P` be a property of
morphisms of algebraic spaces over `S` which is stable under base change, local on the target
for the fppf topology and local on the source for the étale topology; let `W` be an object of
the big fppf site over `S` which is, in schemes, the coproduct of a family `Z i` of objects of
the site; let `g : schemeStack W ⟶ 𝒳` be a 1-morphism into an algebraic stack; and let
`f i : schemeStack (Z i) ⟶ 𝒳` be 1-morphisms with `schemeStackMap (jj i) ≫ g` 2-isomorphic to
`f i` for every `i`. If every `f i` has the relative property `P` of **Stacks 03YK**, then so
does `g`. -/
theorem relativeProperty_of_isColimit_of_forall_relativeProperty
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsLocalAtSource (Space.Topology.etale.precoverage.{u, u} B S hS)]
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type u}
    (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (g : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hfg : ∀ i, Nonempty (schemeStackMap.{u, w} B S hS (jj i) ≫ g ≅ f i))
    (hf : ∀ i, RelativeProperty B S hS P (f i).hom) :
    RelativeProperty B S hS P g.hom :=
  relativeProperty_of_isColimit_of_forall B S hS Z W jj g.hom P hW
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) g.hom)
    (fun i ↦ relativeProperty_congr_twoIso B S hS P
      (Bicategory.InducedBicategory.isoHom (hfg i).some.symm) (hf i))

/-- **Local quasi-finiteness descends from the summands to a 1-morphism out of a coproduct of
objects of the site.** If `schemeStackMap (jj i) ≫ g` is 2-isomorphic to `f i` and every `f i` is
locally quasi-finite, then so is `g`. -/
theorem isLocallyQuasiFinite_of_isColimit_of_forall_isLocallyQuasiFinite
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type u}
    (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (g : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hfg : ∀ i, Nonempty (schemeStackMap.{u, w} B S hS (jj i) ≫ g ≅ f i))
    (hf : ∀ i, IsLocallyQuasiFinite B S hS (f i).hom) :
    IsLocallyQuasiFinite B S hS g.hom :=
  relativeProperty_of_isColimit_of_forall_relativeProperty B S hS
    (Space.locallyQuasiFiniteProperty B S hS) Z W jj hW g f hfg hf

/-- **Flatness descends from the summands to a 1-morphism out of a coproduct of objects of the
site.** If `schemeStackMap (jj i) ≫ g` is 2-isomorphic to `f i` and every `f i` is flat in the
sense of **Stacks 06PW**, then so is `g`. -/
theorem AlgebraicStacks.isFlat_of_isColimit_of_forall_isFlat
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type u}
    (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (g : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hfg : ∀ i, Nonempty (schemeStackMap.{u, w} B S hS (jj i) ≫ g ≅ f i))
    (hf : ∀ i, AlgebraicStacks.IsFlat B S hS (f i)) :
    AlgebraicStacks.IsFlat B S hS g := by
  have : (Space.flatProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have : (Space.flatProperty B S hS).IsLocalAtSource
      (Space.Topology.etale.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtSource.of_le
      (Space.Topology.precoverage_etale_le_fpqc.{u, u} B S hS)
  have hbridge : ∀ (T : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS T ⟶ 𝒳),
      AlgebraicStacks.IsFlat B S hS c ↔
        RelativeProperty B S hS (Space.flatProperty B S hS) c.hom := fun T c ↦ by
    rw [AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram]
    exact hasPropertyOnSomeSmoothDiagram_iff_relative B S hS
      (fun _ _ h ↦ Space.IsFlat B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      (schemeStack.{u, w} B S hS T).property 𝒳.property c.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS T) c.hom)
  exact (hbridge W g).mpr (relativeProperty_of_isColimit_of_forall_relativeProperty B S hS
    (Space.flatProperty B S hS) Z W jj hW g f hfg fun i ↦ (hbridge (Z i) (f i)).mp (hf i))

/-- **Local finite presentation descends from the summands to a 1-morphism out of a coproduct of
objects of the site.** If `schemeStackMap (jj i) ≫ g` is 2-isomorphic to `f i` and every `f i` is
locally of finite presentation in the sense of **Stacks 06Q2**, part (1), then so is `g`. -/
theorem AlgebraicStacks.isLocallyOfFinitePresentation_of_isColimit_of_forall
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type u}
    (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (g : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hfg : ∀ i, Nonempty (schemeStackMap.{u, w} B S hS (jj i) ≫ g ≅ f i))
    (hf : ∀ i, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f i)) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g := by
  have : (Space.locallyOfFinitePresentationProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf.{u, u} B S hS
  have : (Space.locallyOfFinitePresentationProperty B S hS).IsLocalAtSource
      (Space.Topology.etale.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtSource.of_le
      (Space.Topology.precoverage_etale_le_fppf.{u, u} B S hS)
  have hbridge : ∀ (T : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS T ⟶ 𝒳),
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c ↔
        RelativeProperty B S hS (Space.locallyOfFinitePresentationProperty B S hS) c.hom :=
    fun T c ↦ hasPropertyOnEverySmoothDiagram_iff_relative B S hS
      (fun _ _ h ↦ Space.IsLocallyOfFinitePresentation B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS T).property 𝒳.property c.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS T) c.hom)
  exact (hbridge W g).mpr (relativeProperty_of_isColimit_of_forall_relativeProperty B S hS
    (Space.locallyOfFinitePresentationProperty B S hS) Z W jj hW g f hfg
    fun i ↦ (hbridge (Z i) (f i)).mp (hf i))

/-- **Relative étaleness descends from the summands to a 1-morphism out of a coproduct of
objects of the site.** If `schemeStackMap (jj i) ≫ g` is 2-isomorphic to `f i` and every `f i` is
relatively étale, then so is `g`. -/
theorem isRelativelyEtale_of_isColimit_of_forall_isRelativelyEtale
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type u}
    (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (g : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hfg : ∀ i, Nonempty (schemeStackMap.{u, w} B S hS (jj i) ≫ g ≅ f i))
    (hf : ∀ i, IsRelativelyEtale B S hS (f i).hom) :
    IsRelativelyEtale B S hS g.hom :=
  ⟨isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) g.hom,
    relativeProperty_of_isColimit_of_forall_relativeProperty B S hS
      (Space.etaleMorphisms B S hS) Z W jj hW g f hfg fun i ↦ (hf i).2⟩

end Stack

end AlgebraicGeometry

end
