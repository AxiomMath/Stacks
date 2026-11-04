module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCechCoversOverStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardAmbientUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ComponentPresheafBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CocontinuousPushforwardAcyclic

/-!
# Restrictions of injective sheaves are acyclic for the direct image along the subsites

Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks and let `f'` be its restriction to the
lisse-étale sites. For an injective abelian sheaf `I` on `𝒳_étale`, the restriction `(g')⁻¹I` of
`I` to the lisse-étale site of `𝒳` is acyclic for the direct image `f'_*`. This is the input of
Stacks 0GR3 beyond its degree-zero case, Stacks 07AT.

The source reads it off the formulas of Stacks 075G and 0GR2 together with Stacks 07AK, applied
to the 2-fibre product `V ×_{y, 𝒴} 𝒳` and its subcategory `(V ×_{y, 𝒴} 𝒳)'`. Here it is derived in
the form those formulas reduce to. By
`Stacks.Cohomology.CocontinuousPushforward.isZero_rightDerived_sheafPushforwardCocontinuous`
the higher direct images `R^{n+1} f'_* (g')⁻¹I` vanish once

`Ext^{n+1}(ℤ_{K_y}^♯, (g')⁻¹I) = 0`

for every smooth object `y` of `𝒴`, where `K_y` is the presheaf `x ↦ Hom(f' x, y)` on the
lisse-étale site of `𝒳`. That presheaf is the restriction to the lisse-étale site of the
presheaf represented by the projection `V ×_{y, 𝒴} 𝒳 ⟶ 𝒳` of the 2-fibre product
(`Stacks.Sites.CoverDescent.bijective_componentPresheafFstHom`), a smooth 1-morphism with faithful
underlying functor. So `K_y` is a member of `AlgebraicGeometry.Stack.RepresentedOverSubsite`, a
class closed under representable covers, and the descent of
`Stacks.Sites.CoverDescent.ext_restriction_eq_zero_of_mem` — the dévissage that replaces the
source's spectral sequences — gives the vanishing from Stacks 0D6X over the objects of the
lisse-étale site.

The same holds for a flat 1-morphism and the flat-fppf sites.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.ext_restriction_restrictedYoneda_eq_zero` and its flat-fppf
  sibling: the vanishing of `Ext` above.
* `AlgebraicGeometry.Stack.LisseEtale.rightAcyclic_restriction_of_injective` and its flat-fppf
  sibling: `(g')⁻¹I` is acyclic for `f'_*`.

## References

* [Stacks Project, Tag 0GR2](https://stacks.math.columbia.edu/tag/0GR2)
* [Stacks Project, Tag 0GR3](https://stacks.math.columbia.edu/tag/0GR3)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The first projection of a 2-fibre product is faithful as soon as the structure functor of the
second factor is: a morphism of the 2-fibre product is determined by its first component, which
determines the common base morphism, which determines the second component. -/
theorem faithful_twoFibreProductOver_fst {𝒞 𝒜 ℬ 𝒮 : Type*} [Category 𝒞] [Category 𝒜]
    [Category ℬ] [Category 𝒮] (pA : 𝒜 ⥤ 𝒞) (pB : ℬ ⥤ 𝒞) (pS : 𝒮 ⥤ 𝒞) (eA : 𝒜 ⥤ 𝒮)
    (eB : ℬ ⥤ 𝒮) [pB.Faithful] : (TwoFibreProductOver.fst pA pB pS eA eB).Faithful := by
  refine ⟨fun {ξ ξ'} m m' h => TwoFibreProductOver.Hom.ext' h ?_⟩
  have h₁ := m.hb
  have h₂ := m'.hb
  have hb : m.hbase = m'.hbase := by
    rw [m.hbase_eq, m'.hbase_eq]
    exact congrArg (fun a => eqToHom _ ≫ pA.map a ≫ eqToHom _) h
  apply pB.map_injective
  rw [IsHomLift.fac' pB m.hbase m.b, IsHomLift.fac' pB m'.hbase m'.b]
  simp only [hb]

/-- **The presheaf represented by the projection of `V ×_{y, 𝒴} 𝒳` is `x ↦ Hom(f x, y)`.** For a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks and an object `y` of `𝒴` over `V`, let
`y : (Sch/V) ⟶ 𝒴` be the 1-morphism it names; the presheaf of components of the first projection
of the 2-fibre product of `f` and `y` is the pullback along `f` of the representable presheaf of
`y`. -/
def componentPresheafTwoFibreProductFstIso {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (y : 𝒴.val.val.obj) :
    componentPresheaf (CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks B S hS
        f (Bicategory.InducedBicategory.mkHom (objectMorphism B S hS 𝒴.val
          (Functor.Fiber.mk (a := y) rfl)) :
            schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y) ⟶ 𝒴)).fst.hom) ≅
      (CatFiberedInGroupoids.homFunctor f.hom).op ⋙ uliftYoneda.{u + 1}.obj y := by
  let yV : schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y) ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒴.val (Functor.Fiber.mk (a := y) rfl))
  have hbij := bijective_componentPresheafFstHom 𝒳.val.val.p
    (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor yV.hom)
    𝒳.val.isFiberedInGroupoids
    (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids f.hom.hom.w yV.hom.hom.w
  haveI hI : IsIso (componentPresheafFstHom 𝒳.val.val.p
      (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor yV.hom)) :=
    haveI : ∀ a, IsIso ((componentPresheafFstHom 𝒳.val.val.p
        (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor yV.hom)).app a) :=
      fun a => (isIso_iff_bijective _).2 (hbij a)
    NatIso.isIso_of_isIso_app _
  let e := Functor.TwoYoneda.liftBasedEvaluationIso 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    (𝒴.val.val.p.obj y) (Functor.Fiber.mk (a := y) rfl)
  exact @asIso _ _ _ _ (componentPresheafFstHom 𝒳.val.val.p
      (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor yV.hom)) hI ≪≫
    Functor.isoWhiskerLeft (CatFiberedInGroupoids.homFunctor f.hom).op
      (componentPresheafIsoOfIsTerminal (CatFiberedInGroupoids.homFunctor yV.hom)
        (Over.mkIdTerminal (X := 𝒴.val.val.p.obj y)) ≪≫
      uliftYoneda.{u + 1}.mapIso (Functor.Fiber.fiberInclusion.mapIso e))

/-- Vanishing of `Ext^{n+1}(ℤ_K^♯, I|_{𝒳'})` for an injective `I` and a presheaf `K` isomorphic to
the restriction of a presheaf represented over the subsite `𝒳'`, given the vanishing of the
cohomology of `I|_{𝒳'}` over the objects of `𝒳'`. -/
private theorem ext_restriction_eq_zero_of_iso_restriction {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (τ : SiteKind) (P : ObjectProperty 𝒳.val.val.obj)
    (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)
    [P.ι.IsContinuous (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)]
    (hobj : ∀ I : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u + 1},
      Injective I → ∀ (x : P.FullSubcategory) (n : ℕ)
      (a : Abelian.Ext (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{u + 1}
        (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)) x)
        ((subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ) P).obj I) (n + 1)), a = 0)
    {K F : _ ⥤ Type (u + 1)} (e : K ≅ P.ι.op ⋙ F) (hF : RepresentedOverSubsite 𝒳 P F)
    (I : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u + 1})
    (hI : Injective I) (n : ℕ) (b : Abelian.Ext ((Presheaf.freeAbelianSheaf
      (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))).obj K)
      ((subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ) P).obj I) (n + 1)) : b = 0 := by
  have := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  have := hI
  exact Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_iso_first
    ((Presheaf.freeAbelianSheaf _).mapIso e) (n + 1)
    (ext_restriction_eq_zero_of_mem
      (isClosedUnderRepresentableCovers_representedOverSubsite τ P hcl) hobj hF I n) b

namespace LisseEtale

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- The closure condition of Stacks 07AK (1) for the smooth objects, in the form of
`AlgebraicGeometry.Stack.IsClosedUnderSitePullback`. -/
theorem isClosedUnderSitePullback_smoothObject (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    IsClosedUnderSitePullback B S hS 𝒳.val.val.p (smoothObject.{u, w} B S hS 𝒳) .etale :=
  Or.inl ⟨rfl, fun f hf hy => closedUnderSmoothMorphisms.{u, w} B S hS 𝒳 f hf hy⟩

include hf in
omit hf in
/-- **The presheaf represented by `V ×_{y, 𝒴} 𝒳 ⟶ 𝒳` is represented over the lisse-étale site.**
For a smooth object `y` of `𝒴` the projection of the 2-fibre product of `f` and `y` is smooth,
being a base change of `y`, and its underlying functor is faithful. -/
theorem representedOverSubsite_twoFibreProductFst (y : LisseEtale.{u, w} B S hS 𝒴) :
    RepresentedOverSubsite 𝒳 (smoothObject.{u, w} B S hS 𝒳)
      (componentPresheaf (CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks
        B S hS f (Bicategory.InducedBicategory.mkHom (objectMorphism B S hS 𝒴.val
          (Functor.Fiber.mk (a := y.obj) rfl)) :
            schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj) ⟶ 𝒴)).fst.hom)) := by
  let yV : schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj) ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒴.val (Functor.Fiber.mk (a := y.obj) rfl))
  have : (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj)).val.val.p.Faithful :=
    inferInstanceAs (Over.forget _).Faithful
  exact ⟨_, (twoFibreProductSquareAlgebraicStacks B S hS f yV).fst,
    faithful_twoFibreProductOver_fst _ _ _ _ _, fun {D} e he =>
      smoothObject_map.{u, w} B S hS (e ≫ (twoFibreProductSquareAlgebraicStacks B S hS f yV).fst)
        (AlgebraicStacks.isSmooth_comp B S hS _ _ he
          (AlgebraicStacks.isSmooth_baseChange B S hS yV f _
            (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f yV) y.property))
        ⟨Over.mk (𝟙 D), smoothObject_schemeStack_id.{u, w} B S hS D⟩, ⟨Iso.refl _⟩⟩

/-- **`K_y` is the restriction of the presheaf represented by `V ×_{y, 𝒴} 𝒳 ⟶ 𝒳`.** The presheaf
`x ↦ Hom(f' x, y)` on the lisse-étale site of `𝒳` is the restriction of the presheaf of components
of the projection of the 2-fibre product of `f` and `y`. -/
def restrictedYonedaIso (y : LisseEtale.{u, w} B S hS 𝒴) :
    Stacks.Cohomology.CocontinuousPushforward.restrictedYoneda.{u + 1, u + 1, u, u, u}
        (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
          (smoothObject_map.{u, w} B S hS f hf)) y ≅
      (smoothObject.{u, w} B S hS 𝒳).ι.op ⋙
        componentPresheaf (CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks
          B S hS f (Bicategory.InducedBicategory.mkHom (objectMorphism B S hS 𝒴.val
            (Functor.Fiber.mk (a := y.obj) rfl)) :
              schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj) ⟶ 𝒴)).fst.hom) :=
  (Functor.isoWhiskerLeft (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)).op
      (uliftYonedaRestrictIso (u := (smoothObject.{u, w} B S hS 𝒴).ι) y)).symm ≪≫
    (Functor.isoWhiskerLeft (smoothObject.{u, w} B S hS 𝒳).ι.op
      (componentPresheafTwoFibreProductFstIso f y.obj)).symm

include hf in
/-- **`Ext^{n+1}(ℤ_{K_y}^♯, (g')⁻¹I) = 0`** for an injective abelian sheaf `I` on the étale site of
`𝒳`, a smooth object `y` of `𝒴` and the presheaf `K_y = Hom(f' -, y)` on the lisse-étale site of
`𝒳`. This is the descent `Stacks.Sites.CoverDescent.ext_restriction_eq_zero_of_mem` for the class
`AlgebraicGeometry.Stack.RepresentedOverSubsite`, of which `K_y` is a member by
`AlgebraicGeometry.Stack.LisseEtale.representedOverSubsite_twoFibreProductFst`, with Stacks 0D6X
over the objects of the lisse-étale site as its input. -/
theorem ext_restriction_restrictedYoneda_eq_zero
    (I : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AddCommGrpCat.{u + 1})
    [Injective I] (y : LisseEtale.{u, w} B S hS 𝒴) (n : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    ∀ b : Abelian.Ext ((Presheaf.freeAbelianSheaf (inclusionTopology.{u, w} B S hS 𝒳)).obj
        (Stacks.Cohomology.CocontinuousPushforward.restrictedYoneda.{u + 1, u + 1, u, u, u}
          (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
            (smoothObject_map.{u, w} B S hS f hf)) y))
        ((subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
          (smoothObject.{u, w} B S hS 𝒳)).obj I) (n + 1), b = 0 := by
  have hcl := isClosedUnderSitePullback_smoothObject 𝒳
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p _ _ 𝒳.val.isFiberedInGroupoids hcl
  exact fun b => ext_restriction_eq_zero_of_iso_restriction .etale _ hcl
    (fun I hI d n a => objectAcyclic.{u, w} B S hS 𝒳 I hI d n a) (restrictedYonedaIso f hf y)
    (representedOverSubsite_twoFibreProductFst f y) I ‹_› n b

attribute [local instance] isGrothendieckAbelian_sheaf_inclusionTopology
  hasPointwiseRightKanExtension_primedSiteFunctor

include hf in
/-- **The restriction of an injective abelian sheaf to the lisse-étale site is acyclic for the
direct image along `f'`.** For a smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks and an injective
abelian sheaf `I` on the étale site of `𝒳`, the higher direct images `R^p f'_* (g')⁻¹I` vanish for
`p > 0`: by
`Stacks.Cohomology.CocontinuousPushforward.isZero_rightDerived_sheafPushforwardCocontinuous`
this is the vanishing of `Ext^p(ℤ_{K_y}^♯, (g')⁻¹I)`, which is
`AlgebraicGeometry.Stack.LisseEtale.ext_restriction_restrictedYoneda_eq_zero`. -/
theorem isZero_rightDerived_restriction_of_injective
    (I : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AddCommGrpCat.{u + 1})
    [Injective I] (n : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf))
      (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
    IsZero ((((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
        (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
          AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
          (inclusionTopology.{u, w} B S hS 𝒴)).rightDerived (n + 1)).obj
      ((subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)).obj I)) := by
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  exact Stacks.Cohomology.CocontinuousPushforward.isZero_rightDerived_sheafPushforwardCocontinuous.{
    u + 1, u + 1, u, u, u + 1} _ _ _ _ n (ext_restriction_restrictedYoneda_eq_zero f hf I · n)

end LisseEtale

namespace FlatFppf

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f)

/-- The closure condition of Stacks 07AK (1) for the flat objects, in the form of
`AlgebraicGeometry.Stack.IsClosedUnderSitePullback`. -/
theorem isClosedUnderSitePullback_flatObject (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    IsClosedUnderSitePullback B S hS 𝒳.val.val.p (flatObject B S hS 𝒳.val) .fppf :=
  Or.inr ⟨rfl, fun f hf hlfp hy => closedUnderFlatMorphisms B S hS 𝒳 f hf hlfp hy⟩

include hf in
omit hf in
/-- **The presheaf represented by `V ×_{y, 𝒴} 𝒳 ⟶ 𝒳` is represented over the flat-fppf site.**
For a flat object `y` of `𝒴` the projection of the 2-fibre product of `f` and `y` is flat,
being a base change of `y`, and its underlying functor is faithful. -/
theorem representedOverSubsite_twoFibreProductFst (y : FlatFppf B S hS 𝒴) :
    RepresentedOverSubsite 𝒳 (flatObject B S hS 𝒳.val)
      (componentPresheaf (CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks
        B S hS f (Bicategory.InducedBicategory.mkHom (objectMorphism B S hS 𝒴.val
          (Functor.Fiber.mk (a := y.obj) rfl)) :
            schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj) ⟶ 𝒴)).fst.hom)) := by
  let yV : schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj) ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒴.val (Functor.Fiber.mk (a := y.obj) rfl))
  have : (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj)).val.val.p.Faithful :=
    inferInstanceAs (Over.forget _).Faithful
  exact ⟨_, (twoFibreProductSquareAlgebraicStacks B S hS f yV).fst,
    faithful_twoFibreProductOver_fst _ _ _ _ _, fun {D} e he =>
      flatObject_map B S hS (e ≫ (twoFibreProductSquareAlgebraicStacks B S hS f yV).fst)
        (AlgebraicStacks.isFlat_comp B S hS _ _ (AlgebraicStacks.isFlat_of_isSmooth B S hS e he)
          (AlgebraicStacks.isFlat_baseChange B S hS yV f _
            (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f yV) y.property))
        ⟨Over.mk (𝟙 D), flatObject_schemeStack_id.{u, w} B S hS D⟩, ⟨Iso.refl _⟩⟩

/-- **`K_y` is the restriction of the presheaf represented by `V ×_{y, 𝒴} 𝒳 ⟶ 𝒳`.** The presheaf
`x ↦ Hom(f' x, y)` on the flat-fppf site of `𝒳` is the restriction of the presheaf of components
of the projection of the 2-fibre product of `f` and `y`. -/
def restrictedYonedaIso (y : FlatFppf B S hS 𝒴) :
    Stacks.Cohomology.CocontinuousPushforward.restrictedYoneda.{u + 1, u + 1, u, u, u}
        (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
          (flatObject_map B S hS f hf)) y ≅
      (objectProperty B S hS 𝒳).ι.op ⋙
        componentPresheaf (CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks
          B S hS f (Bicategory.InducedBicategory.mkHom (objectMorphism B S hS 𝒴.val
            (Functor.Fiber.mk (a := y.obj) rfl)) :
              schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj) ⟶ 𝒴)).fst.hom) :=
  (Functor.isoWhiskerLeft (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)).op
      (uliftYonedaRestrictIso (u := (objectProperty B S hS 𝒴).ι) y)).symm ≪≫
    (Functor.isoWhiskerLeft (objectProperty B S hS 𝒳).ι.op
      (componentPresheafTwoFibreProductFstIso f y.obj)).symm

include hf in
/-- **`Ext^{n+1}(ℤ_{K_y}^♯, (g')⁻¹I) = 0`** for an injective abelian sheaf `I` on the fppf site of
`𝒳`, a flat object `y` of `𝒴` and the presheaf `K_y = Hom(f' -, y)` on the flat-fppf site of
`𝒳`. This is the descent `Stacks.Sites.CoverDescent.ext_restriction_eq_zero_of_mem` for the class
`AlgebraicGeometry.Stack.RepresentedOverSubsite`, of which `K_y` is a member by
`AlgebraicGeometry.Stack.LisseEtale.representedOverSubsite_twoFibreProductFst`, with Stacks 0D6X
over the objects of the flat-fppf site as its input. -/
theorem ext_restriction_restrictedYoneda_eq_zero
    (I : Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AddCommGrpCat.{u + 1})
    [Injective I] (y : FlatFppf B S hS 𝒴) (n : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    ∀ b : Abelian.Ext ((Presheaf.freeAbelianSheaf (inclusionTopology B S hS 𝒳)).obj
        (Stacks.Cohomology.CocontinuousPushforward.restrictedYoneda.{u + 1, u + 1, u, u, u}
          (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
            (flatObject_map B S hS f hf)) y))
        ((subsiteRestriction B S hS 𝒳.val.val.p B.topology
          (flatObject B S hS 𝒳.val)).obj I) (n + 1), b = 0 := by
  have hcl := isClosedUnderSitePullback_flatObject 𝒳
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p _ _ 𝒳.val.isFiberedInGroupoids hcl
  exact fun b => ext_restriction_eq_zero_of_iso_restriction .fppf _ hcl
    (fun I hI d n a => objectAcyclic B S hS 𝒳 I hI d n a) (restrictedYonedaIso f hf y)
    (representedOverSubsite_twoFibreProductFst f y) I ‹_› n b

attribute [local instance] hasPointwiseRightKanExtension_primedSiteFunctor

include hf in
/-- **The restriction of an injective abelian sheaf to the flat-fppf site is acyclic for the
direct image along `f'`.** For a smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks and an injective
abelian sheaf `I` on the fppf site of `𝒳`, the higher direct images `R^p f'_* (g')⁻¹I` vanish for
`p > 0`: by
`Stacks.Cohomology.CocontinuousPushforward.isZero_rightDerived_sheafPushforwardCocontinuous`
this is the vanishing of `Ext^p(ℤ_{K_y}^♯, (g')⁻¹I)`, which is
`AlgebraicGeometry.Stack.LisseEtale.ext_restriction_restrictedYoneda_eq_zero`. -/
theorem isZero_rightDerived_restriction_of_injective
    (I : Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AddCommGrpCat.{u + 1})
    [Injective I] (n : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    haveI := isCocontinuous_subsiteFunctor B S hS f hf
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf))
      (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
    IsZero ((((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
        (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
          AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
          (inclusionTopology B S hS 𝒴)).rightDerived (n + 1)).obj
      ((subsiteRestriction B S hS 𝒳.val.val.p B.topology
        (flatObject B S hS 𝒳.val)).obj I)) := by
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have := isCocontinuous_subsiteFunctor B S hS f hf
  exact Stacks.Cohomology.CocontinuousPushforward.isZero_rightDerived_sheafPushforwardCocontinuous.{
    u + 1, u + 1, u, u, u + 1} _ _ _ _ n (ext_restriction_restrictedYoneda_eq_zero f hf I · n)

end FlatFppf

end AlgebraicGeometry.Stack
