module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelativeConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePullbackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningEtaleChartTower

/-!
# Étaleness of a 1-morphism from an étale chart of one of its base changes

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks representable by algebraic spaces, let
`V ⟶ 𝒴` be a smooth 1-morphism from an algebraic space and let `U ⟶ V ×_𝒴 𝒳` be an étale
1-morphism from an algebraic space into the 2-fibre product. If the composite `U ⟶ V` is induced
by an étale morphism of algebraic spaces and the composite `U ⟶ 𝒳` is surjective, then `f` is
étale in the sense of Stacks 04XB.

This is the existential étale-smooth diagram test of Stacks 0CIF at étaleness (étale-smooth local
on the source-and-target by Stacks 0CG3), with the diagram read off the chart `U`. In the proof
that a DM algebraic stack is Deligne–Mumford (Stacks 06N3) it is the step which turns an étale
slice of a smooth chart into an étale 1-morphism from a scheme to the stack.

## Main results

* `AlgebraicGeometry.Stack.isRelativelyEtale_of_etaleChart_twoFibreProduct`: the criterion.
* `AlgebraicGeometry.Stack.isRelativelyEtale_of_etaleChart_twoFibreProduct_scheme`: the same,
  with the chart and the smooth 1-morphism out of schemes of the site.
* `AlgebraicGeometry.Stack.isRelativelyEtale_comp_of_etaleSlice`: an open (more generally étale)
  piece of `E ×_U Z`, for `E` an étale chart of `U ×_𝒳 W`, which is étale over `W` and surjects
  onto `Z`, makes `Z ⟶ U ⟶ 𝒳` étale.
* `AlgebraicGeometry.Stack.isSurjective_schemeStackMap`,
  `AlgebraicGeometry.Stack.isRelativelyEtale_schemeFibredCategoryMap`: surjective and étale
  morphisms of the site induce surjective and étale 1-morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Surjectivity of a 1-morphism of algebraic stacks transfers along a 2-isomorphism. -/
private theorem isSurjective_of_iso {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴}
    (α : f ≅ g) (h : IsSurjective B S hS f) : IsSurjective B S hS g :=
  (congrArg Function.Surjective (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS α.hom)).mp h

/-- **Étaleness from an étale chart of a base change along a smooth 1-morphism.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks representable by algebraic spaces, `b` a smooth
1-morphism from an algebraic space `V` to `𝒴`, `Q₁` a 2-fibre product of `(b, f)` and `cc` an
étale 1-morphism from an algebraic space `U` into its apex. If the composite of `cc` with the
projection to `V` is induced by an étale morphism `h : U ⟶ V` of algebraic spaces and the
composite of `cc` with the projection to `𝒳` is surjective, then `f` is étale in the sense of
Stacks 04XB. -/
theorem isRelativelyEtale_of_etaleChart_twoFibreProduct
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (b : fibredCategory B S hS V ⟶ 𝒴.val) (hb : IsRelativelySmooth B S hS b)
    (Q₁ : Bicategory.TwoCommSq b f.hom) (hQ₁ : Bicategory.IsTwoFibreProduct Q₁)
    (cc : fibredCategory B S hS U ⟶ Q₁.pt) (hcc : IsRelativelyEtale B S hS cc)
    (h : U ⟶ V) (hh : Space.IsEtale B S hS h) (e : (associatedMap B S hS h).1 ≅ cc ≫ Q₁.fst)
    (ha : IsSurjective B S hS
      (Bicategory.InducedBicategory.mkHom (cc ≫ Q₁.snd) :
        algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)) :
    IsRelativelyEtale B S hS f.hom := by
  refine ⟨hf, hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram.{u, u, w} B S hS _
    (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) f hf ?_⟩
  exact ⟨U, V, hU, hV, Bicategory.InducedBicategory.mkHom (cc ≫ Q₁.snd),
    Bicategory.InducedBicategory.mkHom b, h,
    Bicategory.whiskerRightIso e b ≪≫ Bicategory.whiskerLeftIso cc Q₁.iso, ha, hb,
    fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom b Q₁ hQ₁ cc hcc
      h e Q hQ k, hh⟩

/-- **Étaleness from an étale chart of a base change, with schemes of the site.** The same
criterion as `AlgebraicGeometry.Stack.isRelativelyEtale_of_etaleChart_twoFibreProduct`, with the
smooth 1-morphism `b` and the étale chart `cc` out of the categories represented by schemes `W`
and `P` of the site, and the composite `P ⟶ W` induced by an étale morphism `h` of the site.

The slices are read as categories of elements through the backward 1-morphisms of their
representing equivalences, which are étale and surjective; the chart is pulled back along the one
for `W` and pasted onto `Q₁`. -/
theorem isRelativelyEtale_of_etaleChart_twoFibreProduct_scheme
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    {P W : BigFppfOver B S hS}
    (b : schemeFibredCategory B S hS W ⟶ 𝒴.val) (hb : IsRelativelySmooth B S hS b)
    (Q₁ : Bicategory.TwoCommSq b f.hom) (hQ₁ : Bicategory.IsTwoFibreProduct Q₁)
    (cc : schemeFibredCategory B S hS P ⟶ Q₁.pt) (hcc : IsRelativelyEtale B S hS cc)
    (h : P ⟶ W) (hh : Etale ((BigFppfOver.toScheme B S hS).map h))
    (e : schemeFibredCategoryMap B S hS h ≅ cc ≫ Q₁.fst)
    (ha : IsSurjective B S hS
      (Bicategory.InducedBicategory.mkHom (cc ≫ Q₁.snd) : schemeStack.{u, w} B S hS P ⟶ 𝒳)) :
    IsRelativelyEtale B S hS f.hom := by
  set κW := equivalenceOverInvMap B S hS (𝒳 := schemeFibredCategory B S hS W) (yoneda.obj W)
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
  set κP := equivalenceOverInvMap B S hS (𝒳 := schemeFibredCategory B S hS P) (yoneda.obj P)
    (PresheafOfCategories.sliceElementsEquivalenceOver P)
  have hκWet : IsRelativelyEtale B S hS κW :=
    isRelativelyEtale_equivalenceOverInvMap B S hS _ (isAlgebraicSpace_yoneda B S hS W) _
  have hκPeq : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor κP) :=
    (PresheafOfCategories.sliceElementsEquivalenceOver P).toEquivalence.symm.isEquivalence_functor
  have hbsm : IsRelativelySmooth B S hS (κW ≫ b) :=
    isRelativelySmooth_comp B S hS κW b (isRelativelySmooth_of_isRelativelyEtale B S hS κW hκWet)
      hb
  obtain ⟨θ₀⟩ := nonempty_twoIso_associatedMap_comp_equivalenceOverInvMap B S hS
    (PresheafOfCategories.sliceElementsEquivalenceOver P)
    (PresheafOfCategories.sliceElementsEquivalenceOver W) (schemeFibredCategoryMap B S hS h)
  rw [representingMap_schemeFibredCategoryMap] at θ₀
  set Tsq : Bicategory.TwoCommSq κW Q₁.fst :=
    { pt := fibredCategory B S hS (yoneda.obj P)
      fst := (associatedMap B S hS (yoneda.map h)).1
      snd := κP ≫ cc
      iso := θ₀ ≪≫ Bicategory.whiskerLeftIso κP e ≪≫ (Bicategory.associator κP cc Q₁.fst).symm }
  set Lq := twoFibreProductSquare.{u, u, u + 1, u + 1} κW Q₁.fst
  have hLq : Bicategory.IsTwoFibreProduct Lq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} κW Q₁.fst
  have hLqsndet : IsRelativelyEtale B S hS Lq.snd :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS (yoneda.obj W))
      (schemeFibredCategory B S hS W) Q₁.pt κW Q₁.fst Lq.swap
      (Bicategory.isTwoFibreProduct_swap hLq) hκWet
  set m := Bicategory.twoFibreProductPreHom hLq Tsq
  have hmet : IsRelativelyEtale B S hS m.hom :=
    isRelativelyEtale_of_comp B S hS m.hom Lq.snd
      (isRelativelyEtale_congr_twoIso B S hS m.isoSnd
        (isRelativelyEtale_of_isEquivalence_comp B S hS κP cc hκPeq hcc)) hLqsndet
  refine isRelativelyEtale_of_etaleChart_twoFibreProduct B S hS f hf
    (isAlgebraicSpace_yoneda B S hS P) (isAlgebraicSpace_yoneda B S hS W) (κW ≫ b) hbsm
    (Q₁.pasteFst Lq) (Bicategory.isTwoFibreProduct_pasteFst Q₁ hQ₁ Lq hLq) m.hom hmet
    (yoneda.map h)
    (Space.isEtale_of_presheaf_etale B S hS ((Space.presheaf_yoneda_map_etale_iff B S hS h).2 hh))
    m.isoFst ?_
  -- surjectivity: the composite is `κP ≫ cc ≫ Q₁.snd` up to a 2-isomorphism
  let aP : algebraicSpaceStack.{u, w} B S hS (yoneda.obj P) (isAlgebraicSpace_yoneda B S hS P) ⟶
      schemeStack.{u, w} B S hS P := Bicategory.InducedBicategory.mkHom κP
  let aC : schemeStack.{u, w} B S hS P ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom (cc ≫ Q₁.snd)
  let aM : algebraicSpaceStack.{u, w} B S hS (yoneda.obj P) (isAlgebraicSpace_yoneda B S hS P) ⟶
      𝒳 := Bicategory.InducedBicategory.mkHom (m.hom ≫ (Q₁.pasteFst Lq).snd)
  have hiso : aP ≫ aC ≅ aM := Bicategory.InducedBicategory.isoMk
    ((Bicategory.associator κP cc Q₁.snd).symm ≪≫ Bicategory.whiskerRightIso m.isoSnd Q₁.snd ≪≫
      Bicategory.associator m.hom Lq.snd Q₁.snd)
  exact isSurjective_of_iso B S hS hiso
    (isSurjective_comp B S hS aP aC (pointsMap_surjective_of_isSurjectiveOnObjects B S hS _
      (isSurjectiveOnObjects_equivalenceOverInvMap B S hS _ _)) ha)

/-- **A surjective morphism of the site induces a surjective 1-morphism of algebraic stacks**
(Stacks 04ZS): the identification of the points of a represented algebraic stack with its
scheme is natural. -/
theorem isSurjective_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Function.Surjective ((BigFppfOver.toScheme B S hS).map g).base) :
    IsSurjective B S hS (schemeStackMap.{u, w} B S hS g) := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  let _ := pointTopology B S hS (schemeFibredCategory B S hS V)
  have hfun : (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g)) =
      (pointsHomeomorphScheme B S hS V).symm ∘
        (((BigFppfOver.toScheme B S hS).map g).base ∘ (pointsHomeomorphScheme B S hS U)) := by
    refine funext fun z => (pointsHomeomorphScheme B S hS V).injective ?_
    rw [Function.comp_apply, Function.comp_apply, Homeomorph.apply_symm_apply]
    exact pointsHomeomorphScheme_naturality B S hS g z
  rw [IsSurjective, hfun]
  exact (pointsHomeomorphScheme B S hS V).symm.surjective.comp
    (hg.comp (pointsHomeomorphScheme B S hS U).surjective)

/-- The 1-morphism of represented categories induced by a composite of morphisms of the site is
the composite of the induced 1-morphisms. -/
theorem schemeFibredCategoryMap_comp {U V W : BigFppfOver B S hS} (a : U ⟶ V) (b : V ⟶ W) :
    schemeFibredCategoryMap B S hS (a ≫ b) =
      schemeFibredCategoryMap B S hS a ≫ schemeFibredCategoryMap B S hS b :=
  Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' (Over.mapComp_eq a b))

/-- **An étale morphism of the site induces an étale 1-morphism** in the sense of Stacks 04XB. -/
theorem isRelativelyEtale_schemeFibredCategoryMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Etale ((BigFppfOver.toScheme B S hS).map g)) :
    IsRelativelyEtale B S hS (schemeFibredCategoryMap B S hS g) :=
  ⟨isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g,
    hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS (Space.etaleMorphisms B S hS) g
      (Space.isEtale_of_presheaf_etale B S hS
        ((Space.presheaf_yoneda_map_etale_iff B S hS g).2 hg))⟩

/-- **An étale slice of a smooth chart is étale over the stack.** Let `𝒳` be an algebraic stack,
`fU : U ⟶ 𝒳` a 1-morphism and `b : W ⟶ 𝒳` a smooth one from schemes of the site, `Q₀` a
2-fibre product of `(fU, b)` and `c : E ⟶ Q₀.pt` an étale 1-morphism from a scheme whose two
composites with the projections are induced by morphisms `s : E ⟶ U` and `t : E ⟶ W` of the
site. Let `ι : Z ⟶ U` be a morphism of the site and `P ⟶ E ×_U Z` an étale morphism such that
the composite `P ⟶ Z` is surjective and the composite `P ⟶ W` is étale. Then `Z ⟶ U ⟶ 𝒳` is
étale in the sense of Stacks 04XB.

The fibre product `E ×_U Z` of the site is the 2-fibre product of `c` with the base change
`Z ×_U Q₀.pt ⟶ Q₀.pt` (cancellation of 2-fibre products), so `E ×_U Z ⟶ Z ×_U Q₀.pt` is étale
as a base change of `c`, and `Z ×_U Q₀.pt` is the 2-fibre product `W ×_𝒳 Z` by pasting. -/
theorem isRelativelyEtale_comp_of_etaleSlice
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U W E Z EZ P : BigFppfOver B S hS}
    (fU : schemeFibredCategory B S hS U ⟶ 𝒳.val) (b : schemeFibredCategory B S hS W ⟶ 𝒳.val)
    (hb : IsRelativelySmooth B S hS b)
    (Q₀ : Bicategory.TwoCommSq fU b) (hQ₀ : Bicategory.IsTwoFibreProduct Q₀)
    (c : schemeFibredCategory B S hS E ⟶ Q₀.pt) (hc : IsRelativelyEtale B S hS c)
    (s : E ⟶ U) (t : E ⟶ W) (eS : schemeFibredCategoryMap B S hS s ≅ c ≫ Q₀.fst)
    (eT : schemeFibredCategoryMap B S hS t ≅ c ≫ Q₀.snd)
    (ι : Z ⟶ U) {pr₁ : EZ ⟶ E} {pr₂ : EZ ⟶ Z} (hpb : IsPullback pr₁ pr₂ s ι)
    (p : P ⟶ EZ) (hp : Etale ((BigFppfOver.toScheme B S hS).map p))
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map (p ≫ pr₂)).base)
    (het : Etale ((BigFppfOver.toScheme B S hS).map (p ≫ pr₁ ≫ t))) :
    IsRelativelyEtale B S hS (schemeFibredCategoryMap B S hS ι ≫ fU) := by
  let f : schemeStack.{u, w} B S hS Z ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS ι ≫ fU)
  have hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS Z) _
  -- the base change of `Q₀` along `ι`, pasted onto `Q₀`
  set T := twoFibreProductSquare.{u, u, u + 1, u + 1} (schemeFibredCategoryMap B S hS ι) Q₀.fst
  have hT : Bicategory.IsTwoFibreProduct T :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hQ₁ : Bicategory.IsTwoFibreProduct (Q₀.pasteFst T).swap :=
    Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_pasteFst Q₀ hQ₀ T hT)
  -- the fibre product `E ×_U Z` of the site, over `(c ≫ Q₀.fst, ι)`
  set Sq := (schemeFibredCategorySquare B S hS hpb.w).reindexFst eS
  have hSq : Bicategory.IsTwoFibreProduct Sq :=
    Bicategory.isTwoFibreProduct_reindexFst eS
      (isTwoFibreProduct_schemeFibredCategorySquare B S hS hpb)
  set p₀ := Bicategory.twoFibreProductPreHom (Bicategory.isTwoFibreProduct_swap hT)
    (Bicategory.pasteOuterSq c Sq)
  have hInner : Bicategory.IsTwoFibreProduct (Bicategory.pasteInnerSq T.swap p₀) :=
    isTwoFibreProduct_pasteInnerSq B S hS T.swap (Bicategory.isTwoFibreProduct_swap hT) hSq p₀
  have hp₀ : IsRelativelyEtale B S hS p₀.hom :=
    isRelativelyEtale_baseChange B S hS (schemeFibredCategory B S hS E) Q₀.pt T.pt c T.snd
      (Bicategory.pasteInnerSq T.swap p₀).swap (Bicategory.isTwoFibreProduct_swap hInner) hc
  set cc := schemeFibredCategoryMap B S hS p ≫ p₀.hom
  have hcc : IsRelativelyEtale B S hS cc :=
    isRelativelyEtale_comp B S hS _ _ (isRelativelyEtale_schemeFibredCategoryMap B S hS p hp) hp₀
  have hcomp₁ : schemeFibredCategoryMap B S hS (p ≫ pr₁ ≫ t) =
      schemeFibredCategoryMap B S hS p ≫ schemeFibredCategoryMap B S hS pr₁ ≫
        schemeFibredCategoryMap B S hS t := by
    rw [schemeFibredCategoryMap_comp, schemeFibredCategoryMap_comp]
  have e : schemeFibredCategoryMap B S hS (p ≫ pr₁ ≫ t) ≅ cc ≫ (Q₀.pasteFst T).swap.fst :=
    eqToIso hcomp₁ ≪≫ Bicategory.whiskerLeftIso (schemeFibredCategoryMap B S hS p)
      (Bicategory.whiskerLeftIso (schemeFibredCategoryMap B S hS pr₁) eT ≪≫
        (Bicategory.associator (schemeFibredCategoryMap B S hS pr₁) c Q₀.snd).symm ≪≫
        Bicategory.whiskerRightIso p₀.isoFst Q₀.snd ≪≫
        Bicategory.associator p₀.hom T.snd Q₀.snd) ≪≫
      (Bicategory.associator (schemeFibredCategoryMap B S hS p) p₀.hom (T.snd ≫ Q₀.snd)).symm
  have ea : schemeFibredCategoryMap B S hS (p ≫ pr₂) ≅ cc ≫ (Q₀.pasteFst T).swap.snd :=
    eqToIso (schemeFibredCategoryMap_comp B S hS p pr₂) ≪≫
      Bicategory.whiskerLeftIso (schemeFibredCategoryMap B S hS p) p₀.isoSnd ≪≫
      (Bicategory.associator (schemeFibredCategoryMap B S hS p) p₀.hom T.fst).symm
  have ha : IsSurjective B S hS
      (Bicategory.InducedBicategory.mkHom (cc ≫ (Q₀.pasteFst T).swap.snd) :
        schemeStack.{u, w} B S hS P ⟶ schemeStack.{u, w} B S hS Z) := by
    exact isSurjective_of_iso B S hS (Bicategory.InducedBicategory.isoMk ea)
      (isSurjective_schemeStackMap.{u, w} B S hS (p ≫ pr₂) hsurj)
  exact isRelativelyEtale_of_etaleChart_twoFibreProduct_scheme B S hS f hf b hb
    (Q₀.pasteFst T).swap hQ₁ cc hcc (p ≫ pr₁ ≫ t) het e ha

end AlgebraicGeometry.Stack

end
