module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFMapCompChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartSectionCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsIdComparison
public import StacksFrontier.CategoryTheory.Adjunction.CompTranspose
public import StacksFrontier.CategoryTheory.Adjunction.CompTransposeExtensions

/-!
# Composition and unit laws for the module comparison maps of equation 076R

For a 2-commutative triangle `φ : a ⋙ f' ≅ f` of 1-morphisms of categories fibred in groupoids
over `(Sch/S)_{fppf}` whose sources are representable by algebraic spaces, equation 076R of the
source constructs the comparison map
`c_φ : a_small^*(f'^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale}`
(`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules`). This file proves for these maps the
composition law of Stacks 075D (1), the unit law, and the 2-cell law.

## Main results

* `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_comp_compTriangleIso`:
  **Stacks 075D (1) for the module comparison maps of equation 076R.** For triangles
  `ψ : b ⋙ g ≅ f'` and `φ : a ⋙ f' ≅ f`, `aSpace^*(c_ψ)` followed by `c_φ` is the comparison map
  of the composite triangle read through `(aSpace ≫ bSpace)^* ≅ aSpace^* ∘ bSpace^*` of
  Stacks 03LU.
* `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_id`: **the unit law.** For the
  identity triangle the comparison map is the unit law `(𝟙 U)^* ≅ 𝟭` of Stacks 03LU.
* `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_twoMorphism`: **the 2-cell law.**
  Two triangles `φ : a ⋙ g ≅ f`, `φ' : a ⋙ g ≅ f'` related by a 2-morphism `t : f' ⟶ f` over the
  identity have `c_{φ'} = c_φ ≫ t^*`, with `t^*` restriction of sections along `t`
  (`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImageTwoMorphism`).
* `AlgebraicGeometry.Space.ModuleFMap.ext_of_app_chartDiagram_comp`: a linear map of sections
  along a composite `f ≫ g` of morphisms of algebraic spaces is determined by its values at the
  chart diagrams that factor through an étale scheme chart of the middle space.

## References

* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w' v'' w'' v''' w'''

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms into an iterated direct image of modules -/

section IteratedPushforward

variable {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
  (F : Modules.{u, u} B S hS X.1 X.2) (H : Modules.{u, u} B S hS Z.1 Z.2)

/-- **A morphism into an iterated direct image of modules is determined by its iterated chart
components.** Two morphisms `H ⟶ g_*(f_*F)` agree as soon as, for every diagram `e` of étale scheme
charts over `g` and every diagram over `f` whose chart of `Y` is the chart `e.U` of `e`, the chart
component along `f` of the chart component along `g` of the two morphisms agree. -/
theorem modulePushforward_comp_hom_ext
    {φ₁ φ₂ : H ⟶ (modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj F)}
    (h : ∀ (e : ChartDiagram B S hS Y.1 Z.1 g.hom)
      (j : StructuredArrow (op (chartBaseChange B S hS f e.U)) (comparisonFunctor B S hS X).op)
      (s : H.val.obj (op e.V)),
      modulePushforwardCounitApp B S hS f F (chartDiagramOfIndex B S hS f e.U j)
          (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj F) e
            (φ₁.val.app (op e.V) s)) =
        modulePushforwardCounitApp B S hS f F (chartDiagramOfIndex B S hS f e.U j)
          (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj F) e
            (φ₂.val.app (op e.V) s))) :
    φ₁ = φ₂ := by
  refine (modulePushforwardHomEquiv B S hS g ((modulePushforward B S hS f).obj F) H).injective ?_
  refine ModuleFMap.ext B S hS (funext fun e ↦ funext fun s ↦ ?_)
  refine directImageChartSection_ext B S hS f F e.U (fun j ↦ ?_)
  refine (directImageChartSection_eq_counitApp B S hS f F e.U j _).trans ?_
  refine Eq.trans ?_ (directImageChartSection_eq_counitApp B S hS f F e.U j _).symm
  exact h e j s

/-- **The chart component along a composite, at a diagram that factors, is the iterated chart
component.** For a morphism `φ : H ⟶ (f ≫ g)_*F`, its chart component along `f ≫ g` at the
composite of a diagram over `f` and a diagram over `g` sharing the middle chart is the chart
component along `f` of the chart component along `g` of `φ`, read in `g_*(f_*F)` through a
comparison `ι` of direct images which is the geometric comparison of Stacks 03G2, part (3), on
underlying sheaves of sets. -/
theorem modulePushforwardHomFMap_app_chartDiagram_comp
    (ι : modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅
      modulePushforward B S hS (f ≫ g))
    (hι : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map (ι.hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
    (φ : H ⟶ (modulePushforward B S hS (f ≫ g)).obj F)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom) (s : H.val.obj (op W)) :
    (modulePushforwardHomFMap B S hS (f ≫ g) F H φ).app
        (ChartDiagram.comp B S hS f g a b ha hb) s =
      modulePushforwardCounitApp B S hS f F ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj F) ⟨V, W, b, hb⟩
          ((φ ≫ ι.inv.app F).val.app (op W) s)) := by
  have hcomp : moduleFMapCompHom B S hS f g F ((modulePushforward B S hS f).obj F) H
      (modulePushforwardHomFMap B S hS g ((modulePushforward B S hS f).obj F) H
        (φ ≫ ι.inv.app F))
      (modulePushforwardCounit B S hS f F) ι = φ := by
    rw [moduleFMapCompHom_eq, moduleFMapHom_modulePushforwardHomFMap,
      moduleFMapHom_modulePushforwardCounit, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have h := ModuleFMap.compOfIso_app B S hS f g a b ha hb F
    ((modulePushforward B S hS f).obj F) H
    (modulePushforwardHomFMap B S hS g ((modulePushforward B S hS f).obj F) H
      (φ ≫ ι.inv.app F))
    (modulePushforwardCounit B S hS f F) ι hι s
  unfold ModuleFMap.compOfIso at h
  rwa [hcomp] at h

/-- **A linear map of sections along a composite is determined by its values at the chart diagrams
that factor through an étale scheme chart of the middle space.** -/
theorem ModuleFMap.ext_of_app_chartDiagram_comp {ζ₁ ζ₂ : ModuleFMap B S hS (f ≫ g) F H}
    (h : ∀ {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
      (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
      (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
      (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom) (s : H.val.obj (op W)),
      ζ₁.app (ChartDiagram.comp B S hS f g a b ha hb) s =
        ζ₂.app (ChartDiagram.comp B S hS f g a b ha hb) s) :
    ζ₁ = ζ₂ := by
  refine (modulePushforwardHomEquiv B S hS (f ≫ g) F H).symm.injective
    (?_ : moduleFMapHom B S hS (f ≫ g) F H ζ₁ = moduleFMapHom B S hS (f ≫ g) F H ζ₂)
  have hι := moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f g F
  refine (cancel_mono ((modulePushforwardCompIso B S hS f g).inv.app F)).mp ?_
  refine modulePushforward_comp_hom_ext B S hS f g F H (fun e j s ↦ ?_)
  have h₁ := modulePushforwardHomFMap_app_chartDiagram_comp B S hS f g F H
    (modulePushforwardCompIso B S hS f g) hι (moduleFMapHom B S hS (f ≫ g) F H ζ₁)
    (chartDiagramOfIndex B S hS f e.U j).g e.g (chartDiagramOfIndex B S hS f e.U j).comm
    e.comm s
  have h₂ := modulePushforwardHomFMap_app_chartDiagram_comp B S hS f g F H
    (modulePushforwardCompIso B S hS f g) hι (moduleFMapHom B S hS (f ≫ g) F H ζ₂)
    (chartDiagramOfIndex B S hS f e.U j).g e.g (chartDiagramOfIndex B S hS f e.U j).comm
    e.comm s
  rw [modulePushforwardHomFMap_moduleFMapHom] at h₁ h₂
  exact h₁.symm.trans ((h _ _ _ _ s).trans h₂)

end IteratedPushforward

/-! ### Postcomposition of scheme charts along a composite -/

section CostructuredArrowMap

variable {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟] (K : 𝒞 ⥤ 𝒟)

/-- Postcomposition of costructured arrows along a composite is the composite of the two
postcompositions. -/
noncomputable def costructuredArrowMapComp {T T' T'' : 𝒟} (f : T ⟶ T') (f' : T' ⟶ T'') :
    CostructuredArrow.map (S := K) (f ≫ f') ≅
      CostructuredArrow.map (S := K) f ⋙ CostructuredArrow.map f' :=
  NatIso.ofComponents (fun Z ↦ CostructuredArrow.isoMk (Iso.refl Z.left) (by simp))
    (fun φ ↦ by ext; simp)

/-- Postcomposition of costructured arrows along an identity is the identity functor. -/
noncomputable def costructuredArrowMapId (T : 𝒟) :
    CostructuredArrow.map (S := K) (𝟙 T) ≅ 𝟭 (CostructuredArrow K T) :=
  NatIso.ofComponents (fun Z ↦ CostructuredArrow.isoMk (Iso.refl Z.left) (by simp))
    (fun φ ↦ by ext; simp)

end CostructuredArrowMap

/-! ### Lifts of identities -/

/-- A morphism lying over an identity lies over the identity of the image of its source. -/
private theorem isHomLift_id_domain {𝒜 : Type*} [Category 𝒜] {𝒮 : Type*} [Category 𝒮]
    (P : 𝒜 ⥤ 𝒮) {R : 𝒮} {x y : 𝒜} {φ : x ⟶ y} (h : P.IsHomLift (𝟙 R) φ) :
    P.IsHomLift (𝟙 (P.obj x)) φ := by
  obtain rfl := IsHomLift.domain_eq P (𝟙 R) φ
  infer_instance

/-- A composite of two morphisms each lying over an identity lies over an identity. -/
private theorem isHomLift_id_comp {𝒜 : Type*} [Category 𝒜] {𝒮 : Type*} [Category 𝒮]
    (P : 𝒜 ⥤ 𝒮) {R R' : 𝒮} {x y z : 𝒜} {φ : x ⟶ y} {ψ : y ⟶ z}
    (h₁ : P.IsHomLift (𝟙 R) φ) (h₂ : P.IsHomLift (𝟙 R') ψ) : P.IsHomLift (𝟙 R) (φ ≫ ψ) := by
  obtain rfl := IsHomLift.codomain_eq P (𝟙 R) φ
  obtain rfl := IsHomLift.domain_eq P (𝟙 R') ψ
  infer_instance

/-- The components of an identity natural isomorphism lie over identities. -/
theorem isHomLift_iso_refl_inv_app {𝒜 : Type*} [Category 𝒜] {𝒳 : Type*} [Category 𝒳]
    (r : 𝒳 ⥤ BigFppfOver B S hS) (F : 𝒜 ⥤ 𝒳) (X : 𝒜) :
    r.IsHomLift (𝟙 (r.obj (F.obj X))) ((Iso.refl F).inv.app X) :=
  inferInstanceAs (r.IsHomLift (𝟙 (r.obj (F.obj X))) (𝟙 (F.obj X)))

/-! ### The presentation of a composite of 1-morphisms -/

section Composite

variable {U V W : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒲 : Type v''} [Category.{w''} 𝒲] {𝒳 : Type v'''} [Category.{w'''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS)
  (t : 𝒲 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (eW : StacksRepresentableCFG.EquivalenceOver t
    (presheafOfCategories (W.1 ⋙ typeToCat)).p)
  (a : 𝒰 ⥤ 𝒱) (b : 𝒱 ⥤ 𝒲) (aSpace : U ⟶ V) (bSpace : V ⟶ W)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hb : schemeChartFunctor B S hS V.1 q eV ⋙ b ≅
    CostructuredArrow.map bSpace.hom ⋙ schemeChartFunctor B S hS W.1 t eW)

/-- **The presentation of a composite of 1-morphisms by the composite morphism of algebraic
spaces.** If `a : 𝒰 ⥤ 𝒱` is, through the chosen presentations, postcomposition with
`aSpace : U ⟶ V` (the datum `ha`), and `b : 𝒱 ⥤ 𝒲` is postcomposition with `bSpace : V ⟶ W`
(the datum `hb`), then `a ⋙ b` is postcomposition with `aSpace ≫ bSpace`: whisker `ha` by `b`,
then `hb` by postcomposition with `aSpace`, then identify the two successive postcompositions
with the postcomposition along the composite. -/
noncomputable def comparisonChartFunctorIsoComp :
    schemeChartFunctor B S hS U.1 p eU ⋙ (a ⋙ b) ≅
      CostructuredArrow.map (aSpace ≫ bSpace).hom ⋙ schemeChartFunctor B S hS W.1 t eW :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ha b ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ hb ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (costructuredArrowMapComp yoneda aSpace.hom bSpace.hom).symm _

/-- The components of `AlgebraicGeometry.Space.comparisonChartFunctorIsoComp`. -/
theorem comparisonChartFunctorIsoComp_hom_app (Z : CostructuredArrow yoneda U.1) :
    (comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb).hom.app Z =
      b.map (ha.hom.app Z) ≫ hb.hom.app ((CostructuredArrow.map aSpace.hom).obj Z) ≫
        (schemeChartFunctor B S hS W.1 t eW).map
          ((costructuredArrowMapComp yoneda aSpace.hom bSpace.hom).inv.app Z) := by
  simp [comparisonChartFunctorIsoComp]

/-- **The presentation of a composite lies over identities**, when `b` is a 1-morphism of fibred
categories and the components of `ha` and `hb` lie over identities. -/
theorem isHomLift_comparisonChartFunctorIsoComp_hom_app (hb₁ : q.IsFibredOneMorphism t b)
    (haL : ∀ Z : CostructuredArrow yoneda U.1,
      q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
        (ha.hom.app Z))
    (hbL : ∀ Z : CostructuredArrow yoneda V.1,
      t.IsHomLift (𝟙 (t.obj (b.obj ((schemeChartFunctor B S hS V.1 q eV).obj Z))))
        (hb.hom.app Z))
    (Z : CostructuredArrow yoneda U.1) :
    t.IsHomLift (𝟙 (t.obj ((a ⋙ b).obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      ((comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb).hom.app
        Z) := by
  rw [comparisonChartFunctorIsoComp_hom_app]
  have := haL Z
  have h₁ : t.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (b.map (ha.hom.app Z)) := hb₁.map_isHomLift _ _
  have h₂ := hbL ((CostructuredArrow.map aSpace.hom).obj Z)
  have : (CostructuredArrow.proj yoneda W.1).IsHomLift (𝟙 Z.left)
      ((costructuredArrowMapComp yoneda aSpace.hom bSpace.hom).inv.app Z) :=
    inferInstanceAs ((CostructuredArrow.proj yoneda W.1).IsHomLift
      ((CostructuredArrow.proj yoneda W.1).map
        ((costructuredArrowMapComp yoneda aSpace.hom bSpace.hom).inv.app Z))
      ((costructuredArrowMapComp yoneda aSpace.hom bSpace.hom).inv.app Z))
  have h₃ : t.IsHomLift (𝟙 Z.left) ((schemeChartFunctor B S hS W.1 t eW).map
      ((costructuredArrowMapComp yoneda aSpace.hom bSpace.hom).inv.app Z)) :=
    Functor.isHomLift_map_of_comp_eq (schemeChartFunctor_comp B S hS W.1 t eW) _ _
  exact isHomLift_id_domain t (isHomLift_id_comp t h₁ (isHomLift_id_comp t h₂ h₃))

/-- **The comparison morphism of charts of a composite is the composite of the comparison
morphisms of charts**, at a diagram of étale scheme charts over `aSpace ≫ bSpace` which factors
through an étale scheme chart of `V`. -/
theorem comparisonChartHom_chartDiagram_comp
    {U' : SmallEtale B S hS U.1} {V' : SmallEtale B S hS V.1} {W' : SmallEtale B S hS W.1}
    (α : (SmallEtale.toOver B S hS U.1).obj U' ⟶ (SmallEtale.toOver B S hS V.1).obj V')
    (β : (SmallEtale.toOver B S hS V.1).obj V' ⟶ (SmallEtale.toOver B S hS W.1).obj W')
    (hα : U'.1.hom ≫ aSpace.hom = yoneda.map α ≫ V'.1.hom)
    (hβ : V'.1.hom ≫ bSpace.hom = yoneda.map β ≫ W'.1.hom) :
    comparisonChartHom B S hS p t eU eW (a ⋙ b) (aSpace ≫ bSpace)
        (comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb)
        (ChartDiagram.comp B S hS aSpace bSpace α β hα hβ) =
      b.map (comparisonChartHom B S hS p q eU eV a aSpace ha ⟨U', V', α, hα⟩) ≫
        comparisonChartHom B S hS q t eV eW b bSpace hb ⟨V', W', β, hβ⟩ := by
  have hn := hb.hom.naturality (chartDiagramChartHom B S hS aSpace ⟨U', V', α, hα⟩)
  simp only [Functor.comp_map] at hn
  show (comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb).hom.app
        U'.1 ≫ (schemeChartFunctor B S hS W.1 t eW).map
          (chartDiagramChartHom B S hS (aSpace ≫ bSpace)
            (ChartDiagram.comp B S hS aSpace bSpace α β hα hβ)) =
      b.map (ha.hom.app U'.1 ≫ (schemeChartFunctor B S hS V.1 q eV).map
          (chartDiagramChartHom B S hS aSpace ⟨U', V', α, hα⟩)) ≫
        hb.hom.app V'.1 ≫ (schemeChartFunctor B S hS W.1 t eW).map
          (chartDiagramChartHom B S hS bSpace ⟨V', W', β, hβ⟩)
  have hc : (costructuredArrowMapComp yoneda aSpace.hom bSpace.hom).inv.app U'.1 ≫
        chartDiagramChartHom B S hS (aSpace ≫ bSpace)
          (ChartDiagram.comp B S hS aSpace bSpace α β hα hβ) =
      (CostructuredArrow.map bSpace.hom).map
          (chartDiagramChartHom B S hS aSpace ⟨U', V', α, hα⟩) ≫
        chartDiagramChartHom B S hS bSpace ⟨V', W', β, hβ⟩ := by
    ext
    simp [chartDiagramChartHom, ChartDiagram.comp, costructuredArrowMapComp]
  have hc' := congrArg (schemeChartFunctor B S hS W.1 t eW).map hc
  rw [comparisonChartFunctorIsoComp_hom_app, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc, reassoc_of% hn]
  congr 2
  exact (Functor.map_comp _ _ _).symm.trans (hc'.trans (Functor.map_comp _ _ _))

end Composite

/-! ### The composition law -/

section CompositionLaw

/-- Two successive restrictions of a presheaf of modules along opposite morphisms are the
restriction along their composite. -/
private theorem module_map_op_apply_of_eq_comp {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} (K : PresheafOfModules.{u} R)
    {X Y Z : C} {z : X ⟶ Z} {x : X ⟶ Y} {y : Y ⟶ Z} (h : z = x ≫ y) (s : K.obj (op Z)) :
    K.map z.op s = K.map x.op (K.map y.op s) := by
  rw [h, op_comp, K.map_comp]
  rfl

variable {U V W : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒲 : Type v''} [Category.{w''} 𝒲] {𝒳 : Type v'''} [Category.{w'''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS)
  (t : 𝒲 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (ht : t.IsFiberedInGroupoids)
  (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (eW : StacksRepresentableCFG.EquivalenceOver t
    (presheafOfCategories (W.1 ⋙ typeToCat)).p)
  (a : 𝒰 ⥤ 𝒱) (b : 𝒱 ⥤ 𝒲) (f : 𝒰 ⥤ 𝒳) (f' : 𝒱 ⥤ 𝒳) (g : 𝒲 ⥤ 𝒳)
  (hb₁ : q.IsFibredOneMorphism t b)
  (hf : p.IsFibredOneMorphism r f) (hf' : q.IsFibredOneMorphism r f')
  (hg : t.IsFibredOneMorphism r g)
  (φ : a ⋙ f' ≅ f) (ψ : b ⋙ g ≅ f') (aSpace : U ⟶ V) (bSpace : V ⟶ W)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hb : schemeChartFunctor B S hS V.1 q eV ⋙ b ≅
    CostructuredArrow.map bSpace.hom ⋙ schemeChartFunctor B S hS W.1 t eW)
  (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
  (hψ : ∀ X : 𝒱, r.IsHomLift (𝟙 (r.obj (f'.obj X))) (ψ.inv.app X))
  (haL : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha.hom.app Z))
  (hbL : ∀ Z : CostructuredArrow yoneda V.1,
    t.IsHomLift (𝟙 (t.obj (b.obj ((schemeChartFunctor B S hS V.1 q eV).obj Z))))
      (hb.hom.app Z))

/-- The 2-morphism of the composite triangle: `(a ⋙ b) ⋙ g ≅ a ⋙ f' ≅ f`, the 2-morphism `ψ`
whiskered by `a` followed by `φ`. -/
noncomputable abbrev compTriangleIso : (a ⋙ b) ⋙ g ≅ f :=
  Functor.associator a b g ≪≫ Functor.isoWhiskerLeft a ψ ≪≫ φ

include hφ hψ in
/-- The components of the 2-morphism of the composite triangle lie over identities. -/
theorem isHomLift_compTriangleIso_inv_app (X : 𝒰) :
    r.IsHomLift (𝟙 (r.obj (f.obj X))) ((compTriangleIso a b f f' g φ ψ).inv.app X) := by
  have h₃ : r.IsHomLift (𝟙 (r.obj (g.obj (b.obj (a.obj X))))) (𝟙 (g.obj (b.obj (a.obj X)))) :=
    inferInstance
  simpa [compTriangleIso] using isHomLift_id_comp r (hφ X) (isHomLift_id_comp r (hψ (a.obj X)) h₃)

/-- **The comparison morphism of the composite triangle is the composite of the two comparison
morphisms**, at a diagram of étale scheme charts over `aSpace ≫ bSpace` which factors through an
étale scheme chart of `V`. -/
theorem comparisonMorphism_chartDiagram_comp
    {U' : SmallEtale B S hS U.1} {V' : SmallEtale B S hS V.1} {W' : SmallEtale B S hS W.1}
    (α : (SmallEtale.toOver B S hS U.1).obj U' ⟶ (SmallEtale.toOver B S hS V.1).obj V')
    (β : (SmallEtale.toOver B S hS V.1).obj V' ⟶ (SmallEtale.toOver B S hS W.1).obj W')
    (hα : U'.1.hom ≫ aSpace.hom = yoneda.map α ≫ V'.1.hom)
    (hβ : V'.1.hom ≫ bSpace.hom = yoneda.map β ≫ W'.1.hom) :
    comparisonMorphism B S hS p t eU eW (a ⋙ b) f g (compTriangleIso a b f f' g φ ψ)
        (aSpace ≫ bSpace)
        (comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb)
        (ChartDiagram.comp B S hS aSpace bSpace α β hα hβ) =
      comparisonMorphism B S hS p q eU eV a f f' φ aSpace ha ⟨U', V', α, hα⟩ ≫
        comparisonMorphism B S hS q t eV eW b f' g ψ bSpace hb ⟨V', W', β, hβ⟩ := by
  unfold comparisonMorphism
  rw [comparisonChartHom_chartDiagram_comp]
  have hn := ψ.inv.naturality
    (comparisonChartHom B S hS p q eU eV a aSpace ha ⟨U', V', α, hα⟩)
  simp only [Functor.comp_map] at hn
  simp only [compTriangleIso, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Category.comp_id, Category.assoc]
  rw [reassoc_of% hn]
  exact congrArg (fun m ↦ φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj U') ≫
    ψ.inv.app (a.obj ((restrictionFunctor B S hS U.1 p eU).obj U')) ≫ m) (g.map_comp _ _)

include hb₁ in
/-- **The chart formula for the linear map of sections of the composite triangle.** At a diagram of
étale scheme charts over `aSpace ≫ bSpace` which factors through an étale scheme chart of `V`, the
linear map of sections of the comparison map of equation 076R for `a ⋙ b` is the composite of the
two linear maps of sections of the triangles for `a` and for `b`. -/
theorem moduleComparisonFMap_comp_app (ℱ : inheritedEtaleModules B S hS r hr)
    {U' : SmallEtale B S hS U.1} {V' : SmallEtale B S hS V.1} {W' : SmallEtale B S hS W.1}
    (α : (SmallEtale.toOver B S hS U.1).obj U' ⟶ (SmallEtale.toOver B S hS V.1).obj V')
    (β : (SmallEtale.toOver B S hS V.1).obj V' ⟶ (SmallEtale.toOver B S hS W.1).obj W')
    (hα : U'.1.hom ≫ aSpace.hom = yoneda.map α ≫ V'.1.hom)
    (hβ : V'.1.hom ≫ bSpace.hom = yoneda.map β ≫ W'.1.hom)
    (s : (etaleRestrictedModuleInverseImage B S hS t r ht hr eW g hg ℱ).val.obj (op W')) :
    (moduleComparisonFMap B S hS p t r hp ht eU eW (a ⋙ b) f g hf hg
        (compTriangleIso a b f f' g φ ψ) (aSpace ≫ bSpace)
        (comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb) hr
        (isHomLift_compTriangleIso_inv_app B S hS r a b f f' g φ ψ hφ hψ)
        (isHomLift_comparisonChartFunctorIsoComp_hom_app B S hS p q t eU eV eW a b aSpace bSpace
          ha hb hb₁ haL hbL) ℱ).app (ChartDiagram.comp B S hS aSpace bSpace α β hα hβ) s =
      (moduleComparisonFMap B S hS p q r hp hq eU eV a f f' hf hf' φ aSpace ha hr hφ haL ℱ).app
        ⟨U', V', α, hα⟩
        ((moduleComparisonFMap B S hS q t r hq ht eV eW b f' g hf' hg ψ bSpace hb hr hψ hbL
          ℱ).app ⟨V', W', β, hβ⟩ s) :=
  module_map_op_apply_of_eq_comp ℱ.val
    (comparisonMorphism_chartDiagram_comp B S hS p q t eU eV eW a b f f' g φ ψ aSpace bSpace
      ha hb α β hα hβ) s

include hb₁ hφ hψ haL hbL in
/-- **The linear map of sections of the composite triangle is the composite of the two linear
maps of sections.** The comparison map of equation 076R for `a ⋙ b` is built from a linear map
of sections along `aSpace ≫ bSpace`; it is the composite
`AlgebraicGeometry.Space.ModuleFMap.comp` of the linear maps of sections of the triangles for `b`
and for `a`. -/
theorem moduleComparisonFMap_comp (ℱ : inheritedEtaleModules B S hS r hr) :
    moduleComparisonFMap B S hS p t r hp ht eU eW (a ⋙ b) f g hf hg
        (compTriangleIso a b f f' g φ ψ) (aSpace ≫ bSpace)
        (comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb) hr
        (isHomLift_compTriangleIso_inv_app B S hS r a b f f' g φ ψ hφ hψ)
        (isHomLift_comparisonChartFunctorIsoComp_hom_app B S hS p q t eU eV eW a b aSpace bSpace
          ha hb hb₁ haL hbL) ℱ =
      ModuleFMap.compOfIso B S hS aSpace bSpace _ _ _
        (moduleComparisonFMap B S hS q t r hq ht eV eW b f' g hf' hg ψ bSpace hb hr hψ hbL ℱ)
        (moduleComparisonFMap B S hS p q r hp hq eU eV a f f' hf hf' φ aSpace ha hr hφ haL ℱ)
        (modulePushforwardCompIso B S hS aSpace bSpace) := by
  refine ModuleFMap.ext_of_app_chartDiagram_comp B S hS aSpace bSpace _ _
    (fun α β hα hβ s ↦ ?_)
  have h := ModuleFMap.compOfIso_app B S hS aSpace bSpace α β hα hβ _ _ _
    (moduleComparisonFMap B S hS q t r hq ht eV eW b f' g hf' hg ψ bSpace hb hr hψ hbL ℱ)
    (moduleComparisonFMap B S hS p q r hp hq eU eV a f f' hf hf' φ aSpace ha hr hφ haL ℱ)
    (modulePushforwardCompIso B S hS aSpace bSpace)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS aSpace bSpace _) s
  exact (moduleComparisonFMap_comp_app B S hS p q t r hp hq ht hr eU eV eW a b f f' g hb₁ hf hf'
    hg φ ψ aSpace bSpace ha hb hφ hψ haL hbL ℱ α β hα hβ s).trans h.symm

include hb₁ in
/-- **The map into the direct image of the composite triangle is the composite of the two maps
into the direct images.** The adjoint `g^*ℱ|_W ⟶ (aSpace ≫ bSpace)_*(f^*ℱ|_U)` of the comparison
map of equation 076R for `a ⋙ b` is the adjoint for `b`, followed by the direct image along
`bSpace` of the adjoint for `a`, followed by the comparison `bSpace_* ∘ aSpace_* ≅
(aSpace ≫ bSpace)_*` of Stacks 03LU. -/
theorem moduleComparisonPushforwardHom_comp (ℱ : inheritedEtaleModules B S hS r hr) :
    moduleComparisonPushforwardHom B S hS p t r hp ht eU eW (a ⋙ b) f g hf hg
        (compTriangleIso a b f f' g φ ψ) (aSpace ≫ bSpace)
        (comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb) hr
        (isHomLift_compTriangleIso_inv_app B S hS r a b f f' g φ ψ hφ hψ)
        (isHomLift_comparisonChartFunctorIsoComp_hom_app B S hS p q t eU eV eW a b aSpace bSpace
          ha hb hb₁ haL hbL) ℱ =
      moduleComparisonPushforwardHom B S hS q t r hq ht eV eW b f' g hf' hg ψ bSpace hb hr hψ
          hbL ℱ ≫
        (modulePushforward B S hS bSpace).map
          (moduleComparisonPushforwardHom B S hS p q r hp hq eU eV a f f' hf hf' φ aSpace ha hr hφ
            haL ℱ) ≫
        (modulePushforwardCompIso B S hS aSpace bSpace).hom.app
          (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ) := by
  unfold moduleComparisonPushforwardHom
  rw [moduleComparisonFMap_comp B S hS p q t r hp hq ht hr eU eV eW a b f f' g hb₁ hf hf' hg φ ψ
    aSpace bSpace ha hb hφ hψ haL hbL ℱ]
  unfold ModuleFMap.compOfIso
  rw [moduleFMapHom_modulePushforwardHomFMap, moduleFMapCompHom_eq]

include hb₁ in
/-- The composition law of the module comparison maps of equation 076R. Let
`a : 𝒰 ⥤ 𝒱`, `b : 𝒱 ⥤ 𝒲` and `g : 𝒲 ⥤ 𝒳` be 1-morphisms of categories fibred in groupoids over
`(Sch/S)_{fppf}` with `𝒰, 𝒱, 𝒲` representable by algebraic spaces `U, V, W`, through which `a`
and `b` are the morphisms `aSpace : U ⟶ V` and `bSpace : V ⟶ W` (`ha`, `hb`), and let
`ψ : b ⋙ g ≅ f'` and `φ : a ⋙ f' ≅ f` be 2-commutative triangles. Then for every `𝒪_𝒳`-module
`ℱ` the composite

`aSpace^*(bSpace^*(g^*ℱ|_W)) --aSpace^*(c_ψ)--> aSpace^*(f'^*ℱ|_V) --c_φ--> f^*ℱ|_U`

is the comparison map `c` of the composite triangle — `a ⋙ b` presented by `aSpace ≫ bSpace`
(`AlgebraicGeometry.Space.comparisonChartFunctorIsoComp`), with 2-morphism `ψ` whiskered by `a`
followed by `φ` — read through the identification
`(aSpace ≫ bSpace)^* = aSpace^* ∘ bSpace^*` of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackCompIso`). -/
theorem comparisonAlgebraicSpacesModules_comp_compTriangleIso
    (ℱ : inheritedEtaleModules B S hS r hr) :
    (modulePullback B S hS aSpace).map
        (comparisonAlgebraicSpacesModules B S hS q t r hq ht eV eW b f' g hf' hg ψ bSpace hb hr
          hψ hbL ℱ) ≫
      comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f f' hf hf' φ aSpace ha hr hφ
        haL ℱ =
    (modulePullbackCompIso B S hS aSpace bSpace).hom.app
        (etaleRestrictedModuleInverseImage B S hS t r ht hr eW g hg ℱ) ≫
      comparisonAlgebraicSpacesModules B S hS p t r hp ht eU eW (a ⋙ b) f g hf hg
        (compTriangleIso a b f f' g φ ψ) (aSpace ≫ bSpace)
        (comparisonChartFunctorIsoComp B S hS p q t eU eV eW a b aSpace bSpace ha hb) hr
        (isHomLift_compTriangleIso_inv_app B S hS r a b f f' g φ ψ hφ hψ)
        (isHomLift_comparisonChartFunctorIsoComp_hom_app B S hS p q t eU eV eW a b aSpace bSpace
          ha hb hb₁ haL hbL) ℱ := by
  have hiso : modulePullbackCompIso B S hS aSpace bSpace =
      Adjunction.leftAdjointUniq (((modulePullbackAdjunction B S hS bSpace).comp
        (modulePullbackAdjunction B S hS aSpace)).ofNatIsoRight
          (modulePushforwardCompIso B S hS aSpace bSpace))
        (modulePullbackAdjunction B S hS (aSpace ≫ bSpace)) := rfl
  rw [hiso]
  refine Stacks.CategoryTheory.map_comp_eq_leftAdjointUniq_hom_app_comp
    (modulePullbackAdjunction B S hS bSpace) (modulePullbackAdjunction B S hS aSpace)
    (modulePullbackAdjunction B S hS (aSpace ≫ bSpace))
    (modulePushforwardCompIso B S hS aSpace bSpace) _ _ _ ?_
  rw [comparisonAlgebraicSpacesModules_adjoint, comparisonAlgebraicSpacesModules_adjoint,
    comparisonAlgebraicSpacesModules_adjoint]
  exact (moduleComparisonPushforwardHom_comp B S hS p q t r hp hq ht hr eU eV eW a b f f' g hb₁
    hf hf' hg φ ψ aSpace bSpace ha hb hφ hψ haL hbL ℱ).symm

end CompositionLaw

/-! ### The unit law -/

/-- Restrictions of a presheaf of modules along equal morphisms agree. -/
private theorem module_map_op_congr {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} (K : PresheafOfModules.{u} R)
    {X Y : C} {x y : X ⟶ Y} (h : x = y) (s : K.obj (op Y)) :
    K.map x.op s = K.map y.op s := by
  rw [h]

section UnitLaw

variable {U : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒳 : Type v'''} [Category.{w'''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (g : 𝒰 ⥤ 𝒳) (hg : p.IsFibredOneMorphism r g)

/-- **The presentation of the identity 1-morphism by the identity morphism of algebraic
spaces.** Postcomposition of scheme charts with `𝟙 U` is the identity functor. -/
noncomputable def comparisonChartFunctorIsoId :
    schemeChartFunctor B S hS U.1 p eU ⋙ 𝟭 𝒰 ≅
      CostructuredArrow.map (𝟙 U : U ⟶ U).hom ⋙ schemeChartFunctor B S hS U.1 p eU :=
  Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (costructuredArrowMapId yoneda U.1).symm _

/-- The components of `AlgebraicGeometry.Space.comparisonChartFunctorIsoId`. -/
theorem comparisonChartFunctorIsoId_hom_app (Z : CostructuredArrow yoneda U.1) :
    (comparisonChartFunctorIsoId B S hS p eU).hom.app Z =
      (schemeChartFunctor B S hS U.1 p eU).map ((costructuredArrowMapId yoneda U.1).inv.app Z) := by
  simp [comparisonChartFunctorIsoId]

/-- The presentation of the identity 1-morphism lies over identities. -/
theorem isHomLift_comparisonChartFunctorIsoId_hom_app (Z : CostructuredArrow yoneda U.1) :
    p.IsHomLift (𝟙 (p.obj ((𝟭 𝒰).obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      ((comparisonChartFunctorIsoId B S hS p eU).hom.app Z) := by
  rw [comparisonChartFunctorIsoId_hom_app]
  have : (CostructuredArrow.proj yoneda U.1).IsHomLift (𝟙 Z.left)
      ((costructuredArrowMapId yoneda U.1).inv.app Z) :=
    inferInstanceAs ((CostructuredArrow.proj yoneda U.1).IsHomLift
      ((CostructuredArrow.proj yoneda U.1).map ((costructuredArrowMapId yoneda U.1).inv.app Z))
      ((costructuredArrowMapId yoneda U.1).inv.app Z))
  have h : p.IsHomLift (𝟙 Z.left) ((schemeChartFunctor B S hS U.1 p eU).map
      ((costructuredArrowMapId yoneda U.1).inv.app Z)) :=
    Functor.isHomLift_map_of_comp_eq (schemeChartFunctor_comp B S hS U.1 p eU) _ _
  exact isHomLift_id_domain p h

/-- **The comparison morphism of charts of the identity triangle is the morphism of charts the
diagram is.** A diagram of étale scheme charts over `𝟙 U` is a morphism of étale charts of `U`
(`AlgebraicGeometry.Space.chartMapOfIdChartDiagram`), and the comparison morphism is its image in
`𝒰`. -/
theorem comparisonChartHom_id (d : ChartDiagram B S hS U.1 U.1 (𝟙 U : U ⟶ U).hom) :
    comparisonChartHom B S hS p p eU eU (𝟭 𝒰) (𝟙 U) (comparisonChartFunctorIsoId B S hS p eU) d =
      (restrictionFunctor B S hS U.1 p eU).map (chartMapOfIdChartDiagram B S hS U d) := by
  show (comparisonChartFunctorIsoId B S hS p eU).hom.app d.U.1 ≫
      (schemeChartFunctor B S hS U.1 p eU).map (chartDiagramChartHom B S hS (𝟙 U) d) =
    (schemeChartFunctor B S hS U.1 p eU).map
      ((SmallEtale.inclusion B S hS U.1).map (chartMapOfIdChartDiagram B S hS U d))
  rw [comparisonChartFunctorIsoId_hom_app, ← Functor.map_comp]
  congr 1

/-- The restriction maps of `g^*ℱ|_U` are the restriction maps of `ℱ` along the images in `𝒳` of
the morphisms of étale charts of `U`. -/
theorem etaleRestrictedModuleInverseImage_map_apply (ℱ : inheritedEtaleModules B S hS r hr)
    {W₁ W₂ : SmallEtale B S hS U.1} (k : W₁ ⟶ W₂)
    (s : (etaleRestrictedModuleInverseImage B S hS p r hp hr eU g hg ℱ).val.obj (op W₂)) :
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU g hg ℱ).val.map k.op s =
      ℱ.val.map (g.map ((restrictionFunctor B S hS U.1 p eU).map k)).op s :=
  rfl

/-- **The linear map of sections of the identity triangle is restriction along the diagram.** -/
theorem moduleComparisonFMap_id_app (ℱ : inheritedEtaleModules B S hS r hr)
    (d : ChartDiagram B S hS U.1 U.1 (𝟙 U : U ⟶ U).hom)
    (s : (etaleRestrictedModuleInverseImage B S hS p r hp hr eU g hg ℱ).val.obj (op d.V)) :
    (moduleComparisonFMap B S hS p p r hp hp eU eU (𝟭 𝒰) g g hg hg (Iso.refl g) (𝟙 U)
        (comparisonChartFunctorIsoId B S hS p eU) hr (isHomLift_iso_refl_inv_app B S hS r g)
        (isHomLift_comparisonChartFunctorIsoId_hom_app B S hS p eU) ℱ).app d s =
      (etaleRestrictedModuleInverseImage B S hS p r hp hr eU g hg ℱ).val.map
        (chartMapOfIdChartDiagram B S hS U d).op s := by
  have h : comparisonMorphism B S hS p p eU eU (𝟭 𝒰) g g (Iso.refl g) (𝟙 U)
        (comparisonChartFunctorIsoId B S hS p eU) d =
      g.map ((restrictionFunctor B S hS U.1 p eU).map (chartMapOfIdChartDiagram B S hS U d)) := by
    unfold comparisonMorphism
    rw [comparisonChartHom_id]
    exact Category.id_comp _
  exact (module_map_op_congr ℱ.val h s).trans
    (etaleRestrictedModuleInverseImage_map_apply B S hS p r hp hr eU g hg ℱ
      (chartMapOfIdChartDiagram B S hS U d) _).symm

/-- **The map into the direct image of the identity triangle is the unit law of Stacks 03LU.**
The adjoint `g^*ℱ|_U ⟶ (𝟙 U)_*(g^*ℱ|_U)` of the comparison map of equation 076R for the identity
triangle is the inverse of the identification `(𝟙 U)_* ≅ 𝟭`
(`AlgebraicGeometry.Space.modulePushforwardIdIso`). -/
theorem moduleComparisonPushforwardHom_id (ℱ : inheritedEtaleModules B S hS r hr) :
    moduleComparisonPushforwardHom B S hS p p r hp hp eU eU (𝟭 𝒰) g g hg hg (Iso.refl g) (𝟙 U)
        (comparisonChartFunctorIsoId B S hS p eU) hr (isHomLift_iso_refl_inv_app B S hS r g)
        (isHomLift_comparisonChartFunctorIsoId_hom_app B S hS p eU) ℱ =
      (modulePushforwardIdIso B S hS U).inv.app
        (etaleRestrictedModuleInverseImage B S hS p r hp hr eU g hg ℱ) := by
  refine (modulePushforwardHomEquiv B S hS (𝟙 U) _ _).symm_apply_eq.mpr ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  refine (moduleComparisonFMap_id_app B S hS p r hp hr eU g hg ℱ d s).trans ?_
  exact (modulePushforwardCounitApp_modulePushforwardIdIso_inv_app B S hS U _ d s).symm

/-- **The unit law for the module comparison maps of equation 076R.** For the identity triangle
— `a = 𝟭 𝒰` presented by `𝟙 U` (`AlgebraicGeometry.Space.comparisonChartFunctorIsoId`), with
`f = g` and the identity 2-morphism — the comparison map
`c : (𝟙 U)^*(g^*ℱ|_U) ⟶ g^*ℱ|_U` is the unit law `(𝟙 U)^* ≅ 𝟭` of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackIdIso`). -/
theorem comparisonAlgebraicSpacesModules_id (ℱ : inheritedEtaleModules B S hS r hr) :
    comparisonAlgebraicSpacesModules B S hS p p r hp hp eU eU (𝟭 𝒰) g g hg hg (Iso.refl g)
        (𝟙 U) (comparisonChartFunctorIsoId B S hS p eU) hr
        (isHomLift_iso_refl_inv_app B S hS r g)
        (isHomLift_comparisonChartFunctorIsoId_hom_app B S hS p eU) ℱ =
      (modulePullbackIdIso B S hS U).hom.app
        (etaleRestrictedModuleInverseImage B S hS p r hp hr eU g hg ℱ) := by
  refine ((modulePullbackAdjunction B S hS (𝟙 U)).homEquiv _ _).injective ?_
  rw [comparisonAlgebraicSpacesModules_adjoint, homEquiv_modulePullbackIdIso_hom_app]
  exact moduleComparisonPushforwardHom_id B S hS p r hp hr eU g hg ℱ

end UnitLaw

/-! ### The 2-cell law -/

section TwoCellLaw

/-- Two successive restrictions of a presheaf of rings along opposite morphisms are the
restriction along their composite. -/
private theorem ring_map_op_comp_apply' {C : Type*} [Category C] (K : Cᵒᵖ ⥤ RingCat.{u})
    {X Y Z : C} (x : X ⟶ Y) (y : Y ⟶ Z) (s : K.obj (op Z)) :
    K.map x.op (K.map y.op s) = K.map (x ≫ y).op s := by
  rw [op_comp, K.map_comp]
  rfl

variable {U V : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type v'''} [Category.{w'''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (f f' : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) (hf' : p.IsFibredOneMorphism r f')
  (t : f' ⟶ f) (ht : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f'.obj X))) (t.app X))

include ht in
/-- A 2-morphism `t : f' ⟶ f` over the identity carries the structure-sheaf identification of
`AlgebraicGeometry.Space.etaleChartStructureHom` for `f` to the one for `f'`. -/
theorem etaleChartStructureHom_comp_sheafPushforwardContinuousNatTrans :
    letI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
    letI := etaleChartToFibred_isContinuous B S hS p r hp eU f' hf'
    etaleChartStructureHom B S hS p r hp hr eU f hf ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (Functor.whiskerLeft (restrictionFunctor B S hS U.1 p eU) t) RingCat.{u}
          (SmallEtale.topology B S hS U.1)
          (BigFppfOver.associatedTopology B S hS r .etale)).app
          (FibredSite.ringStructureSheafCore B S hS r hr .etale) =
      etaleChartStructureHom B S hS p r hp hr eU f' hf' := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ RingCat.hom_ext (RingHom.ext fun ρ ↦ ?_)))
  have := ht ((restrictionFunctor B S hS U.1 p eU).obj W.unop)
  show (FibredSite.ringStructureSheafCore B S hS r hr .etale).obj.map
      (t.app ((restrictionFunctor B S hS U.1 p eU).obj W.unop)).op
      ((etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app W ρ) =
    (etaleChartStructureHom B S hS p r hp hr eU f' hf').hom.app W ρ
  rw [etaleChartStructureHom_app, etaleChartStructureHom_app]
  refine Eq.trans (ring_map_op_comp_apply' (BigFppfOver.structureSheaf B S hS).obj
    (r.map (t.app ((restrictionFunctor B S hS U.1 p eU).obj W.unop)))
    (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p r eU f hf) W.unop)) ρ) ?_
  refine congrArg (fun m : (etaleChartToFibred B S hS p eU f' ⋙ r).obj W.unop ⟶
      (SmallEtale.toOver B S hS U.1).obj W.unop =>
    (BigFppfOver.structureSheaf B S hS).obj.map m.op ρ) ?_
  rw [IsHomLift.fac' r (𝟙 (r.obj (f'.obj ((restrictionFunctor B S hS U.1 p eU).obj W.unop))))
    (t.app ((restrictionFunctor B S hS U.1 p eU).obj W.unop))]
  simp

/-- **Restriction along a 2-morphism**, `f^*ℱ|_{U_étale} ⟶ f'^*ℱ|_{U_étale}`: for a
2-morphism `t : f' ⟶ f` over the identity, the morphism of `𝒪_U`-modules which on sections over
an étale chart `W` of `U` is restriction of sections of `ℱ` along `t` at `u_U W`. -/
noncomputable def etaleRestrictedModuleInverseImageTwoMorphism
    (ℱ : inheritedEtaleModules B S hS r hr) :
    etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ ⟶
      etaleRestrictedModuleInverseImage B S hS p r hp hr eU f' hf' ℱ :=
  letI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  letI := etaleChartToFibred_isContinuous B S hS p r hp eU f' hf'
  (SheafOfModules.pushforwardNatTrans (etaleChartStructureHom B S hS p r hp hr eU f hf)
      (Functor.whiskerLeft (restrictionFunctor B S hS U.1 p eU) t)).app ℱ ≫
    (SheafOfModules.pushforwardCongr
      (etaleChartStructureHom_comp_sheafPushforwardContinuousNatTrans B S hS p r hp hr eU f f'
        hf hf' t ht)).hom.app ℱ

/-- On sections, restriction along a 2-morphism is restriction of sections of `ℱ`. -/
theorem etaleRestrictedModuleInverseImageTwoMorphism_val_app
    (ℱ : inheritedEtaleModules B S hS r hr) (W : SmallEtale B S hS U.1)
    (s : (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ).val.obj (op W)) :
    (etaleRestrictedModuleInverseImageTwoMorphism B S hS p r hp hr eU f f' hf hf' t ht
        ℱ).val.app (op W) s =
      ℱ.val.map (t.app ((restrictionFunctor B S hS U.1 p eU).obj W)).op s :=
  rfl

variable (a : 𝒰 ⥤ 𝒱) (g : 𝒱 ⥤ 𝒳) (hg : q.IsFibredOneMorphism r g)
  (φ : a ⋙ g ≅ f) (φ' : a ⋙ g ≅ f') (aSpace : U ⟶ V)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
  (hφ' : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f'.obj X))) (φ'.inv.app X))
  (haL : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha.hom.app Z))
  (htφ : φ'.hom ≫ t = φ.hom)

include htφ in
/-- The comparison morphism of the triangle `φ'` is the component of `t` followed by the
comparison morphism of the triangle `φ`. -/
theorem comparisonMorphism_twoMorphism (d : ChartDiagram B S hS U.1 V.1 aSpace.hom) :
    comparisonMorphism B S hS p q eU eV a f' g φ' aSpace ha d =
      t.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) ≫
        comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d := by
  unfold comparisonMorphism
  have h : t.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) ≫
      φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) =
      φ'.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) := by
    rw [← cancel_epi (φ'.hom.app ((restrictionFunctor B S hS U.1 p eU).obj d.U)),
      ← Category.assoc, ← NatTrans.comp_app, htφ, Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  rw [← reassoc_of% h]

include htφ in
/-- **The 2-cell law for the maps into the direct image.** -/
theorem moduleComparisonPushforwardHom_twoMorphism (ℱ : inheritedEtaleModules B S hS r hr) :
    moduleComparisonPushforwardHom B S hS p q r hp hq eU eV a f' g hf' hg φ' aSpace ha hr hφ'
        haL ℱ =
      moduleComparisonPushforwardHom B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
          haL ℱ ≫
        (modulePushforward B S hS aSpace).map
          (etaleRestrictedModuleInverseImageTwoMorphism B S hS p r hp hr eU f f' hf hf' t ht ℱ) :=
  moduleFMapHom_postcomp B S hS aSpace _ _ _ _
    (fun d s ↦ module_map_op_apply_of_eq_comp ℱ.val
      (comparisonMorphism_twoMorphism B S hS p q eU eV f f' t a g φ φ' aSpace ha htφ d) s)

include htφ in
/-- **The 2-cell law for the module comparison maps of equation 076R.** Two 2-commutative
triangles `φ : a ⋙ g ≅ f` and `φ' : a ⋙ g ≅ f'` with the same `a` and `g`, related by a
2-morphism `t : f' ⟶ f` over the identity with `φ' ≫ t = φ`, have comparison maps related by
restriction along `t`: `c_{φ'} = c_φ ≫ t^*`, where
`t^* : f^*ℱ|_{U_étale} ⟶ f'^*ℱ|_{U_étale}` is
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImageTwoMorphism`. This is the module form of
the compatibility of the comparison maps with the identifications of Stacks 06TM induced by
2-morphisms (Stacks 075D, part (4)). -/
theorem comparisonAlgebraicSpacesModules_twoMorphism (ℱ : inheritedEtaleModules B S hS r hr) :
    comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f' g hf' hg φ' aSpace ha hr hφ'
        haL ℱ =
      comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
          haL ℱ ≫
        etaleRestrictedModuleInverseImageTwoMorphism B S hS p r hp hr eU f f' hf hf' t ht ℱ := by
  refine ((modulePullbackAdjunction B S hS aSpace).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, comparisonAlgebraicSpacesModules_adjoint,
    comparisonAlgebraicSpacesModules_adjoint]
  exact moduleComparisonPushforwardHom_twoMorphism B S hS p q r hp hq hr eU eV f f' hf hf' t ht
    a g hg φ φ' aSpace ha hφ hφ' haL htφ ℱ

end TwoCellLaw

end AlgebraicGeometry.Space

end
