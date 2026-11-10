module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOnBoundedResolutions
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionBaseChangeFlat

/-!
# The connecting morphisms of the reduction triangles under base change

Let `g : O ⟶ O'` be a morphism of square-zero extensions of `O₀`, over `O₀`. For a complex `P`
of flat `O`-modules, the morphism of reduction sequences
`Deformation.ComplexLift.reductionSequenceBaseChange` relates the connecting morphism of the
reduction triangle of `Q(P)` along `f : O ⟶ O₀` to the one of `Q(O' ⊗_O P)` along `f'`.

## Main definitions

* `Deformation.ComplexLift.derivedTensorRightMap`: the map `- ⊗^L I₀ ⟶ - ⊗^L I₀'` induced by a map
  of ideals `I₀ ⟶ I₀'`.
* `Deformation.ComplexLift.flatReductionBaseChange`: derived extension of scalars along `g` as a
  base change between the reduction triangles along `f` and `f'`.

## Main results

* `Deformation.ComplexLift.connecting_baseChange`: at every object of `D^{≤ 0}`, the connecting
  morphisms of the reduction triangles along `f` and `f'` correspond under base change along `g`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe d d' d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The derived map of ideal parts -/

section IdealMap

variable {O₀ : Sheaf J CommRingCat.{u}}
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
  {I₀ I₀' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (u₀ : I₀ ⟶ I₀')

/-- The map `- ⊗^L I₀ ⟶ - ⊗^L I₀'` of derived tensor products induced by a map `u₀ : I₀ ⟶ I₀'`:
the left derived natural transformation of the degreewise map `- ⊗ I₀ ⟶ - ⊗ I₀'`. -/
def derivedTensorRightMap : derivedTensorRight.{d₀} I₀ ⟶ derivedTensorRight.{d₀} I₀' :=
  Functor.leftDerivedNatTrans (derivedTensorRight.{d₀} I₀) (derivedTensorRight.{d₀} I₀')
    (derivedTensorRightCounit.{d₀} I₀) (derivedTensorRightCounit.{d₀} I₀')
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).flip.map u₀)
        (ComplexShape.up ℤ)) DerivedCategory.Q)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The derived map of ideal parts, at a complex: the degreewise map, through the comparisons of
the derived tensor products with the degreewise ones. -/
@[reassoc]
theorem derivedTensorRightMap_app_Q
    (Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (derivedTensorRightMap.{d₀} u₀).app (DerivedCategory.Q.obj Y) ≫
        (derivedTensorRightCounit.{d₀} I₀').app Y =
      (derivedTensorRightCounit.{d₀} I₀).app Y ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).flip.map u₀)
            (ComplexShape.up ℤ)).app Y) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ _ _ Y

end IdealMap

section VertexIsos

variable {O₁ O₂ : Sheaf J CommRingCat.{u}} (h : O₁ ⟶ O₂)
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))]
  {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)}
  {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) ℤ}
  (hP : IsFlatCellular P)

/-- The inverse of the third vertex identification at the identity of `Q(P)` is the third
vertex. -/
theorem vertexThreeIso_refl_inv :
    (vertexThreeIso.{d, d₀} h hP (Iso.refl (DerivedCategory.Q.obj P))).inv =
      (vertexThree.{d, d₀} h).app P := by
  simp [vertexThreeIso]

/-- The inverse of the third vertex identification at the inverse of an isomorphism
`c : K ⟶ Q(P)` is the image of `c` followed by the third vertex. -/
theorem vertexThreeIso_asIso_symm_inv
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))}
    (c : K ⟶ DerivedCategory.Q.obj P) [IsIso c] :
    (vertexThreeIso.{d, d₀} h hP (asIso c).symm).inv =
      (restrictionOnDerived.{d, d₀} h).map ((derivedExtensionOfScalars.{d, d₀} h).map c) ≫
        (vertexThree.{d, d₀} h).app P := by
  simp [vertexThreeIso]

/-- The first vertex identification at the identity of `Q(P)`, followed by the first vertex, is
the identity. -/
theorem vertexOneIso_refl_hom_comp :
    (vertexOneIso.{d, d₀} (I₀ := M) h hP (Iso.refl (DerivedCategory.Q.obj P))).hom ≫
      (vertexOne.{d, d₀} h M).app P = 𝟙 _ := by
  simp [vertexOneIso]

/-- The inverse of the first vertex identification at the inverse of an isomorphism
`c : K ⟶ Q(P)` is the image of `c` followed by the first vertex. -/
theorem vertexOneIso_asIso_symm_inv
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))}
    (c : K ⟶ DerivedCategory.Q.obj P) [IsIso c] :
    (vertexOneIso.{d, d₀} (I₀ := M) h hP (asIso c).symm).inv =
      (restrictionOnDerived.{d, d₀} h).map ((derivedTensorRight.{d₀} M).map
        ((derivedExtensionOfScalars.{d, d₀} h).map c)) ≫ (vertexOne.{d, d₀} h M).app P := by
  simp [vertexOneIso]

end VertexIsos

/-! ### The vertices under base change -/

section Vertices

variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀} (g : O ⟶ O')
  (hg : g ≫ f' = f)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- Degreewise, the base change of the reduction is restriction of the comparison of the
extensions of scalars, followed by the comparison of the restrictions of scalars. -/
theorem reductionPartBaseChangeComplex_eq
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    reductionPartBaseChangeComplex g hg P =
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (extensionOfScalarsCompComplexIso g hg P).hom ≫
        (Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
          (ComplexShape.up ℤ)).inv.app ((extensionOfScalarsCochainComplex J f').obj
            ((extensionOfScalarsCochainComplex J g).obj P)) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  dsimp only [reductionPartBaseChangeComplex, reductionPartBaseChange, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, extensionOfScalarsCompComplexIso_hom_f,
    Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex_inv_app_f, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rfl

/-- A chain of morphisms through a functor `G` collapses through five relations. -/
theorem vertex_chain_eq {D D' : Type*} [Category D] [Category D'] (G : D' ⥤ D)
    {A B S₁ T₁ K₀ K₁ Z : D} {B' C' M' E' : D'}
    (a : A ⟶ B) (r : B ⟶ G.obj B') (p : B' ⟶ C') (v : C' ⟶ E') (z : G.obj E' ⟶ Z)
    (c' : C' ⟶ M') (e' : M' ⟶ E') (hv : v = c' ≫ e')
    (s : B ⟶ S₁) (r' : S₁ ⟶ G.obj M') (hn : r ≫ G.map (p ≫ c') = s ≫ r')
    (t : A ⟶ T₁) (y : T₁ ⟶ S₁) (hΦ : a ≫ s = t ≫ y)
    (k : S₁ ⟶ K₁) (l : K₁ ⟶ Z) (hρ : r' ≫ G.map e' ≫ z = k ≫ l)
    (k₀ : T₁ ⟶ K₀) (j : K₀ ⟶ K₁) (hfac : y ≫ k = k₀ ≫ j)
    (V : A ⟶ K₀) (hV : V = t ≫ k₀) (q : K₀ ⟶ Z) (hq : q = j ≫ l) :
    a ≫ r ≫ G.map (p ≫ v) ≫ z = V ≫ q := by
  subst hv hV hq
  have hn' : r ≫ G.map (p ≫ c' ≫ e') = s ≫ r' ≫ G.map e' := by
    rw [← Category.assoc p, G.map_comp, reassoc_of% hn]
  rw [reassoc_of% hn', hρ, reassoc_of% hΦ, reassoc_of% hfac, Category.assoc]

/-- A composite `c ≫ a ≫ k⁻¹ ≫ k ≫ b` with `a ≫ b = 𝟙` collapses to `c`. -/
theorem comp_inv_hom_cancel_chain {D : Type*} [Category D] {A B C₁ E : D} (m c : A ⟶ B)
    (hm : m = c) (a a' : B ⟶ C₁) (ha : a = a') (kinv : C₁ ⟶ E) (khom : E ⟶ C₁)
    (hk : kinv ≫ khom = 𝟙 _) (b : C₁ ⟶ B) (hb : a' ≫ b = 𝟙 _) :
    m = (c ≫ a ≫ kinv) ≫ khom ≫ b := by
  subst hm ha
  rw [Category.assoc, Category.assoc, reassoc_of% hk, hb, Category.comp_id]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The composite of the comparisons of the two derived restrictions with the degreewise ones. -/
theorem restrictionOnDerivedCompFactors_hom_app
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (restrictionOnDerivedCompFactors.{d, d', d₀} g).hom.app K =
      (restrictionOnDerived.{d, d'} g).map
          ((SheafOfModules.restrictScalars.{u}
            (ringSheafMapOf J f')).mapDerivedCategoryFactors.hom.app K) ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
          (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) := by
  dsimp only [restrictionOnDerivedCompFactors, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
  exact (Category.id_comp _).trans (congrArg _ (Category.id_comp _))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- The identification of the composite of the degreewise restrictions with degreewise
restriction along `f`, at a complex. -/
theorem restrictScalarsCompMapHomologicalComplexIso_hom_app
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (restrictScalarsCompMapHomologicalComplexIso.{d} g hg).hom.app K =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
        (ComplexShape.up ℤ)).hom.app K) := by
  dsimp only [restrictScalarsCompMapHomologicalComplexIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_inv_app]
  exact Category.id_comp _

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `restrictionOnDerivedCompFactors_hom_app` at an extension of scalars along `f'`. -/
theorem restrictionOnDerivedCompFactors_hom_app_ext
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O')) ℤ) :
    (restrictionOnDerivedCompFactors.{d, d', d₀} g).hom.app
        ((extensionOfScalarsCochainComplex J f').obj P) =
      (restrictionOnDerived.{d, d'} g).map
          ((SheafOfModules.restrictScalars.{u}
            (ringSheafMapOf J f')).mapDerivedCategoryFactors.hom.app
              ((extensionOfScalarsCochainComplex J f').obj P)) ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
          (((reductionPart f').mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  restrictionOnDerivedCompFactors_hom_app.{d, d', d₀} (f' := f') g _

/-- The inverse of the identification of the two derived restrictions, at the localization of a
complex, through the comparisons with the degreewise restrictions. -/
private theorem restrictionOnDerivedCompIso_inv_app_Q_comp_factors_aux
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app (DerivedCategory.Q.obj K) ≫
      (restrictionOnDerived.{d, d'} g).map
          ((SheafOfModules.restrictScalars.{u}
            (ringSheafMapOf J f')).mapDerivedCategoryFactors.hom.app K) ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
          (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) =
      (SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
            (ComplexShape.up ℤ)).inv.app K) := by
  -- keeps the section instance in use, as in the lemmas below (no unused-variable warning)
  have _ : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  have hρ := restrictionOnDerivedCompIso_hom_app_Q.{d, d', d₀} g hg K
  refine (Iso.inv_comp_eq ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).app _)).2 ?_
  refine Eq.trans ?_ (congrArg (· ≫ _) hρ.symm)
  have h1 := (restrictionOnDerivedCompFactors_hom_app.{d, d', d₀} (f' := f') g K).symm
  have h2 := restrictScalarsCompMapHomologicalComplexIso_hom_app.{d} g hg K
  have h3 := Iso.inv_hom_id_app
    (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors K
  have h4 : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
      (ComplexShape.up ℤ)).hom.app K) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
      (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact comp_inv_hom_cancel_chain _ _ h1 _ _ h2 _ _ h3 _ h4

/-- The inverse of the identification of the two derived restrictions, at the localization of
an extension of scalars along `f'`, through the comparisons with the degreewise restrictions. -/
theorem restrictionOnDerivedCompIso_inv_app_comp_factors
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O')) ℤ) :
    (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app
        ((extensionOfScalarsCochainComplex J f' ⋙ DerivedCategory.Q).obj P) ≫
      (restrictionOnDerived.{d, d'} g).map
          ((SheafOfModules.restrictScalars.{u}
            (ringSheafMapOf J f')).mapDerivedCategoryFactors.hom.app
              ((extensionOfScalarsCochainComplex J f').obj P)) ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
          (((reductionPart f').mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors.hom.app
          ((extensionOfScalarsCochainComplex J f').obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
            (ComplexShape.up ℤ)).inv.app ((extensionOfScalarsCochainComplex J f').obj P)) :=
  restrictionOnDerivedCompIso_inv_app_Q_comp_factors_aux.{d, d', d₀} g hg _

/-- **The third vertex under base change.** At a complex `P` of `O`-modules, the base change of
the third vertex identification along `g` is the degreewise base change of the reduction. -/
theorem vertexThree_baseChange
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (restrictionOnDerived.{d, d₀} f).map
        ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app (DerivedCategory.Q.obj P)) ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _ ≫
      (restrictionOnDerived.{d, d'} g).map
        ((restrictionOnDerived.{d', d₀} f').map ((derivedExtensionOfScalars.{d', d₀} f').map
          ((derivedExtensionOfScalarsCounit.{d, d'} g).app P)) ≫
          (vertexThree.{d', d₀} f').app ((extensionOfScalarsCochainComplex J g).obj P)) ≫
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
        (((reductionPart f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((extensionOfScalarsCochainComplex J g).obj P)) =
      (vertexThree.{d, d₀} f).app P ≫
        DerivedCategory.Q.map (reductionPartBaseChangeComplex g hg P) := by
  refine vertex_chain_eq (restrictionOnDerived.{d, d'} g) _ _ _ _ _ _ _
    (vertexThree_app.{d', d₀} f' ((extensionOfScalarsCochainComplex J g).obj P))
    ((restrictionOnDerived.{d, d₀} f).map
      ((derivedExtensionOfScalars.{d', d₀} f').map
          ((derivedExtensionOfScalarsCounit.{d, d'} g).app P) ≫
        (derivedExtensionOfScalarsCounit.{d', d₀} f').app
          ((extensionOfScalarsCochainComplex J g).obj P)))
    ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _) ?_
    ((restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P))
    ((restrictionOnDerived.{d, d₀} f).map
      (DerivedCategory.Q.map (extensionOfScalarsCompComplexIso g hg P).hom)) ?_
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors.hom.app
      ((extensionOfScalarsCochainComplex J f').obj ((extensionOfScalarsCochainComplex J g).obj P)))
    (DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
      (ComplexShape.up ℤ)).inv.app ((extensionOfScalarsCochainComplex J f').obj
        ((extensionOfScalarsCochainComplex J g).obj P)))) ?_
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors.hom.app
      ((extensionOfScalarsCochainComplex J f).obj P))
    (DerivedCategory.Q.map
      (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (extensionOfScalarsCompComplexIso g hg P).hom)) ?_
    _ (vertexThree_app.{d, d₀} f P) _ ?_
  · rw [← Functor.map_comp (restrictionOnDerived.{d', d₀} f')]
    exact ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.naturality _).symm
  · rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (restrictionOnDerived.{d, d₀} f).map
      (derivedExtensionOfScalarsCompIso_inv_app_Q.{d, d', d₀} g hg P)
  · exact restrictionOnDerivedCompIso_inv_app_comp_factors.{d, d', d₀} g hg _
  · exact Functor.mapDerivedCategoryFactors_hom_naturality _ _
  · rw [reductionPartBaseChangeComplex_eq]
    exact Functor.map_comp _ _ _

variable {I₀ I₀' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (u₀ : I₀ ⟶ I₀')

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- Degreewise, the base change of the ideal part is restriction of the comparison of the
extensions of scalars tensored with `I₀`, then of `u₀`, followed by the comparison of the
restrictions of scalars. -/
theorem idealPartBaseChangeComplex_eq
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    idealPartBaseChangeComplex g hg u₀ P =
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (extensionOfScalarsCompComplexIso g hg P).hom ≫
            (NatTrans.mapHomologicalComplex
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).flip.map u₀)
                (ComplexShape.up ℤ)).app ((extensionOfScalarsCochainComplex J f').obj
                  ((extensionOfScalarsCochainComplex J g).obj P))) ≫
        (Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
          (ComplexShape.up ℤ)).inv.app (((tensorRight O₀ I₀').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochainComplex J f').obj
              ((extensionOfScalarsCochainComplex J g).obj P))) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  dsimp only [idealPartBaseChangeComplex, idealPartBaseChange, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, extensionOfScalarsCompComplexIso_hom_f,
    Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex_inv_app_f, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.mapHomologicalComplex_app_f]
  rw [Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map, NatTrans.mapHomologicalComplex_app_f,
    NatIso.mapHomologicalComplex_inv_app_f, Functor.mapHomologicalComplex_obj_X,
    extensionOfScalarsCochainComplex_obj_X, Functor.comp_obj]

/-- The derived map of ideal parts commutes with the base change, at the localization of a
complex: through the comparisons with the degreewise functors it is the degreewise comparison
of the extensions of scalars followed by the degreewise map of ideal parts. -/
theorem derivedTensorRightMap_baseChange
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (derivedTensorRightMap.{d₀} u₀).app
        ((derivedExtensionOfScalars.{d, d₀} f).obj (DerivedCategory.Q.obj P)) ≫
      (derivedTensorRight.{d₀} I₀').map
        ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app (DerivedCategory.Q.obj P) ≫
          (derivedExtensionOfScalars.{d', d₀} f').map
            ((derivedExtensionOfScalarsCounit.{d, d'} g).app P) ≫
          (derivedExtensionOfScalarsCounit.{d', d₀} f').app
            ((extensionOfScalarsCochainComplex J g).obj P)) ≫
      (derivedTensorRightCounit.{d₀} I₀').app ((extensionOfScalarsCochainComplex J f').obj
        ((extensionOfScalarsCochainComplex J g).obj P)) =
      (derivedTensorRight.{d₀} I₀).map ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P) ≫
        (derivedTensorRightCounit.{d₀} I₀).app ((extensionOfScalarsCochainComplex J f).obj P) ≫
        DerivedCategory.Q.map
          (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (extensionOfScalarsCompComplexIso g hg P).hom ≫
            (NatTrans.mapHomologicalComplex
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).flip.map u₀)
                (ComplexShape.up ℤ)).app ((extensionOfScalarsCochainComplex J f').obj
                  ((extensionOfScalarsCochainComplex J g).obj P))) := by
  rw [derivedExtensionOfScalarsCompIso_inv_app_Q.{d, d', d₀} g hg P, Functor.map_comp,
    Category.assoc, ← reassoc_of% ((derivedTensorRightMap.{d₀} u₀).naturality
      ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P)),
    ← reassoc_of% ((derivedTensorRightMap.{d₀} u₀).naturality
      (DerivedCategory.Q.map (extensionOfScalarsCompComplexIso g hg P).hom)),
    derivedTensorRightMap_app_Q]
  have h :=
    (derivedTensorRightCounit.{d₀} I₀).naturality (extensionOfScalarsCompComplexIso g hg P).hom
  dsimp only [Functor.comp_map] at h
  rw [reassoc_of% h, Functor.map_comp]

/-- The first vertex at a complex, componentwise. -/
theorem vertexOne_app_eq {O₁ O₂ : Sheaf J CommRingCat.{u}} (h : O₁ ⟶ O₂)
    [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))]
    [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))]
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) ℤ) :
    (vertexOne.{d, d₀} h M).app P =
      ((restrictionOnDerived.{d, d₀} h).map ((derivedTensorRight.{d₀} M).map
          ((derivedExtensionOfScalarsCounit.{d, d₀} h).app P)) ≫
        (restrictionOnDerived.{d, d₀} h).map
          ((derivedTensorRightCounit.{d₀} M).app ((extensionOfScalarsCochainComplex J h).obj P))) ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J h)).mapDerivedCategoryFactors.hom.app
          (((tensorRight O₂ M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((extensionOfScalarsCochainComplex J h).obj P)) :=
  (Category.assoc _ _ _).symm

/-- The inverse of the identification of the two derived restrictions, at the localization of a
complex, through the comparisons with the degreewise restrictions. -/
theorem restrictionOnDerivedCompIso_inv_app_Q_comp_factors
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app (DerivedCategory.Q.obj K) ≫
      (restrictionOnDerived.{d, d'} g).map
          ((SheafOfModules.restrictScalars.{u}
            (ringSheafMapOf J f')).mapDerivedCategoryFactors.hom.app K) ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
          (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) =
      (SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
            (ComplexShape.up ℤ)).inv.app K) :=
  restrictionOnDerivedCompIso_inv_app_Q_comp_factors_aux.{d, d', d₀} g hg K

/-- **The first vertex under base change.** At a complex `P` of `O`-modules, the base change of
the first vertex identification along `g`, followed by the map of ideal parts, is the degreewise
base change of the ideal part. -/
theorem vertexOne_baseChange
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (restrictionOnDerived.{d, d₀} f).map
        ((derivedTensorRightMap.{d₀} u₀).app
            ((derivedExtensionOfScalars.{d, d₀} f).obj (DerivedCategory.Q.obj P)) ≫
          (derivedTensorRight.{d₀} I₀').map
            ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app
              (DerivedCategory.Q.obj P))) ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _ ≫
      (restrictionOnDerived.{d, d'} g).map
        ((restrictionOnDerived.{d', d₀} f').map ((derivedTensorRight.{d₀} I₀').map
          ((derivedExtensionOfScalars.{d', d₀} f').map
            ((derivedExtensionOfScalarsCounit.{d, d'} g).app P))) ≫
          (vertexOne.{d', d₀} f' I₀').app ((extensionOfScalarsCochainComplex J g).obj P)) ≫
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
        (((idealPart f' I₀').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((extensionOfScalarsCochainComplex J g).obj P)) =
      (vertexOne.{d, d₀} f I₀).app P ≫
        DerivedCategory.Q.map (idealPartBaseChangeComplex g hg u₀ P) := by
  refine vertex_chain_eq (restrictionOnDerived.{d, d'} g) _ _ _ _ _ _ _
    (vertexOne_app_eq.{d', d₀} f' I₀' ((extensionOfScalarsCochainComplex J g).obj P))
    ((restrictionOnDerived.{d, d₀} f).map
      ((derivedTensorRight.{d₀} I₀').map ((derivedExtensionOfScalars.{d', d₀} f').map
          ((derivedExtensionOfScalarsCounit.{d, d'} g).app P)) ≫
        (derivedTensorRight.{d₀} I₀').map ((derivedExtensionOfScalarsCounit.{d', d₀} f').app
          ((extensionOfScalarsCochainComplex J g).obj P)) ≫
        (derivedTensorRightCounit.{d₀} I₀').app ((extensionOfScalarsCochainComplex J f').obj
          ((extensionOfScalarsCochainComplex J g).obj P))))
    ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _) ?_
    _ ((restrictionOnDerived.{d, d₀} f).map (DerivedCategory.Q.map
        (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extensionOfScalarsCompComplexIso g hg P).hom ≫
        (NatTrans.mapHomologicalComplex
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).flip.map u₀)
            (ComplexShape.up ℤ)).app ((extensionOfScalarsCochainComplex J f').obj
              ((extensionOfScalarsCochainComplex J g).obj P))))) ?_
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors.hom.app
      (((tensorRight O₀ I₀').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochainComplex J f').obj
          ((extensionOfScalarsCochainComplex J g).obj P))))
    (DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
      (ComplexShape.up ℤ)).inv.app
        (((tensorRight O₀ I₀').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((extensionOfScalarsCochainComplex J f').obj
            ((extensionOfScalarsCochainComplex J g).obj P))))) ?_
    _ (DerivedCategory.Q.map
      (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extensionOfScalarsCompComplexIso g hg P).hom ≫
        (NatTrans.mapHomologicalComplex
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).flip.map u₀)
            (ComplexShape.up ℤ)).app ((extensionOfScalarsCochainComplex J f').obj
              ((extensionOfScalarsCochainComplex J g).obj P))))) ?_
    _ (vertexOne_app_eq.{d, d₀} f I₀ P) _ ?_
  · rw [← Functor.map_comp (restrictionOnDerived.{d', d₀} f'),
      ← Functor.map_comp (restrictionOnDerived.{d', d₀} f')]
    exact ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.naturality _).symm
  · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (by simpa only [Functor.map_comp, Category.assoc] using
      derivedTensorRightMap_baseChange.{d, d', d₀} g hg u₀ P)
  · exact restrictionOnDerivedCompIso_inv_app_Q_comp_factors.{d, d', d₀} g hg _
  · exact Functor.mapDerivedCategoryFactors_hom_naturality _ _
  · rw [idealPartBaseChangeComplex_eq]
    exact Functor.map_comp _ _ _

/-! ### The connecting morphisms under base change -/

/-- The connecting morphisms of two reduction triangles, related through a functor `G` commuting
with the shift: the third vertices (`hA`), the image of the connecting morphism under `G` (`hC`),
the naturality of the connecting morphisms for the morphism of reduction sequences (`hB`) and the
first vertices (`hD`). -/
theorem connecting_chain_eq {D D' : Type*} [Category D] [Category D'] [HasShift D ℤ]
    [HasShift D' ℤ] (G : D' ⥤ D) [G.CommShift ℤ]
    {A B E₃ E₁ T₁ U Z₃ Z₁ : D} {B' E₃' E₁' T₁' : D'}
    (a : A ⟶ B) (r : B ⟶ G.obj B') (c₃' : B' ⟶ E₃') (δ' : E₃' ⟶ E₁'⟦(1 : ℤ)⟧)
    (c₁' : E₁' ⟶ T₁') (ρh : G.obj T₁' ⟶ U)
    (c₃ : A ⟶ E₃) (δ : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (c₁ : E₁ ⟶ T₁) (x : T₁ ⟶ U)
    (z₃ : G.obj E₃' ⟶ Z₃) (q₃ : E₃ ⟶ Z₃) (δg : Z₃ ⟶ Z₁⟦(1 : ℤ)⟧) (y₁ : Z₁ ⟶ G.obj E₁')
    (q₁ : E₁ ⟶ Z₁) (κ' : B' ⟶ T₁'⟦(1 : ℤ)⟧) (hκ' : κ' = c₃' ≫ δ' ≫ c₁'⟦(1 : ℤ)⟧')
    (κ : A ⟶ T₁⟦(1 : ℤ)⟧) (hκ : κ = c₃ ≫ δ ≫ c₁⟦(1 : ℤ)⟧')
    (hA : a ≫ r ≫ G.map c₃' ≫ z₃ = c₃ ≫ q₃)
    (hC : G.map δ' = z₃ ≫ δg ≫ y₁⟦(1 : ℤ)⟧' ≫ (G.commShiftIso (1 : ℤ)).inv.app E₁')
    (hB : q₃ ≫ δg = δ ≫ q₁⟦(1 : ℤ)⟧')
    (hD : q₁ ≫ y₁ ≫ G.map c₁' ≫ ρh = c₁ ≫ x) :
    a ≫ r ≫ G.map κ' ≫ (G.commShiftIso (1 : ℤ)).hom.app T₁' ≫ ρh⟦(1 : ℤ)⟧' =
      κ ≫ x⟦(1 : ℤ)⟧' := by
  subst hκ hκ'
  simp only [Functor.map_comp, Category.assoc, hC]
  rw [Functor.commShiftIso_hom_naturality_assoc, Iso.inv_hom_id_app_assoc, reassoc_of% hA,
    reassoc_of% hB]
  simp only [← Functor.map_comp, hD]

/-- A relation `x ≫ r ≫ G m ≫ z = V ≫ q` between isomorphisms is inverted. -/
theorem vertex_inverse_eq {D D' : Type*} [Category D] [Category D'] (G : D' ⥤ D)
    {T₁ U Z₁ E₁ : D} {B' E₁' : D'}
    (x : T₁ ⟶ U) (r : U ⟶ G.obj B') (m : B' ⟶ E₁') (z : G.obj E₁' ⟶ Z₁) (V : T₁ ⟶ E₁)
    (q : E₁ ⟶ Z₁) (hV : x ≫ r ≫ G.map m ≫ z = V ≫ q)
    (c₁' : E₁' ⟶ B') (hm : m ≫ c₁' = 𝟙 _) (y : Z₁ ⟶ G.obj E₁') (hz : z ≫ y = 𝟙 _)
    (ρh : G.obj B' ⟶ U) (hr : r ≫ ρh = 𝟙 _) (c₁ : E₁ ⟶ T₁) (hc : c₁ ≫ V = 𝟙 _) :
    q ≫ y ≫ G.map c₁' ≫ ρh = c₁ ≫ x := by
  calc q ≫ y ≫ G.map c₁' ≫ ρh = (c₁ ≫ V) ≫ q ≫ y ≫ G.map c₁' ≫ ρh := by
        rw [hc, Category.id_comp]
    _ = c₁ ≫ x ≫ r ≫ G.map (m ≫ c₁') ≫ ρh := by
        rw [Category.assoc, reassoc_of% hV.symm]
        simp only [Category.assoc, reassoc_of% hz, Functor.map_comp]
    _ = c₁ ≫ x := by rw [hm, CategoryTheory.Functor.map_id, Category.id_comp, hr,
        Category.comp_id]

section Connecting

variable (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
  (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
  (ι' : restrictIdeal f' I₀' ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
  (hι' :
    ι' ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f') = 0)
  (hS' : (idealSequenceOf f' I₀' ι' hι').ShortExact)
  (hu : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J g) =
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map u₀ ≫
        (restrictScalarsCompIsoOf g hg).inv.app I₀' ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map ι')

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))] in
/-- Extension of scalars of a complex strictly in degrees `≤ 0` is strictly in degrees `≤ 0`. -/
theorem isStrictlyLE_extensionOfScalarsCochainComplex
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    [P.IsStrictlyLE 0] : ((extensionOfScalarsCochainComplex J g).obj P).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
    (extensionOfScalars g).map_isZero (CochainComplex.isZero_of_isStrictlyLE P 0 i hi)

include hu in
/-- **The connecting morphisms of the reduction triangles under base change**, at the
localization of a complex `P` of flat modules strictly in degrees `≤ 0`: through the identification
of the derived base changes, the identification of the derived restrictions and the map of ideal
parts, the connecting morphism of the reduction triangle of `Q(P)` along `f` is the one of its
derived base change along `f'`. -/
theorem connecting_baseChange_Q
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    [P.IsStrictlyLE 0] (hP : ∀ n, flatObjects O (P.X n)) :
    (restrictionOnDerived.{d, d₀} f).map
        ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app (DerivedCategory.Q.obj P)) ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _ ≫
      (restrictionOnDerived.{d, d'} g).map ((flatReduction.{d', d₀} f' ι' hι' hS').connecting
        ((derivedExtensionOfScalars.{d, d'} g).obj (DerivedCategory.Q.obj P))) ≫
      ((restrictionOnDerived.{d, d'} g).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.app _)⟦(1 : ℤ)⟧' =
      (flatReduction.{d, d₀} f ι hι hS).connecting (DerivedCategory.Q.obj P) ≫
        ((restrictionOnDerived.{d, d₀} f).map
          ((derivedTensorRightMap.{d₀} u₀).app
              ((derivedExtensionOfScalars.{d, d₀} f).obj (DerivedCategory.Q.obj P)) ≫
            (derivedTensorRight.{d₀} I₀').map
              ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app
                (DerivedCategory.Q.obj P))))⟦(1 : ℤ)⟧' := by
  have hPc : IsFlatCellular P :=
    StacksDraft.UnboundedLeftDerivedFunctor.isPCellular_of_isStrictlyLE_zero _ P hP
  have hP' : ∀ n, flatObjects O' (((extensionOfScalarsCochainComplex J g).obj P).X n) :=
    fun n => flatObjects_extensionOfScalars g (hP n)
  have := isStrictlyLE_extensionOfScalarsCochainComplex g P
  have hP'c : IsFlatCellular ((extensionOfScalarsCochainComplex J g).obj P) :=
    StacksDraft.UnboundedLeftDerivedFunctor.isPCellular_of_isStrictlyLE_zero _ _ hP'
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d'} g P hPc
  refine connecting_chain_eq (restrictionOnDerived.{d, d'} g) _ _ _ _ _ _ _ _ _ _
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
      (((reductionPart f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochainComplex J g).obj P)))
    (DerivedCategory.Q.map (reductionPartBaseChangeComplex g hg P))
    (DerivedCategory.triangleOfSESδ ((shortExact_reductionSequence ι' hι' hS' _ hP').map_of_exact
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
        (ComplexShape.up ℤ))))
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.inv.app
      (((idealPart f' I₀').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochainComplex J g).obj P)))
    (DerivedCategory.Q.map (idealPartBaseChangeComplex g hg u₀ P)) _
    (flatReduction_connecting.{d', d₀} f' ι' hι' hS' hP'c
      (asIso ((derivedExtensionOfScalarsCounit.{d, d'} g).app P)).symm)
    _ (flatReduction_connecting.{d, d₀} f ι hι hS hPc (Iso.refl _)) ?_ ?_ ?_ ?_
  · rw [vertexThreeIso_asIso_symm_inv, vertexThreeIso_refl_inv]
    exact vertexThree_baseChange.{d, d', d₀} g hg P
  · exact DerivedCategory.map_triangleOfSESδ _ _
  · exact (DerivedCategory.triangleOfSESδ_naturality _ _
      (reductionSequenceBaseChange g hg u₀ ι hι ι' hι' hu P)).symm
  · refine vertex_inverse_eq (restrictionOnDerived.{d, d'} g) _ _ _ _ _ _
      (vertexOne_baseChange.{d, d', d₀} g hg u₀ P) _ ?_ _ ?_ _ ?_ _ ?_
    · rw [← vertexOneIso_asIso_symm_inv _ hP'c, Iso.inv_hom_id]
    · exact Iso.hom_inv_id_app _ _
    · exact Iso.inv_hom_id_app _ _
    · exact vertexOneIso_refl_hom_comp _ _


/-- Naturality of a composite through a functor `G` and two endofunctors `F`, `F'`, from the
naturality of its five factors. -/
theorem naturality_chain_lhs {D D' : Type*} [Category D] [Category D'] (G : D' ⥤ D) (F : D ⥤ D)
    (F' : D' ⥤ D') {A₁ A₂ B₁ B₂ V₁ V₂ : D} {C₁ C₂ W₁ W₂ : D'}
    (y : A₁ ⟶ A₂) (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂) (m₁ : B₁ ⟶ B₂)
    (r₁ : B₁ ⟶ G.obj C₁) (r₂ : B₂ ⟶ G.obj C₂) (m₂ : C₁ ⟶ C₂)
    (κ₁ : C₁ ⟶ F'.obj W₁) (κ₂ : C₂ ⟶ F'.obj W₂) (m₃ : W₁ ⟶ W₂)
    (c₁ : G.obj (F'.obj W₁) ⟶ F.obj (G.obj W₁)) (c₂ : G.obj (F'.obj W₂) ⟶ F.obj (G.obj W₂))
    (ρ₁ : G.obj W₁ ⟶ V₁) (ρ₂ : G.obj W₂ ⟶ V₂) (X : V₁ ⟶ V₂)
    (h₁ : y ≫ a₂ = a₁ ≫ m₁) (h₂ : m₁ ≫ r₂ = r₁ ≫ G.map m₂) (h₃ : m₂ ≫ κ₂ = κ₁ ≫ F'.map m₃)
    (h₄ : G.map (F'.map m₃) ≫ c₂ = c₁ ≫ F.map (G.map m₃)) (h₅ : G.map m₃ ≫ ρ₂ = ρ₁ ≫ X) :
    y ≫ a₂ ≫ r₂ ≫ G.map κ₂ ≫ c₂ ≫ F.map ρ₂ =
      (a₁ ≫ r₁ ≫ G.map κ₁ ≫ c₁ ≫ F.map ρ₁) ≫ F.map X := by
  rw [reassoc_of% h₁, reassoc_of% h₂, ← G.map_comp_assoc, h₃, G.map_comp_assoc, reassoc_of% h₄,
    ← F.map_comp, h₅]
  simp

/-- A functor carries a commutative square to a commutative square. -/
theorem functor_map_comp_eq_of_eq {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {X Y Y' Z : D} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Y') (e : Y' ⟶ Z) (h : a ≫ b = c ≫ e) :
    F.map a ≫ F.map b = F.map c ≫ F.map e := by
  rw [← F.map_comp, h, F.map_comp]

/-- Naturality of a composite `κ ≫ F x` from the naturality of its two factors. -/
theorem naturality_chain_rhs {D : Type*} [Category D] (F : D ⥤ D) {A₁ A₂ T₁ T₂ V₁ V₂ : D}
    (y : A₁ ⟶ A₂) (κ₁ : A₁ ⟶ F.obj T₁) (κ₂ : A₂ ⟶ F.obj T₂) (n : T₁ ⟶ T₂)
    (x₁ : T₁ ⟶ V₁) (x₂ : T₂ ⟶ V₂) (X : V₁ ⟶ V₂)
    (h₁ : y ≫ κ₂ = κ₁ ≫ F.map n) (h₂ : n ≫ x₂ = x₁ ≫ X) :
    y ≫ κ₂ ≫ F.map x₂ = (κ₁ ≫ F.map x₁) ≫ F.map X := by
  rw [reassoc_of% h₁, ← F.map_comp, h₂]
  simp

/-- The two sides of the comparison of the connecting morphisms are natural: the left side. -/
theorem connecting_baseChange_lhs_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (e : K ⟶ K') :
    (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalars.{d, d₀} f).map e) ≫
      (restrictionOnDerived.{d, d₀} f).map
        ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K') ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _ ≫
      (restrictionOnDerived.{d, d'} g).map ((flatReduction.{d', d₀} f' ι' hι' hS').connecting
        ((derivedExtensionOfScalars.{d, d'} g).obj K')) ≫
      ((restrictionOnDerived.{d, d'} g).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.app _)⟦(1 : ℤ)⟧' =
    ((restrictionOnDerived.{d, d₀} f).map
        ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K) ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _ ≫
      (restrictionOnDerived.{d, d'} g).map ((flatReduction.{d', d₀} f' ι' hι' hS').connecting
        ((derivedExtensionOfScalars.{d, d'} g).obj K)) ≫
      ((restrictionOnDerived.{d, d'} g).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.app _)⟦(1 : ℤ)⟧') ≫
      ((restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀').map
        ((derivedExtensionOfScalars.{d', d₀} f').map
          ((derivedExtensionOfScalars.{d, d'} g).map e))))⟦(1 : ℤ)⟧' := by
  have h1 := (derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.naturality e
  dsimp only [Functor.comp_map] at h1
  refine naturality_chain_lhs (restrictionOnDerived.{d, d'} g) (shiftFunctor _ (1 : ℤ))
    (shiftFunctor _ (1 : ℤ)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by rw [← Functor.map_comp, ← Functor.map_comp, h1])
    ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.naturality _)
    (flatReduction_connecting_naturality.{d', d₀} f' ι' hι' hS'
      ((derivedExtensionOfScalars.{d, d'} g).map e)).symm
    (Functor.commShiftIso_hom_naturality _ _ _)
    ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.naturality _)

/-- The derived map of ideal parts followed by the identification of the derived base changes is
natural. -/
theorem derivedTensorRightMap_comp_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (e : K ⟶ K') :
    (derivedTensorRight.{d₀} I₀).map ((derivedExtensionOfScalars.{d, d₀} f).map e) ≫
        ((derivedTensorRightMap.{d₀} u₀).app ((derivedExtensionOfScalars.{d, d₀} f).obj K') ≫
          (derivedTensorRight.{d₀} I₀').map
            ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K')) =
      ((derivedTensorRightMap.{d₀} u₀).app ((derivedExtensionOfScalars.{d, d₀} f).obj K) ≫
          (derivedTensorRight.{d₀} I₀').map
            ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K)) ≫
        (derivedTensorRight.{d₀} I₀').map ((derivedExtensionOfScalars.{d', d₀} f').map
          ((derivedExtensionOfScalars.{d, d'} g).map e)) := by
  have h1 := (derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.naturality e
  have h2 :=
    (derivedTensorRightMap.{d₀} u₀).naturality ((derivedExtensionOfScalars.{d, d₀} f).map e)
  dsimp only [Functor.comp_map] at h1
  rw [reassoc_of% h2, ← Functor.map_comp, h1, Functor.map_comp, Category.assoc]

/-- The two sides of the comparison of the connecting morphisms are natural: the right side. -/
theorem connecting_baseChange_rhs_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (e : K ⟶ K') :
    (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalars.{d, d₀} f).map e) ≫
      (flatReduction.{d, d₀} f ι hι hS).connecting K' ≫
        ((restrictionOnDerived.{d, d₀} f).map
          ((derivedTensorRightMap.{d₀} u₀).app ((derivedExtensionOfScalars.{d, d₀} f).obj K') ≫
            (derivedTensorRight.{d₀} I₀').map
              ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K')))⟦(1 : ℤ)⟧' =
    ((flatReduction.{d, d₀} f ι hι hS).connecting K ≫
        ((restrictionOnDerived.{d, d₀} f).map
          ((derivedTensorRightMap.{d₀} u₀).app ((derivedExtensionOfScalars.{d, d₀} f).obj K) ≫
            (derivedTensorRight.{d₀} I₀').map
              ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K)))⟦(1 : ℤ)⟧') ≫
      ((restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀').map
        ((derivedExtensionOfScalars.{d', d₀} f').map
          ((derivedExtensionOfScalars.{d, d'} g).map e))))⟦(1 : ℤ)⟧' := by
  refine naturality_chain_rhs (shiftFunctor _ (1 : ℤ)) _ _ _ _ _ _ _
    (flatReduction_connecting_naturality.{d, d₀} f ι hι hS e).symm ?_
  exact functor_map_comp_eq_of_eq (restrictionOnDerived.{d, d₀} f) _ _ _ _
    (derivedTensorRightMap_comp_naturality.{d, d', d₀} g hg u₀ e)

include hu in
/-- **The connecting morphisms of the reduction triangles under base change**, at any object `K`
of `D^{≤ 0}`: through the identification of the derived base changes, the identification of the
derived restrictions and the map of ideal parts, the connecting morphism of the reduction triangle
of `K` along `f` is the one of its derived base change along `f'`. -/
theorem connecting_baseChange
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    [K.IsLE 0] :
    (restrictionOnDerived.{d, d₀} f).map
        ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K) ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _ ≫
      (restrictionOnDerived.{d, d'} g).map ((flatReduction.{d', d₀} f' ι' hι' hS').connecting
        ((derivedExtensionOfScalars.{d, d'} g).obj K)) ≫
      ((restrictionOnDerived.{d, d'} g).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.app _)⟦(1 : ℤ)⟧' =
      (flatReduction.{d, d₀} f ι hι hS).connecting K ≫
        ((restrictionOnDerived.{d, d₀} f).map
          ((derivedTensorRightMap.{d₀} u₀).app
              ((derivedExtensionOfScalars.{d, d₀} f).obj K) ≫
            (derivedTensorRight.{d₀} I₀').map
              ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K)))⟦(1 : ℤ)⟧' := by
  have hK : (DerivedCategory.Q.objPreimage K).IsLE 0 := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso (DerivedCategory.Q.objObjPreimageIso K).symm 0
  obtain ⟨L, q, hq, hL, hLE⟩ := (CochainComplex.exists_quasiIso_prop (flatObjects O)
    (flatObjects_cover O) 0).2 (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := q)).2 hq
  let e : DerivedCategory.Q.obj L ≅ K := asIso (DerivedCategory.Q.map q) ≪≫
    DerivedCategory.Q.objObjPreimageIso K
  refine (cancel_epi ((restrictionOnDerived.{d, d₀} f).map
    ((derivedExtensionOfScalars.{d, d₀} f).map e.hom))).1 ?_
  exact (connecting_baseChange_lhs_naturality.{d, d', d₀} g hg ι' hι' hS' e.hom).trans
    ((congrArg (· ≫ _)
        (connecting_baseChange_Q.{d, d', d₀} g hg u₀ ι hι hS ι' hι' hS' hu L hL)).trans
      (connecting_baseChange_rhs_naturality.{d, d', d₀} g hg u₀ ι hι hS e.hom).symm)

include hu in
/-- **The base change between the reduction triangles of two square-zero thickenings.** For a
morphism `g : O ⟶ O'` over `O₀` of square-zero extensions with ideals `I₀` and `I₀'` and a map
`u₀ : I₀ ⟶ I₀'` compatible with the inclusions of the ideals (`hu`), derived extension of
scalars along `g` is a base change between the reduction triangles of
`Deformation.ComplexLift.flatReduction`, with the map of ideal parts induced by `u₀`. -/
def flatReductionBaseChange :
    DerivedReductionBaseChange (flatReduction.{d, d₀} f ι hι hS)
      (flatReduction.{d', d₀} f' ι' hι' hS') where
  functor := derivedExtensionOfScalars.{d, d'} g
  minus K := (derivedExtensionOfScalarsData.{d, d'} g).minus_baseChange_obj K.obj K.property
  baseChangeIso := derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg
  idealMap := derivedTensorRightMap.{d₀} u₀
  extLiftObstruction_eq K₁ K₂ _ α := by
    have : NatTrans.CommShift
        (F₁ := (flatReduction.{d', d₀} f' ι' hι' hS').restriction ⋙ restrictionOnDerived.{d, d'} g)
        (F₂ := (flatReduction.{d, d₀} f ι hι hS).restriction)
        (restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom ℤ :=
      commShift_restrictionOnDerivedCompIso_hom.{d, d', d₀} g hg
    refine extLiftObstruction_baseChange_of_connecting (flatReduction.{d, d₀} f ι hι hS)
      (flatReduction.{d', d₀} f' ι' hι' hS') (derivedAdjunction.{d, d'} g)
      (derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg)
      (restrictionOnDerivedCompIso.{d, d', d₀} g hg) ?_
      (derivedTensorRightMap.{d₀} u₀) K₁ K₂ ?_ α
    · exact derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg
    · exact connecting_baseChange.{d, d', d₀} g hg u₀ ι hι hS ι' hι' hS' hu K₂

end Connecting

end Vertices


end Deformation.ComplexLift

end
