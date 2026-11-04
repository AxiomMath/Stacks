module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackSheafTensorUnit
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatTensorComplexGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality

/-!
# The isomorphism of Stacks 07A4 and the right unitors

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The isomorphism
`Lf^*(E ⊗^L O_D) ≅ Lf^*E ⊗^L Lf^*O_D` of Stacks 07A4, followed by `Lf^*O_D ≅ O_C` in the second
factor and by the unit law of `⊗^L`, is `Lf^*` of the unit law `E ⊗^L O_D ≅ E`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackSingleUnitMap`: `f^*(O_D[0]) ⟶ O_C[0]`.

## Main results

* `Stacks.SheafOfModules.ι_tensorComplexUnitIsoFreeSections_hom_f`: the unit law
  `Tot(K ⊗ O[0]) ≅ K` on a summand.
* `DerivedPullbackOfToposHom.pullbackComplex_map_tensorComplexUnitIsoFreeSections`: the comparison
  of total tensor complexes of Stacks 03EL is compatible with the unit laws.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral_hom_eq`:
  `Lf^*O_D[0] ≅ O_C[0]` through the K-flat model `O_D[0]`.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_unit`: the
  right-unitor coherence of Stacks 07A4.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} S).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} S).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor S)
      (ComplexShape.up ℤ)]

/-- **The unit law `Tot(K ⊗_O O[0]) ≅ K` on a summand**: on the summand of bidegree `(n, 0)` it
is the unit law `K^n ⊗_O O ≅ K^n` of `⊗_O`. -/
lemma ι_tensorComplexUnitIsoFreeSections_hom_f
    (K : CochainComplex (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ)
    (n : ℤ) (h : n + 0 = n) :
    HomologicalComplex.ιMapBifunctor K ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)))
        (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ) n 0 n h ≫
        (tensorComplexUnitIsoFreeSections S K).hom.f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor S).obj (K.X n)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))).hom ≫
        (sheafTensorUnitIsoFreeSections S (K.X n)).hom := by
  have h1 := CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f
    (Stacks.SheafOfModules.Tensor.sheafTensor S) K
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) n
  have h2 : (tensorComplexUnitIsoFreeSections S K).hom.f n =
      (CochainComplex.KFlatBifunctor.totalSingleIso (Stacks.SheafOfModules.Tensor.sheafTensor S) K
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))).hom.f n ≫
        (rowComplexUnitIsoFreeSections S K).hom.f n := rfl
  have h3 : (rowComplexUnitIsoFreeSections S K).hom.f n =
      (sheafTensorUnitIsoFreeSections S (K.X n)).hom :=
    Category.comp_id _
  rw [h2, ← Category.assoc, h1, h3]
  rfl

end Stacks.SheafOfModules

namespace Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

universe u c c'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- The comparison `f^*(O_D[0]) ⟶ O_C[0]` of complexes: the degreewise pullback of a complex
concentrated in degree `0`, followed by `f^*O_D ≅ O_C`. -/
def pullbackSingleUnitMap :
    (pullbackComplex f).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (HomologicalComplex.singleMapHomologicalComplex (f.toModulesHom.pullbackModules)
      (ComplexShape.up ℤ) 0).hom.app _ ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).inv

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- A rearrangement of composites in an arbitrary category, given commuting squares. -/
private lemma summand_assemble_aux {D : Type*} [Category D]
    {S₀ T₀ K₀ M₀ P₀ P₁ P₂ P₃ T₁ T₂ : D}
    (a : S₀ ⟶ T₀) (b : T₀ ⟶ K₀) (m : S₀ ⟶ M₀) (k : M₀ ⟶ K₀) (p₀ : S₀ ⟶ P₀) (p₁ : M₀ ⟶ P₁)
    (g' : P₀ ⟶ P₁) (g : P₁ ⟶ P₂) (e : P₂ ⟶ K₀) (c : T₀ ⟶ T₁) (d : T₁ ⟶ T₂) (e' : T₂ ⟶ K₀)
    (i₁ : P₀ ⟶ T₁) (i₂ : P₃ ⟶ T₂) (v : P₀ ⟶ P₃) (x : P₃ ⟶ P₂)
    (hL : a ≫ b = m ≫ k) (hM : k = p₁ ≫ g ≫ e) (hN : m ≫ p₁ = p₀ ≫ g')
    (hR₁ : a ≫ c = p₀ ≫ i₁) (hR₂ : i₁ ≫ d = v ≫ i₂) (hR₃ : i₂ ≫ e' = x ≫ e)
    (hν : v ≫ x = g' ≫ g) :
    a ≫ b = a ≫ c ≫ d ≫ e' := by
  rw [hL, hM, ← Category.assoc m, hN, ← Category.assoc a c, hR₁]
  simp only [Category.assoc]
  rw [reassoc_of% hR₂, hR₃, reassoc_of% hν]

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
private lemma single_unit_aux {D : Type*} [Category D] {P Q Q' R R' : D}
    (z : P ⟶ R') (a : P ⟶ Q') (b : Q' ⟶ R') (x : P ⟶ Q) (y : Q' ≅ Q) (n : Q ⟶ R) (w : R' ≅ R)
    (h1 : z = a ≫ b) (h2 : a = x ≫ y.inv) (h3 : b = y.hom ≫ n ≫ w.inv) :
    z ≫ w.hom = x ≫ n := by
  rw [h1, h2, h3]
  simp

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The summand of bidegree `(p, 0)` of `pullbackComplex_map_tensorComplexUnitIsoFreeSections`. -/
private lemma summand_unit
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p : ℤ) (hpq : p + 0 = p) :
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).map
        (HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p 0 p hpq) ≫
      ((pullbackComplex f).map
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections Y.O K).hom).f p =
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).map
        (HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p 0 p hpq) ≫
      ((pullbackTensorTotalComplexIso f K ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom ≫
        HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackSingleUnitMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) ≫
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O
          ((pullbackComplex f).obj K)).hom).f p := by
  have hL : (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).map
        (HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p 0 p hpq) ≫
      ((pullbackComplex f).map
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections Y.O K).hom).f p =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (K.X p)).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom) ≫
        (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).map
          (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections Y.O (K.X p)).hom :=
    ((Functor.map_comp _ _ _).symm.trans (congrArg
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).map
      (Stacks.SheafOfModules.ι_tensorComplexUnitIsoFreeSections_hom_f Y.O K p hpq))).trans
      (Functor.map_comp _ _ _)
  have hM :=
    Stacks.SheafOfModules.RingedToposPullback.pullbackModules_map_sheafTensorUnitIsoFreeSections
      f.toModulesHom (K.X p)
  have hN := Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_snd f.toModulesHom (K.X p)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom
  have hR₁ := Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom f.toModulesHom K
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) p 0 p hpq
  have hR₂ : HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K)
        ((pullbackComplex f).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p 0 p hpq ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackSingleUnitMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)).f p =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (((pullbackComplex f).obj K).X p)).map
          ((pullbackSingleUnitMap f).f 0) ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p 0 p hpq := by
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp
  have hR₃ := Stacks.SheafOfModules.ι_tensorComplexUnitIsoFreeSections_hom_f X.O
    ((pullbackComplex f).obj K) p hpq
  have hν : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        (((pullbackComplex f).obj K).X p)).map ((pullbackSingleUnitMap f).f 0) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (((pullbackComplex f).obj K).X p)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (((pullbackComplex f).obj K).X p)).map
          ((f.toModulesHom.pullbackModules).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (((pullbackComplex f).obj K).X p)).map
          (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).inv := by
    have h0 : (pullbackSingleUnitMap f).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom =
        (f.toModulesHom.pullbackModules).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom ≫
          (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).inv :=
      single_unit_aux _ _ _ _ _ _ _ rfl
        (HomologicalComplex.singleMapHomologicalComplex_hom_app_self
          (f.toModulesHom.pullbackModules) (ComplexShape.up ℤ) 0 _)
        (HomologicalComplex.single_map_f_self _ _ _)
    exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ h0).trans (Functor.map_comp _ _ _))
  exact summand_assemble_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hM hN hR₁ hR₂ hR₃ hν

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The comparison of total tensor complexes of Stacks 03EL and the unit law**: at `(K, O_D[0])`
it is followed by `f^*O_D[0] ⟶ O_C[0]` and the unit law of `f^*K`, and this is `f^*` of the unit
law of `K`. -/
theorem pullbackComplex_map_tensorComplexUnitIsoFreeSections
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).map (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections Y.O K).hom =
      (pullbackTensorTotalComplexIso f K ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom ≫
        HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackSingleUnitMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) ≫
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O
          ((pullbackComplex f).obj K)).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine Stacks.Sheaves.DerivedPullback.hom_ext_pullbackTotal f.toModulesHom K
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) n
    (fun p q hpq => ?_)
  by_cases hq : q = 0
  · subst hq
    obtain rfl : n = p := by omega
    exact summand_unit f K _ hpq
  · refine IsZero.eq_of_src ?_ _ _
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hq

section Derived

open Stacks.Sheaves.DerivedPullback (isFlat_tensorComplex_X_general flatKFlatModelsQGeneral
  flatKFlatModelsWGeneral flatKFlatModelsQGeneral_isLocalization)

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
private lemma unitIso_aux {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A : C}
    {B B' E : D} (a : F.obj A ⟶ B) (b : B ⟶ B') (c c' : B' ⟶ E) (hc : c = c') :
    F.map (𝟙 A) ≫ a ≫ b ≫ 𝟙 B' ≫ c = a ≫ b ≫ c' := by
  simp [hc]

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
private lemma assoc_model_aux {D : Type*} [Category D] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : D}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) (e : A₄ ⟶ A₅) (g : A₅ ⟶ A₆) :
    (a ≫ b) ≫ (c ≫ d) ≫ e ≫ g = a ≫ b ≫ c ≫ d ≫ e ≫ g := by
  simp only [Category.assoc]

/-- `Lf^*(O_D[0]) ≅ O_C[0]` is the computation of `Lf^*(O_D[0])` by its K-flat model followed by
the image of the complex comparison `f^*(O_D[0]) ⟶ O_C[0]`. -/
lemma derivedPullbackUnitIsoGeneral_hom_eq :
    (derivedPullbackUnitIsoGeneral f).hom =
      (flatPullbackIso f _ (Stacks.SheafOfModules.isKFlat_single_unit Y.O)
          (isFlat_single_unit_X (Y := Y))).hom ≫
        DerivedCategory.Q.map (pullbackSingleUnitMap f) := by
  simp only [derivedPullbackUnitIsoGeneral, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, pullbackSingleUnitMap, Functor.map_comp]
  exact unitIso_aux _ _ _ _ _ rfl

/-- The isomorphism of Stacks 07A4 at `(K, O_D[0])` for a K-flat `K` with flat terms, written out
as the six-fold composite of the source. -/
private lemma derivedPullbackTensorIso_hom_app_unit_model_eq
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)) :
    (derivedPullbackTensorIso f TX TY).hom.app (DerivedCategory.Q.obj K,
        (DerivedCategory.singleFunctor _ 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) =
      (derivedPullback f).map (TY.comparison K _ hK
          (Stacks.SheafOfModules.isKFlat_single_unit Y.O)).hom ≫
        (flatPullbackIso f _ (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK
            (Stacks.SheafOfModules.isKFlat_single_unit Y.O))
          (isFlat_tensorComplex_X_general Y.O K _ hflat (isFlat_single_unit_X (Y := Y)))).hom ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f K _).hom ≫
        (TX.comparison ((pullbackComplex f).obj K)
            ((pullbackComplex f).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
          (kFlat_pullbackComplex' f K hK hflat)
          (kFlat_pullbackComplex' f _ (Stacks.SheafOfModules.isKFlat_single_unit Y.O)
            (isFlat_single_unit_X (Y := Y)))).inv ≫
        (TX.tensor.map (flatPullbackIso f K hK hflat).inv).app
          (DerivedCategory.Q.obj ((pullbackComplex f).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))) ≫
        (TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj K))).map
          (flatPullbackIso f _ (Stacks.SheafOfModules.isKFlat_single_unit Y.O)
            (isFlat_single_unit_X (Y := Y))).inv :=
  (derivedPullbackTensorIso_hom_app_model f TX TY K _ hK
      (Stacks.SheafOfModules.isKFlat_single_unit Y.O) hflat (isFlat_single_unit_X (Y := Y))).trans
    (assoc_model_aux _ _ _ _ _ _)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The complex-level coherence `pullbackComplex_map_tensorComplexUnitIsoFreeSections`, mapped to
the derived category. -/
private lemma Q_map_pullbackComplex_map_tensorComplexUnitIsoFreeSections
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    DerivedCategory.Q.map (pullbackTensorTotalComplexIso f K
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackSingleUnitMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O
          ((pullbackComplex f).obj K)).hom =
      DerivedCategory.Q.map ((pullbackComplex f).map
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections Y.O K).hom) :=
  (congrArg (fun z => DerivedCategory.Q.map (pullbackTensorTotalComplexIso f K
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom ≫ z)
      (DerivedCategory.Q.map_comp _ _).symm).trans
    ((DerivedCategory.Q.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Q.map
        (pullbackComplex_map_tensorComplexUnitIsoFreeSections f K).symm))

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
private lemma unit_side_aux {D : Type*} [Category D]
    {A₃ A₄ A₅ A₆ A₇ B₁ B₂ E₀ E₁ : D}
    (bi : A₃ ⟶ A₄) (k₁ : A₄ ⟶ A₇) (k₂ : A₇ ⟶ A₅) (m : A₅ ⟶ A₆) (u : A₆ ⟶ E₀)
    (n₁ : A₇ ⟶ A₆) (n₂ : A₄ ⟶ B₁) (k₁' : B₁ ⟶ A₆) (φ : E₀ ≅ E₁)
    (u' : B₁ ⟶ E₁) (cr : B₁ ⟶ B₂) (q₁ : B₂ ⟶ E₁) (q₂ : A₃ ⟶ B₂)
    (F3 : k₂ ≫ m = n₁) (F4 : k₁ ≫ n₁ = n₂ ≫ k₁') (F5 : k₁' ≫ u = u' ≫ φ.inv) (F6 : u' = cr ≫ q₁)
    (F7 : bi ≫ n₂ ≫ cr = q₂) :
    bi ≫ k₁ ≫ k₂ ≫ m ≫ u = q₂ ≫ q₁ ≫ φ.inv := by
  rw [reassoc_of% F3, reassoc_of% F4, F5, F6, ← reassoc_of% F7]
  simp only [Category.assoc]

/-- The `O_C`-side of `derivedPullbackTensorIso_hom_app_unit` at a K-flat complex with flat
terms. -/
private lemma derivedPullbackTensorIso_hom_app_unit_model_right
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)) :
    (TX.comparison ((pullbackComplex f).obj K)
        ((pullbackComplex f).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
          (kFlat_pullbackComplex' f K hK hflat)
          (kFlat_pullbackComplex' f _ (Stacks.SheafOfModules.isKFlat_single_unit Y.O)
            (isFlat_single_unit_X (Y := Y)))).inv ≫
        (TX.tensor.map (flatPullbackIso f K hK hflat).inv).app
          (DerivedCategory.Q.obj ((pullbackComplex f).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))) ≫
        (TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj K))).map
          (flatPullbackIso f _ (Stacks.SheafOfModules.isKFlat_single_unit Y.O)
            (isFlat_single_unit_X (Y := Y))).inv ≫
      (TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj K))).map
          (derivedPullbackUnitIsoGeneral f).hom ≫
        TX.unitComplexNatIso.hom.app ((derivedPullback f).obj (DerivedCategory.Q.obj K)) =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackSingleUnitMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O
          ((pullbackComplex f).obj K)).hom ≫ (flatPullbackIso f K hK hflat).inv := by
  have hS := Stacks.SheafOfModules.isKFlat_single_unit Y.O
  have hflatS := isFlat_single_unit_X (Y := Y)
  have hSX := Stacks.SheafOfModules.isKFlat_single_unit X.O
  have hKp := kFlat_pullbackComplex' f K hK hflat
  have hSp := kFlat_pullbackComplex' f _ hS hflatS
  have F3 : (TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj K))).map
        (flatPullbackIso f _ hS hflatS).inv ≫
      (TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj K))).map
        (derivedPullbackUnitIsoGeneral f).hom =
      (TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj K))).map
        (DerivedCategory.Q.map (pullbackSingleUnitMap f)) := by
    rw [← Functor.map_comp, derivedPullbackUnitIsoGeneral_hom_eq, Iso.inv_hom_id_assoc]
  have F4 := ((TX.tensor.map (flatPullbackIso f K hK hflat).inv).naturality
    (DerivedCategory.Q.map (pullbackSingleUnitMap f))).symm
  have F5 := TX.unitComplexNatIso.hom.naturality (flatPullbackIso f K hK hflat).inv
  have F6 := TX.unitNatIso_hom_app_Q ((pullbackComplex f).obj K)
  rw [TX.comparisonRight_eq_comparison _ _ hKp] at F6
  have F7 := TX.comparison_naturality (𝟙 ((pullbackComplex f).obj K)) (pullbackSingleUnitMap f)
    hKp hKp hSp hSX
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at F7
  exact unit_side_aux _ _ _ _ _ _ _ _ (flatPullbackIso f K hK hflat) _ _ _ _ F3 F4 F5 F6
    ((Iso.inv_comp_eq _).2 F7)

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
private lemma final_assemble_aux {D : Type*} [Category D]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ B₂ E₀ E₁ : D}
    (t : A₀ ⟶ A₅) (m : A₅ ⟶ A₆) (u : A₆ ⟶ E₀) (r : A₀ ⟶ E₀)
    (l₁ : A₀ ⟶ A₁) (l₂ : A₁ ⟶ A₂) (l₃ : A₂ ⟶ A₃) (bi : A₃ ⟶ A₄) (k₁ : A₄ ⟶ A₇)
    (k₂ : A₇ ⟶ A₅) (φ : E₀ ≅ E₁) (q₁ : B₂ ⟶ E₁) (q₂ : A₃ ⟶ B₂) (q₃ : A₂ ⟶ E₁)
    (l₄ : A₁ ⟶ E₀)
    (F12 : t = l₁ ≫ l₂ ≫ l₃ ≫ bi ≫ k₁ ≫ k₂) (R : bi ≫ k₁ ≫ k₂ ≫ m ≫ u = q₂ ≫ q₁ ≫ φ.inv)
    (F8 : l₃ ≫ q₂ ≫ q₁ = q₃) (F9 : l₄ ≫ φ.hom = l₂ ≫ q₃) (F10 : r = l₁ ≫ l₄) :
    t ≫ m ≫ u = r := by
  rw [F12, F10]
  simp only [Category.assoc]
  rw [R, reassoc_of% F8, ← reassoc_of% F9, Iso.hom_inv_id, Category.comp_id]

/-- The coherence of `derivedPullbackTensorIso_hom_app_unit` at a K-flat complex with flat
terms. -/
private lemma derivedPullbackTensorIso_hom_app_unit_model
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)) :
    (derivedPullbackTensorIso f TX TY).hom.app (DerivedCategory.Q.obj K,
        (DerivedCategory.singleFunctor _ 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
      (TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj K))).map
          (derivedPullbackUnitIsoGeneral f).hom ≫
        TX.unitComplexNatIso.hom.app ((derivedPullback f).obj (DerivedCategory.Q.obj K)) =
      (derivedPullback f).map (TY.unitComplexNatIso.hom.app (DerivedCategory.Q.obj K)) := by
  have hS := Stacks.SheafOfModules.isKFlat_single_unit Y.O
  have hflatS := isFlat_single_unit_X (Y := Y)
  have hT := Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hS
  have hflatT := isFlat_tensorComplex_X_general Y.O K _ hflat hflatS
  have F9 := flatPullbackIso_naturality f
    (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections Y.O K).hom
    hT hK hflatT hflat
  have F10 : (derivedPullback f).map (TY.unitComplexNatIso.hom.app (DerivedCategory.Q.obj K)) =
      (derivedPullback f).map (TY.comparison K _ hK hS).hom ≫
        (derivedPullback f).map (DerivedCategory.Q.map
          (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections Y.O K).hom) := by
    rw [TY.unitNatIso_hom_app_Q, TY.comparisonRight_eq_comparison K _ hK hS, Functor.map_comp]
  exact final_assemble_aux _ _ _ _ _ _ _ _ _ _ (flatPullbackIso f K hK hflat) _ _ _ _
    (derivedPullbackTensorIso_hom_app_unit_model_eq f TX TY K hK hflat)
    (derivedPullbackTensorIso_hom_app_unit_model_right f TX K hK hflat)
    (Q_map_pullbackComplex_map_tensorComplexUnitIsoFreeSections f K) F9 F10

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
private lemma extend_aux {D : Type*} [Category D] {A B E₀ E₁ : D}
    (lE : A ⟶ E₀) (lK : B ⟶ E₁) (rE : A ⟶ E₀) (rK : B ⟶ E₁) (s : A ⟶ B) (g : E₀ ≅ E₁)
    (hl : s ≫ lK = lE ≫ g.hom) (hr : s ≫ rK = rE ≫ g.hom) (h : lK = rK) : lE = rE := by
  rw [← cancel_mono g.hom, ← hl, ← hr, h]

/-- **The isomorphism of Stacks 07A4 is compatible with the right unitors**: for `E ∈ D(O_D)`,
`Lf^*(E ⊗^L O_D) ≅ Lf^*E ⊗^L Lf^*O_D`, followed by `Lf^*O_D ≅ O_C` in the second factor and by the
unit law of `Lf^*E`, is `Lf^*` of the unit law `E ⊗^L O_D ≅ E`. -/
theorem derivedPullbackTensorIso_hom_app_unit
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackTensorIso f TX TY).hom.app (E, (DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
      (TX.tensor.obj ((derivedPullback f).obj E)).map (derivedPullbackUnitIsoGeneral f).hom ≫
        TX.unitComplexNatIso.hom.app ((derivedPullback f).obj E) =
      (derivedPullback f).map (TY.unitComplexNatIso.hom.app E) := by
  have := flatKFlatModelsQGeneral_isLocalization Y
  have := Localization.essSurj (flatKFlatModelsQGeneral Y) (flatKFlatModelsWGeneral Y)
  let P := (flatKFlatModelsQGeneral Y).objPreimage E
  let e : DerivedCategory.Q.obj P.obj.as ≅ E :=
    (DerivedCategory.quotientCompQhIso _).symm.app P.obj.as ≪≫
      (flatKFlatModelsQGeneral Y).objObjPreimageIso E
  have hl := (derivedPullbackTensorIso f TX TY).hom.naturality
    (((e.inv, 𝟙 _) : (E, (DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
      (DerivedCategory.Q.obj P.obj.as, (DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))))
  have h2 := TX.unitComplexNatIso.hom.naturality ((derivedPullback f).map e.inv)
  have h3 := TY.unitComplexNatIso.hom.naturality e.inv
  refine extend_aux _ _ _ _ ((derivedPullback f).map ((TY.tensor.map e.inv).app _))
    ((derivedPullback f).mapIso e.symm) ?_ ?_
    (derivedPullbackTensorIso_hom_app_unit_model f TX TY P.obj.as P.property.1 P.property.2)
  · simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
      CategoryTheory.Functor.map_id, Category.comp_id] at hl
    simp only [Functor.flip_obj_map, Functor.id_map] at h2
    simp only [Functor.mapIso_hom, Iso.symm_hom]
    rw [reassoc_of% hl]
    simp only [Functor.prod_obj, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
    rw [← NatTrans.naturality_assoc, h2]
  · simp only [Functor.flip_obj_map, Functor.id_map] at h3
    simp only [Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp, h3]

end Derived

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
