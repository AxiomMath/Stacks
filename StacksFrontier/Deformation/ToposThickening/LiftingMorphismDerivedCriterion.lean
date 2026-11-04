module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageConormalBaseChange
public import StacksFrontier.Deformation.ToposThickening.InverseImageConormalSolutions
public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedForward
public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedShift

/-!
# Stacks 0GQ7: lifting a morphism of ringed topoi to first order thickenings

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi, `ℱ` an `𝒪_𝒞`-module, `𝒢` an `𝒪_𝒟`-module and `c : g^*ℱ ⟶ 𝒢` an `𝒪_𝒟`-linear map.
Let `0 ⟶ ℱ ⟶ 𝒪_{𝒞'} ⟶ 𝒪_𝒞 ⟶ 0` be an extension of `f⁻¹𝒪_ℬ`-algebras with class
`ξ ∈ Ext¹_{𝒪_𝒞}(NL_{𝒪_𝒞/𝒪_ℬ}, ℱ)` and `0 ⟶ 𝒢 ⟶ 𝒪_{𝒟'} ⟶ 𝒪_𝒟 ⟶ 0` an extension of
`g⁻¹f⁻¹𝒪_ℬ`-algebras with class `ζ ∈ Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢)` (**Stacks 0GQ5**). **Stacks
0GQ7** says that a morphism `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` of ringed topoi over
`(Sh(ℬ), 𝒪_ℬ)` compatible with `g` and `c` exists if and only if `ξ` and `ζ` map to the same
element of `Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`.

## Main results

* `Deformation.ToposThickening.LiftingMorphismDerived.nonempty_compatibleMorphism_iff`:
  **Stacks 0GQ7**.
* `nonempty_compatibleHom_iff`: the same statement for compatible comorphisms
  `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}`.
* `pullbackExtClass_canonical`: the image of a class `Q(φ) ≫ Q(η)⁻¹ ≫ κ[1]` under `Lg^*`.
* `rhoClass_pullbackExtClass_eq`: read over `g⁻¹𝒪_𝒞`, the image of `ξ` is the class of the
  pushout `𝒪'₁` (Stacks 0GQ8).
* `pullbackExtClass_eq_restrictExtClass_of_compatibleHom`: a compatible comorphism identifies
  the two images.

## References

* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.RingedToposModules (inverseImageModules)
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Deformation.ToposThickening.InverseImageExtension
open Deformation.ToposThickening.RingedToposExtensionProblem (ofTrivialBase)
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

universe u v' u' w'

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

namespace Deformation.ToposThickening.LiftingMorphismDerived

variable {X Y : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Exact functors on classes in degree one -/

section ExactFunctor

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})] [Y.J.HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- An exact functor carries the shift isomorphism `M[-(-1)] ≅ (M[0])[1]` of the single functors
to the one of `F M`, read through the comparison of `F` with the single functors. -/
theorem _root_.CategoryTheory.Functor.mapDerivedCategoryFactors_inv_map_shiftIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category D] [Abelian D]
    [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (M : C) :
    F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C (-1)).obj M) ≫
        F.mapDerivedCategory.map
          (((DerivedCategory.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) (-1)).hom.app M) ≫
        ((DerivedCategory.singleFunctors D).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app
          (F.obj M) := by
  have hb : (F.mapDerivedCategorySingleFunctor (-1)).hom.app M =
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ)
          (-1)).obj
        M) ≫ DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ)
              (-1)).hom.app M) := by
    simp only [Int.reduceNeg, Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
      Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj, Functor.whiskerRight_app,
      NatTrans.id_app, Category.comp_id, Category.id_comp]
    exact Category.id_comp _
  rw [F.mapDerivedCategory_map_singleShiftIso_inv M, hb, Category.assoc]
  exact Iso.inv_hom_id_app_assoc F.mapDerivedCategoryFactors _ _

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})] [Y.J.HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- An exact functor on `Q(φ) ≫ Q(η)⁻¹`, read through the comparisons with `Q`. -/
theorem _root_.CategoryTheory.Functor.mapDerivedCategoryFactors_inv_map_Q_map_comp_inv
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category D] [Abelian D]
    [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {K L P : CochainComplex C ℤ} (φ : K ⟶ P) (η : L ⟶ P)
    (_ : IsIso (DerivedCategory.Q.map η)) :
    haveI := F.isIso_Q_map_mapHomologicalComplex_map η
    F.mapDerivedCategoryFactors.inv.app K ≫
        F.mapDerivedCategory.map (DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map η)) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ≫
        inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map η)) ≫
        F.mapDerivedCategoryFactors.inv.app L := by
  have := F.isIso_Q_map_mapHomologicalComplex_map η
  have h₁ := F.mapDerivedCategoryFactors.inv.naturality φ
  have h₂ := F.mapDerivedCategoryFactors.inv.naturality η
  dsimp only [Functor.comp_map] at h₁ h₂
  rw [Functor.map_comp, Functor.map_inv, ← Category.assoc, ← h₁, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, ← h₂, IsIso.inv_hom_id_assoc]

end ExactFunctor

/-! ### The image of a class written through canonical complexes -/

section PullbackClass

variable (g : RingedToposHom Y X)
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}
  (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G)

/-- `pullbackExtClass_canonical` for an arbitrary shift-compatible comparison `τ` in place of
`Lg^* ⟶ g^*`. -/
theorem pullbackExtClass_canonical_of_comparison
    (τ : DerivedCategory.Q ⋙ derivedPullback g ⟶
      g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) [NatTrans.CommShift τ ℤ]
    {F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (c' : g.toRingedToposModulesHom.pullbackModules.obj F' ⟶ G')
    {N P : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} {M : SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : N ⟶ P)
    (η : (CochainComplex.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).obj M ⟶ P) [IsIso
            (DerivedCategory.Q.map η)]
    (κ : M ⟶ F') :
    (derivedPullback g).map (DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map η) ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).map κ) ≫
          ((DerivedCategory.singleFunctors (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso (1 : ℤ) (-1) 0
                  (by decide)).inv.app F') ≫
        ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F') ≫
        (singleObjComparison (derivedPullback g) g.toRingedToposModulesHom.pullbackModules τ 0 F' ≫
          (DerivedCategory.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map c')⟦(1 : ℤ)⟧' =
      (derivedPullback g).map (DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map η)) ≫
        τ.app ((CochainComplex.singleFunctor (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).obj M) ≫
        DerivedCategory.Q.map
          ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((CochainComplex.singleFunctor (SheafOfModules.{u}
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).map κ) ≫
            (HomologicalComplex.singleMapHomologicalComplex
              g.toRingedToposModulesHom.pullbackModules (ComplexShape.up ℤ) (-1)).hom.app F' ≫
            (CochainComplex.singleFunctor (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (-1)).map c') ≫
        ((DerivedCategory.singleFunctors (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).shiftIso (1 : ℤ) (-1) 0
                (by decide)).inv.app G' := by
  have h₁ := map_singleFunctors_shiftIso_inv_app_comp_singleObjComparison (derivedPullback g)
    g.toRingedToposModulesHom.pullbackModules τ 1 (-1) 0 (by decide) F'
  have h₂ := ((DerivedCategory.singleFunctors (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).shiftIso (1 : ℤ) (-1) 0
          (by decide)).inv.naturality c'
  have h₃ := τ.naturality ((CochainComplex.singleFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).map κ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₂ h₃
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, ← h₂, singleObjComparison_eq, Category.assoc]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ((reassoc_of% h₃) _))

/-- **`pullbackExtClass` on a class `Q(φ) ≫ Q(η)⁻¹ ≫ κ[1]`** written through a chain map
`φ : N ⟶ P`, a chain map `η : M[1] ⟶ P` invertible in the derived category and `κ : M ⟶ ℱ`: it is
`Lg^*` of `Q(φ) ≫ Q(η)⁻¹`, the comparison `Lg^*(M[1]) ⟶ (g^*M)[1]`, and `c ∘ g^*κ`. -/
theorem pullbackExtClass_canonical
    {N P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : N ⟶ P)
    (η : (CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).obj M ⟶ P) [IsIso
              (DerivedCategory.Q.map η)]
    (κ : M ⟶ F) :
    pullbackExtClass g c (DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map η) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).map κ) ≫
        ((DerivedCategory.singleFunctors
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
            (1 : ℤ) (-1) 0 (by decide)).inv.app F) =
      (derivedPullback g).map (DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map η)) ≫
        (derivedPullbackComparisonNat g).app ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).obj M) ≫
        DerivedCategory.Q.map
          ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).map κ) ≫
            (HomologicalComplex.singleMapHomologicalComplex
              g.toRingedToposModulesHom.pullbackModules (ComplexShape.up ℤ) (-1)).hom.app F ≫
            (CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (-1)).map c) ≫
        ((DerivedCategory.singleFunctors
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).shiftIso
            (1 : ℤ) (-1) 0 (by decide)).inv.app G := by
  unfold pullbackExtClass derivedPullbackSingleObj
  exact pullbackExtClass_canonical_of_comparison g (derivedPullbackComparisonNat g) c φ η κ

end PullbackClass

/-! ### Stacks 0GQ7 -/

section Main

variable [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  {f : RingedToposHom X B} (g : RingedToposHom Y X)
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}
  (QC : (ofTrivialBase f F).CompatibleFirstOrderThickening)
  (QD : (ofTrivialBase (f.comp g) G).CompatibleFirstOrderThickening)
  (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G)

/-- On a module `M` in degree `-1`, a degreewise natural map `U : I ⟶ Φ ⋙ R` followed by `R` of
`Φ(a)` and `x : Φ M' ⟶ N` is the single complex of `I a ≫ u M' ≫ R x`. -/
private theorem single_comp_degreewise {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Preadditive 𝒜]
    [HasZeroObject 𝒜] [Category ℬ] [Preadditive ℬ] [HasZeroObject ℬ] [Category 𝒞] [Preadditive 𝒞]
    [HasZeroObject 𝒞] (I : 𝒜 ⥤ ℬ) (Φ : 𝒜 ⥤ 𝒞) (R : 𝒞 ⥤ ℬ) [hI : I.Additive] [hΦ : Φ.Additive]
    [hR : R.Additive]
    (u : ∀ X, I.obj X ⟶ R.obj (Φ.obj X))
    (hu : ∀ {X Y : 𝒜} (f : X ⟶ Y), I.map f ≫ u Y = u X ≫ R.map (Φ.map f))
    {M M' : 𝒜} {N : 𝒞} (a : M ⟶ M') (x : Φ.obj M' ⟶ N)
    (U : (I.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) (-1)).obj M) ⟶
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) (-1)).obj M)))
    (hU : ∀ i, U.f i = u _) :
    (HomologicalComplex.singleMapHomologicalComplex I (ComplexShape.up ℤ) (-1)).inv.app M ≫ U ≫
        (R.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) (-1)).map a) ≫
            (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) (-1)).hom.app M' ≫
            (HomologicalComplex.single 𝒞 (ComplexShape.up ℤ) (-1)).map x) ≫
        (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) (-1)).hom.app N =
      (HomologicalComplex.single ℬ (ComplexShape.up ℤ) (-1)).map (I.map a ≫ u M' ≫ R.map x) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hU,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  rw [HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self,
    HomologicalComplex.single_map_f_self]
  have h₁ := hu (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) M).inv
  have h₂ := hu a
  rw [Category.assoc, reassoc_of% h₁]
  simp only [Category.assoc, reassoc_of% h₂]
  congr 2
  rw [← R.map_comp_assoc, ← R.map_comp_assoc, ← R.map_comp_assoc]
  congr 2
  simp

/-- `single_comp_degreewise` preceded by an identification `e : I M ≅ E`, in the shape of the
computation of `rhoClass` on the image of `ξ`. -/
private theorem single_comp_degreewise_iso {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Preadditive 𝒜]
    [HasZeroObject 𝒜] [Category ℬ] [Preadditive ℬ] [HasZeroObject ℬ] [Category 𝒞] [Preadditive 𝒞]
    [HasZeroObject 𝒞] (I : 𝒜 ⥤ ℬ) (Φ : 𝒜 ⥤ 𝒞) (R : 𝒞 ⥤ ℬ) [hI : I.Additive] [hΦ : Φ.Additive]
    [hR : R.Additive] (u : ∀ X, I.obj X ⟶ R.obj (Φ.obj X))
    (hu : ∀ {X Y : 𝒜} (f : X ⟶ Y), I.map f ≫ u Y = u X ≫ R.map (Φ.map f))
    {M M' : 𝒜} {N : 𝒞} {E : ℬ} (e : I.obj M ≅ E) (a : M ⟶ M') (x : Φ.obj M' ⟶ N)
    (U : (I.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor 𝒜 (-1)).obj M) ⟶
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor 𝒜 (-1)).obj M)))
    (hU : ∀ i, U.f i = u _) {pc : E ⟶ R.obj N} (hpc : e.inv ≫ I.map a ≫ u M' ≫ R.map x = pc) :
    ((CochainComplex.singleFunctor ℬ (-1)).mapIso e).inv ≫
        ((HomologicalComplex.singleMapHomologicalComplex I (ComplexShape.up ℤ) (-1)).app M).inv ≫
        (U ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((CochainComplex.singleFunctor 𝒜 (-1)).map a) ≫
            (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) (-1)).hom.app M' ≫
            (CochainComplex.singleFunctor 𝒞 (-1)).map x)) ≫
        (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) (-1)).hom.app N =
      (CochainComplex.singleFunctor ℬ (-1)).map pc := by
  have h := single_comp_degreewise I Φ R u hu a x U hU
  subst hpc
  refine Eq.trans ?_ ((congrArg ((CochainComplex.singleFunctor ℬ (-1)).map e.inv ≫ ·) h).trans
    ((CochainComplex.singleFunctor ℬ (-1)).map_comp _ _).symm)
  simp only [Functor.mapIso_inv, Iso.app_inv, Category.assoc, Functor.map_comp]
  rfl

/-- For a natural transformation `u : I' ⟶ L ⋙ R` and morphisms satisfying the relations `H₂`,
`H₃`, `H₄` and `H₅`, the composite
`b₀ ≫ i₀ ≫ m₀ ≫ u.app N ≫ R.map (L.map (φ ≫ ε) ≫ τS ≫ ψ ≫ sh) ≫ cs ≫ rs` is
`T₁' ≫ T₂' ≫ T₃' ≫ shW`. -/
private theorem rho_assemble {𝒟 𝒟' 𝒲 : Type*} [Category 𝒟] [Category 𝒟'] [Category 𝒲]
    (L : 𝒟 ⥤ 𝒟') (R : 𝒟' ⥤ 𝒲) (I' : 𝒟 ⥤ 𝒲) (u : I' ⟶ L ⋙ R)
    {N P S : 𝒟} {LS' LG LG' : 𝒟'} {T₀ T₁ T₂ W₁ W₂ Z₁ Z₂ Z₃ Z₄ V₁ V₂ : 𝒲}
    (b₀ : T₀ ⟶ T₁) (i₀ : T₁ ⟶ T₂) (m₀ : T₂ ⟶ I'.obj N) (φ : N ⟶ P) (ε : P ⟶ S)
    (τS : L.obj S ⟶ LS') (ψ : LS' ⟶ LG) (sh : LG ⟶ LG') (cs : R.obj LG' ⟶ W₁) (rs : W₁ ⟶ W₂)
    (X : T₂ ⟶ Z₁) (Y : Z₁ ⟶ Z₂) (mS : Z₂ ⟶ I'.obj S) (Z : Z₂ ⟶ Z₃) (rD : Z₃ ⟶ R.obj LG)
    (Wm : Z₃ ⟶ Z₄) (shW : Z₄ ⟶ W₂) (T₁' : T₀ ⟶ V₁) (T₂' : V₁ ⟶ V₂) (T₃' : V₂ ⟶ Z₄)
    (H₂ : m₀ ≫ I'.map (φ ≫ ε) = X ≫ Y ≫ mS)
    (H₃ : mS ≫ u.app S ≫ R.map (τS ≫ ψ) = Z ≫ rD)
    (H₄ : rD ≫ R.map sh ≫ cs ≫ rs = Wm ≫ shW)
    (H₅ : b₀ ≫ i₀ ≫ X ≫ Y ≫ Z ≫ Wm = T₁' ≫ T₂' ≫ T₃') :
    b₀ ≫ i₀ ≫ m₀ ≫ u.app N ≫ R.map (L.map (φ ≫ ε) ≫ τS ≫ ψ ≫ sh) ≫ cs ≫ rs =
      T₁' ≫ T₂' ≫ T₃' ≫ shW := by
  have h₁ := u.naturality (φ ≫ ε)
  dsimp only [Functor.comp_map] at h₁
  rw [← Category.assoc τS ψ sh, R.map_comp (L.map (φ ≫ ε)), R.map_comp (τS ≫ ψ)]
  simp only [Category.assoc]
  rw [← reassoc_of% h₁, reassoc_of% H₂, reassoc_of% H₃, H₄]
  exact (reassoc_of% H₅) shW

/-- The inverse of `Q(f)` for a chain map `f` which, up to isomorphisms, is `η'`. -/
private theorem inv_map_eq_of_comp {𝒦 𝒟 : Type*} [Category 𝒦] [Category 𝒟] (Q : 𝒦 ⥤ 𝒟)
    {S P R S₁ S₂ : 𝒦} (f : S ⟶ P) (h : P ≅ R) (a : S ≅ S₁) (b : S₁ ≅ S₂) (η' : S₂ ⟶ R)
    [IsIso (Q.map f)] [IsIso (Q.map η')] (hf : f ≫ h.hom = a.hom ≫ b.hom ≫ η') :
    inv (Q.map f) = Q.map h.hom ≫ inv (Q.map η') ≫ Q.map b.inv ≫ Q.map a.inv := by
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [← Q.map_comp_assoc, hf]
  simp

/-- The chain level part of the computation of `rhoClass` on the image of `ξ`. -/
private theorem rho_chain {𝒦 𝒟 : Type*} [Category 𝒦] [Category 𝒟] (Q : 𝒦 ⥤ 𝒟)
    {A B₀ IN IP R' IS S₁ S₂ T T' : 𝒦} (bC : A ⟶ B₀) (i : IN ≅ B₀) (Ib : IN ⟶ IP)
    (invBC : B₀ ⟶ R') (j : IP ≅ R') (hZ : Ib ≫ j.hom = i.hom ≫ invBC) (Iη : IS ⟶ IP)
    (_ : IsIso (Q.map Iη)) (a : IS ≅ S₁) (b : S₁ ≅ S₂) (ηW : S₂ ⟶ R') (_ : IsIso (Q.map ηW))
    (hZ' : Iη ≫ j.hom = a.hom ≫ b.hom ≫ ηW) (pΨ : IS ⟶ T) (sm : T ⟶ T') (pc : S₂ ⟶ T')
    (hpc : b.inv ≫ a.inv ≫ pΨ ≫ sm = pc) :
    Q.map bC ≫ Q.map i.inv ≫ Q.map Ib ≫ inv (Q.map Iη) ≫ Q.map pΨ ≫ Q.map sm =
      Q.map (bC ≫ invBC) ≫ inv (Q.map ηW) ≫ Q.map pc := by
  have hi : i.inv ≫ Ib = invBC ≫ j.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hZ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [inv_map_eq_of_comp Q Iη j a b ηW hZ', ← hpc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Q.map_comp_assoc i.inv Ib, hi, Q.map_comp_assoc, ← Q.map_comp_assoc j.inv j.hom,
    Iso.inv_hom_id, Q.map_id, Category.id_comp]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The unit of extension and restriction of scalars along `g^♯`, on inverse images, is natural. -/
theorem inverseImage_comp_unit {Z Z' : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (φ : Z ⟶ Z') :
    (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ ≫
        (extendRestrictAdjunction g).unit.app
          ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj Z') =
      (extendRestrictAdjunction g).unit.app
          ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj Z) ≫
        (restrictAlong g).map (g.toRingedToposModulesHom.pullbackModules.map φ) :=
  (extendRestrictAdjunction g).unit.naturality _

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})] [HasWeakSheafify Y.J CommRingCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
/-- The degreewise unit in degree `i`. -/
theorem pullbackUnitComplex_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (i : ℤ) :
    (pullbackUnitComplex g K).f i = (extendRestrictAdjunction g).unit.app
      ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
          (K.X i)) :=
  rfl

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The adjoint `g⁻¹ℱ ⟶ 𝒢` of `c` is the unit followed by the restriction of scalars of `c`. -/
theorem prescribedAdjoint_eq_unit_comp :
    prescribedAdjoint g c = (extendRestrictAdjunction g).unit.app
        ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F) ≫
      (restrictAlong g).map c :=
  (extendRestrictAdjunction g).homEquiv_unit _ _ _

/-- **The image of `ξ` read over `g⁻¹𝒪_𝒞` is the class of `𝒪'₁`** (Stacks 0GQ8), from the
compatibilities of the identification of Stacks 08TZ with base change (`hZ`), with `η` (`hZ'`)
and with the pushout datum (`hZ''`). -/
theorem rhoClass_pullbackExtClass_eq_aux
    (e : (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
      (Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} X.J QC.extension X.O QC.reduction) ≅
      Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} Y.J ((invImage g).obj QC.extension)
        ((invImage g).obj X.O) ((invImage g).map QC.reduction))
    (hZ : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          QC.naiveCotangentBaseChange ≫ (inverseImageIsoReduction g QC).hom =
        (inverseImageIsoBase (f := f) g).hom ≫ invBaseChange g QC)
    (hZ' : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.conormalToNaiveCotangentComplex X.J QC.extension X.O
            QC.reduction) ≫ (inverseImageIsoReduction g QC).hom =
        (HomologicalComplex.singleMapHomologicalComplex
          (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) (-1)).hom.app _ ≫
          (CochainComplex.singleFunctor _ (-1)).map e.hom ≫
          Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J ((invImage g).obj QC.extension)
            ((invImage g).obj X.O) ((invImage g).map QC.reduction))
    (hZ'' : e.inv ≫ (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map QC.kernelConormalToModule ≫
        prescribedAdjoint g c = pushoutConormalToModule g QC c) :
    rhoClass g (pullbackExtClass g c
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv f F
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
            QC))) =
      RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp (toInverseImage g))
        (restrictedIdeal g G)
        (Quotient.mk (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
          (pushoutSolution g QC QD c)) := by
  rw [pushoutSolution_class g QC QD c]
  refine (congrArg (fun t ↦ rhoClass g (pullbackExtClass g c t))
    QC.squareZeroExtensionClassesEquiv_mk_eq_canonical).trans ?_
  refine (congrArg (rhoClass g) (pullbackExtClass_canonical g c _ _ _)).trans ?_
  unfold rhoClass
  refine rho_assemble (derivedPullback g) (restrictDerived g) (invImageDerived g) (derivedUnit g)
    (Z₁ := ?Z₁) (Z₂ := ?Z₂) (Z₃ := ?Z₃) (Z₄ := ?Z₄) _ _ _ _ _ _ _ _ _ _ ?X ?Y ?mS ?Z ?rD ?Wm
    _ _ _ _ ?H₂ ?H₃ ?H₄ ?H₅
  case H₂ =>
    exact (inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors_inv_map_Q_map_comp_inv
        _ _ _
  case H₃ => exact derivedUnit_comp_restrictDerived_map g _ _
  case H₄ => exact (restrictAlong g).mapDerivedCategoryFactors_inv_map_shiftIso G
  case H₅ =>
    refine rho_chain DerivedCategory.Q _ (inverseImageIsoBase (f := f) g) _ _
      (inverseImageIsoReduction g QC) ?hZ _ ?iso₁
      ((HomologicalComplex.singleMapHomologicalComplex
        (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) (-1)).app _)
      ((CochainComplex.singleFunctor _ (-1)).mapIso e) _ ?iso₂ ?hZ' _ _ _ ?hpc
    case hZ => exact hZ
    case hZ' => exact hZ'
    case hpc =>
      refine single_comp_degreewise_iso (hR := (extendRestrictAdjunction g).right_adjoint_additive)
        (hI := CategoryTheory.Sheaf.inverseImageTargetModules_additive.{u, u, u, u, u, u} Y.J X.J
          g.toToposHom (B := X.O)) (hΦ := pullbackModules_additive g)
        (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        g.toRingedToposModulesHom.pullbackModules (restrictAlong g)
        (fun Z ↦ (extendRestrictAdjunction g).unit.app
          ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj Z))
        (inverseImage_comp_unit g) e _ _ _ (pullbackUnitComplex_f g _) ?_
      refine Eq.trans ?_ hZ''
      exact congrArg (_ ≫ _ ≫ ·) (prescribedAdjoint_eq_unit_comp g c).symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})] [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
/-- **The identification of Stacks 08TZ is compatible with the base change** along
`f⁻¹𝒪_ℬ ⟶ 𝒪_{𝒞'}`. -/
theorem inverseImage_naiveCotangentBaseChange_comp :
    ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          QC.naiveCotangentBaseChange ≫ (inverseImageIsoReduction g QC).hom =
      (inverseImageIsoBase (f := f) g).hom ≫ invBaseChange g QC :=
  Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso_naturality.{u, u, u, u, u, u} Y.J X.J
    g.toToposHom f.fSharpInverseImage QC.reduction QC.baseMap
    (RingedToposExtensionProblem.baseMap_comp_reduction_ofTrivialBase QC).symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J CommRingCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **The identification `e` of conormal sheaves carries `κ` to the pushout datum**, as soon as
`e⁻¹` followed by `g⁻¹κ` sends the class of a local section `x` of the kernel of
`g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞` to the section of `g⁻¹ℱ` lying over `x`. -/
theorem inv_comp_map_kernelConormalToModule_comp_prescribedAdjoint
    (e : (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
      (Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} X.J QC.extension X.O QC.reduction) ≅
      Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} Y.J ((invImage g).obj QC.extension)
        ((invImage g).obj X.O) ((invImage g).map QC.reduction))
    (he : ∀ (U : Y.Cᵒᵖ)
      (x : Stacks.Sites.Conormal.kernelIdeal ((invImage g).map QC.reduction).hom U),
      (show ((invImage g).obj QC.extension).obj.obj U from
        (invKernelIncl QC g).val.app U
          (((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
            QC.kernelConormalToModule).val.app U (e.inv.val.app U
              (Stacks.Sites.Conormal.toAssociatedModule.{u, u, u, u} Y.J
                ((invImage g).obj QC.extension) ((invImage g).obj X.O)
                ((invImage g).map QC.reduction)
                (Stacks.Sites.Conormal.conormalPresheaf ((invImage g).map QC.reduction).hom) U
                ((Stacks.Sites.Conormal.kernelIdeal
                    ((invImage g).map QC.reduction).hom U).toCotangent
                  x))))) = x.1) :
    e.inv ≫ (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map QC.kernelConormalToModule ≫
        prescribedAdjoint g c = pushoutConormalToModule g QC c := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun U x ↦ ?_)
  refine Eq.trans ?_ (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule _ _ _ U x).symm
  show (prescribedAdjoint g c).val.app U _ = (prescribedAdjoint g c).val.app U _
  exact congrArg _ (invIdealPreimage_eq QC g U x _ (he U x)).symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
/-- **The identification of Stacks 08TZ is compatible with `η`**, through the identification
`g⁻¹(ℐ/ℐ²) ≅ ℐ'/ℐ'²` of the conormal sheaves of `𝒪_{𝒞'} ⟶ 𝒪_𝒞` and of its inverse image. -/
theorem inverseImage_conormalToNaiveCotangentComplex_comp :
    ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.conormalToNaiveCotangentComplex X.J QC.extension X.O
            QC.reduction) ≫ (inverseImageIsoReduction g QC).hom =
      (HomologicalComplex.singleMapHomologicalComplex
          (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) (-1)).hom.app _ ≫
        (CochainComplex.singleFunctor _ (-1)).map
          (Stacks.SheafOfModules.inverseImageConormalSheafIso Y.J X.J g.toToposHom
            QC.reduction).hom ≫
        Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J ((invImage g).obj QC.extension)
          ((invImage g).obj X.O) ((invImage g).map QC.reduction) :=
  Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso_conormalToNaiveCotangentComplex
    Y.J X.J g.toToposHom QC.reduction

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The identification `g⁻¹(ℐ/ℐ²) ≅ ℐ'/ℐ'²` carries `κ` to the pushout datum.** -/
theorem inverseImageConormalSheafIso_inv_comp_prescribedAdjoint :
    (Stacks.SheafOfModules.inverseImageConormalSheafIso Y.J X.J g.toToposHom QC.reduction).inv ≫
        (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          QC.kernelConormalToModule ≫ prescribedAdjoint g c =
      pushoutConormalToModule g QC c :=
  inv_comp_map_kernelConormalToModule_comp_prescribedAdjoint g QC c _
    (fun U x ↦ invKernelIncl_inverseImageConormalSheafIso_inv QC g U x)

/-- **The image of `ξ` read over `g⁻¹𝒪_𝒞` is the class of `𝒪'₁`** (Stacks 0GQ8). -/
theorem rhoClass_pullbackExtClass_eq :
    rhoClass g (pullbackExtClass g c
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv f F
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
            QC))) =
      RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp (toInverseImage g))
        (restrictedIdeal g G)
        (Quotient.mk (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
          (pushoutSolution g QC QD c)) :=
  rhoClass_pullbackExtClass_eq_aux g QC QD c _ (inverseImage_naiveCotangentBaseChange_comp g QC)
    (inverseImage_conormalToNaiveCotangentComplex_comp g QC)
    (inverseImageConormalSheafIso_inv_comp_prescribedAdjoint g QC c)

omit [Y.J.HasSheafCompose (forget CommRingCat.{u})] [HasWeakSheafify Y.J CommRingCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The comparison `Lg^* ⟶ g^*` on the target of a chain map `η` invertible in the derived
category, through the comparison on its source. -/
theorem derivedPullbackComparisonComplex_eq_of_isIso
    {L P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (η : L ⟶ P) (_ : IsIso (DerivedCategory.Q.map η)) :
    derivedPullbackComparisonComplex g P =
      (derivedPullback g).map (inv (DerivedCategory.Q.map η)) ≫
        derivedPullbackComparisonComplex g L ≫
        DerivedCategory.Q.map
          ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
            η) := by
  rw [← derivedPullbackComparisonComplex_naturality, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})] [Y.J.HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
/-- For morphisms satisfying the relations `hN`, `hP`, `hc` and `key`, the composite
`(dN ≫ can) ≫ bcD ≫ r₁ ≫ r₂ ≫ sh` is `L.map (φ ≫ ε) ≫ dS ≫ ψ ≫ sh`. -/
private theorem forward_assemble {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (L : 𝒞 ⥤ 𝒟)
    {N P S : 𝒞} {LN LP LS : 𝒟} {T₁ T₂ T₂' T₃ T₄ : 𝒟}
    (φ : N ⟶ P) (ε : P ⟶ S) (dN : L.obj N ⟶ LN) (dP : L.obj P ⟶ LP) (dS : L.obj S ⟶ LS)
    (gφ : LN ⟶ LP) (can : LN ⟶ T₁) (bcD : T₁ ⟶ T₂) (can' : LP ⟶ T₂) (gη : LS ⟶ LP)
    (r₁ : T₂ ⟶ T₂') (r₂ : T₂' ⟶ T₃) (ψ : LS ⟶ T₃) (sh : T₃ ⟶ T₄)
    (hN : L.map φ ≫ dP = dN ≫ gφ) (hP : dP = L.map ε ≫ dS ≫ gη)
    (hc : can ≫ bcD = gφ ≫ can') (key : gη ≫ can' ≫ r₁ ≫ r₂ = ψ) :
    (dN ≫ can) ≫ bcD ≫ r₁ ≫ r₂ ≫ sh = L.map (φ ≫ ε) ≫ dS ≫ ψ ≫ sh := by
  rw [Category.assoc, reassoc_of% hc, ← reassoc_of% hN, hP, ← key]
  simp only [Category.assoc, Functor.map_comp]

/-- The direct implication of Stacks 0GQ7, from the three compatibilities of the identification
of Stacks 08TZ: with base change (`hZ`), with `η` (`hZ'`) and with the pushout datum (`hZ''`). -/
theorem pullbackExtClass_eq_restrictExtClass_of_compatibleHom_aux
    (h : (Data.ofSolutions g QC QD c).CompatibleHom)
    (e : (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
      (Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} X.J QC.extension X.O QC.reduction) ≅
      Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} Y.J ((invImage g).obj QC.extension)
        ((invImage g).obj X.O) ((invImage g).map QC.reduction))
    (hZ : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          QC.naiveCotangentBaseChange ≫ (inverseImageIsoReduction g QC).hom =
        (inverseImageIsoBase (f := f) g).hom ≫ invBaseChange g QC)
    (hZ' : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.conormalToNaiveCotangentComplex X.J QC.extension X.O
            QC.reduction) ≫ (inverseImageIsoReduction g QC).hom =
        (HomologicalComplex.singleMapHomologicalComplex
          (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) (-1)).hom.app _ ≫
          (CochainComplex.singleFunctor _ (-1)).map e.hom ≫
          Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J ((invImage g).obj QC.extension)
            ((invImage g).obj X.O) ((invImage g).map QC.reduction))
    (hZ'' : e.inv ≫ (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map QC.kernelConormalToModule ≫
        prescribedAdjoint g c = pushoutConormalToModule g QC c) :
    pullbackExtClass g c
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv f F
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
            QC)) =
      restrictExtClass f g
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp g) G
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
            QD)) := by
  have h₃ := pullback_baseChange_comp_liftNaiveCotangentMap g QC QD c h hZ
  have h₄ := pullback_eta_comp_liftNaiveCotangentMap g QC QD c h e hZ'
  have h₅ := liftConormalComplexMap_eq g QC QD c h e
  have h₆ := liftConormalModuleMap_comp g QC QD c h e hZ''
  refine (congrArg (pullbackExtClass g c) QC.squareZeroExtensionClassesEquiv_mk_eq_canonical).trans
    (((pullbackExtClass_canonical g c _ _ _).trans ?_).trans
      (congrArg (restrictExtClass f g) QD.squareZeroExtensionClassesEquiv_mk_eq_canonical).symm)
  unfold restrictExtClass naiveCotangentDerivedComparison
  have hnat := (HomologicalComplex.singleMapHomologicalComplex
    g.toRingedToposModulesHom.pullbackModules (ComplexShape.up ℤ) (-1)).hom.naturality
      QC.kernelConormalToModule
  have h₃' := congrArg DerivedCategory.Q.map h₃
  rw [Functor.map_comp, Functor.map_comp] at h₃'
  refine (forward_assemble (derivedPullback g) (LP := ?LP) _ _ _ ?dP _ ?gφ _ _ ?can' ?gη _ _ _ _
    ?hN ?hP ?hc ?key).symm
  case hP =>
    exact derivedPullbackComparisonComplex_eq_of_isIso g _ _
  case hN =>
    exact derivedPullbackComparisonComplex_naturality g
      (K := Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
        ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)
      QC.naiveCotangentBaseChange
  case hc => exact h₃'.symm
  case key =>
    rw [← Functor.map_comp_assoc, h₄, Functor.map_comp, Category.assoc]
    refine (congrArg (_ ≫ ·) (IsIso.hom_inv_id_assoc _ _)).trans ?_
    refine (DerivedCategory.Q.map_comp _ _).symm.trans ?_
    refine (congrArg (fun t ↦ DerivedCategory.Q.map (t ≫ _)) h₅).trans ?_
    congr 1
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((CochainComplex.singleFunctor _ (-1)).map_comp _ _).symm).trans ?_
    refine (congrArg (fun t ↦ _ ≫ (CochainComplex.singleFunctor _ (-1)).map t) h₆).trans ?_
    refine (congrArg (_ ≫ ·) ((CochainComplex.singleFunctor _ (-1)).map_comp _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ _) hnat.symm).trans (Category.assoc _ _ _)

/-- **A compatible comorphism identifies the two images** in
`Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`. -/
theorem pullbackExtClass_eq_restrictExtClass_of_compatibleHom
    (h : (Data.ofSolutions g QC QD c).CompatibleHom) :
    pullbackExtClass g c
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv f F
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
            QC)) =
      restrictExtClass f g
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp g) G
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
            QD)) :=
  pullbackExtClass_eq_restrictExtClass_of_compatibleHom_aux g QC QD c h _
    (inverseImage_naiveCotangentBaseChange_comp g QC)
    (inverseImage_conormalToNaiveCotangentComplex_comp g QC)
    (inverseImageConormalSheafIso_inv_comp_prescribedAdjoint g QC c)

/-- **Stacks 0GQ7, on comorphisms**: a comorphism `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` of
`g⁻¹f⁻¹𝒪_ℬ`-algebras over `g^♯` restricting to `c` exists if and only if the classes `ξ` of
`𝒪_{𝒞'}` and `ζ` of `𝒪_{𝒟'}` have the same image in `Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`. -/
theorem nonempty_compatibleHom_iff :
    Nonempty (Data.ofSolutions g QC QD c).CompatibleHom ↔
      pullbackExtClass g c
          (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv f F
            (Quotient.mk
              (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
              QC)) =
        restrictExtClass f g
          (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp g) G
            (Quotient.mk
              (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
              QD)) := by
  refine ⟨fun ⟨h⟩ ↦ pullbackExtClass_eq_restrictExtClass_of_compatibleHom g QC QD c h,
    fun heq ↦ ?_⟩
  refine (nonempty_compatibleHom_iff_isomorphic_solutions g QC QD c).2 ?_
  have h₁ := congrArg (rhoClass g) heq
  rw [rhoClass_pullbackExtClass_eq g QC QD c, rhoClass_restrictExtClass_eq g QC QD c] at h₁
  exact Quotient.exact
    ((RingedToposExtensionProblem.squareZeroExtensionClassesEquiv _ _).injective h₁)

/-- Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi, `ℱ` an `𝒪_𝒞`-module, `𝒢` an `𝒪_𝒟`-module and `c : g^*ℱ ⟶ 𝒢` an `𝒪_𝒟`-linear map. Let
`0 ⟶ ℱ ⟶ 𝒪_{𝒞'} ⟶ 𝒪_𝒞 ⟶ 0` be an extension of `f⁻¹𝒪_ℬ`-algebras (a solution `QC` of the problem of
Stacks 0GQ5 for `f` and `ℱ`) corresponding to `ξ ∈ Ext¹_{𝒪_𝒞}(NL_{𝒪_𝒞/𝒪_ℬ}, ℱ)`, and
`0 ⟶ 𝒢 ⟶ 𝒪_{𝒟'} ⟶ 𝒪_𝒟 ⟶ 0` an extension of `g⁻¹f⁻¹𝒪_ℬ`-algebras (a solution `QD` of the problem for
`f ∘ g` and `𝒢`) corresponding to `ζ ∈ Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢)`, the classes being those of
Stacks 0GQ5. Then there is a morphism `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` of ringed topoi over
`(Sh(ℬ), 𝒪_ℬ)` compatible with `g` and `c` if and only if `ξ` and `ζ` map to the same element of
`Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`: `ξ` through `Lg^*` and `Lg^*ℱ ⟶ g^*ℱ ⟶ 𝒢` (`pullbackExtClass`),
`ζ` through the canonical map `Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}` (`restrictExtClass`). -/
@[stacks 0GQ7]
theorem nonempty_compatibleMorphism_iff :
    Nonempty (CompatibleMorphism g QC QD c) ↔
      pullbackExtClass g c
          (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv f F
            (Quotient.mk
              (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
              QC)) =
        restrictExtClass f g
          (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp g) G
            (Quotient.mk
              (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
              QD)) :=
  (Iff.intro (fun ⟨m⟩ ↦ ⟨m.toCompatibleHom⟩)
    (fun ⟨h⟩ ↦ ⟨CompatibleMorphism.ofCompatibleHom g QC QD c h⟩)).trans
    (nonempty_compatibleHom_iff g QC QD c)

end Main

end Deformation.ToposThickening.LiftingMorphismDerived

end
