module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.EssentiallySmallDerivedDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.EssentiallySmallTensorPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived dual on an essentially small ringed site represents `Hom(- ⊗^𝐋 K, 𝒪)`

Let `(C, 𝒪)` be a ringed site whose objects form a type in an arbitrary universe while its
morphisms and the sections of `𝒪` lie in one universe `u`, and suppose `C` is essentially small
at `u`.  The derived internal Hom of this library is constructed on a ringed site all three of
whose universes agree, so on `(C, 𝒪)` it is computed on a small model `C₀` of the site:
`R𝓗om(K, M)` is the object corresponding, under the equivalence `Φ : D(𝒪) ≌ D(𝒪|_{C₀})` which
restriction of sheaves of modules induces, to `R𝓗om(Φ K, Φ M)` on `C₀`.

This file proves that the functor so obtained is right adjoint to `- ⊗^𝐋 K` on `D(𝒪)` itself:

`Hom_{D(𝒪)}(M ⊗^𝐋 K, N) = Hom_{D(𝒪)}(M, Φ⁻¹ R𝓗om(Φ K, Φ N))`,

which is Stacks 08J8 on `(C, 𝒪)`.  The input is that `Φ` commutes with the derived tensor
product, `Φ(M ⊗^𝐋 K) ≅ Φ M ⊗^𝐋 Φ K` naturally in `M`.  In particular the derived dual
`AlgebraicGeometry.RingedSite.essentiallySmallDerivedDual` is the value at `𝒪` of a right
adjoint of `- ⊗^𝐋 K`, which characterises it up to unique isomorphism: any other construction
of `R𝓗om(K, 𝒪)` as such a value is canonically isomorphic to it.

## Main definitions

* `AlgebraicGeometry.RingedSite.smallModelDerivedTensorFlipIso`: `Φ(M ⊗^𝐋 K) ≅ Φ M ⊗^𝐋 Φ K`,
  naturally in `M`.
* `AlgebraicGeometry.RingedSite.essentiallySmallDerivedSheafHom`: the functor
  `N ↦ Φ⁻¹ R𝓗om(Φ K, Φ N)`.
* `AlgebraicGeometry.RingedSite.essentiallySmallDerivedTensorSheafHomAdjunction`:
  `- ⊗^𝐋 K ⊣ Φ⁻¹ R𝓗om(Φ K, Φ -)`, Stacks 08J8 on `(C, 𝒪)`.
* `AlgebraicGeometry.RingedSite.essentiallySmallDerivedDualIso`: the derived dual is the value of
  that right adjoint at `𝒪`.

## Implementation notes

The comparison of the tensor products is first built on K-flat complexes in the first variable,
where both sides are total tensor complexes (Stacks 06YU) and restriction to the small model
commutes with total tensor complexes degreewise (Stacks 01CU,
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexModTensorComplexIso`), and is then
descended along the localization of the K-flat complexes at the quasi-isomorphisms.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u

namespace Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.functor.IsCocontinuous J' J]
  (O : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Tensor.sheafTensor.{u₁, v₁, w} O).Additive]
  [∀ M, ((Tensor.sheafTensor.{u₁, v₁, w} O).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u₁, v₁, w} O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Tensor.sheafTensor.{u₁, v₁, w} O) (ComplexShape.up ℤ)]
  [(Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O)).Additive]
  [∀ M, ((Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O)).obj M).Additive]
  [∀ (K L : CochainComplex
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u₂, v₂, w} (reindexCommRingGeneral J' e O))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O)) (ComplexShape.up ℤ)]

/-- `Φ(Tot(K ⊗ L)) ≅ Tot(Φ K ⊗ Φ L)` is natural in the first complex. -/
theorem reindexModTensorComplexIso_hom_naturality_left {K K' : CochainComplex
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u₁, v₁, w} O)) ℤ} (f : K ⟶ K')
    (L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u₁, v₁, w} O)) ℤ) :
    ((reindexMod J' e O).functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorMap f (𝟙 L) (Tensor.sheafTensor.{u₁, v₁, w} O)
            (ComplexShape.up ℤ)) ≫
        (reindexModTensorComplexIso J' e O K' L).hom =
      (reindexModTensorComplexIso J' e O K L).hom ≫
        HomologicalComplex.mapBifunctorMap
          (((reindexMod J' e O).functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          (𝟙 (((reindexMod J' e O).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
          (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O)) (ComplexShape.up ℤ) := by
  let := fun K L => CochainComplex.KFlatBifunctor.hasTotal_mapBicomplex_of_equivalence
    (Tensor.sheafTensor.{u₁, v₁, w} O)
    (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u₁, v₁, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g) K L
  exact CochainComplex.KFlatBifunctor.transportComplexIso_naturality_left
    (Tensor.sheafTensor.{u₁, v₁, w} O)
    (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O))
    (reindexMod J' e O).functor (reindexMod J' e O).functor (reindexMod J' e O).functor
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u₁, v₁, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g) f L

end Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

section KFlatComparison

variable (Y : RingedSite.{c, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- On a K-flat first factor `A` and a fixed complex `L`, the derived tensor product
`A ⊗^𝐋 L` is the total tensor complex `Tot(A ⊗ L)`, naturally in `A`. -/
def kFlatComplexQTensorRightIso
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    Stacks.SheafOfModules.kFlatComplexQ Y ⋙
        (Stacks.SheafOfModules.derivedTensorBifunctor Y).flip.obj (DerivedCategory.Q.obj L) ≅
      (Stacks.SheafOfModules.kFlatComplexes Y).ι ⋙
        (Stacks.SheafOfModules.Tensor.tensorComplex Y.O).flip.obj L ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun A => ((Stacks.SheafOfModules.kFlatComparisonNatIso Y).app A).app L)
    (fun f => NatTrans.congr_app
      ((Stacks.SheafOfModules.kFlatComparisonNatIso Y).hom.naturality f) L)

end KFlatComparison

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

attribute [local instance] continuous_equivSmallModel_symm_functor
  cocontinuous_equivSmallModel_symm_functor continuous_equivSmallModel_symm_inverse
  smallModelSheafTensorAdditive smallModelSheafTensorObjAdditive smallModelHasMapBifunctor
  smallModelRingedSiteSheafTensorAdditive smallModelRingedSiteSheafTensorObjAdditive
  smallModelRingedSiteHasMapBifunctor

/-- The restriction of the derived tensor product with a fixed complex `L`, on K-flat first
factors: `Φ(A ⊗^𝐋 L) ≅ Φ A ⊗^𝐋 Φ L` for `A` K-flat, naturally in `A`. -/
def smallModelKFlatTensorRightIso
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Stacks.SheafOfModules.kFlatComplexQ X ⋙
        (Stacks.SheafOfModules.derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj L) ⋙
          (smallModelDerivedEquivalence X).functor ≅
      Stacks.SheafOfModules.kFlatComplexQ X ⋙ (smallModelDerivedEquivalence X).functor ⋙
        (Stacks.SheafOfModules.derivedTensorBifunctor
          (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).flip.obj
          ((smallModelDerivedEquivalence X).functor.obj (DerivedCategory.Q.obj L)) :=
  let R := Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod (smallTopology X)
    (equivSmallModel.{u} X.C).symm X.O
  let Φc := R.functor.mapHomologicalComplex (ComplexShape.up ℤ)
  let fac : Φc ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ (smallModelDerivedEquivalence X).functor :=
    R.functor.mapDerivedCategoryFactors.symm
  let Lift : (Stacks.SheafOfModules.kFlatComplexes X).FullSubcategory ⥤
      (Stacks.SheafOfModules.kFlatComplexes
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).FullSubcategory :=
    ObjectProperty.lift _ ((Stacks.SheafOfModules.kFlatComplexes X).ι ⋙ Φc) fun A =>
      Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.kFlat_reindexMod_map (smallTopology X)
        (equivSmallModel.{u} X.C).symm X.O A.obj A.2
  let e3 : (Stacks.SheafOfModules.kFlatComplexes X).ι ⋙
        (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj L ⋙ Φc ≅
      (Stacks.SheafOfModules.kFlatComplexes X).ι ⋙ Φc ⋙
        (Stacks.SheafOfModules.Tensor.tensorComplex
          (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O).flip.obj (Φc.obj L) :=
    NatIso.ofComponents (fun A =>
      Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexModTensorComplexIso
        (smallTopology X) (equivSmallModel.{u} X.C).symm X.O A.obj L)
      (fun f => by
        open Stacks.SheafOfModules.SiteEquivalenceDerivedTensor in
        have h := reindexModTensorComplexIso_hom_naturality_left
          (smallTopology X) (equivSmallModel.{u} X.C).symm X.O f.hom L
        refine Eq.trans ?_ (h.trans ?_)
        · rfl
        · rfl)
  Functor.isoWhiskerRight (kFlatComplexQTensorRightIso X L) _ ≪≫
    Functor.isoWhiskerLeft ((Stacks.SheafOfModules.kFlatComplexes X).ι ⋙
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj L) fac.symm ≪≫
    Functor.isoWhiskerRight e3 DerivedCategory.Q ≪≫
    (Functor.isoWhiskerLeft Lift (kFlatComplexQTensorRightIso
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X) (Φc.obj L))).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (Stacks.SheafOfModules.kFlatComplexes X).ι fac)
      ((Stacks.SheafOfModules.derivedTensorBifunctor
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).flip.obj
          (DerivedCategory.Q.obj (Φc.obj L))) ≪≫
    Functor.isoWhiskerLeft (Stacks.SheafOfModules.kFlatComplexQ X ⋙
      (smallModelDerivedEquivalence X).functor)
      ((Stacks.SheafOfModules.derivedTensorBifunctor
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).flip.mapIso (fac.app L))

/-- **Restriction to the small model commutes with the derived tensor product with a fixed
object**, on the derived tensor bifunctor of Stacks 06YU: `Φ(M ⊗^𝐋 Q L) ≅ Φ M ⊗^𝐋 Φ(Q L)`,
naturally in `M`.  It is descended from the K-flat case
`AlgebraicGeometry.RingedSite.smallModelKFlatTensorRightIso` along the localization of the K-flat
complexes at the quasi-isomorphisms. -/
def smallModelDerivedTensorBifunctorRightIso
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (Stacks.SheafOfModules.derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj L) ⋙
        (smallModelDerivedEquivalence X).functor ≅
      (smallModelDerivedEquivalence X).functor ⋙
        (Stacks.SheafOfModules.derivedTensorBifunctor
          (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).flip.obj
          ((smallModelDerivedEquivalence X).functor.obj (DerivedCategory.Q.obj L)) :=
  (Localization.whiskeringLeftFunctor' (Stacks.SheafOfModules.kFlatComplexQ X)
    (Stacks.SheafOfModules.kFlatComplexQuasiIso X) _).preimageIso
      (smallModelKFlatTensorRightIso X L)

/-- **Restriction to the small model commutes with the derived tensor product with a fixed
object**: `Φ(M ⊗^𝐋 K) ≅ Φ M ⊗^𝐋 Φ K`, naturally in `M`, for the derived tensor products
`Stacks.SheafOfModules.derivedTensorProductFunctor` of the site and of its small model. -/
def smallModelDerivedTensorFlipIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj K ⋙
        (smallModelDerivedEquivalence X).functor ≅
      (smallModelDerivedEquivalence X).functor ⋙
        (Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).flip.obj
          ((smallModelDerivedEquivalence X).functor.obj K) :=
  let e := DerivedCategory.Q.objObjPreimageIso K
  Functor.isoWhiskerRight
      (eqToIso (congrArg (fun T => T.flip.obj K)
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct_tensor X)) ≪≫
        (Stacks.SheafOfModules.derivedTensorBifunctor X).flip.mapIso e.symm) _ ≪≫
    smallModelDerivedTensorBifunctorRightIso X (DerivedCategory.Q.objPreimage K) ≪≫
    Functor.isoWhiskerLeft _
      ((Stacks.SheafOfModules.derivedTensorBifunctor
          (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).flip.mapIso
          ((smallModelDerivedEquivalence X).functor.mapIso e) ≪≫
        eqToIso (congrArg (fun T => T.flip.obj ((smallModelDerivedEquivalence X).functor.obj K))
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct_tensor
            (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).symm))

/-- **The derived internal Hom out of `K` on an essentially small ringed site**:
`N ↦ Φ⁻¹ R𝓗om(Φ K, Φ N)`, the derived internal Hom of the small model carried back along the
equivalence `Φ` of derived categories. -/
def essentiallySmallDerivedSheafHom
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (smallModelDerivedEquivalence X).functor ⋙
    (derivedSheafHomBifunctor (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).obj
      (op ((smallModelDerivedEquivalence X).functor.obj K)) ⋙
    (smallModelDerivedEquivalence X).inverse

/-- **Stacks 08J8 on an essentially small ringed site**: `- ⊗^𝐋 K` is left adjoint to
`N ↦ Φ⁻¹ R𝓗om(Φ K, Φ N)`, that is,
`Hom(M ⊗^𝐋 K, N) = Hom(M, Φ⁻¹ R𝓗om(Φ K, Φ N))` naturally in `M` and `N`. -/
@[sga "5 IIIB 5.2" "special case"]
def essentiallySmallDerivedTensorSheafHomAdjunction
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj K ⊣
      essentiallySmallDerivedSheafHom X K :=
  (((smallModelDerivedEquivalence X).toAdjunction.comp
    (derivedTensorSheafHomAdjunction (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)
      ((smallModelDerivedEquivalence X).functor.obj K))).comp
        (smallModelDerivedEquivalence X).symm.toAdjunction).ofNatIsoLeft
    ((Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ (smallModelDerivedEquivalence X).unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (smallModelDerivedTensorFlipIso X K) _ ≪≫
      Functor.associator _ _ _).symm

/-- Restriction to the small model carries the structure sheaf `𝒪` in degree zero to the
structure sheaf of the small model in degree zero. -/
def smallModelDerivedEquivalenceStructureSheafIso :
    (smallModelDerivedEquivalence X).functor.obj (derivedStructureSheaf X) ≅
      derivedStructureSheaf (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X) :=
  (smallModelModulesEquivalence X).functor.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (smallModelModulesEquivalence X).functor
        (ComplexShape.up ℤ) 0).app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The derived dual on an essentially small ringed site is the value at `𝒪` of the right
adjoint of `- ⊗^𝐋 K`**: `essentiallySmallDerivedDual K ≅ Φ⁻¹ R𝓗om(Φ K, Φ 𝒪)`, the right adjoint
being `AlgebraicGeometry.RingedSite.essentiallySmallDerivedSheafHom`. -/
def essentiallySmallDerivedDualIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    essentiallySmallDerivedDual X K ≅
      (essentiallySmallDerivedSheafHom X K).obj (derivedStructureSheaf X) :=
  (smallModelDerivedEquivalence X).inverse.mapIso
    (((derivedSheafHomBifunctor (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)).obj
      (op ((smallModelDerivedEquivalence X).functor.obj K))).mapIso
        (smallModelDerivedEquivalenceStructureSheafIso X).symm)

end AlgebraicGeometry.RingedSite

end
