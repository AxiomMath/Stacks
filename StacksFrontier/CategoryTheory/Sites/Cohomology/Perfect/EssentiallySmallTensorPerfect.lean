module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SiteEquivalenceDerivedTensorTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SmallModelPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.TensorOfPerfectObjects

/-!
# The derived tensor product of perfect objects on an essentially small ringed site

Let `(C, O)` be a ringed site whose objects form a type in an arbitrary universe while its
morphisms and the sections of `O` lie in one universe `u`, and suppose `C` is essentially small
at `u` — the small étale site of an algebraic space is one. If `K` and `L` are perfect objects
of `D(O)`, then so is `K ⊗^{𝐋}_O L`, for any derived tensor product of Stacks 06YU. This is
Stacks 09JB on such a site.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_derivedTensorProduct_of_essentiallySmall`:
  **Stacks 09JB** on an essentially small ringed site.

## Implementation notes

Stacks 09JB is available on a ringed site all three of whose universes agree,
`AlgebraicGeometry.RingedSite.isPerfect_tensor_of_isPerfect`, because the criterion of
Stacks 08G6 it rests on is. The statement here is reduced to that one along the restriction to a
small model `C₀` of the site, which is an equivalence `Mod(O) ≌ Mod(O|_{C₀})` commuting with the
tensor product of sheaves of modules (Stacks 01CU,
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso`):

* the factors are represented by K-flat complexes `A` and `B` (Stacks 06YS), so that
  `K ⊗^{𝐋} L` is the class of `Tot(A ⊗_O B)`;
* the restriction of `Tot(A ⊗_O B)` is `Tot(A|_{C₀} ⊗ B|_{C₀})`, the restrictions of `A` and `B`
  are K-flat, and so that class restricts to the derived tensor product of the restrictions of
  `K` and `L` on the small model, which is perfect;
* perfectness is detected after restriction to the small model
  (`AlgebraicGeometry.RingedSite.isPerfect_smallModelDerivedEquivalence_functor_obj_iff`).

The restriction is the reindexing
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod` along the equivalence of the
small model with the site, which is by definition the functor of
`AlgebraicGeometry.RingedSite.smallModelModulesEquivalence`; the comparison of the tensor
products and its two naturality squares are the ones
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexDerivedTensorNatIso` is built from,
and the transport of K-flatness and of total complexes is
`CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence` and
`CochainComplex.KFlatBifunctor.transportComplexIso`.

## References

* [Stacks Project, Tag 09JB](https://stacks.math.columbia.edu/tag/09JB)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u

/-! ### K-flatness and total tensor complexes along a reindexing of sheaves of modules -/

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

/-- **The reindexing of sheaves of modules along an equivalence of sites carries K-flat
complexes to K-flat complexes.** -/
theorem kFlat_reindexMod_map (L : CochainComplex
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u₁, v₁, w} O)) ℤ)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Tensor.sheafTensor.{u₁, v₁, w} O) L) :
    CochainComplex.KFlatBifunctor.KFlat
      (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O))
      (((reindexMod J' e O).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence (Tensor.sheafTensor.{u₁, v₁, w} O)
    (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u₁, v₁, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g) L hL

/-- **The reindexing of sheaves of modules along an equivalence of sites commutes with total
tensor complexes**: `Φ(Tot(K ⊗_𝒪 L)) ≅ Tot(Φ K ⊗ Φ L)`, degreewise by Stacks 01CU. -/
def reindexModTensorComplexIso (K L : CochainComplex
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u₁, v₁, w} O)) ℤ) :
    ((reindexMod J' e O).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K L (Tensor.sheafTensor.{u₁, v₁, w} O)
          (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        (((reindexMod J' e O).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((reindexMod J' e O).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
        (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O)) (ComplexShape.up ℤ) :=
  letI := fun K L => CochainComplex.KFlatBifunctor.hasTotal_mapBicomplex_of_equivalence
    (Tensor.sheafTensor.{u₁, v₁, w} O)
    (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u₁, v₁, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g) K L
  CochainComplex.KFlatBifunctor.transportComplexIso (Tensor.sheafTensor.{u₁, v₁, w} O)
    (Tensor.sheafTensor.{u₂, v₂, w} (reindexCommRingGeneral J' e O))
    (reindexMod J' e O).functor (reindexMod J' e O).functor (reindexMod J' e O).functor
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u₁, v₁, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g) K L

end Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The inclusion of the small model, read as the functor of the equivalence
`(equivSmallModel C).symm`, is continuous. -/
local instance continuous_equivSmallModel_symm_functor :
    (equivSmallModel.{u} X.C).symm.functor.IsContinuous (smallTopology X) X.J :=
  inferInstanceAs ((smallFunctor X).IsContinuous (smallTopology X) X.J)

/-- The inclusion of the small model, read as the functor of the equivalence
`(equivSmallModel C).symm`, is cocontinuous. -/
local instance cocontinuous_equivSmallModel_symm_functor :
    (equivSmallModel.{u} X.C).symm.functor.IsCocontinuous (smallTopology X) X.J :=
  inferInstanceAs ((smallFunctor X).IsCocontinuous (smallTopology X) X.J)

/-- The quasi-inverse of the inclusion of the small model, read as the inverse of the
equivalence `(equivSmallModel C).symm`, is continuous. -/
local instance continuous_equivSmallModel_symm_inverse :
    (equivSmallModel.{u} X.C).symm.inverse.IsContinuous X.J (smallTopology X) :=
  inferInstanceAs ((equivSmallModel.{u} X.C).functor.IsContinuous X.J (smallTopology X))

/-- The tensor product of sheaves of modules on the small model is additive. -/
local instance smallModelSheafTensorAdditive :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.SheafOfModules.reindexCommRingGeneral (smallTopology X)
        (equivSmallModel.{u} X.C).symm X.O)).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} _

/-- The tensor product of sheaves of modules on the small model is additive in its second
variable. -/
local instance smallModelSheafTensorObjAdditive (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.reindexCommRingGeneral
        (smallTopology X) (equivSmallModel.{u} X.C).symm X.O))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.SheafOfModules.reindexCommRingGeneral (smallTopology X)
        (equivSmallModel.{u} X.C).symm X.O)).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} _ M

/-- Total tensor complexes of complexes of sheaves of modules on the small model exist. -/
local instance smallModelHasMapBifunctor (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.reindexCommRingGeneral
        (smallTopology X) (equivSmallModel.{u} X.C).symm X.O))) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.SheafOfModules.reindexCommRingGeneral (smallTopology X)
        (equivSmallModel.{u} X.C).symm X.O)) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor _ K₁ K₂

/-- The tensor product of sheaves of modules on the ringed site of the small model is
additive. -/
local instance smallModelRingedSiteSheafTensorAdditive :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} _

/-- The tensor product of sheaves of modules on the ringed site of the small model is additive
in its second variable. -/
local instance smallModelRingedSiteSheafTensorObjAdditive (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} _ M

/-- Total tensor complexes on the ringed site of the small model exist. -/
local instance smallModelRingedSiteHasMapBifunctor (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor _ K₁ K₂

/-- The tensor product of sheaves of modules on a slice of the small model is additive. -/
local instance smallModelOverSheafTensorAdditive
    (V : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O.over V)).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} _

/-- The tensor product of sheaves of modules on a slice of the small model is additive in its
second variable. -/
local instance smallModelOverSheafTensorObjAdditive
    (V : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).C)
    (M : Stacks.DerivedTensor.RingedSite.Modules
      ((Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O.over V)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O.over V)).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} _ M

/-- Total tensor complexes on a slice of the small model exist. -/
local instance smallModelOverHasMapBifunctor
    (V : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).C)
    (K₁ K₂ : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules
      ((Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O.over V)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O.over V))
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor _ K₁ K₂

/-- Every perfect object of `D(O)` is represented by a K-flat complex whose restriction to the
small model is again K-flat and represents a perfect object. -/
private theorem exists_kFlat_restrict_perfect (M : DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (hM : X.IsPerfect M) :
    ∃ (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (_ : DerivedCategory.Q.obj A ≅ M),
      CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A ∧
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (Stacks.SheafOfModules.reindexCommRingGeneral (smallTopology X)
            (equivSmallModel.{u} X.C).symm X.O))
        (((Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod (smallTopology X)
          (equivSmallModel.{u} X.C).symm X.O).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A) ∧
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).IsPerfect
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod (smallTopology X)
            (equivSmallModel.{u} X.C).symm X.O).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj A)) := by
  obtain ⟨A, p, hA, hp⟩ :=
    Stacks.SheafOfModules.exists_kFlat_quasiIso X (DerivedCategory.Q.objPreimage M)
  let eA : DerivedCategory.Q.obj A ≅ M :=
    CochainComplex.derivedIsoOfQuasiIso p hp ≪≫ DerivedCategory.Q.objObjPreimageIso M
  refine ⟨A, eA, hA, Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.kFlat_reindexMod_map
    (smallTopology X) (equivSmallModel.{u} X.C).symm X.O A hA, ?_⟩
  let R := Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod (smallTopology X)
    (equivSmallModel.{u} X.C).symm X.O
  exact IsPerfect.of_iso _ (isPerfect_smallModelDerivedEquivalence_functor_obj X M hM)
    ((R.functor.mapDerivedCategory.mapIso eA).symm ≪≫ R.functor.mapDerivedCategoryFactors.app A)

/-- **Stacks 09JB on an essentially small ringed site.** Let `(C, O)` be a ringed site whose
underlying category is essentially small at the universe of the sections of `O`. If `K` and `L`
are perfect objects of `D(O)`, then so is `K ⊗^{𝐋}_O L`.

Stated for an arbitrary derived tensor product of Stacks 06YU: only its comparison with the total
tensor complex on K-flat complexes is used. -/
theorem isPerfect_derivedTensorProduct_of_essentiallySmall
    (T : Stacks.SheafOfModules.DerivedTensorProduct X)
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) (hL : X.IsPerfect L) :
    X.IsPerfect ((T.tensor.obj K).obj L) := by
  classical
  let R := Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod (smallTopology X)
    (equivSmallModel.{u} X.C).symm X.O
  obtain ⟨A, eA, hA, hA', hK'⟩ := exists_kFlat_restrict_perfect X K hK
  obtain ⟨B, eB, hB, hB', hL'⟩ := exists_kFlat_restrict_perfect X L hL
  refine IsPerfect.of_iso _ ?_ ((T.comparison A B hA hB).symm ≪≫
    (T.tensor.mapIso eA).app _ ≪≫ (T.tensor.obj K).mapIso eB)
  rw [← isPerfect_smallModelDerivedEquivalence_functor_obj_iff]
  exact IsPerfect.of_iso _ (isPerfect_canonicalDerivedTensorProduct_of_isPerfect _ _ _ hK' hL')
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O).comparison _ _ hA' hB' ≪≫
      (DerivedCategory.Q.mapIso
        (Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexModTensorComplexIso
          (smallTopology X) (equivSmallModel.{u} X.C).symm X.O A B)).symm ≪≫
      (R.functor.mapDerivedCategoryFactors.app
        (HomologicalComplex.mapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ))).symm)

end AlgebraicGeometry.RingedSite

end
