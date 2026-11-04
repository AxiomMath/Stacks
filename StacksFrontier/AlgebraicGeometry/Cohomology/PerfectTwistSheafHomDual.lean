module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHomFunctorial
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectBidual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.DerivedEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit

/-!
# `- ⊗^L E ≅ R𝓗om(E^∨, -)` for a perfect `E`, natural in `E`

For a perfect object `E` of `D(𝒪_X)` the derived tensor product with `E` is the derived internal
Hom out of the dual `E^∨ = R𝓗om(E, 𝒪_X)`: biduality `E ≅ (E^∨)^∨` ([Stacks, Tag 08DQ], second
assertion) followed by `- ⊗^L (E^∨)^∨ ≅ R𝓗om(E^∨, -)` ([Stacks, Tag 08DQ], third assertion, as a
natural isomorphism) gives

`- ⊗^L E ≅ R𝓗om(E^∨, -)`.

This file proves that this isomorphism is natural in `E` as well, with `E ⟼ E^∨` acting on
morphisms by `R𝓗om(-, 𝒪_X)`.

## Main results

* `Stacks.Cohomology.CountableSections.derivedBidualMap_naturality`: the biduality map
  `K ⟶ (K^∨)^∨` is natural in `K`.
* `derivedTensorIsoSheafHomDual`, `derivedTensorIsoSheafHomDual_hom_naturality`: the isomorphism
  `- ⊗^L E ≅ R𝓗om(E^∨, -)` on a ringed space, and its naturality in `E`.
* `schemeDerivedTensorIsoSheafHomDual`, `schemeDerivedTensorIsoSheafHomDual_hom_naturality`: the
  same on a scheme, read from the derived tensor product of the projection formula
  (`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`) through
  `AlgebraicGeometry.derivedTensorSpellingIso`.

## Implementation notes

Biduality, the isomorphism of Tag 08DQ and `derivedTensorSpellingIso` exist only at
`HasDerivedCategory.standard`, so each declaration is stated there, with the model scoped to that
declaration.

The sheafification instances `Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens` and
`wEqualsLocallyBijectiveOpens` are installed locally, as in the file of
`derivedTensorSpellingIso`: without them, composing that isomorphism with the ones of Tag 08DQ
exhausts the heartbeat budget in instance search. Both classes are `Prop`s, so this assumes
nothing.

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0CRR](https://stacks.math.columbia.edu/tag/0CRR)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace

universe u

namespace Stacks.Cohomology.CountableSections

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
  Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

/-! ### Naturality of biduality -/

section Biduality

variable {T : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} T)

open CategoryTheory.MonoidalCategory in
attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The biduality map `K ⟶ (K^∨)^∨` is natural in `K`**, at `HasDerivedCategory.standard`, the
model of the biduality map. -/
theorem derivedBidualMap_naturality
    {K K' : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Rc)} (k : K ⟶ K') :
    k ≫ Stacks.SheafOfModules.derivedBidualMap Rc K' =
      Stacks.SheafOfModules.derivedBidualMap Rc K ≫
        ((Stacks.SheafOfModules.derivedSheafHom Rc).map
          (((Stacks.SheafOfModules.derivedSheafHom Rc).map k.op).app
            (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Rc))).op).app
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Rc)) := by
  let := Stacks.SheafOfModules.derivedMonoidalStructure Rc
  let O := RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Rc)
  let T₁ := Stacks.SheafOfModules.derivedTensor Rc
  let φ := T₁.map (Stacks.SheafOfModules.derivedDualStructureSheafIso Rc).symm.hom
  have hev : (T₁.obj (Stacks.SheafOfModules.derivedDual Rc O)).map k ≫
        Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K' O O =
      Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K O O ≫
        ((Stacks.SheafOfModules.derivedSheafHom Rc).map
          (((Stacks.SheafOfModules.derivedSheafHom Rc).map k.op).app O).op).app O := by
    have h0 := RingedSite.derivedSheafHomEvaluation_natural (Stacks.SheafOfModules.ringedSite Rc)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (Stacks.SheafOfModules.ringedSite Rc))
      (Stacks.SheafOfModules.derivedInternalHom Rc) k (𝟙 O) (𝟙 O)
    rw [RingedSite.derivedSheafHomMap_id] at h0
    simp only [RingedSite.derivedTensorMap, RingedSite.derivedSheafHomMap,
      CategoryTheory.Functor.map_id, Category.comp_id] at h0
    exact (congrArg (fun t => t ≫ Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K' O O)
      (Category.id_comp ((T₁.obj (Stacks.SheafOfModules.derivedDual Rc O)).map k))).symm.trans h0
  have h1 : k ≫ (λ_ K').inv = (λ_ K).inv ≫ (T₁.obj O).map k :=
    MonoidalCategory.leftUnitor_inv_naturality k
  have h2 : (T₁.obj O).map k ≫ φ.app K' = φ.app K ≫
      (T₁.obj (Stacks.SheafOfModules.derivedDual Rc O)).map k := φ.naturality k
  rw [Stacks.SheafOfModules.derivedBidualMap_eq, Stacks.SheafOfModules.derivedBidualMap_eq]
  show k ≫ (λ_ K').inv ≫ φ.app K' ≫ Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K' O O =
    ((λ_ K).inv ≫ φ.app K ≫ Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K O O) ≫ _
  have e1 : k ≫ (λ_ K').inv ≫ φ.app K' ≫ Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K' O O =
      (λ_ K).inv ≫ ((T₁.obj O).map k ≫ φ.app K' ≫
        Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K' O O) := by
    rw [← Category.assoc, h1, Category.assoc]
  have e2 : (T₁.obj O).map k ≫ φ.app K' ≫
      Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K' O O =
      φ.app K ≫ ((T₁.obj (Stacks.SheafOfModules.derivedDual Rc O)).map k ≫
        Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K' O O) :=
    (Category.assoc _ _ _).symm.trans ((congrArg
      (fun t => t ≫ Stacks.SheafOfModules.derivedSheafHomEvaluation Rc K' O O) h2).trans
        (Category.assoc _ _ _))
  exact e1.trans ((congrArg _ e2).trans ((congrArg _ (congrArg _ hev)).trans
    ((congrArg _ (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)))

end Biduality

section Twist

variable {T : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} T)
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens T, HasSheafify ((Opens.grothendieckTopology T).over V) AddCommGrpCat.{u}]
  [∀ V : Opens T, ((Opens.grothendieckTopology T).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens T, HasWeakSheafify ((Opens.grothendieckTopology T).over V) AddCommGrpCat.{u}]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`- ⊗^L E ≅ R𝓗om(E^∨, -)` for a perfect `E`** on a ringed space: biduality
`E ≅ (E^∨)^∨` ([Stacks, Tag 08DQ], second assertion), then the natural isomorphism
`- ⊗^L (E^∨)^∨ ≅ R𝓗om(E^∨, -)` ([Stacks, Tag 08DQ], third assertion) for the perfect object
`E^∨`. At `HasDerivedCategory.standard`, the model of Tag 08DQ. -/
def derivedTensorIsoSheafHomDual
    (E : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Rc))
    (hE : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect E) :
    (Stacks.SheafOfModules.derivedTensor Rc).flip.obj E ≅
      (Stacks.SheafOfModules.derivedSheafHom Rc).obj
        (op (Stacks.SheafOfModules.derivedDual Rc E)) :=
  (Stacks.SheafOfModules.derivedTensor Rc).flip.mapIso
      (Stacks.SheafOfModules.derivedBidualIso Rc E hE) ≪≫
    Stacks.SheafOfModules.derivedTensorDualNatIso Rc _
      (Stacks.SheafOfModules.isPerfect_derivedDual Rc E hE)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`- ⊗^L E ≅ R𝓗om(E^∨, -)` is natural in `E`**: for `e : E ⟶ E'` between perfect objects the
square formed by `K ⊗^L e` and `R𝓗om(R𝓗om(e, 𝒪_X), K)` commutes. At `HasDerivedCategory.standard`.
-/
theorem derivedTensorIsoSheafHomDual_hom_naturality
    {E E' : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Rc)} (e : E ⟶ E')
    (hE : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect E)
    (hE' : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect E')
    (K : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Rc)) :
    ((Stacks.SheafOfModules.derivedTensor Rc).obj K).map e ≫
        (derivedTensorIsoSheafHomDual Rc E' hE').hom.app K =
      (derivedTensorIsoSheafHomDual Rc E hE).hom.app K ≫
        ((Stacks.SheafOfModules.derivedSheafHom Rc).map
          (((Stacks.SheafOfModules.derivedSheafHom Rc).map e.op).app
            (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Rc))).op).app
          K := by
  have hb := derivedBidualMap_naturality Rc e
  have hs := RingedSite.derivedTensorDualToSheafHom_naturality_source
    (Stacks.SheafOfModules.ringedSite Rc)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (Stacks.SheafOfModules.ringedSite Rc))
    (((Stacks.SheafOfModules.derivedSheafHom Rc).map e.op).app
      (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Rc))) K
  show ((Stacks.SheafOfModules.derivedTensor Rc).obj K).map e ≫
      ((Stacks.SheafOfModules.derivedTensor Rc).obj K).map
        (Stacks.SheafOfModules.derivedBidualMap Rc E') ≫
        Stacks.SheafOfModules.derivedTensorDualToSheafHom Rc _ K =
    (((Stacks.SheafOfModules.derivedTensor Rc).obj K).map
        (Stacks.SheafOfModules.derivedBidualMap Rc E) ≫
        Stacks.SheafOfModules.derivedTensorDualToSheafHom Rc _ K) ≫ _
  let F := (Stacks.SheafOfModules.derivedTensor Rc).obj K
  have h1 : F.map e ≫ F.map (Stacks.SheafOfModules.derivedBidualMap Rc E') =
      F.map (Stacks.SheafOfModules.derivedBidualMap Rc E) ≫ F.map
        (((Stacks.SheafOfModules.derivedSheafHom Rc).map
          (((Stacks.SheafOfModules.derivedSheafHom Rc).map e.op).app
            (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Rc))).op).app
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Rc))) :=
    (F.map_comp _ _).symm.trans ((congrArg F.map hb).trans (F.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h1).trans <|
    (Category.assoc _ _ _).trans <| (congrArg _ hs).trans (Category.assoc _ _ _).symm

end Twist

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`- ⊗^L E ≅ R𝓗om(E^∨, -)` for a perfect `E` on a scheme**, with `- ⊗^L E` the derived tensor
product of the projection formula: `derivedTensorIsoSheafHomDual` read through
`AlgebraicGeometry.derivedTensorSpellingIso`. At `HasDerivedCategory.standard`. -/
def schemeDerivedTensorIsoSheafHomDual (X : Scheme.{u}) (E : DerivedCategory X.Modules)
    (hE : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect E) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf).flip.obj
        E : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules) ≅
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op (Stacks.SheafOfModules.derivedDual X.sheaf E)) :=
  ((flipFunctor _ _ _).mapIso (derivedTensorSpellingIso X)).app E ≪≫
    derivedTensorIsoSheafHomDual X.sheaf E hE

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`schemeDerivedTensorIsoSheafHomDual` is natural in `E`**, with `E ⟼ E^∨` acting on morphisms
by `R𝓗om(-, 𝒪_X)`. At `HasDerivedCategory.standard`. -/
theorem schemeDerivedTensorIsoSheafHomDual_hom_naturality (X : Scheme.{u})
    {E E' : DerivedCategory X.Modules} (e : E ⟶ E')
    (hE : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect E)
    (hE' : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect E')
    (K : DerivedCategory X.Modules) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf).obj K).map
        e ≫ (schemeDerivedTensorIsoSheafHomDual X E' hE').hom.app K =
      (schemeDerivedTensorIsoSheafHomDual X E hE).hom.app K ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map e.op).app
            (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf))).op).app
          K := by
  have hs := ((derivedTensorSpellingIso X).hom.app K).naturality e
  have ht := derivedTensorIsoSheafHomDual_hom_naturality X.sheaf e hE hE' K
  show _ ≫ ((derivedTensorSpellingIso X).hom.app K).app E' ≫
      (derivedTensorIsoSheafHomDual X.sheaf E' hE').hom.app K =
    (((derivedTensorSpellingIso X).hom.app K).app E ≫
      (derivedTensorIsoSheafHomDual X.sheaf E hE).hom.app K) ≫ _
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hs).trans <|
    (Category.assoc _ _ _).trans <| (congrArg _ ht).trans (Category.assoc _ _ _).symm

end Stacks.Cohomology.CountableSections

end
