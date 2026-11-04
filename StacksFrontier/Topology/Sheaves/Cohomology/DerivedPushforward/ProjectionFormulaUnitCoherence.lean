module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.Duality.RightUnitorCoherenceInvariance
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility

/-!
# The right-unitor coherence of the Tag 079U comparison, on K-flat representatives

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject` proves
[Stacks, Tag 08EU] at `K = 𝒪_Y[0]` from one remaining equation, the right-unitor coherence of the
comparison of [Stacks, Tag 079U]: for **every** `Z` in `D(𝒪_Y)`,

`Lf^*(Z ⊗^𝐋_{𝒪_Y} 𝒪_Y) ⟶ Lf^*Z ⊗^𝐋_{𝒪_X} Lf^*𝒪_Y`, then `𝟙 ⊗ ν`, then `ρX`, equals `Lf^*ρY`.

That quantifier is the obstacle, not the equation: the comparison of [Stacks, Tag 079U] is
`CategoryTheory.Localization.liftNatIso` of a comparison defined on *K-flat* representatives
(`Stacks.Cohomology.DerivedPullbackTensor.modelsComparison`), so at a general `Z` neither side
has a formula.  This file removes the quantifier.  Its result is that the equation need only be
checked at `Z = QK` for a **K-flat** complex `K` of `𝒪_Y`-modules, which is exactly where every
constituent is computable: the comparison is
`Stacks.Cohomology.DerivedPullbackTensor.modelComparison` there, and the two right unitors are
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso_hom_app_q` there.

Nothing is assumed about `f` beyond its being a morphism of ringed spaces, and the unit
comparison `ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` is carried as a parameter, so a caller may supply any
such isomorphism — the conclusion of `isIso_projectionFormulaMap_unitObject` does not mention it.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_of_kFlat`: the right-unitor
  coherence at every `Z` in `D(𝒪_Y)`, from the coherence at `QK` for K-flat `K` only.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_of_kFlat`:
  **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]` carrying one hypothesis about K-flat complexes only** —
  the base case of the source's dévissage, with the right unitors and their naturality
  discharged and the coherence reduced to K-flat representatives.  That one hypothesis is
  discharged in the module `ProjectionFormulaUnitCoherenceMonoidal` of this directory, so the
  base case is available with nothing carried; see the implementation note below.

## Implementation notes

*Where the two right unitors come from.*  They are supplied as the components of the **natural**
isomorphism `Stacks.RingedSpace.derivedTensorRightUnitorNatIso`, not as the pointwise
`Stacks.RingedSpace.derivedTensorRightUnitIso`.  That is forced: the reduction consumes the
naturality of the unitor on `Y` as well as on `X` — the first to move `Lf^*` of the unitor past
an isomorphism of the object, the second as the hypothesis `hρX` of the base case — and the
pointwise isomorphism carries neither.

*Why `Q` is not the functor the reduction is run against.*  `DerivedCategory.Q` is also
essentially surjective, and the coherence at `QK` for *arbitrary* `K` would be a formally
stronger reduction; it is useless, because the comparison of [Stacks, Tag 079U] has no formula
at a representative that is not K-flat.  The functor used is therefore
`CochainComplex.KFlatBifunctor.kFlatQ`, the K-flat objects of the homotopy category viewed in
`D(𝒪_Y)`, whose essential surjectivity is `CochainComplex.KFlatBifunctor.kFlatQ_essSurj` — the
statement that every object of `D(𝒪_Y)` has a K-flat representative, [Stacks, Tag 06YS].  One
further transport, along the `Q` versus `Qh ∘ quotient` bridge
`DerivedCategory.quotientCompQhIso`, turns `kFlatQ.obj M` into `Q` of the underlying complex.

*Where the reduced hypothesis is discharged.*  The coherence at a K-flat representative is not
proved here, and it is proved: it is
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_app_q` of
`ProjectionFormulaUnitCoherenceMonoidal.lean` in this directory, and the base case with nothing
carried is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_unconditional`
of `ProjectionFormulaUnitObject.lean`.

Reduced to a K-flat representative the equation is a statement about complexes of modules — that
the comparison of [Stacks, Tag 01CD] assembled on total complexes is compatible with the right
unitors of the monoidal structure of [Stacks, Tag 0FPQ] — whose degreewise content is
`Stacks.RingedSpace.comparison_rightUnitor`.  No total complex has to be taken apart to get
there: the comparison of total complexes **is** the tensorator of the monoidal lift of `f^*` to
complexes (`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso_inv_eq`), so
the equation is a unitality axiom of `CategoryTheory.Functor.Monoidal`.  The two identifications
that make the lift available are `SheafOfModules.rightUnitor_sheafTensor_eq`, which identifies
the right unitor of `SheafOfModules.monoidalCategorySheafTensor` — what
`CategoryTheory.MonoidalCategory.rightUnitorNatIso` on complexes is built from — with
`Stacks.RingedSpace.tensorSheafUnitRightIso`, the unitor
`Stacks.RingedSpace.comparison_rightUnitor` is stated about; and
`Stacks.PullbackSheafTensor.monoidal`, which is `f^*` as a monoidal functor for the re-seated
structure with that comparison as its oplax tensorator.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The right-unitor coherence of [Stacks, Tag 079U] needs checking on K-flat representatives
only.**  If the equation holds at `QK` for every K-flat complex `K` of `𝒪_Y`-modules, it holds at
every object of `D(𝒪_Y)`.

Both right unitors are the components of
`Stacks.RingedSpace.derivedTensorRightUnitorNatIso`, so both naturality hypotheses of
`Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_essSurj` are available; the
essentially surjective functor is `CochainComplex.KFlatBifunctor.kFlatQ`, and the passage from
`kFlatQ.obj M` to `Q` of the underlying complex is `DerivedCategory.quotientCompQhIso`. -/
theorem rightUnitorCoherence_of_kFlat
    (ν : (derivedPullback f).obj (singleUnit Y) ≅ singleUnit X)
    (h : ∀ K : CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ,
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K →
      (pullbackTensorComparison f).app (DerivedCategory.Q.obj K, singleUnit Y) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ ν.hom) :
              (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
                ((derivedPullback f).obj (DerivedCategory.Q.obj K), singleUnit X)) ≫
            ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
              ((derivedPullback f).obj (DerivedCategory.Q.obj K))).hom =
        (derivedPullback f).map
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app
            (DerivedCategory.Q.obj K)).hom)
    (Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (pullbackTensorComparison f).app (Z, singleUnit Y) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((𝟙 ((derivedPullback f).obj Z) ×ₘ ν.hom) :
            (((derivedPullback f).obj Z, (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
              ((derivedPullback f).obj Z, singleUnit X)) ≫
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
            ((derivedPullback f).obj Z)).hom =
      (derivedPullback f).map
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app Z).hom := by
  have hloc := Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization Y.sheaf
  have hes := CochainComplex.KFlatBifunctor.kFlatQ_essSurj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
  refine Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_essSurj _ _
    (pullbackTensorComparison f)
    (fun W => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app W)
    (fun W => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app W) ν
    (CochainComplex.KFlatBifunctor.kFlatQ
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))
    (fun u => Stacks.RingedSpace.derivedTensorRightUnitor_naturality Y u)
    (fun u => Stacks.RingedSpace.derivedTensorRightUnitor_naturality X u) ?_ Z
  intro M
  exact Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_iso _ _
    (pullbackTensorComparison f)
    (fun W => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app W)
    (fun W => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app W) ν
    (fun u => Stacks.RingedSpace.derivedTensorRightUnitor_naturality Y u)
    (fun u => Stacks.RingedSpace.derivedTensorRightUnitor_naturality X u)
    ((DerivedCategory.quotientCompQhIso _).app M.obj.as) (h M.obj.as M.property)

/-! ### The two formulas that make the reduced hypothesis computable -/

section Formulas

attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.kFlatQPair_isLocalization

/-- **The comparison of [Stacks, Tag 079U] at a pair of K-flat objects of the homotopy
category** is the comparison on representatives,
`Stacks.Cohomology.DerivedPullbackTensor.modelComparison`, transported along the `Q` versus
`Qh ∘ quotient` bridge.

The lift `CategoryTheory.Localization.liftNatIso` adds nothing at an object of the form
`kFlatQPair.obj M`, because the two `CategoryTheory.Localization.Lifting` instances it uses are
`CategoryTheory.Localization.Lifting.compLeft`, whose isomorphism is the identity; the value at
the image pair `(QK, QL)` is then read off by naturality of the comparison along the bridge. -/
theorem derivedPullbackTensorIso_hom_app_q_models
    (M : (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ×
      (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj M.1.obj.as, DerivedCategory.Q.obj M.2.obj.as) =
      (Stacks.Cohomology.DerivedPullbackTensor.modelComparison f M.1.obj.as M.2.obj.as
        M.1.property M.2.property).hom := by
  have h1 : (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.app
      ((Stacks.Cohomology.DerivedPullbackTensor.kFlatQPair (Y := Y)).obj M) =
      (Stacks.Cohomology.DerivedPullbackTensor.modelsComparison f).hom.app M := by
    dsimp only [Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso,
      Localization.liftNatIso]
    rw [Localization.liftNatTrans_app]
    simp [Localization.Lifting.iso]
  have hpe : IsIso ((Stacks.Cohomology.DerivedPullbackTensor.pullbackOfTensor f).map
      (Stacks.Cohomology.DerivedPullbackTensor.kFlatQPairIso M).hom) :=
    ((Stacks.Cohomology.DerivedPullbackTensor.pullbackOfTensor f).mapIso
      (Stacks.Cohomology.DerivedPullbackTensor.kFlatQPairIso M)).isIso_hom
  apply (cancel_epi ((Stacks.Cohomology.DerivedPullbackTensor.pullbackOfTensor f).map
    (Stacks.Cohomology.DerivedPullbackTensor.kFlatQPairIso M).hom)).1
  rw [(Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.naturality
    (Stacks.Cohomology.DerivedPullbackTensor.kFlatQPairIso M).hom, h1]
  dsimp only [Stacks.Cohomology.DerivedPullbackTensor.modelsComparison,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.mapIso_inv]
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The comparison of [Stacks, Tag 079U] on a pair of K-flat complexes** is
`Stacks.Cohomology.DerivedPullbackTensor.modelComparison`.  This is
`derivedPullbackTensorIso_hom_app_q_models` read at the homotopy classes of the two complexes
and at the type ascription `pullbackTensorComparison` carries, and it is the formula the reduced
hypothesis of `rightUnitorCoherence_of_kFlat` is to be computed with. -/
theorem pullbackTensorComparison_app_q_of_kFlat
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (pullbackTensorComparison f).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (Stacks.Cohomology.DerivedPullbackTensor.modelComparison f K L hK hL).hom :=
  derivedPullbackTensorIso_hom_app_q_models f
    (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K, hK⟩,
      ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L, hL⟩)

end Formulas

/-- **The right unit constraint of `⊗^𝐋_{𝒪_Z}` on a ringed space, at the image of a complex**:
there it is the right K-flat comparison followed by `Q` of the right unitor of complexes.

This is `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso_hom_app_q` read
at the ringed site of the space.  Together with `pullbackTensorComparison_app_q_of_kFlat` it
turns the hypothesis of `rightUnitorCoherence_of_kFlat` into a statement about complexes: no
object of `D(𝒪)` and no localization is left in it. -/
theorem derivedTensorRightUnitorNatIso_hom_app_q (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).hom.app (DerivedCategory.Q.obj K) =
      ((canonicalDerivedTensorProduct Z.sheaf).comparisonRight K
          (unitComplex (Stacks.RingedSpace.toRingedSite Z))
          (Stacks.SheafOfModules.isKFlat_single_unit
            (Stacks.RingedSpace.toRingedSite Z).O)).hom ≫
        DerivedCategory.Q.map
          ((tensorComplexRightUnitorNatIso (Stacks.RingedSpace.toRingedSite Z)).app K).hom :=
  DerivedTensorProduct.rightUnitorNatIso_hom_app_q (Stacks.RingedSpace.toRingedSite Z)
    (canonicalDerivedTensorProduct Z.sheaf) K

/-- **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]`, carrying one hypothesis about K-flat complexes
only.**  For an arbitrary morphism of ringed spaces `f : X ⟶ Y`, an arbitrary unit comparison
`ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` and an arbitrary `E` in `D(𝒪_X)`, the derived projection-formula
morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} 𝒪_Y ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*𝒪_Y)`

is an isomorphism, provided the right-unitor coherence of the comparison of [Stacks, Tag 079U]
holds at `QK` for every **K-flat** complex `K` of `𝒪_Y`-modules.

Compared with `isIso_projectionFormulaMap_unitObject` this carries one hypothesis instead of
four: the two right unitors are supplied, the naturality of the one on `X` is supplied, and the
coherence is restricted to K-flat representatives, which is where its constituents have
formulas. -/
theorem isIso_projectionFormulaMap_unitObject_of_kFlat
    (ν : (derivedPullback f).obj (singleUnit Y) ≅ singleUnit X)
    (h : ∀ K : CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ,
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K →
      (pullbackTensorComparison f).app (DerivedCategory.Q.obj K, singleUnit Y) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ ν.hom) :
              (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
                ((derivedPullback f).obj (DerivedCategory.Q.obj K), singleUnit X)) ≫
            ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
              ((derivedPullback f).obj (DerivedCategory.Q.obj K))).hom =
        (derivedPullback f).map
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app
            (DerivedCategory.Q.obj K)).hom)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (projectionFormulaMap f E (singleUnit Y)) :=
  isIso_projectionFormulaMap_unitObject f
    (fun Z => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app Z)
    (fun W => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app W) ν
    (fun u => Stacks.RingedSpace.derivedTensorRightUnitor_naturality X u)
    (rightUnitorCoherence_of_kFlat f ν h) E

end Stacks.Cohomology.DerivedProjectionFormula

end
