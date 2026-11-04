module

public import StacksFrontier.AlgebraicGeometry.Duality.ShiftedUnitorCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackCommShiftOnKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSingleUnitor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaUnitObject
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.UnitComparison

/-! # Stacks 0944 at the structure sheaf placed in an arbitrary degree

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor of
the underlying sites which is a morphism of sites.  **Stacks 0944** asserts that Equation
21.50.0.1 of [Stacks, Tag 0B56],

`Rf_*E ⊗^𝐋_{𝒪_D} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_C} Lf^*K)`,

is invertible for `K` a strictly perfect complex, and the dévissage
`isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit` of
`Stacks.Cohomology.ProjectionFormulaPerfectDevissage` reduces that to invertibility at the
structure sheaf placed in *every* degree.  This file proves that base case.

## Main results

* `Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.isIso_projectionFormulaMap_singleUnit`:
  **Equation 21.50.0.1 is invertible at `𝒪_D[i]` for every `i : ℤ`**, for every `E` in `D(𝒪_C)`,
  with nothing assumed beyond `f` being a morphism of ringed topoi presented by a morphism of
  sites.  The *ordinary* comparison `f^*𝒪_D ⟶ 𝒪_C` is invertible for such an `f`, by
  `Stacks.Sites.UnitComparison.isIso_pullbackObjUnitToUnit_of_isMorphismOfSites`.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_singleUnitor`: **the shifted-unitor
  coherence of [Stacks, Tag 07A4]** — for every `Z` in `D(𝒪_D)` the comparison of Stacks 07A4 at
  `(Z, 𝒪_D[q])`, followed by the unit comparison `Lf^*(𝒪_D[q]) ⟶ 𝒪_C[q]` in the second tensor
  factor and by the twisted unitor `Lf^*Z ⊗^𝐋 𝒪_C[q] ≅ (Lf^*Z)⟦-q⟧`, is `Lf^*` of the twisted
  unitor on the target followed by the commutation of `Lf^*` with the shift.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackSingleUnitMap`: the unit comparison
  `Lf^*(𝒪_D[q]) ⟶ 𝒪_C[q]`, and `isIso_derivedPullbackSingleUnitMap`, its invertibility.

## Implementation notes

**Why degree `q` is not the degree zero.**  `𝒪_D[0]` is the unit of `⊗^𝐋_{𝒪_D}`, so at `q = 0`
the identification `Z ⊗^𝐋 𝒪_D[0] ≅ Z` is the right unit constraint and
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj` applies.  For
`q ≠ 0` what is available is `Z ⊗^𝐋 𝒪_D[q] ≅ Z⟦-q⟧`
(`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso`), which is not a unitor,
and the coherence it satisfies carries the commutation of `Lf^*` with the shift.  The abstract
reduction for that shape is
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_shiftedUnitObj`: its
conclusion needs, besides the coherence, that the *mate* of that commutation be invertible, and
the mate is the commutation of `Rf_*` with the shift by
`Stacks.AlgebraicGeometry.ProjectionFormula.homEquiv_commShift_counit`.

**The three extra factors.**  Against the degree-zero proof, three factors enter and cancel in
pairs between the two halves of the five-step chain of Stacks 07A4:

* the commutation of `DerivedCategory.Q` with the shift, which is where the twisted unitor's
  value at the image of a complex ends
  (`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso_hom_app_q`);
* the commutation of the degreewise pullback with the shift, which is what the complex-level
  shifted-unitor coherence
  `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_singleUnitor` produces;
* the commutation of `Lf^*` with the shift, which is the `γ` of the coherence and whose value at
  the image of a K-flat complex with flat terms is
  `Stacks.Sheaves.DerivedPullback.flatPullbackIso_commShift`.

Nothing else changes: the model computation is the degree-zero one with
`Stacks.Sheaves.DerivedPullback.mapBifunctorSingleUnitIso` in place of
`Stacks.Sheaves.DerivedPullback.mapBifunctorUnitIso`.

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Sheaves.DerivedPullback.KFlatPullback

open scoped CategoryTheory.Prod

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Sheaves.DerivedPullback

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-! ## The unit comparison at the structure sheaf placed in a degree -/

/-- **The computation of `Lf^*` on the K-flat complex `𝒪_D[q]` with flat terms.** -/
def singleUnitFlatPullbackIso (q : ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj (singleUnitComplex Y.O q)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj (singleUnitComplex Y.O q)) :=
  flatPullbackIso f hmos (singleUnitComplex Y.O q)
    (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q) (isFlat_single_unit_X_deg Y q)

/-- **The unit comparison `Lf^*(𝒪_D[q]) ⟶ 𝒪_C[q]`**: the computation of `Lf^*` on the K-flat
complex `𝒪_D[q]` followed by `Q` of the unit comparison on complexes. -/
def derivedPullbackSingleUnitMap (q : ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj (singleUnitComplex Y.O q)) ⟶
      DerivedCategory.Q.obj (singleUnitComplex X.O q) :=
  (singleUnitFlatPullbackIso f hmos q).hom ≫
    DerivedCategory.Q.map (pullbackUnitComplexMapDeg f q)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
include hmos in
/-- **The unit comparison on complexes is invertible.**  Both of its factors are: the first is
the `hom` of an isomorphism, and the second is `HomologicalComplex.single` of the ordinary
comparison `f^*𝒪_D ⟶ 𝒪_C`, which is invertible along a morphism of sites by
`Stacks.Sites.UnitComparison.isIso_pullbackObjUnitToUnit_of_isMorphismOfSites`. -/
theorem isIso_pullbackUnitComplexMapDeg (q : ℤ) :
    IsIso (pullbackUnitComplexMapDeg f q) := by
  have : IsIso (pullbackUnitComparison f) :=
    Stacks.Sites.UnitComparison.isIso_pullbackObjUnitToUnit_of_isMorphismOfSites
      f.u Y.J X.J f.fSharpRing hmos
  rw [pullbackUnitComplexMapDeg]
  infer_instance

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The unit comparison `Lf^*(𝒪_D[q]) ⟶ 𝒪_C[q]` is invertible.** -/
theorem isIso_derivedPullbackSingleUnitMap (q : ℤ) :
    IsIso (derivedPullbackSingleUnitMap f hmos q) := by
  have := isIso_pullbackUnitComplexMapDeg f hmos q
  rw [derivedPullbackSingleUnitMap]
  infer_instance

/-! ## The shifted-unitor coherence at the image of a K-flat complex with flat terms -/

section Model

variable (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
  (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
  (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
  (q : ℤ)

/-- **The K-flat comparison of [Stacks, Tag 06YU] at `(K, 𝒪_D[q])`**, with its source spelled at
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitObject` and its target with
`HomologicalComplex.mapBifunctor`. -/
def singleTensorComparisonTarget :
    ((canonicalDerivedTensorProduct Y.O).tensor.obj (DerivedCategory.Q.obj K)).obj
        (DerivedTensorProduct.singleUnitObject Y.toRingedSite q) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K (singleUnitComplex Y.O q)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) :=
  (canonicalDerivedTensorProduct Y.O).comparison K (singleUnitComplex Y.O q) hK
    (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q)

/-- **The computation of `Lf^*` on the total tensor complex `Tot(K ⊗_{𝒪_D} 𝒪_D[q])`**, which is
again K-flat with flat terms. -/
def singleTotalFlatPullbackIso :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K (singleUnitComplex Y.O q)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj
        (HomologicalComplex.mapBifunctor K (singleUnitComplex Y.O q)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
  flatPullbackIso f hmos
    (HomologicalComplex.mapBifunctor K (singleUnitComplex Y.O q)
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK
      (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q))
    (isFlat_tensorComplex_X Y.O K (singleUnitComplex Y.O q) hflatK
      (isFlat_single_unit_X_deg Y q))

/-- **The K-flat comparison of [Stacks, Tag 06YU] at the pair of degreewise pullbacks.** -/
def singleTensorComparisonSource :
    ((canonicalDerivedTensorProduct X.O).tensor.obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj (singleUnitComplex Y.O q))) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K)
        ((pullbackComplex f).obj (singleUnitComplex Y.O q))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (canonicalDerivedTensorProduct X.O).comparison ((pullbackComplex f).obj K)
    ((pullbackComplex f).obj (singleUnitComplex Y.O q))
    (kFlat_pullbackComplex' f hmos K hK hflatK)
    (kFlat_pullbackComplex' f hmos (singleUnitComplex Y.O q)
      (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q) (isFlat_single_unit_X_deg Y q))

/-- **The right K-flat comparison of [Stacks, Tag 06YU] at `(f^*K, 𝒪_C[q])`.** -/
def singleComparisonSource :
    ((canonicalDerivedTensorProduct X.O).tensor.obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).obj
        (DerivedTensorProduct.singleUnitObject X.toRingedSite q) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K)
        (singleUnitComplex X.O q)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (canonicalDerivedTensorProduct X.O).comparisonRight ((pullbackComplex f).obj K)
    (singleUnitComplex X.O q) (Stacks.SheafOfModules.isKFlat_single_unit_deg X.O q)

/-- **The first half of the five-step chain of [Stacks, Tag 07A4] at `(K, 𝒪_D[q])`.** -/
def singleModelLeft :
    (derivedPullback f).obj
        (((canonicalDerivedTensorProduct Y.O).tensor.obj (DerivedCategory.Q.obj K)).obj
          (DerivedTensorProduct.singleUnitObject Y.toRingedSite q)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj
        (HomologicalComplex.mapBifunctor K (singleUnitComplex Y.O q)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
  derivedPullbackTensorModelLeft f hmos K (singleUnitComplex Y.O q) hK
    (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q) hflatK (isFlat_single_unit_X_deg Y q)

/-- **The second half of the five-step chain of [Stacks, Tag 07A4] at `(K, 𝒪_D[q])`.** -/
def singleModelRight :
    ((canonicalDerivedTensorProduct X.O).tensor.obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj K))).obj
        ((derivedPullback f).obj (DerivedTensorProduct.singleUnitObject Y.toRingedSite q)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj
        (HomologicalComplex.mapBifunctor K (singleUnitComplex Y.O q)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
  derivedPullbackTensorModelRight f hmos K (singleUnitComplex Y.O q) hK
    (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q) hflatK (isFlat_single_unit_X_deg Y q)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The first half of the chain is `Lf^*` of the K-flat comparison on the target followed by the
computation of `Lf^*` on the total tensor complex. -/
theorem singleModelLeft_inv :
    (singleModelLeft f hmos K hK hflatK q).inv =
      (singleTotalFlatPullbackIso f hmos K hK hflatK q).inv ≫
        (derivedPullback f).map (singleTensorComparisonTarget K hK q).inv :=
  rfl

/-- The second half of the chain is the pair of computations of `Lf^*`, then the K-flat
comparison on the source, then the comparison of total tensor complexes read backwards. -/
theorem singleModelRight_hom :
    (singleModelRight f hmos K hK hflatK q).hom =
      (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
          (((flatPullbackIso f hmos K hK hflatK).hom ×ₘ
              (singleUnitFlatPullbackIso f hmos q).hom) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj
                  (DerivedTensorProduct.singleUnitObject Y.toRingedSite q)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                DerivedCategory.Q.obj
                  ((pullbackComplex f).obj (singleUnitComplex Y.O q)))) ≫
        (singleTensorComparisonSource f hmos K hK hflatK q).hom ≫
          DerivedCategory.Q.map
            (pullbackToposTensorTotalIso f hmos K (singleUnitComplex Y.O q)).inv :=
  rfl

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The twisted unitor of `⊗^𝐋_{𝒪_D}` at `QK`**, in the ascribed spellings. -/
theorem singleUnitorIso_target_eq :
    (DerivedTensorProduct.singleUnitorIso Y.toRingedSite
        (canonicalDerivedTensorProduct Y.O) q).hom.app (DerivedCategory.Q.obj K) =
      (singleTensorComparisonTarget K hK q).hom ≫
        DerivedCategory.Q.map (mapBifunctorSingleUnitIso Y.O K q).hom ≫
          (DerivedCategory.Q.commShiftIso (-q)).hom.app K := by
  rw [DerivedTensorProduct.singleUnitorIso_hom_app_q,
    (canonicalDerivedTensorProduct Y.O).comparisonRight_eq_comparison K
      (singleUnitComplex Y.O q) hK (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q)]
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
/-- **The twisted unitor of `⊗^𝐋_{𝒪_C}` at `Q(f^*K)`**, in the ascribed spellings. -/
theorem singleUnitorIso_source_eq :
    (DerivedTensorProduct.singleUnitorIso X.toRingedSite
          (canonicalDerivedTensorProduct X.O) q).hom.app
        (DerivedCategory.Q.obj ((pullbackComplex f).obj K)) =
      (singleComparisonSource f K q).hom ≫
        DerivedCategory.Q.map (mapBifunctorSingleUnitIso X.O ((pullbackComplex f).obj K) q).hom ≫
          (DerivedCategory.Q.commShiftIso (-q)).hom.app ((pullbackComplex f).obj K) :=
  DerivedTensorProduct.singleUnitorIso_hom_app_q X.toRingedSite
    (canonicalDerivedTensorProduct X.O) q ((pullbackComplex f).obj K)

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
/-- **The right K-flat comparison of [Stacks, Tag 06YU] is natural in the degreewise unit
comparison**, in the ascribed spellings. -/
theorem singleComparisonSource_naturality :
    (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
        ((𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj K)) ×ₘ
            DerivedCategory.Q.map (pullbackUnitComplexMapDeg f q)) :
          ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              DerivedCategory.Q.obj
                ((pullbackComplex f).obj (singleUnitComplex Y.O q))) : _ × _) ⟶
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              DerivedTensorProduct.singleUnitObject X.toRingedSite q)) ≫
      (singleComparisonSource f K q).hom =
    (singleTensorComparisonSource f hmos K hK hflatK q).hom ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
        (𝟙 ((pullbackComplex f).obj K)) (pullbackUnitComplexMapDeg f q)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  have h := (canonicalDerivedTensorProduct X.O).comparisonRight_naturality
    (𝟙 ((pullbackComplex f).obj K)) (pullbackUnitComplexMapDeg f q)
    (kFlat_pullbackComplex' f hmos (singleUnitComplex Y.O q)
      (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q) (isFlat_single_unit_X_deg Y q))
    (Stacks.SheafOfModules.isKFlat_single_unit_deg X.O q)
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp,
    (canonicalDerivedTensorProduct X.O).comparisonRight_eq_comparison
      ((pullbackComplex f).obj K) ((pullbackComplex f).obj (singleUnitComplex Y.O q))
      (kFlat_pullbackComplex' f hmos K hK hflatK)
      (kFlat_pullbackComplex' f hmos (singleUnitComplex Y.O q)
        (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q)
        (isFlat_single_unit_X_deg Y q))] at h
  rw [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  exact h

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The computation of `Lf^*` is natural in the unit law `Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧`**, in the
ascribed spellings. -/
theorem singleTotalFlatPullbackIso_naturality :
    (derivedPullback f).map
          (DerivedCategory.Q.map (mapBifunctorSingleUnitIso Y.O K q).hom) ≫
        (flatPullbackIso f hmos
          ((CategoryTheory.shiftFunctor
            (CochainComplex (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (-q)).obj K)
          (kFlat_shift Y.O K hK (-q)) (fun i => hflatK (i + -q))).hom =
      (singleTotalFlatPullbackIso f hmos K hK hflatK q).hom ≫
        DerivedCategory.Q.map
          ((pullbackComplex f).map (mapBifunctorSingleUnitIso Y.O K q).hom) :=
  flatPullbackIso_naturality f hmos (mapBifunctorSingleUnitIso Y.O K q).hom
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK
      (Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q))
    (kFlat_shift Y.O K hK (-q))
    (isFlat_tensorComplex_X Y.O K (singleUnitComplex Y.O q) hflatK
      (isFlat_single_unit_X_deg Y q))
    (fun i => hflatK (i + -q))

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
/-- **The identity of morphisms of complexes behind the coherence**, with the comparison of total
tensor complexes moved to the other side.  This is
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_singleUnitor` with one isomorphism
cancelled. -/
theorem singleUnitComparison_mapBifunctorSingleUnitIso :
    HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackUnitComplexMapDeg f q) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) ≫
        (mapBifunctorSingleUnitIso X.O ((pullbackComplex f).obj K) q).hom =
      (pullbackToposTensorTotalIso f hmos K (singleUnitComplex Y.O q)).inv ≫
        (pullbackComplex f).map (mapBifunctorSingleUnitIso Y.O K q).hom ≫
          ((pullbackComplex f).commShiftIso (-q)).hom.app K := by
  rw [← pullbackToposTensorTotalIso_singleUnitor f hmos K q, Iso.inv_hom_id_assoc]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The commutation of `Lf^*` with the shift at `QK`, solved for**: the two factors of the
right-hand side of the coherence, read against the computation of `Lf^*` by the degreewise
pullback.  This is `Stacks.Sheaves.DerivedPullback.flatPullbackIso_commShift` with the
isomorphism at the far end moved to the other side. -/
theorem commShiftIso_app_q_solved :
    (derivedPullback f).map ((DerivedCategory.Q.commShiftIso (-q)).hom.app K) ≫
        ((derivedPullback f).commShiftIso (-q)).hom.app (DerivedCategory.Q.obj K) =
      (flatPullbackIso f hmos
            ((CategoryTheory.shiftFunctor
              (CochainComplex (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (-q)).obj K)
            (kFlat_shift Y.O K hK (-q)) (fun i => hflatK (i + -q))).hom ≫
        DerivedCategory.Q.map (((pullbackComplex f).commShiftIso (-q)).hom.app K) ≫
          (DerivedCategory.Q.commShiftIso (-q)).hom.app ((pullbackComplex f).obj K) ≫
            ((flatPullbackIso f hmos K hK hflatK).inv)⟦-q⟧' := by
  rw [← reassoc_of% (flatPullbackIso_commShift f hmos (-q) K hK hflatK),
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The first half of the chain, read backwards against `Lf^*` of the twisted unitor on the
target followed by the commutation of `Lf^*` with the shift.** -/
theorem singleModelLeft_inv_singleUnitor :
    (singleModelLeft f hmos K hK hflatK q).inv ≫
        ((derivedPullback f).map
            ((DerivedTensorProduct.singleUnitorIso Y.toRingedSite
              (canonicalDerivedTensorProduct Y.O) q).hom.app (DerivedCategory.Q.obj K)) ≫
          ((derivedPullback f).commShiftIso (-q)).hom.app (DerivedCategory.Q.obj K)) =
      DerivedCategory.Q.map
          ((pullbackComplex f).map (mapBifunctorSingleUnitIso Y.O K q).hom) ≫
        DerivedCategory.Q.map (((pullbackComplex f).commShiftIso (-q)).hom.app K) ≫
          (DerivedCategory.Q.commShiftIso (-q)).hom.app ((pullbackComplex f).obj K) ≫
            ((flatPullbackIso f hmos K hK hflatK).inv)⟦-q⟧' := by
  rw [singleModelLeft_inv, singleUnitorIso_target_eq K hK q,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((derivedPullback f).map (singleTensorComparisonTarget K hK q).inv),
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, commShiftIso_app_q_solved f hmos K hK hflatK q,
    reassoc_of% (singleTotalFlatPullbackIso_naturality f hmos K hK hflatK q),
    Iso.inv_hom_id_assoc]

/-- **The second half of the chain, against the unit comparison and the twisted unitor on the
source.** -/
theorem singleModelRight_hom_singleUnitor :
    (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
          ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
              derivedPullbackSingleUnitMap f hmos q) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj
                  (DerivedTensorProduct.singleUnitObject Y.toRingedSite q)) : _ × _) ⟶
              ((derivedPullback f).obj (DerivedCategory.Q.obj K),
                DerivedTensorProduct.singleUnitObject X.toRingedSite q)) ≫
        (DerivedTensorProduct.singleUnitorIso X.toRingedSite
            (canonicalDerivedTensorProduct X.O) q).hom.app
          ((derivedPullback f).obj (DerivedCategory.Q.obj K)) =
      (singleModelRight f hmos K hK hflatK q).hom ≫
        DerivedCategory.Q.map
            ((pullbackComplex f).map (mapBifunctorSingleUnitIso Y.O K q).hom) ≫
          DerivedCategory.Q.map (((pullbackComplex f).commShiftIso (-q)).hom.app K) ≫
            (DerivedCategory.Q.commShiftIso (-q)).hom.app ((pullbackComplex f).obj K) ≫
              ((flatPullbackIso f hmos K hK hflatK).inv)⟦-q⟧' := by
  have hsplit :
      ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
            derivedPullbackSingleUnitMap f hmos q) :
          (((derivedPullback f).obj (DerivedCategory.Q.obj K),
              (derivedPullback f).obj
                (DerivedTensorProduct.singleUnitObject Y.toRingedSite q)) : _ × _) ⟶
            ((derivedPullback f).obj (DerivedCategory.Q.obj K),
              DerivedTensorProduct.singleUnitObject X.toRingedSite q)) =
        (((flatPullbackIso f hmos K hK hflatK).hom ×ₘ
            (singleUnitFlatPullbackIso f hmos q).hom) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj
                  (DerivedTensorProduct.singleUnitObject Y.toRingedSite q)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                DerivedCategory.Q.obj
                  ((pullbackComplex f).obj (singleUnitComplex Y.O q)))) ≫
          (((𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj K)) ×ₘ
              DerivedCategory.Q.map (pullbackUnitComplexMapDeg f q)) :
              ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                  DerivedCategory.Q.obj
                    ((pullbackComplex f).obj (singleUnitComplex Y.O q))) : _ × _) ⟶
                (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                  DerivedTensorProduct.singleUnitObject X.toRingedSite q)) ≫
            (((flatPullbackIso f hmos K hK hflatK).inv ×ₘ
                𝟙 (DerivedTensorProduct.singleUnitObject X.toRingedSite q)) :
              ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                  DerivedTensorProduct.singleUnitObject X.toRingedSite q) : _ × _) ⟶
                ((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  DerivedTensorProduct.singleUnitObject X.toRingedSite q))) := by
    rw [derivedPullbackSingleUnitMap]
    apply Prod.ext <;> simp
  rw [hsplit, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    singleModelRight_hom]
  simp only [Category.assoc]
  rw [DerivedTensorProduct.singleUnitorIso_uncurry_naturality X.toRingedSite
      (canonicalDerivedTensorProduct X.O) q (flatPullbackIso f hmos K hK hflatK).inv,
    singleUnitorIso_source_eq f K q]
  simp only [Category.assoc]
  rw [reassoc_of% (singleComparisonSource_naturality f hmos K hK hflatK q),
    ← CategoryTheory.Functor.map_comp_assoc,
    singleUnitComparison_mapBifunctorSingleUnitIso f hmos K q,
    CategoryTheory.Functor.map_comp_assoc, CategoryTheory.Functor.map_comp_assoc]

include hK hflatK in
/-- **The shifted-unitor coherence of [Stacks, Tag 07A4] at the image of a K-flat complex with
flat terms.**

Every constituent has a formula there: the comparison of Stacks 07A4 is
`derivedPullbackTensorModelIso`, by `derivedPullbackTensorIso_hom_app_q_models`; the two twisted
unitors are the K-flat comparison of [Stacks, Tag 06YU] followed by the unit law
`Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧` and the commutation of `Q` with the shift, by
`singleUnitorIso_target_eq` and `singleUnitorIso_source_eq`; the unit comparison is the
computation of `Lf^*` on `𝒪_D[q]` followed by the unit comparison on complexes; and the
commutation of `Lf^*` with the shift is `flatPullbackIso_commShift`.  The two halves of the
five-step chain are then `singleModelLeft_inv_singleUnitor` and
`singleModelRight_hom_singleUnitor`, and what they share is the complex-level coherence. -/
theorem derivedPullbackTensorIso_singleUnitor_model :
    (derivedPullbackTensorIso f hmos).hom.app
          (DerivedCategory.Q.obj K,
            DerivedTensorProduct.singleUnitObject Y.toRingedSite q) ≫
        (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
            ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
                derivedPullbackSingleUnitMap f hmos q) :
              (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  (derivedPullback f).obj
                    (DerivedTensorProduct.singleUnitObject Y.toRingedSite q)) : _ × _) ⟶
                ((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  DerivedTensorProduct.singleUnitObject X.toRingedSite q)) ≫
          (DerivedTensorProduct.singleUnitorIso X.toRingedSite
              (canonicalDerivedTensorProduct X.O) q).hom.app
            ((derivedPullback f).obj (DerivedCategory.Q.obj K)) =
      (derivedPullback f).map
          ((DerivedTensorProduct.singleUnitorIso Y.toRingedSite
            (canonicalDerivedTensorProduct Y.O) q).hom.app (DerivedCategory.Q.obj K)) ≫
        ((derivedPullback f).commShiftIso (-q)).hom.app (DerivedCategory.Q.obj K) := by
  have hmodel : (derivedPullbackTensorIso f hmos).hom.app
        (DerivedCategory.Q.obj K,
          DerivedTensorProduct.singleUnitObject Y.toRingedSite q) =
      (singleModelLeft f hmos K hK hflatK q).hom ≫
        (singleModelRight f hmos K hK hflatK q).inv :=
    derivedPullbackTensorIso_hom_app_q_models f hmos
      (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K, hK, hflatK⟩,
        ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (singleUnitComplex Y.O q),
          Stacks.SheafOfModules.isKFlat_single_unit_deg Y.O q, isFlat_single_unit_X_deg Y q⟩)
  rw [hmodel, Category.assoc, singleModelRight_hom_singleUnitor f hmos K hK hflatK q,
    ← singleModelLeft_inv_singleUnitor f hmos K hK hflatK q, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]

end Model

/-! ## The shifted-unitor coherence at every object of the derived category -/

/-- **The shifted-unitor coherence of [Stacks, Tag 07A4].**  For every `Z` in `D(𝒪_D)` the
comparison

`Lf^*(Z ⊗^𝐋_{𝒪_D} 𝒪_D[q]) ⟶ Lf^*Z ⊗^𝐋_{𝒪_C} Lf^*(𝒪_D[q])`

of Stacks 07A4, followed by the unit comparison `Lf^*(𝒪_D[q]) ⟶ 𝒪_C[q]` in the second tensor
factor and by the twisted unitor `Lf^*Z ⊗^𝐋_{𝒪_C} 𝒪_C[q] ≅ (Lf^*Z)⟦-q⟧`, is `Lf^*` of the
twisted unitor on the target followed by the commutation of `Lf^*` with the shift.

There is no hypothesis beyond `f.u.IsMorphismOfSites Y.J X.J`; the quantifier over `Z` is
removed by
`Stacks.AlgebraicGeometry.ProjectionFormula.shiftedUnitorCoherence_of_essSurj` against the
localization functor of the K-flat complexes with flat terms. -/
theorem derivedPullbackTensorIso_singleUnitor (q : ℤ)
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackTensorIso f hmos).hom.app
          (Z, DerivedTensorProduct.singleUnitObject Y.toRingedSite q) ≫
        (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
            ((𝟙 ((derivedPullback f).obj Z) ×ₘ derivedPullbackSingleUnitMap f hmos q) :
              (((derivedPullback f).obj Z,
                  (derivedPullback f).obj
                    (DerivedTensorProduct.singleUnitObject Y.toRingedSite q)) : _ × _) ⟶
                ((derivedPullback f).obj Z,
                  DerivedTensorProduct.singleUnitObject X.toRingedSite q)) ≫
          (DerivedTensorProduct.singleUnitorIso X.toRingedSite
              (canonicalDerivedTensorProduct X.O) q).hom.app ((derivedPullback f).obj Z) =
      (derivedPullback f).map
          ((DerivedTensorProduct.singleUnitorIso Y.toRingedSite
            (canonicalDerivedTensorProduct Y.O) q).hom.app Z) ≫
        ((derivedPullback f).commShiftIso (-q)).hom.app Z := by
  have := flatKFlatModelsQ_isLocalization Y
  have : (flatKFlatModelsQ Y).EssSurj :=
    Localization.essSurj (flatKFlatModelsQ Y) (flatKFlatModelsW Y)
  have key := fun {Z Z' : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} (i : Z ≅ Z') h =>
    Stacks.AlgebraicGeometry.ProjectionFormula.shiftedUnitorCoherence_of_iso
    (Functor.uncurry.obj (canonicalDerivedTensorProduct Y.O).tensor)
    (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor)
    (derivedPullbackTensorIso f hmos).hom
    (fun W => (DerivedTensorProduct.singleUnitorIso Y.toRingedSite
      (canonicalDerivedTensorProduct Y.O) q).app W)
    (fun W => (DerivedTensorProduct.singleUnitorIso X.toRingedSite
      (canonicalDerivedTensorProduct X.O) q).app W)
    ((derivedPullback f).commShiftIso (-q)).hom
    (derivedPullbackSingleUnitMap f hmos q)
    (fun u => DerivedTensorProduct.singleUnitorIso_uncurry_naturality Y.toRingedSite
      (canonicalDerivedTensorProduct Y.O) q u)
    (fun u => DerivedTensorProduct.singleUnitorIso_uncurry_naturality X.toRingedSite
      (canonicalDerivedTensorProduct X.O) q u) i h
  refine key ((flatKFlatModelsQ Y).objObjPreimageIso Z).symm ?_
  set e := (flatKFlatModelsQ Y).objPreimage Z
  exact key ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app e.obj.as)
    (derivedPullbackTensorIso_singleUnitor_model f hmos e.obj.as e.property.1 e.property.2 q)

end Stacks.Sheaves.DerivedPullback

/-! ## The base case of Stacks 0944 at the structure sheaf in every degree -/

namespace Stacks.Cohomology.ProjectionFormulaOnRingedTopoi

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **Equation 21.50.0.1 of [Stacks, Tag 0B56] is invertible at `Q(𝒪_D[q])` for every `q`.**

This is
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_shiftedUnitObj` with all
four of its inputs supplied: the two twisted unitors
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso`, the naturality of the one
on `D(𝒪_C)`, the unit comparison
`Stacks.Sheaves.DerivedPullback.derivedPullbackSingleUnitMap`, and the shifted-unitor coherence
of [Stacks, Tag 07A4], which is
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_singleUnitor`. -/
theorem isIso_projectionFormulaMap_singleUnitComplex (q : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (projectionFormulaMap f hmos E
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitObject
        Y.toRingedSite q)) := by
  have := Stacks.Sheaves.DerivedPullback.isIso_derivedPullbackSingleUnitMap f hmos q
  exact Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_shiftedUnitObj
    (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj (canonicalDerivedTensorProduct Y.O).tensor)
    (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom (-q)
    (fun W => (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso
      Y.toRingedSite (canonicalDerivedTensorProduct Y.O) q).app W)
    (fun W => (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso
      X.toRingedSite (canonicalDerivedTensorProduct X.O) q).app W)
    (asIso (Stacks.Sheaves.DerivedPullback.derivedPullbackSingleUnitMap f hmos q))
    (fun u =>
      Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso_uncurry_naturality
        X.toRingedSite (canonicalDerivedTensorProduct X.O) q u)
    (fun Z => Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_singleUnitor f hmos q Z) E

/-- **The base case of [Stacks, Tag 0944]: Equation 21.50.0.1 is invertible at the structure
sheaf placed in every degree.**

This is what the dévissage `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit` of
`Stacks.Cohomology.ProjectionFormulaPerfectDevissage` asks for, so with it [Stacks, Tag 0944]
holds at every shift of every strictly perfect complex.

Nothing is assumed beyond `f` being a morphism of ringed topoi presented by a morphism of sites.
The *ordinary* comparison `f^*𝒪_D ⟶ 𝒪_C` of Mathlib's `SheafOfModules.pullbackObjUnitToUnit`,
which the unit comparison in the derived category is built from, is invertible along a morphism of
sites by `Stacks.Sites.UnitComparison.isIso_pullbackObjUnitToUnit_of_isMorphismOfSites`, and the
shifted-unitor coherence this is read off from is unconditional. -/
theorem isIso_projectionFormulaMap_singleUnit
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (i : ℤ) :
    IsIso (projectionFormulaMap f hmos E
      (Stacks.Cohomology.ProjectionFormulaPerfectDevissage.singleUnit Y.O i)) :=
  isIso_projectionFormulaMap_singleUnitComplex f hmos i E

/-- **[Stacks, Tag 0944] at every shift of every strictly perfect complex.**  Equation
21.50.0.1 of [Stacks, Tag 0B56],

`Rf_*E ⊗^𝐋_{𝒪_D} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_C} Lf^*K)`,

is invertible for `K` a shift of a strictly perfect complex of `𝒪_D`-modules, for every `E` in
`D(𝒪_C)`.

This is the dévissage `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit` of
`Stacks.Cohomology.ProjectionFormulaPerfectDevissage` with its base case
`isIso_projectionFormulaMap_singleUnit` supplied.  Nothing is assumed beyond `f` being a morphism
of ringed topoi presented by a morphism of sites: the invertibility of the ordinary comparison
`f^*𝒪_D ⟶ 𝒪_C` that the base case rests on is itself a consequence of that, by
`Stacks.Sites.UnitComparison.isIso_pullbackObjUnitToUnit_of_isMorphismOfSites`. -/
theorem isIso_projectionFormulaMap_isStrictlyPerfect
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (n : ℤ) :
    IsIso (projectionFormulaMap f hmos E ((DerivedCategory.Q.obj P)⟦n⟧)) :=
  ProjectionFormulaPerfectDevissage.isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit
    f hmos E (fun i => isIso_projectionFormulaMap_singleUnit f hmos E i) P hP n

end Stacks.Cohomology.ProjectionFormulaOnRingedTopoi

end
