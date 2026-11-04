module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.AlgebraicGeometry.Duality.RightUnitorCoherenceInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorRightUnitor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-! # The right-unitor coherence of Stacks 07A4 in the derived category

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor of
the underlying sites which is a morphism of sites.  **Stacks 07A4** is the bifunctorial
isomorphism

`Lf^*(K ⊗^𝐋_{𝒪_D} L) ≅ Lf^*K ⊗^𝐋_{𝒪_C} Lf^*L`

of `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`, produced by
`CategoryTheory.Localization.liftNatIso` out of its values on pairs of K-flat complexes with
flat terms.  This file proves its **right-unitor coherence**: for every `Z` in `D(𝒪_D)` the
comparison at `(Z, 𝒪_D[0])`, followed by the unit comparison `Lf^*(𝒪_D[0]) ⟶ 𝒪_C[0]` in the
second tensor factor and by the right unit constraint of `⊗^𝐋_{𝒪_C}`, is `Lf^*` of the right
unit constraint of `⊗^𝐋_{𝒪_D}`.

That equation is the one missing input of the **base case `K = 𝒪_D[0]` of Stacks 0944**, which is
derived from it below.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_rightUnitor`: **the right-unitor
  coherence of Stacks 07A4**, at every object of `D(𝒪_D)`, under no hypothesis beyond
  `f.u.IsMorphismOfSites Y.J X.J`.  The unit comparison in it is
  `Stacks.Sheaves.DerivedPullback.derivedPullbackUnitMap`, a morphism; no invertibility of it is
  assumed.
* `Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.isIso_projectionFormulaMap_unitObject`:
  **the base case of Stacks 0944 at `K = 𝒪_D[0]`** — Equation 21.50.0.1 of Stacks 0B56 is
  invertible there, for every `E` in `D(𝒪_C)`, given that the *ordinary* comparison
  `f^*𝒪_D ⟶ 𝒪_C` of Mathlib's `SheafOfModules.pullbackObjUnitToUnit` is invertible.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_q_models`: the comparison of
  Stacks 07A4 at a pair of K-flat complexes with flat terms is the five-step composite
  `derivedPullbackTensorModelIso` of representatives.  This is what the lift
  `CategoryTheory.Localization.liftNatIso` adds nothing to.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_rightUnitor_model`: the coherence at
  the image of a K-flat complex with flat terms, which is where every constituent has a formula.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_uncurry_naturality`: the
  naturality of the right unit constraint of a derived tensor product, with the tensor product
  read as a functor on the product category — the shape the projection formula consumes.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_app_q`: the value of
  that constraint at the image of a complex — the right K-flat comparison of Stacks 06YU
  followed by `Q` of the unit law of Tag 06YM.

## Implementation notes

**The shape of the proof.**  Both sides of the coherence are morphisms out of
`Lf^*(Z ⊗^𝐋_{𝒪_D} 𝒪_D[0])`, and at a general `Z` neither has a formula: the comparison of
Stacks 07A4 is a lift along a localization.  The quantifier over `Z` is removed first, by
`Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherenceHom_of_essSurj`, against the
localization functor `Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ` of the K-flat complexes
with flat terms — essentially surjective because it is a localization functor.  At `Z = QK` for
such a `K` every constituent is computable:

* the comparison of Stacks 07A4 is `derivedPullbackTensorModelIso`, by
  `derivedPullbackTensorIso_hom_app_q_models`;
* the two right unit constraints are the right K-flat comparison followed by `Q` of the unit law
  `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` of Tag 06YM, by
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_app_q`, which is
  `rightUnitIso_hom_eq` composed with `rightUnitTrans_app_Q`;
* the unit comparison is the computation of `Lf^*` on the K-flat complex `𝒪_D[0]` followed by
  `Q` of the unit comparison on complexes, by `derivedPullbackUnitMap_eq_flatPullbackIso`.

What is left is an identity of morphisms of complexes, and it is exactly the complex-level
right-unitor coherence
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_rightUnitor`.  The passage from it to
the derived identity is: the naturality of
`Stacks.Sheaves.DerivedPullback.flatPullbackIso` in the complex (which moves `Lf^*` of the unit
law past the computation of `Lf^*`), the naturality of the K-flat comparison of Stacks 06YU in
the right variable (`comparisonRight_naturality` with an identity on the left), and the
bifunctoriality of `⊗^𝐋_{𝒪_C}` (which moves the computation of `Lf^*` on `K` through the first
tensor factor).  No new mathematics enters at the derived level.

**The seams, and the ascriptions that absorb them.**  Five pairs of spellings meet here, each a
definitional equality that unfolds a semireducible definition and that `rw` therefore does not
see: the structure sheaf in degree zero as
`Stacks.DerivedTensor.RingedSite.unitComplex` against
`Stacks.Sheaves.DerivedPullback.unitComplexTarget` / `unitComplexSource`; the unit *object* of
`⊗^𝐋_𝒪` as `DerivedCategory.singleFunctor` of the structure sheaf against `Q` of that complex;
the target of the K-flat comparison of Stacks 06YU spelled with
`Stacks.SheafOfModules.Tensor.tensorComplex` against `HomologicalComplex.mapBifunctor`;
K-flatness as `Stacks.SheafOfModules.IsKFlat` against
`CochainComplex.KFlatBifunctor.KFlat`; and the derived tensor bifunctor named through the
abbreviation `derivedTensorProductFunctor` against the field `DerivedTensorProduct.tensor`.

The cure is the one this directory prescribes: *declare the crossing once, in a type*.
`unitComplexComparison`, `kFlat_unitComplexTarget`, `isFlat_unitComplexTarget`,
`unitFlatPullbackIso`, `unitTensorComparisonTarget`, `totalFlatPullbackIso`,
`unitTensorComparisonSource`, `unitComparisonSource`, `unitModelLeft` and `unitModelRight` are
the ten aliases that let every statement below be written in one spelling, and each crossing is
paid exactly once, by `rfl` or `exact`, inside the lemma that introduces the alias.  Every
rewrite below then happens between declared types, and the bifunctor is always named by its
field.

**Which right unit constraint.**  The one of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso` (Stacks 0FPT), whose value on
the image of a complex is the unit law `Stacks.SheafOfModules.tensorComplexUnitIso` of Tag 06YM —
the very isomorphism the complex-level coherence is stated about.  The other right unitor of this
repository, `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RightUnitorNaturality.lean`, is built
from the right unitor of Mathlib's monoidal structure on complexes instead, and no identification
of the two is available; using it would owe that identification and nothing else.

**What the base case carries, and what it does not.**  The coherence itself is unconditional.
The base case of Stacks 0944 needs the unit comparison to be *invertible*, because the
invertibility of Equation 21.50.0.1 at the unit object is read off from the coherence by
inverting `Rf_*(𝟙 ⊗ ν)`; so `isIso_projectionFormulaMap_unitObject` takes the invertibility of
the ordinary comparison `f^*𝒪_D ⟶ 𝒪_C` as a hypothesis, exactly as the ringed-space analogue
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject` takes an
isomorphism `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` as a parameter.  Mathlib proves
`SheafOfModules.pullbackObjUnitToUnit` invertible when the functor presenting `f` is final; no
unconditional proof of it exists in this repository.

**Only the degree zero.**  The dévissage of Stacks 0944 —
`isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit` of
`Stacks.Cohomology.ProjectionFormulaPerfectDevissage` — asks for invertibility at `𝒪_D[i]` for
*every* degree `i`, and what is proved here is the degree
`i = 0`, where `𝒪_D[0]` is the unit object of `⊗^𝐋_{𝒪_D}` and the right unit constraint applies.
For `i ≠ 0` the constraint to use is `Z ⊗^𝐋_{𝒪_D} 𝒪_D[i] ≅ Z⟦-i⟧` rather than `Z`, which is not
a right unitor; it is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso`, and the coherence it
satisfies — which carries the commutation of `Lf^*` with the shift in place of nothing — is
proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/ProjectionFormulaSingleUnit.lean`,
where the dévissage is fed in every degree.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Sheaves.DerivedPullback.KFlatPullback

open scoped CategoryTheory.Prod

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

variable (Z : RingedSite.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Z.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Z.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules Z.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct Z.O)

/-- **Naturality of the right unit constraint of `⊗^𝐋_𝒪`, with the tensor product read as a
functor on the product category.**  This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality` with `u ⊗ 𝟙 𝒪`
written as the image of `(u, 𝟙 𝒪)` under `CategoryTheory.Functor.uncurry` of the derived tensor
bifunctor, which is the shape the projection formula and the right-unitor coherence consume. -/
theorem rightUnitIso_uncurry_naturality {A B : DerivedModules Z.O} (u : A ⟶ B) :
    (Functor.uncurry.obj T.tensor).map
          ((u ×ₘ 𝟙 (unitObject Z)) :
            ((A, unitObject Z) : _ × _) ⟶ (B, unitObject Z)) ≫
        (T.rightUnitIso Z B).hom =
      (T.rightUnitIso Z A).hom ≫ u := by
  rw [Functor.uncurry_obj_map, (T.tensor.obj B).map_id, Category.comp_id]
  exact rightUnitIso_hom_naturality Z T u

/-- **The right unit constraint at the image of a complex** is the right K-flat comparison of
Stacks 06YU against the K-flat complex `𝒪[0]`, followed by `Q` of the unit law
`Tot(K ⊗_𝒪 𝒪[0]) ≅ K` of Tag 06YM.  This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_eq` composed with
`rightUnitTrans_app_Q`; no K-flat model of `K` is chosen, because the right factor is already
K-flat. -/
theorem rightUnitIso_hom_app_q (K : CochainComplex (Modules Z.O) ℤ) :
    (T.rightUnitIso Z (DerivedCategory.Q.obj K)).hom =
      (T.comparisonRight K (unitComplex Z)
          (Stacks.SheafOfModules.isKFlat_single_unit Z.O)).hom ≫
        DerivedCategory.Q.map (Stacks.SheafOfModules.tensorComplexUnitIso Z.O K).hom :=
  (rightUnitIso_hom_eq Z T (DerivedCategory.Q.obj K)).trans (rightUnitTrans_app_Q Z T K)

end Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

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

/-! ## The unit comparison on complexes, at the spelling of the derived tensor product -/

/-- **The unit comparison `f^*(𝒪_D[0]) ⟶ 𝒪_C[0]` on complexes**, with its source and target
spelled through `Stacks.DerivedTensor.RingedSite.unitComplex`, which is the spelling the derived
tensor product and its right unit constraint are stated at.  This is
`Stacks.Sheaves.DerivedPullback.pullbackUnitComplexMap` and the spelling is the only difference;
declaring it once absorbs the crossing into a declared type. -/
def unitComplexComparison :
    (pullbackComplex f).obj (unitComplex Y.toRingedSite) ⟶ unitComplex X.toRingedSite :=
  pullbackUnitComplexMap f

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **`𝒪_D[0]` is K-flat**, at the spelling `Stacks.Sheaves.DerivedPullback.flatPullbackIso`
consumes.  This is `Stacks.SheafOfModules.isKFlat_single_unit`; declaring it once keeps the
crossing between the two spellings of K-flatness out of the goals below. -/
theorem kFlat_unitComplexTarget :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (unitComplex Y.toRingedSite) :=
  Stacks.SheafOfModules.isKFlat_single_unit Y.O

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **`𝒪_D[0]` has flat terms**, at the `Stacks.DerivedTensor.RingedSite.unitComplex` spelling.
This is `Stacks.Sheaves.DerivedPullback.isFlat_single_unit_X`. -/
theorem isFlat_unitComplexTarget (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      ((unitComplex Y.toRingedSite).X i) :=
  isFlat_single_unit_X Y i

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **The right-unitor coherence of the comparison of total tensor complexes**, restated at the
`Stacks.DerivedTensor.RingedSite.unitComplex` spelling of the structure sheaf in degree zero.
This is `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_rightUnitor`, and the
spelling is the only difference. -/
theorem pullbackToposTensorTotalIso_unitComplex_rightUnitor
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackToposTensorTotalIso f hmos K (unitComplex Y.toRingedSite)).hom ≫
        HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
            (unitComplexComparison f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ) ≫
          (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom =
      (pullbackComplex f).map (mapBifunctorUnitIso Y.O K).hom :=
  pullbackToposTensorTotalIso_rightUnitor f hmos K

/-- **The identity of morphisms of complexes behind the coherence**, with the comparison of total
tensor complexes moved to the other side.  This is
`pullbackToposTensorTotalIso_unitComplex_rightUnitor` with one isomorphism cancelled. -/
theorem unitComplexComparison_mapBifunctorUnitIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (unitComplexComparison f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) ≫
        (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom =
      (pullbackToposTensorTotalIso f hmos K (unitComplex Y.toRingedSite)).inv ≫
        (pullbackComplex f).map (mapBifunctorUnitIso Y.O K).hom := by
  rw [← pullbackToposTensorTotalIso_unitComplex_rightUnitor f hmos K, Iso.inv_hom_id_assoc]

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))]

/-- **The computation of `Lf^*` on the K-flat complex `𝒪_D[0]` with flat terms**, with its
source spelled as `Lf^*` of the unit object of `⊗^𝐋_{𝒪_D}`.  This is
`Stacks.Sheaves.DerivedPullback.flatPullbackIso`, and the spelling of the source is the only
difference: `Stacks.DerivedTensor.RingedSite.unitObject` is
`DerivedCategory.singleFunctor` of the structure sheaf while `flatPullbackIso` has
`Q` of a complex, and the two agree only by unfolding `DerivedCategory.singleFunctors`. -/
def unitFlatPullbackIso :
    (derivedPullback f).obj (unitObject Y.toRingedSite) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj (unitComplex Y.toRingedSite)) :=
  flatPullbackIso f hmos (unitComplex Y.toRingedSite) (kFlat_unitComplexTarget (Y := Y))
    (isFlat_unitComplexTarget (Y := Y))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The unit comparison `Lf^*(𝒪_D[0]) ⟶ 𝒪_C[0]` is the computation of `Lf^*` on the K-flat
complex `𝒪_D[0]` followed by the unit comparison on complexes.**  Both legs of
`Stacks.Sheaves.DerivedPullback.derivedPullbackUnitMap` live over the complex `𝒪_D[0]`, and
`DerivedCategory.singleFunctor` is `HomologicalComplex.single` followed by `Q`, so the second leg
is `Q` of a morphism of complexes; collecting the two is what this says. -/
theorem derivedPullbackUnitMap_eq_flatPullbackIso :
    derivedPullbackUnitMap f hmos =
      (unitFlatPullbackIso f hmos).hom ≫
        DerivedCategory.Q.map (unitComplexComparison f) := by
  rw [unitComplexComparison, pullbackUnitComplexMap, Functor.map_comp, derivedPullbackUnitMap_eq,
    derivedPullbackSingleUnitIso, unitFlatPullbackIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Category.assoc]
  rfl

/-! ## The comparison of Stacks 07A4 on a pair of K-flat complexes with flat terms -/

/-- **The comparison of Stacks 07A4 at a pair of K-flat complexes with flat terms** is the
five-step composite `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorModelIso` of the
source's proof.

The lift `CategoryTheory.Localization.liftNatIso` adds nothing at an object of the form
`flatKFlatModelPairsQ.obj P`, because the two `CategoryTheory.Localization.Lifting` instances it
is given have the identity as their isomorphism; the value at the pair `(QK, QL)` of images is
then read off by naturality of the comparison along
`Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso`. -/
theorem derivedPullbackTensorIso_hom_app_q_models
    (P : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory) :
    (derivedPullbackTensorIso f hmos).hom.app
        (DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) =
      (derivedPullbackTensorModelIso f hmos P.1.obj.as P.2.obj.as
        P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2).hom := by
  have h1 : (derivedPullbackTensorIso f hmos).hom.app ((flatKFlatModelPairsQ Y).obj P) =
      (flatKFlatModelPairsTensorIso f hmos).hom.app P := by
    dsimp only [derivedPullbackTensorIso, Localization.liftNatIso]
    rw [Localization.liftNatTrans_app]
    simp [Localization.Lifting.iso]
  have hpe : IsIso ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O) ⋙
      derivedPullback f).map (flatKFlatModelPairsIso Y P).hom) :=
    ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O) ⋙
      derivedPullback f).mapIso (flatKFlatModelPairsIso Y P)).isIso_hom
  apply (cancel_epi ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O) ⋙
    derivedPullback f).map (flatKFlatModelPairsIso Y P).hom)).1
  rw [(derivedPullbackTensorIso f hmos).hom.naturality
    (flatKFlatModelPairsIso Y P).hom, h1]
  dsimp only [flatKFlatModelPairsTensorIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv]
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-! ## The coherence at the image of a K-flat complex with flat terms -/

section Model

variable
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflatK : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))

/-- **The K-flat comparison of Stacks 06YU at `(K, 𝒪_D[0])`**, with its source spelled at the
unit object of `⊗^𝐋_{𝒪_D}` and its target with `HomologicalComplex.mapBifunctor`.  This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison`; the ascription is what lets
the reassociations below be found by `rw`. -/
def unitTensorComparisonTarget :
    ((canonicalDerivedTensorProduct Y.O).tensor.obj (DerivedCategory.Q.obj K)).obj
        (unitObject Y.toRingedSite) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K (unitComplex Y.toRingedSite)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) :=
  (canonicalDerivedTensorProduct Y.O).comparison K (unitComplex Y.toRingedSite) hK
    (kFlat_unitComplexTarget (Y := Y))

/-- **The computation of `Lf^*` on the total tensor complex `Tot(K ⊗_{𝒪_D} 𝒪_D[0])`**, which is
again K-flat with flat terms.  This is `Stacks.Sheaves.DerivedPullback.flatPullbackIso`, declared
once so that its two witnesses stay out of the goals. -/
def totalFlatPullbackIso :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K (unitComplex Y.toRingedSite)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj
        (HomologicalComplex.mapBifunctor K (unitComplex Y.toRingedSite)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
  flatPullbackIso f hmos
    (HomologicalComplex.mapBifunctor K (unitComplex Y.toRingedSite)
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK (kFlat_unitComplexTarget (Y := Y)))
    (isFlat_tensorComplex_X Y.O K (unitComplex Y.toRingedSite) hflatK
      (isFlat_unitComplexTarget (Y := Y)))

/-- **The K-flat comparison of Stacks 06YU at the pair of degreewise pullbacks**, with its target
spelled with `HomologicalComplex.mapBifunctor`. -/
def unitTensorComparisonSource :
    ((canonicalDerivedTensorProduct X.O).tensor.obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj (unitComplex Y.toRingedSite))) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K)
        ((pullbackComplex f).obj (unitComplex Y.toRingedSite))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (canonicalDerivedTensorProduct X.O).comparison ((pullbackComplex f).obj K)
    ((pullbackComplex f).obj (unitComplex Y.toRingedSite))
    (kFlat_pullbackComplex' f hmos K hK hflatK)
    (kFlat_pullbackComplex' f hmos (unitComplex Y.toRingedSite) (kFlat_unitComplexTarget (Y := Y))
      (isFlat_unitComplexTarget (Y := Y)))

/-- **The right K-flat comparison of Stacks 06YU at `(f^*K, 𝒪_C[0])`**, with its source spelled
at the unit object of `⊗^𝐋_{𝒪_C}` and its target with `HomologicalComplex.mapBifunctor`. -/
def unitComparisonSource :
    ((canonicalDerivedTensorProduct X.O).tensor.obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).obj
        (unitObject X.toRingedSite) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K)
        (unitComplex X.toRingedSite)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (canonicalDerivedTensorProduct X.O).comparisonRight ((pullbackComplex f).obj K)
    (unitComplex X.toRingedSite) (Stacks.SheafOfModules.isKFlat_single_unit X.O)

/-- **The first half of the five-step chain of Stacks 07A4 at `(K, 𝒪_D[0])`**, with its source
spelled at the unit object.  This is
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorModelLeft`. -/
def unitModelLeft :
    (derivedPullback f).obj
        (((canonicalDerivedTensorProduct Y.O).tensor.obj (DerivedCategory.Q.obj K)).obj
          (unitObject Y.toRingedSite)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj
        (HomologicalComplex.mapBifunctor K (unitComplex Y.toRingedSite)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
  derivedPullbackTensorModelLeft f hmos K (unitComplex Y.toRingedSite) hK
    (kFlat_unitComplexTarget (Y := Y)) hflatK (isFlat_unitComplexTarget (Y := Y))

/-- **The second half of the five-step chain of Stacks 07A4 at `(K, 𝒪_D[0])`**, with its source
spelled at the unit object.  This is
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorModelRight`. -/
def unitModelRight :
    ((canonicalDerivedTensorProduct X.O).tensor.obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj K))).obj
        ((derivedPullback f).obj (unitObject Y.toRingedSite)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj
        (HomologicalComplex.mapBifunctor K (unitComplex Y.toRingedSite)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
  derivedPullbackTensorModelRight f hmos K (unitComplex Y.toRingedSite) hK
    (kFlat_unitComplexTarget (Y := Y)) hflatK (isFlat_unitComplexTarget (Y := Y))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The first half of the chain is `Lf^*` of the K-flat comparison on the target followed by the
computation of `Lf^*` on the total tensor complex. -/
theorem unitModelLeft_inv :
    (unitModelLeft f hmos K hK hflatK).inv =
      (totalFlatPullbackIso f hmos K hK hflatK).inv ≫
        (derivedPullback f).map (unitTensorComparisonTarget K hK).inv :=
  rfl

/-- The second half of the chain is the pair of computations of `Lf^*`, then the K-flat
comparison on the source, then the comparison of total tensor complexes read backwards. -/
theorem unitModelRight_hom :
    (unitModelRight f hmos K hK hflatK).hom =
      (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
          (((flatPullbackIso f hmos K hK hflatK).hom ×ₘ (unitFlatPullbackIso f hmos).hom) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj (unitObject Y.toRingedSite)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                DerivedCategory.Q.obj
                  ((pullbackComplex f).obj (unitComplex Y.toRingedSite)))) ≫
        (unitTensorComparisonSource f hmos K hK hflatK).hom ≫
          DerivedCategory.Q.map
            (pullbackToposTensorTotalIso f hmos K (unitComplex Y.toRingedSite)).inv :=
  rfl

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The right unit constraint of `⊗^𝐋_{𝒪_D}` at `QK`**, in the ascribed spellings: the K-flat
comparison of Stacks 06YU followed by `Q` of the unit law of Tag 06YM. -/
theorem rightUnitIso_target_eq :
    ((canonicalDerivedTensorProduct Y.O).rightUnitIso Y.toRingedSite
        (DerivedCategory.Q.obj K)).hom =
      (unitTensorComparisonTarget K hK).hom ≫
        DerivedCategory.Q.map (mapBifunctorUnitIso Y.O K).hom := by
  rw [DerivedTensorProduct.rightUnitIso_hom_app_q,
    (canonicalDerivedTensorProduct Y.O).comparisonRight_eq_comparison K
      (unitComplex Y.toRingedSite) hK (kFlat_unitComplexTarget (Y := Y))]
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
/-- **The right unit constraint of `⊗^𝐋_{𝒪_C}` at `Q(f^*K)`**, in the ascribed spellings. -/
theorem rightUnitIso_source_eq :
    ((canonicalDerivedTensorProduct X.O).rightUnitIso X.toRingedSite
        (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).hom =
      (unitComparisonSource f K).hom ≫
        DerivedCategory.Q.map (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom :=
  DerivedTensorProduct.rightUnitIso_hom_app_q X.toRingedSite
    (canonicalDerivedTensorProduct X.O) ((pullbackComplex f).obj K)

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
/-- **The right K-flat comparison of Stacks 06YU is natural in the degreewise unit comparison**,
in the ascribed spellings.  This is the field `comparisonRight_naturality` at the identity of
`f^*K` in the first variable, with the right comparison at the pair of degreewise pullbacks
rewritten as the two-sided one. -/
theorem unitComparisonSource_naturality :
    (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
        ((𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj K)) ×ₘ
            DerivedCategory.Q.map (unitComplexComparison f)) :
          ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              DerivedCategory.Q.obj
                ((pullbackComplex f).obj (unitComplex Y.toRingedSite))) : _ × _) ⟶
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              unitObject X.toRingedSite)) ≫
      (unitComparisonSource f K).hom =
    (unitTensorComparisonSource f hmos K hK hflatK).hom ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
        (𝟙 ((pullbackComplex f).obj K)) (unitComplexComparison f)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  have h := (canonicalDerivedTensorProduct X.O).comparisonRight_naturality
    (𝟙 ((pullbackComplex f).obj K)) (unitComplexComparison f)
    (kFlat_pullbackComplex' f hmos (unitComplex Y.toRingedSite)
      (kFlat_unitComplexTarget (Y := Y)) (isFlat_unitComplexTarget (Y := Y)))
    (Stacks.SheafOfModules.isKFlat_single_unit X.O)
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp,
    (canonicalDerivedTensorProduct X.O).comparisonRight_eq_comparison
      ((pullbackComplex f).obj K) ((pullbackComplex f).obj (unitComplex Y.toRingedSite))
      (kFlat_pullbackComplex' f hmos K hK hflatK)
      (kFlat_pullbackComplex' f hmos (unitComplex Y.toRingedSite)
        (kFlat_unitComplexTarget (Y := Y)) (isFlat_unitComplexTarget (Y := Y)))] at h
  rw [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  exact h

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The computation of `Lf^*` is natural in the unit law of Tag 06YM**, in the ascribed
spellings.  This is `Stacks.Sheaves.DerivedPullback.flatPullbackIso_naturality`. -/
theorem totalFlatPullbackIso_naturality :
    (derivedPullback f).map
          (DerivedCategory.Q.map (mapBifunctorUnitIso Y.O K).hom) ≫
        (flatPullbackIso f hmos K hK hflatK).hom =
      (totalFlatPullbackIso f hmos K hK hflatK).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (mapBifunctorUnitIso Y.O K).hom) :=
  flatPullbackIso_naturality f hmos (mapBifunctorUnitIso Y.O K).hom
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK (kFlat_unitComplexTarget (Y := Y))) hK
    (isFlat_tensorComplex_X Y.O K (unitComplex Y.toRingedSite) hflatK
      (isFlat_unitComplexTarget (Y := Y))) hflatK

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The first half of the chain, read backwards against `Lf^*` of the right unit constraint on
the target.** -/
theorem unitModelLeft_inv_rightUnitor :
    (unitModelLeft f hmos K hK hflatK).inv ≫
        (derivedPullback f).map
          (((canonicalDerivedTensorProduct Y.O).rightUnitIso Y.toRingedSite
            (DerivedCategory.Q.obj K)).hom) =
      DerivedCategory.Q.map ((pullbackComplex f).map (mapBifunctorUnitIso Y.O K).hom) ≫
        (flatPullbackIso f hmos K hK hflatK).inv := by
  rw [unitModelLeft_inv, rightUnitIso_target_eq K hK, CategoryTheory.Functor.map_comp,
    Category.assoc, ← Category.assoc ((derivedPullback f).map _) ((derivedPullback f).map _),
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_comp_eq, ← Category.assoc,
    ← totalFlatPullbackIso_naturality f hmos K hK hflatK, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **The second half of the chain, against the unit comparison and the right unit constraint on
the source.** -/
theorem unitModelRight_hom_rightUnitor :
    (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
          ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
              derivedPullbackUnitMap f hmos) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj (unitObject Y.toRingedSite)) : _ × _) ⟶
              ((derivedPullback f).obj (DerivedCategory.Q.obj K),
                unitObject X.toRingedSite)) ≫
        ((canonicalDerivedTensorProduct X.O).rightUnitIso X.toRingedSite
          ((derivedPullback f).obj (DerivedCategory.Q.obj K))).hom =
      (unitModelRight f hmos K hK hflatK).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (mapBifunctorUnitIso Y.O K).hom) ≫
          (flatPullbackIso f hmos K hK hflatK).inv := by
  have hsplit :
      ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
            derivedPullbackUnitMap f hmos) :
          (((derivedPullback f).obj (DerivedCategory.Q.obj K),
              (derivedPullback f).obj (unitObject Y.toRingedSite)) : _ × _) ⟶
            ((derivedPullback f).obj (DerivedCategory.Q.obj K),
              unitObject X.toRingedSite)) =
        (((flatPullbackIso f hmos K hK hflatK).hom ×ₘ (unitFlatPullbackIso f hmos).hom) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj (unitObject Y.toRingedSite)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                DerivedCategory.Q.obj
                  ((pullbackComplex f).obj (unitComplex Y.toRingedSite)))) ≫
          (((𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj K)) ×ₘ
              DerivedCategory.Q.map (unitComplexComparison f)) :
              ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                  DerivedCategory.Q.obj
                    ((pullbackComplex f).obj (unitComplex Y.toRingedSite))) : _ × _) ⟶
                (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                  unitObject X.toRingedSite)) ≫
            (((flatPullbackIso f hmos K hK hflatK).inv ×ₘ
                𝟙 (unitObject X.toRingedSite)) :
              ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                  unitObject X.toRingedSite) : _ × _) ⟶
                ((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  unitObject X.toRingedSite))) := by
    rw [derivedPullbackUnitMap_eq_flatPullbackIso]
    apply Prod.ext <;> simp
  rw [hsplit, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    unitModelRight_hom]
  simp only [Category.assoc]
  rw [DerivedTensorProduct.rightUnitIso_uncurry_naturality X.toRingedSite
      (canonicalDerivedTensorProduct X.O) (flatPullbackIso f hmos K hK hflatK).inv,
    rightUnitIso_source_eq f K]
  simp only [Category.assoc]
  rw [reassoc_of% (unitComparisonSource_naturality f hmos K hK hflatK),
    ← CategoryTheory.Functor.map_comp_assoc,
    unitComplexComparison_mapBifunctorUnitIso f hmos K,
    CategoryTheory.Functor.map_comp_assoc]

include hK hflatK in
/-- **The right-unitor coherence of Stacks 07A4 at the image of a K-flat complex with flat
terms.**

Every constituent has a formula there: the comparison of Stacks 07A4 is
`derivedPullbackTensorModelIso`, by `derivedPullbackTensorIso_hom_app_q_models`; the two right
unit constraints are the right K-flat comparison of Stacks 06YU followed by the unit law of
Tag 06YM, by `rightUnitIso_target_eq` and `rightUnitIso_source_eq`; and the unit comparison is
the computation of `Lf^*` on `𝒪_D[0]` followed by the unit comparison on complexes, by
`derivedPullbackUnitMap_eq_flatPullbackIso`.  The two halves of the five-step chain are then
`unitModelLeft_inv_rightUnitor` and `unitModelRight_hom_rightUnitor`, and what they share is the
complex-level coherence. -/
theorem derivedPullbackTensorIso_rightUnitor_model :
    (derivedPullbackTensorIso f hmos).hom.app
          (DerivedCategory.Q.obj K, unitObject Y.toRingedSite) ≫
        (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
            ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
                derivedPullbackUnitMap f hmos) :
              (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  (derivedPullback f).obj (unitObject Y.toRingedSite)) : _ × _) ⟶
                ((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  unitObject X.toRingedSite)) ≫
          ((canonicalDerivedTensorProduct X.O).rightUnitIso X.toRingedSite
            ((derivedPullback f).obj (DerivedCategory.Q.obj K))).hom =
      (derivedPullback f).map
        (((canonicalDerivedTensorProduct Y.O).rightUnitIso Y.toRingedSite
          (DerivedCategory.Q.obj K)).hom) := by
  have hmodel : (derivedPullbackTensorIso f hmos).hom.app
        (DerivedCategory.Q.obj K, unitObject Y.toRingedSite) =
      (unitModelLeft f hmos K hK hflatK).hom ≫ (unitModelRight f hmos K hK hflatK).inv :=
    derivedPullbackTensorIso_hom_app_q_models f hmos
      (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K, hK, hflatK⟩,
        ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (unitComplex Y.toRingedSite),
          kFlat_unitComplexTarget (Y := Y), isFlat_unitComplexTarget (Y := Y)⟩)
  rw [hmodel, Category.assoc, unitModelRight_hom_rightUnitor f hmos K hK hflatK,
    ← unitModelLeft_inv_rightUnitor f hmos K hK hflatK, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]

end Model

/-! ## The coherence at every object of the derived category -/

/-- **The right-unitor coherence of Stacks 07A4.**  For every `Z` in `D(𝒪_D)`, the comparison

`Lf^*(Z ⊗^𝐋_{𝒪_D} 𝒪_D[0]) ⟶ Lf^*Z ⊗^𝐋_{𝒪_C} Lf^*(𝒪_D[0])`

of Stacks 07A4, followed by the unit comparison `Lf^*(𝒪_D[0]) ⟶ 𝒪_C[0]` in the second tensor
factor and by the right unit constraint of `⊗^𝐋_{𝒪_C}`, is `Lf^*` of the right unit constraint
of `⊗^𝐋_{𝒪_D}`.

There is no hypothesis beyond `f.u.IsMorphismOfSites Y.J X.J`, which is what makes the Lean
object a morphism of ringed topoi; in particular the unit comparison is only a morphism and no
invertibility of it is used.

The quantifier over `Z` is removed by
`Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherenceHom_of_essSurj` against the
localization functor of the K-flat complexes with flat terms, which is essentially surjective
because it is a localization functor; at the image of such a complex the equation is
`derivedPullbackTensorIso_rightUnitor_model`. -/
theorem derivedPullbackTensorIso_rightUnitor
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackTensorIso f hmos).hom.app (Z, unitObject Y.toRingedSite) ≫
        (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor).map
            ((𝟙 ((derivedPullback f).obj Z) ×ₘ derivedPullbackUnitMap f hmos) :
              (((derivedPullback f).obj Z,
                  (derivedPullback f).obj (unitObject Y.toRingedSite)) : _ × _) ⟶
                ((derivedPullback f).obj Z, unitObject X.toRingedSite)) ≫
          ((canonicalDerivedTensorProduct X.O).rightUnitIso X.toRingedSite
            ((derivedPullback f).obj Z)).hom =
      (derivedPullback f).map
        (((canonicalDerivedTensorProduct Y.O).rightUnitIso Y.toRingedSite Z).hom) := by
  have := flatKFlatModelsQ_isLocalization Y
  have : (flatKFlatModelsQ Y).EssSurj :=
    Localization.essSurj (flatKFlatModelsQ Y) (flatKFlatModelsW Y)
  have hρY := fun {A B : DerivedModules Y.O} (u : A ⟶ B) =>
    DerivedTensorProduct.rightUnitIso_uncurry_naturality Y.toRingedSite
      (canonicalDerivedTensorProduct Y.O) u
  have hρX := fun {A B : DerivedModules X.O} (u : A ⟶ B) =>
    DerivedTensorProduct.rightUnitIso_uncurry_naturality X.toRingedSite
      (canonicalDerivedTensorProduct X.O) u
  refine Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherenceHom_of_essSurj
    (Functor.uncurry.obj (canonicalDerivedTensorProduct Y.O).tensor)
    (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor)
    (derivedPullbackTensorIso f hmos).hom
    (fun W => (canonicalDerivedTensorProduct Y.O).rightUnitIso Y.toRingedSite W)
    (fun W => (canonicalDerivedTensorProduct X.O).rightUnitIso X.toRingedSite W)
    (derivedPullbackUnitMap f hmos) (flatKFlatModelsQ Y) hρY hρX (fun e => ?_) Z
  exact Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherenceHom_of_iso
    _ _ _ _ _ _ hρY hρX
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app e.obj.as)
    (derivedPullbackTensorIso_rightUnitor_model f hmos e.obj.as e.property.1 e.property.2)

end Stacks.Sheaves.DerivedPullback

/-! ## The base case of Stacks 0944 -/

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

/-- **The base case `K = 𝒪_D[0]` of [Stacks, Tag 0944].**  Equation 21.50.0.1 of
[Stacks, Tag 0B56],

`Rf_*E ⊗^𝐋_{𝒪_D} 𝒪_D[0] ⟶ Rf_*(E ⊗^𝐋_{𝒪_C} Lf^*(𝒪_D[0]))`,

is an isomorphism for every `E` in `D(𝒪_C)`.

This is `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj` with all
four of its inputs supplied: the two right unit constraints of [Stacks, Tag 0FPT], the
naturality of the one on `D(𝒪_C)`, the unit comparison
`Stacks.Sheaves.DerivedPullback.derivedPullbackUnitMap`, and the right-unitor coherence of
[Stacks, Tag 07A4], which is
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_rightUnitor`.

The hypothesis is the invertibility of the *ordinary* comparison `f^*𝒪_D ⟶ 𝒪_C` of Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`, which is what makes the unit comparison on derived
categories invertible, by
`Stacks.Sheaves.DerivedPullback.isIso_derivedPullbackUnitMap`; Mathlib supplies it when the
functor presenting `f` is final.  It is not a weakening of the right-unitor coherence, which is
unconditional: it is what the *invertibility* of Equation 21.50.0.1 at the unit object needs,
since that is read off from the coherence by inverting `Rf_*(𝟙 ⊗ ν)`. -/
theorem isIso_projectionFormulaMap_unitObject
    (hν : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (projectionFormulaMap f hmos E
      (Stacks.DerivedTensor.RingedSite.unitObject Y.toRingedSite)) := by
  have := Stacks.Sheaves.DerivedPullback.isIso_derivedPullbackUnitMap f hmos hν
  exact Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj
    (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj (canonicalDerivedTensorProduct Y.O).tensor)
    (Functor.uncurry.obj (canonicalDerivedTensorProduct X.O).tensor)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom
    (fun W => (canonicalDerivedTensorProduct Y.O).rightUnitIso Y.toRingedSite W)
    (fun W => (canonicalDerivedTensorProduct X.O).rightUnitIso X.toRingedSite W)
    (asIso (Stacks.Sheaves.DerivedPullback.derivedPullbackUnitMap f hmos))
    (fun u => DerivedTensorProduct.rightUnitIso_uncurry_naturality X.toRingedSite
      (canonicalDerivedTensorProduct X.O) u)
    (fun Z => Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_rightUnitor f hmos Z) E

end Stacks.Cohomology.ProjectionFormulaOnRingedTopoi

end
