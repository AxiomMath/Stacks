module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicMilnorCompletionComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.StrictAdicRestrictionToAnOpen
import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheafRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjectionsFunctor

/-!
# The restriction of the named `R lim` to a slice is a derived limit of the slice's own tower

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals, `K̃` a K-flat complex of
`𝒪`-modules and `U` an object of `𝒞`. `AdicMilnorCompletionComparison.lean` names an object
`R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)` of `D(𝒪)`, for `K = Q K̃`, together with a map `K ⟶ R lim` out of the
strict cone of [Stacks, Tag 0CQH]. This file proves that restriction to the slice site `𝒞/U`
carries that presentation to a presentation of the **slice's own** tower: writing `R` for the
restriction functor `D(𝒪) ⟶ D(𝒪_U)`,

* `R(R lim)` is a derived limit of the tower `n ↦ R K ⊗^𝐋_{𝒪_U} 𝒪_U/(ℐ|_U)ⁿ⁺¹`, through named
  projections, and
* the restricted comparison map followed by the `n`-th projection is the slice's own derived
  reduction `R K ⟶ R K ⊗^𝐋_{𝒪_U} 𝒪_U/(ℐ|_U)ⁿ⁺¹`.

This is the slice-local input to part (1) of [Stacks, Tag 0A0K]: by
`RingedSite.isDerivedLimit_derivedCompletion_adicReductionTower_of_coversTop_slice` part (1) for an
arbitrary object of `D(𝒪)` reduces to a statement on the slices about the restricted comparison
map, and the restriction of the completion is the slice's completion by [Stacks, Tag 0A0F]. What is
proved here puts the *other* side of that comparison into the same slice-local form, so that the
statement to be proved on a slice mentions only the slice's own tower and its own derived
reductions.

The proof has three steps. First, the presentation of the named object over the strictified
tower `n ↦ Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])` is transported to the tower of derived reductions along the
K-flat comparison, and the comparison map is seen to induce the derived reductions
(`AlgebraicGeometry.RingedSite.kInjectiveAdicComparison_comp_kInjectiveAdicProj`). Second, the
restriction functor is triangulated and preserves countable products, so it carries the
presentation to one of the restricted tower. Third, the restricted tower is identified with the
slice's own tower: on strict models, restriction commutes with the total tensor complex and the
adic quotients (`AlgebraicGeometry.RingedSite.strictAdicReductionTowerOverIso`) and with the unit
law of the strict cone
(`AlgebraicGeometry.RingedSite.strictAdicAugmentationApp_comp_strictAdicReductionTowerOverIso`),
and `K̃|_U` is again K-flat ([Stacks, Tag 0E8K]), so the slice's tower is computed by the same
strict model one site down.

## Main definitions

* `AlgebraicGeometry.RingedSite.kInjectiveAdicProj` — the projections of the named `R lim` onto
  the terms `K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` of the tower of derived reductions.
* `AlgebraicGeometry.RingedSite.adicReductionTowerOverIso` — **the restriction of the tower of
  derived reductions of `Q K̃` is the slice's tower of derived reductions of `R(Q K̃)`**.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_kInjectiveAdicMilnorObj` — the named
  `R lim` is a derived limit of the tower of derived reductions through
  `AlgebraicGeometry.RingedSite.kInjectiveAdicProj`.
* `AlgebraicGeometry.RingedSite.kInjectiveAdicComparison_comp_kInjectiveAdicProj` — the named
  comparison map followed by those projections is the derived reduction of [Stacks, Tag 0CQH].
* `AlgebraicGeometry.RingedSite.map_adicQuotientReduction_comp_adicReductionTowerOverIso_hom_app`
  — the identification of towers carries the restricted derived reductions to the slice's own.
* `AlgebraicGeometry.RingedSite.exists_isDerivedLimitWithProjections_map_kInjectiveAdicMilnorObj`
  — **the restricted named `R lim` is a derived limit of the slice's own tower, through
  projections under which the restricted comparison map induces the slice's own derived
  reductions.**

## References

* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- Countable products of `D(𝒪)`, from K-injective resolutions and not from exactness of the
countable products of sheaves of modules. -/
local instance hasProductsOfShape_nat_derivedCategory_adicMilnorSlice :
    HasProductsOfShape ℕ
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  hasProductsOfShape_nat_derivedCategory_ringSheaf.{u, u, u} X

variable (Kt : CochainComplex (Modules X) ℤ) (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt)

/-- **The projections of the named `R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)` onto the derived reductions**: the
named projection `Stacks.MilnorTower.kInjectiveProj` onto the `n`-th term of the strictified tower,
read through the K-flat comparison `AlgebraicGeometry.RingedSite.strictAdicReductionTowerIso`. -/
def kInjectiveAdicProj (n : ℕ) :
    kInjectiveAdicMilnorObj X I Kt ⟶ (adicReductionTower X I (DerivedCategory.Q.obj Kt)).obj ⟨n⟩ :=
  Stacks.MilnorTower.kInjectiveProj (Modules X) (strictAdicReductionTower X I Kt) n ≫
    (strictAdicReductionTowerIso X I Kt hKt).inv.app ⟨n⟩

/-- **The named `R lim` is a derived limit of the tower of derived reductions through
`AlgebraicGeometry.RingedSite.kInjectiveAdicProj`.** This is
`Stacks.MilnorTower.isDerivedLimitWithProjections_Q_kInjectiveMilnorObj`, which presents it over
the strictified tower, transported along the K-flat comparison of the two towers. -/
theorem isDerivedLimitWithProjections_kInjectiveAdicMilnorObj :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicReductionTower X I (DerivedCategory.Q.obj Kt))
      (kInjectiveAdicMilnorObj X I Kt) (kInjectiveAdicProj X I Kt hKt) :=
  (Stacks.MilnorTower.isDerivedLimitWithProjections_Q_kInjectiveMilnorObj (Modules X)
    (strictAdicReductionTower X I Kt)).comp_of_hasEventualInverses
      (strictAdicReductionTowerIso X I Kt hKt).inv
      (NoetherianAdicCompletion.HasEventualInverses.of_isIso_app _ fun _ => inferInstance)

/-- The image of the `n`-th map of the strict cone, followed by the inverse of the K-flat
comparison, is the derived reduction. -/
private theorem Q_map_strictAdicAugmentationApp_comp_strictAdicReductionTowerIso_inv_app
    (X : RingedSite.{u, u, u})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (Kt : CochainComplex (Modules X) ℤ) (hKt : Stacks.SheafOfModules.IsKFlat X.O Kt) (n : ℕ) :
    DerivedCategory.Q.map (strictAdicAugmentationApp X I Kt n) ≫
      (strictAdicReductionTowerIso X I Kt hKt).inv.app ⟨n⟩ =
    adicQuotientReduction X I (DerivedCategory.Q.obj Kt) (n + 1) :=
  (((strictAdicReductionTowerIso X I Kt hKt).app ⟨n⟩).comp_inv_eq).2
    (adicQuotientReduction_comp_comparisonLeft X I Kt hKt n).symm

/-- **The named comparison map induces the derived reductions of [Stacks, Tag 0CQH]**: followed by
the `n`-th projection `AlgebraicGeometry.RingedSite.kInjectiveAdicProj` it is the derived
reduction `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`.

`AlgebraicGeometry.RingedSite.kInjectiveAdicComparison_comp_kInjectiveProj` identifies the
composite with the image of the `n`-th map of the strict cone, and
`AlgebraicGeometry.RingedSite.adicQuotientReduction_comp_comparisonLeft` identifies that, through
the K-flat comparison, with the derived reduction. -/
theorem kInjectiveAdicComparison_comp_kInjectiveAdicProj (n : ℕ) :
    kInjectiveAdicComparison X I Kt ≫ kInjectiveAdicProj X I Kt hKt n =
      adicQuotientReduction X I (DerivedCategory.Q.obj Kt) (n + 1) :=
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (strictAdicReductionTowerIso X I Kt hKt).inv.app ⟨n⟩)
      (kInjectiveAdicComparison_comp_kInjectiveProj X I Kt n)).trans <|
    Q_map_strictAdicAugmentationApp_comp_strictAdicReductionTowerIso_inv_app X I Kt hKt n

/-- **The derived reductions are natural in the object**: an isomorphism `e : K ≅ K'` of `D(𝒪)`
carries the derived reduction of `K` to that of `K'` through the induced isomorphism
`AlgebraicGeometry.RingedSite.adicReductionTowerIsoOfIso` of towers. This is the naturality of
the unit law of the derived tensor product
(`Stacks.SheafOfModules.DerivedTensorProduct.unitIso_inv_naturality`). -/
@[reassoc]
theorem adicQuotientReduction_comp_adicReductionTowerIsoOfIso_hom_app
    {K K' : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (e : K ≅ K') (n : ℕ) :
    adicQuotientReduction X I K (n + 1) ≫ (adicReductionTowerIsoOfIso X I e).hom.app ⟨n⟩ =
      e.hom ≫ adicQuotientReduction X I K' (n + 1) := by
  have hnat := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map e.hom).naturality
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
      (Stacks.Sites.adicQuotientModuleπ (X := X) I (n + 1)))
  have hunit := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).unitIso_inv_naturality
    X e.hom
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun w => _ ≫ w) hnat).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun w => w ≫ _) hunit.symm).trans ?_
  exact Category.assoc _ _ _

section Slice

variable (U : X.C) [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Restriction to a slice carries the tower of derived reductions to the slice's own tower**:
for a K-flat complex `K̃`, the restriction of `n ↦ Q K̃ ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` is
`n ↦ R(Q K̃) ⊗^𝐋_{𝒪_U} 𝒪_U/(ℐ|_U)ⁿ⁺¹`, naturally in `n`.

It is assembled from strict models: the K-flat comparison upstairs, the identification of the
restriction of `Q` of a complex with `Q` of its restriction
(`CategoryTheory.Functor.mapDerivedCategoryFactors`), the restriction of the strictified tower
(`AlgebraicGeometry.RingedSite.strictAdicReductionTowerOverIso`), and the K-flat comparison on the
slice, available because `K̃|_U` is K-flat ([Stacks, Tag 0E8K]). -/
def adicReductionTowerOverIso :
    adicReductionTower X I (DerivedCategory.Q.obj Kt) ⋙
        (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ≅
      adicReductionTower (X.over U) (overIdeal I U)
        ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj Kt)) :=
  Functor.isoWhiskerRight (strictAdicReductionTowerIso X I Kt hKt) _ ≪≫
    Functor.isoWhiskerLeft (strictAdicReductionTower X I Kt)
      (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight (strictAdicReductionTowerOverIso X U I Kt) DerivedCategory.Q ≪≫
    (strictAdicReductionTowerIso (X.over U) (overIdeal I U) (restrictComplex X Kt U)
      (Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex X U Kt hKt)).symm ≪≫
    adicReductionTowerIsoOfIso (X.over U) (overIdeal I U)
      ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategoryFactors.app Kt).symm

/-- The components of `AlgebraicGeometry.RingedSite.adicReductionTowerOverIso`, written out. -/
theorem adicReductionTowerOverIso_hom_app (n : ℕ) :
    (adicReductionTowerOverIso X I Kt hKt U).hom.app ⟨n⟩ =
      (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map
          ((strictAdicReductionTowerIso X I Kt hKt).hom.app ⟨n⟩) ≫
        (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategoryFactors.hom.app
          ((strictAdicReductionTower X I Kt).obj ⟨n⟩) ≫
        DerivedCategory.Q.map ((strictAdicReductionTowerOverIso X U I Kt).hom.app ⟨n⟩) ≫
        (strictAdicReductionTowerIso (X.over U) (overIdeal I U) (restrictComplex X Kt U)
          (Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex X U Kt hKt)).inv.app
            ⟨n⟩ ≫
        (adicReductionTowerIsoOfIso (X.over U) (overIdeal I U)
          ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategoryFactors.app
            Kt).symm).hom.app ⟨n⟩ :=
  rfl

/-- **The identification of towers carries the restricted derived reductions to the slice's own
derived reductions.** The restriction of `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`, followed by the `n`-th component
of `AlgebraicGeometry.RingedSite.adicReductionTowerOverIso`, is
`R K ⟶ R K ⊗^𝐋_{𝒪_U} 𝒪_U/(ℐ|_U)ⁿ⁺¹`.

Through the K-flat comparisons both derived reductions are images of maps of strict cones, so
this is the chain-level statement
`AlgebraicGeometry.RingedSite.strictAdicAugmentationApp_comp_strictAdicReductionTowerOverIso` —
restriction commutes with the total tensor complex, the adic quotients and the unit law — read in
the derived category. -/
theorem map_adicQuotientReduction_comp_adicReductionTowerOverIso_hom_app (n : ℕ) :
    (SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map
        (adicQuotientReduction X I (DerivedCategory.Q.obj Kt) (n + 1)) ≫
      (adicReductionTowerOverIso X I Kt hKt U).hom.app ⟨n⟩ =
    adicQuotientReduction (X.over U) (overIdeal I U)
      ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj Kt)) (n + 1) := by
  let R := (SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory
  let φ := (SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategoryFactors
  have hKt' := Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex X U Kt hKt
  have h1 : R.map (adicQuotientReduction X I (DerivedCategory.Q.obj Kt) (n + 1)) ≫
      R.map ((strictAdicReductionTowerIso X I Kt hKt).hom.app ⟨n⟩) =
      R.map (DerivedCategory.Q.map (strictAdicAugmentationApp X I Kt n)) :=
    (R.map_comp _ _).symm.trans
      (congrArg R.map (adicQuotientReduction_comp_comparisonLeft X I Kt hKt n))
  have h2 : R.map (DerivedCategory.Q.map (strictAdicAugmentationApp X I Kt n)) ≫
      φ.hom.app ((strictAdicReductionTower X I Kt).obj ⟨n⟩) =
      φ.hom.app Kt ≫ DerivedCategory.Q.map
        (restrictComplexMap X U (strictAdicAugmentationApp X I Kt n)) :=
    Functor.mapDerivedCategoryFactors_hom_naturality _ _
  have h3 : DerivedCategory.Q.map (restrictComplexMap X U (strictAdicAugmentationApp X I Kt n)) ≫
      DerivedCategory.Q.map ((strictAdicReductionTowerOverIso X U I Kt).hom.app ⟨n⟩) =
      DerivedCategory.Q.map (strictAdicAugmentationApp (X.over U) (overIdeal I U)
        (restrictComplex X Kt U) n) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
      (strictAdicAugmentationApp_comp_strictAdicReductionTowerOverIso X U I Kt n))
  have h4 := Q_map_strictAdicAugmentationApp_comp_strictAdicReductionTowerIso_inv_app
    (X.over U) (overIdeal I U) (restrictComplex X Kt U) hKt' n
  have h5 := adicQuotientReduction_comp_adicReductionTowerIsoOfIso_hom_app (X.over U)
    (overIdeal I U) (φ.app Kt).symm n
  refine (congrArg (fun w => _ ≫ w) (adicReductionTowerOverIso_hom_app X I Kt hKt U n)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun w => w ≫ _) h1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun w => w ≫ _) h2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  have h6 : DerivedCategory.Q.map (restrictComplexMap X U (strictAdicAugmentationApp X I Kt n)) ≫
      DerivedCategory.Q.map ((strictAdicReductionTowerOverIso X U I Kt).hom.app ⟨n⟩) ≫
      (strictAdicReductionTowerIso (X.over U) (overIdeal I U) (restrictComplex X Kt U)
        hKt').inv.app ⟨n⟩ ≫
      (adicReductionTowerIsoOfIso (X.over U) (overIdeal I U) (φ.app Kt).symm).hom.app ⟨n⟩ =
      (φ.app Kt).inv ≫ adicQuotientReduction (X.over U) (overIdeal I U)
        (R.obj (DerivedCategory.Q.obj Kt)) (n + 1) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun w => w ≫ _) h3).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun w => w ≫ _) h4).trans ?_
    exact h5
  exact (congrArg (fun w => φ.hom.app Kt ≫ w) h6).trans ((φ.app Kt).hom_inv_id_assoc _)

include hKt in
/-- **The restriction to a slice of the named `R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹)` is a derived limit of the
slice's own adic reduction tower, through projections under which the restricted comparison map
induces the slice's own derived reductions.**

Here `K = Q K̃` for a K-flat complex `K̃`, the named object is
`AlgebraicGeometry.RingedSite.kInjectiveAdicMilnorObj`, the comparison map is
`AlgebraicGeometry.RingedSite.kInjectiveAdicComparison`, and the restriction is the functor
`D(𝒪) ⟶ D(𝒪_U)` induced by the exact restriction of sheaves of modules. This is the slice-local
input of part (1) of [Stacks, Tag 0A0K]: combined with the identification of the completion of a
restriction with the restriction of the completion ([Stacks, Tag 0A0F]), it lets the chart
hypothesis of `RingedSite.isDerivedLimit_derivedCompletion_adicReductionTower_of_coversTop_slice`
be stated in terms of the slice's own tower and its own derived reductions of [Stacks, Tag 0CQH].

The projections are the restrictions of `AlgebraicGeometry.RingedSite.kInjectiveAdicProj` read
through `AlgebraicGeometry.RingedSite.adicReductionTowerOverIso`; the presentation is the
restriction of `RingedSite.isDerivedLimitWithProjections_kInjectiveAdicMilnorObj`, restriction
being triangulated and preserving countable products
(`AlgebraicGeometry.RingedSite.preservesProducts_mapDerivedCategory_overFunctor`). -/
theorem exists_isDerivedLimitWithProjections_map_kInjectiveAdicMilnorObj :
    ∃ π' : ∀ n : ℕ,
        (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
            (kInjectiveAdicMilnorObj X I Kt) ⟶
          (adicReductionTower (X.over U) (overIdeal I U)
            ((SheafOfModules.overFunctor.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
              (DerivedCategory.Q.obj Kt))).obj ⟨n⟩,
      NoetherianAdicCompletion.IsDerivedLimitWithProjections
        (adicReductionTower (X.over U) (overIdeal I U)
          ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj Kt)))
        ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
          (kInjectiveAdicMilnorObj X I Kt)) π' ∧
      ∀ n : ℕ, (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map
          (kInjectiveAdicComparison X I Kt) ≫ π' n =
        adicQuotientReduction (X.over U) (overIdeal I U)
          ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj Kt)) (n + 1) := by
  let R := (SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory
  refine ⟨fun n => R.map (kInjectiveAdicProj X I Kt hKt n) ≫
    (adicReductionTowerOverIso X I Kt hKt U).hom.app ⟨n⟩, ?_, fun n => ?_⟩
  · have := preservesProducts_mapDerivedCategory_overFunctor X U
    have : HasProductsOfShape ℕ
        (DerivedCategory
          (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))) :=
      hasProductsOfShape_nat_derivedCategory_over.{u, u, u} X U
    exact NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses
      (adicReductionTowerOverIso X I Kt hKt U).hom
      (NoetherianAdicCompletion.HasEventualInverses.of_isIso_app _ fun n =>
        Iso.isIso_hom ((adicReductionTowerOverIso X I Kt hKt U).app ⟨n⟩))
      ((isDerivedLimitWithProjections_kInjectiveAdicMilnorObj X I Kt hKt).map R)
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun w => w ≫ (adicReductionTowerOverIso X I Kt hKt U).hom.app ⟨n⟩)
      ((R.map_comp _ _).symm.trans (congrArg R.map
        (kInjectiveAdicComparison_comp_kInjectiveAdicProj X I Kt hKt n)))).trans ?_
    exact map_adicQuotientReduction_comp_adicReductionTowerOverIso_hom_app X I Kt hKt U n

end Slice

end AlgebraicGeometry.RingedSite

end
