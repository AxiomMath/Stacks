module

public import StacksFrontier.Cotangent.ChartSiteDifferentialsPresheaf
public import StacksFrontier.Cotangent.SchemeOverRingComparison
public import StacksFrontier.Cotangent.SchemeOverRingSectionwise
public import StacksFrontier.Cotangent.StandardResolutionCharts
public import StacksFrontier.Cotangent.Triangle.BaseChangeComparison

/-!
# The sections of `Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X` on the charts of the standard resolutions

Let `Λ` be a ring and `X` a scheme over `Λ`. For an open `U ⊆ X` let `P_{•,U}` be the standard
resolution of `𝒪_X(U)` over `Λ` and `A_{n,U} = Spec(P_{n,U})` the corresponding polynomial charts
of Tag 08VB. The proof of Tag 08T9 computes the value of the presheaf
`(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` of the chart site, whose sheafification is
`Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X`, on these charts:
`𝒪_X(U) ⊗_{Γ(A_{n,U})} Ω_{Γ(A_{n,U})/Λ} = 𝒪_X(U) ⊗_{P_{n,U}} Ω_{P_{n,U}/Λ}`, the degree `-n`
term of the cotangent complex `L_{𝒪_X(U)/Λ}`. This file proves that identification at a single
chart; its compatibility with the simplicial structure and with restriction to smaller opens is
`StacksFrontier/Cotangent/ChartSiteStandardResolutionNaturality.lean`, and the resulting isomorphism
of complexes of presheaves is `StacksFrontier/Cotangent/ChartSiteStandardResolutionEvaluation.lean`.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.sectionCotangentAlgebra`: `𝒪_X(U)` as a `Λ`-algebra through
  `Λ → Λ̲(U) → 𝒪_X(U)`, the algebra of `U ↦ L_{𝒪_X(U)/Λ}`.
* `AlgebraicGeometry.PolynomialChart.openAlgebraIso`: the functions on the open subscheme `U` are
  that algebra.
* `AlgebraicGeometry.PolynomialChart.chartResolutionIso`: `Γ(A_{n,U}) ≅ P_n` for `P_•` the standard
  resolution of `sectionCotangentAlgebra`.
* `AlgebraicGeometry.PolynomialChart.chartToCotangent` and
  `AlgebraicGeometry.PolynomialChart.cotangentToChart`: the two maps
  `𝒪_X(U) ⊗_{Γ(A_{n,U})} Ω_{Γ(A_{n,U})/Λ} ⇄ L^{-n}_{𝒪_X(U)/Λ}`, `b ⊗ d p ↦ b ⊗ d p`.

## Main results

* `AlgebraicGeometry.PolynomialChart.chartToCotangent_cotangentToChart` and
  `AlgebraicGeometry.PolynomialChart.cotangentToChart_chartToCotangent`: the two maps are inverse
  to each other.
* `CommAlgCat.cotangentTerm_addMonoidHom_ext`: additive maps out of a cotangent term, semilinear
  along a ring map, are determined by the pure differentials `1 ⊗ d p`.

## Implementation notes

All modules of the chart site live in the universe `u + 1` of its objects: the value of the
presheaf at `A_{n,U}` is `ULift 𝒪_X(U) ⊗_{ULift Γ(A_{n,U})} ULift Ω_{ULift Γ(A_{n,U})/ULift Λ}`,
while `L_{𝒪_X(U)/Λ}` lives in the universe `u` of the scheme. The comparison maps are therefore
written as additive maps, semilinear along `ULift 𝒪_X(U) ≃ 𝒪_X(U)`, rather than as morphisms of
`ModuleCat`.

## References

* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings TensorProduct
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sites.FibredCategory.FibredCategorySituation

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}

/-- In the degree `n` cotangent term `B ⊗_{P_n} Ω_{P_n/A}`, the action of `P_n` on the right factor
is the action of `B` through the augmentation. -/
theorem cotangentTerm_one_tmul_smul (n : SimplexCategoryᵒᵖ)
    (q : (standardResolution.{u, u} A B).left.obj n)
    (ω : Ω[(standardResolution.{u, u} A B).left.obj n⁄A]) :
    ((1 : B) ⊗ₜ[(standardResolution.{u, u} A B).left.obj n,
        standardResolutionAugmentationHom.{u, u} A B n] (q • ω) : cotangentTerm.{u, u} A B n) =
      standardResolutionAugmentationHom.{u, u} A B n q •
        (show cotangentTerm.{u, u} A B n from (1 : B) ⊗ₜ[(standardResolution.{u, u} A B).left.obj n,
          standardResolutionAugmentationHom.{u, u} A B n] ω) := by
  let : Algebra ((standardResolution.{u, u} A B).left.obj n) B :=
    (standardResolutionAugmentationHom.{u, u} A B n).toAlgebra
  change (1 : B) ⊗ₜ[(standardResolution.{u, u} A B).left.obj n] (q • ω) =
    standardResolutionAugmentationHom.{u, u} A B n q •
      ((1 : B) ⊗ₜ[(standardResolution.{u, u} A B).left.obj n] ω)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  congr 1

/-- Two additive maps out of the degree `n` cotangent term `B ⊗_{P_n} Ω_{P_n/A}`, semilinear along
the same ring map, agree as soon as they agree on the pure differentials `1 ⊗ d p`. Unlike
`CommAlgCat.cotangentTerm_hom_ext`, the target need not live in the universe of the term. -/
theorem cotangentTerm_addMonoidHom_ext (n : SimplexCategoryᵒᵖ) {R : Type*} [Semiring R]
    {N : Type*} [AddCommGroup N] [Module R N] (σ : B →+* R) (f g : cotangentTerm.{u, u} A B n →+ N)
    (hf : ∀ (b : B) (x : cotangentTerm.{u, u} A B n), f (b • x) = σ b • f x)
    (hg : ∀ (b : B) (x : cotangentTerm.{u, u} A B n), g (b • x) = σ b • g x)
    (h : ∀ p, f (cotangentTermDifferential.{u, u} A B n p) =
      g (cotangentTermDifferential.{u, u} A B n p)) : f = g := by
  have hone : ∀ ω : Ω[(standardResolution.{u, u} A B).left.obj n⁄A],
      f ((1 : B) ⊗ₜ[(standardResolution.{u, u} A B).left.obj n,
        standardResolutionAugmentationHom.{u, u} A B n] ω) =
      g ((1 : B) ⊗ₜ[(standardResolution.{u, u} A B).left.obj n,
        standardResolutionAugmentationHom.{u, u} A B n] ω) := by
    intro ω
    have hω : ω ∈ Submodule.span ((standardResolution.{u, u} A B).left.obj n)
        (Set.range (KaehlerDifferential.D A ((standardResolution.{u, u} A B).left.obj n))) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact h p
    | zero =>
      exact (congrArg f (TensorProduct.tmul_zero _ _)).trans ((map_zero f).trans
        ((map_zero g).symm.trans (congrArg g (TensorProduct.tmul_zero _ _).symm)))
    | add x y _ _ hx hy =>
      exact (congrArg f (TensorProduct.tmul_add _ _ _)).trans ((map_add f _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans ((map_add g _ _).symm.trans
          (congrArg g (TensorProduct.tmul_add _ _ _).symm))))
    | smul q x _ hx =>
      rw [cotangentTerm_one_tmul_smul, hf, hg, hx]
  ext x
  induction x using TensorProduct.inductionOn (R := (standardResolution.{u, u} A B).left.obj n)
      (M := (ModuleCat.restrictScalars (standardResolutionAugmentationHom.{u, u} A B n)).obj
        (ModuleCat.of _ B))
      (N := Ω[(standardResolution.{u, u} A B).left.obj n⁄A]) with
  | add x y hx hy =>
    exact (map_add f x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add g x y).symm)
  | tmul b ω =>
    have hb : (b ⊗ₜ[(standardResolution.{u, u} A B).left.obj n,
        standardResolutionAugmentationHom.{u, u} A B n] ω : cotangentTerm.{u, u} A B n) =
        (show B from b) • (show cotangentTerm.{u, u} A B n from
          (1 : B) ⊗ₜ[(standardResolution.{u, u} A B).left.obj n,
            standardResolutionAugmentationHom.{u, u} A B n] ω) :=
      (congrArg (fun z : B => (z ⊗ₜ[(standardResolution.{u, u} A B).left.obj n,
        standardResolutionAugmentationHom.{u, u} A B n] ω : cotangentTerm.{u, u} A B n))
          (mul_one (show B from b)).symm).trans
        (ModuleCat.ExtendScalars.smul_tmul (f := standardResolutionAugmentationHom.{u, u} A B n)
          (M := ModuleCat.of _ Ω[(standardResolution.{u, u} A B).left.obj n⁄A])
          (show B from b) 1 ω).symm
    exact (congrArg f hb).trans ((hf _ _).trans ((congrArg (σ b • ·) (hone ω)).trans
      ((hg _ _).symm.trans (congrArg g hb.symm))))

end CommAlgCat

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
  (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-- The structure map `Λ → Λ̲(U) → 𝒪_X(U)` of `U ↦ L_{𝒪_X(U)/Λ}` is `Λ → Γ(X, 𝒪_X) → 𝒪_X(U)`. -/
theorem constantBasePresheafToSheaf_comp_constantStructureMap_app (U : X.Opens) :
    (SchemeOverRing.constantBasePresheafToSheaf Λ X).app (op U) ≫
        (SchemeOverRing.constantStructureMap Λ structureMap).hom.app (op U) =
      SchemeOverRing.globalStructureMap Λ structureMap ≫
        X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
  have h1 : (toSheafify (Opens.grothendieckTopology X)
      (SchemeOverRing.constantBasePresheaf Λ X)).app (op U) =
      (toSheafify (Opens.grothendieckTopology X)
        (SchemeOverRing.constantBasePresheaf Λ X)).app (op ⊤) ≫
      (SchemeOverRing.constantBaseSheaf Λ X).obj.map (homOfLE (le_top : U ≤ ⊤)).op :=
    (Category.id_comp _).symm.trans ((toSheafify (Opens.grothendieckTopology X)
      (SchemeOverRing.constantBasePresheaf Λ X)).naturality (homOfLE (le_top : U ≤ ⊤)).op)
  have h2 := (SchemeOverRing.constantAdjunction X).homEquiv_unit (CommRingCat.of Λ)
    (SchemeOverRing.structureSheafOfSite X) (SchemeOverRing.constantStructureMap Λ structureMap)
  rw [SchemeOverRing.constantStructureMap_eq, Equiv.apply_symm_apply,
    SchemeOverRing.constantAdjunction_unit_app, ← SchemeOverRing.constantStructureMap_eq] at h2
  change (toSheafify _ _).app (op U) ≫ _ = _
  rw [h1]
  exact (Category.assoc _ _ _).trans ((congrArg (fun t => (toSheafify _ _).app (op ⊤) ≫ t)
    ((SchemeOverRing.constantStructureMap Λ structureMap).hom.naturality
      (homOfLE (le_top : U ≤ ⊤)).op)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ _) h2.symm)))

/-- `𝒪_X(U)` as a `Λ`-algebra through `Λ → Λ̲(U) → 𝒪_X(U)`: the algebra whose cotangent complex is
the term over `U` of the complex of presheaves `U ↦ L_{𝒪_X(U)/Λ}` of Tag 08T9. -/
def sectionCotangentAlgebra (U : X.Opens) : CommAlgCat.{u} Λ :=
  letI : Algebra Λ (X.presheaf.obj (op U)) :=
    ((SchemeOverRing.constantBasePresheafToSheaf Λ X).app (op U) ≫
      (SchemeOverRing.constantStructureMap Λ structureMap).hom.app (op U)).hom.toAlgebra
  CommAlgCat.of Λ (X.presheaf.obj (op U))

/-- `sectionCotangentAlgebra` is the algebra of sections of Tag 08SX over the base `U ↦ Λ`. -/
theorem sectionCotangentAlgebra_eq (U : X.Opens) :
    sectionCotangentAlgebra Λ X structureMap U =
      CategoryTheory.Sheaf.sectionsAlgebra.{u, u, u} ⊥
        (CategoryTheory.Sheaf.presheafBaseHom.{u, u, u} (Opens.grothendieckTopology X)
          (SchemeOverRing.constantStructureMap Λ structureMap)
          (SchemeOverRing.constantBasePresheafToSheaf Λ X)) (op U) :=
  rfl

/-- The structure map of `sectionCotangentAlgebra` is `Λ → Γ(X, 𝒪_X) → 𝒪_X(U)`, the one of the
charts. -/
theorem baseRingHom_comp_restrictFunctorΓ (U : X.Opens) :
    baseRingHom Λ X structureMap ≫ U.ι.appTop ≫ (X.restrictFunctorΓ.app (op U)).hom =
      CommRingCat.ofHom (algebraMap Λ (sectionCotangentAlgebra Λ X structureMap U)) := by
  change _ = (SchemeOverRing.constantBasePresheafToSheaf Λ X).app (op U) ≫
    (SchemeOverRing.constantStructureMap Λ structureMap).hom.app (op U)
  rw [constantBasePresheafToSheaf_comp_constantStructureMap_app]
  refine congrArg (baseRingHom Λ X structureMap ≫ ·) ?_
  refine (X.presheaf.map_comp _ _).symm.trans ?_
  congr 1

/-- The functions on the open subscheme `U` are, as a `Λ`-algebra, the sections `𝒪_X(U)` with
the structure map of `U ↦ L_{𝒪_X(U)/Λ}`. -/
def openAlgEquiv (U : X.Opens) :
    (openAlgebra Λ X structureMap).obj (op U) ≃ₐ[Λ] sectionCotangentAlgebra Λ X structureMap U :=
  { (X.restrictFunctorΓ.app (op U)).commRingCatIsoToRingEquiv with
    commutes' := fun r =>
      ConcreteCategory.congr_hom (baseRingHom_comp_restrictFunctorΓ Λ X structureMap U) r }

/-- `openAlgEquiv` as an isomorphism of commutative `Λ`-algebras. -/
def openAlgebraIso (U : X.Opens) :
    (openAlgebra Λ X structureMap).obj (op U) ≅ sectionCotangentAlgebra Λ X structureMap U :=
  CommAlgCat.isoMk (openAlgEquiv Λ X structureMap U)

/-- The ring of global functions on the affine space `A_{n,U} = Spec(P_{n,U})` is the degree `n`
term of the standard resolution of `𝒪_X(U)` over `Λ`. -/
def chartResolutionIso (U : X.Opens) (n : SimplexCategory) :
    (affineSectionsPresheaf Λ X structureMap).obj
        (op (((standardResolutionChart Λ X structureMap).obj U).obj n)) ≅
      (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).obj
        ((CommAlgCat.standardResolution.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U)).left.obj (op n)) :=
  Scheme.ΓSpecIso _ ≪≫ (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapIso
    ((SimplicialObject.Augmented.drop.mapIso
      ((CommAlgCat.standardResolutionFunctor.{u, u} Λ).mapIso
        (openAlgebraIso Λ X structureMap U))).app (op n))

/-- The comparison of `chartResolutionIso` lies over `𝒪_X(U)`: followed by the augmentation of the
standard resolution of `𝒪_X(U)` it is pullback of functions along the chart `U ⟶ A_{n,U}`. -/
theorem chartResolutionIso_hom_augmentation (U : X.Opens) (n : SimplexCategory) :
    (chartResolutionIso Λ X structureMap U n).hom ≫
        CommRingCat.ofHom (CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U) (op n)) =
      (evaluationSections Λ X structureMap).app
        (op (((standardResolutionChart Λ X structureMap).obj U).obj n)) := by
  have hw : ((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
        (openAlgebraIso Λ X structureMap U).hom).left.app (op n) ≫
        (CommAlgCat.standardResolution.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U)).hom.app (op n) =
      ((openStandardResolution Λ X structureMap).obj (op U)).hom.app (op n) ≫
        (openAlgebraIso Λ X structureMap U).hom := by
    simpa using NatTrans.congr_app ((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
      (openAlgebraIso Λ X structureMap U).hom).w (op n)
  have hw' := congrArg (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map hw
  rw [Functor.map_comp, Functor.map_comp] at hw'
  change (Scheme.ΓSpecIso _).hom ≫ ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
    (((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
      (openAlgebraIso Λ X structureMap U).hom).left.app (op n)) ≫
    (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
      ((CommAlgCat.standardResolution.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U)).hom.app (op n))) = _
  rw [hw', ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc]
  change _ = Scheme.Γ.map (Spec.map _).op ≫ Scheme.Γ.map ((U : Scheme.{u}).toSpecΓ).op ≫ _
  rw [Scheme.Γ_map_op, Scheme.Γ_map_op, Scheme.toSpecΓ_appTop]
  rfl

/-- The comparison of `chartResolutionIso` is compatible with the structure maps from `Λ`: on the
chart side the structure map is pullback of functions along `A_{n,U} ⟶ Spec Λ`. -/
theorem baseSectionsMap_comp_chartResolutionIso_hom (U : X.Opens) (n : SimplexCategory) :
    (baseSectionsMap Λ X structureMap).app
        (op (((standardResolutionChart Λ X structureMap).obj U).obj n)) ≫
        (chartResolutionIso Λ X structureMap U n).hom =
      CommRingCat.ofHom (algebraMap Λ ((CommAlgCat.standardResolution.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U)).left.obj (op n))) := by
  change (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
    (ofAugmentation (resolutionPresentation Λ X structureMap U n)
      (((openStandardResolution Λ X structureMap).obj (op U)).hom.app (op n))).toBase.appTop ≫
    (Scheme.ΓSpecIso _).hom ≫ (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
      (((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
        (openAlgebraIso Λ X structureMap U).hom).left.app (op n)) = _
  rw [ofAugmentation_toBase, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc (Scheme.ΓSpecIso _) _)).trans
    (algebraMap_comp Λ _)

/-- The comparison of `chartResolutionIso` is compatible with the simplicial structure: the
cosimplicial structure maps of `A_{•,U}` correspond to the simplicial structure maps of the
standard resolution of `𝒪_X(U)`. -/
theorem chartResolutionIso_hom_naturality (U : X.Opens) {m n : SimplexCategory} (θ : m ⟶ n) :
    Scheme.Γ.map (((standardResolutionChart Λ X structureMap).obj U).map θ).affine.op ≫
        (chartResolutionIso Λ X structureMap U m).hom =
      (chartResolutionIso Λ X structureMap U n).hom ≫
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
          ((CommAlgCat.standardResolution.{u, u} Λ
            (sectionCotangentAlgebra Λ X structureMap U)).left.map θ.op) := by
  have hnat := congrArg (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
    (((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
      (openAlgebraIso Λ X structureMap U).hom).left.naturality θ.op)
  rw [Functor.map_comp, Functor.map_comp] at hnat
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Scheme.ΓSpecIso_naturality _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (_ ≫ ·) hnat).trans (Category.assoc _ _ _).symm

/-- Restriction of sections `𝒪_X(U) ⟶ 𝒪_X(V)`, a map of `Λ`-algebras for the structure maps of
`U ↦ L_{𝒪_X(U)/Λ}`. -/
def sectionCotangentAlgHom {U V : X.Opens} (h : V ⟶ U) :
    sectionCotangentAlgebra Λ X structureMap U →ₐ[Λ] sectionCotangentAlgebra Λ X structureMap V :=
  { toRingHom := (X.presheaf.map h.op).hom
    commutes' := fun r => (ConcreteCategory.congr_hom
      ((SchemeOverRing.constantBasePresheafToSheaf Λ X ≫
        (SchemeOverRing.constantStructureMap Λ structureMap).hom).naturality h.op) r).symm }

/-- `sectionCotangentAlgHom` as a morphism of commutative `Λ`-algebras. -/
def sectionCotangentAlgebraMap {U V : X.Opens} (h : V ⟶ U) :
    sectionCotangentAlgebra Λ X structureMap U ⟶ sectionCotangentAlgebra Λ X structureMap V :=
  CommAlgCat.ofHom (R := Λ) (X := (sectionCotangentAlgebra Λ X structureMap U : Type u))
    (Y := (sectionCotangentAlgebra Λ X structureMap V : Type u))
    (sectionCotangentAlgHom Λ X structureMap h)

/-- The restriction squares of `U ↦ L_{𝒪_X(U)/Λ}` do not move the base ring `Λ`. -/
theorem sectionsRestrictionSquare_eq_idSquare {U V : X.Opens} (h : V ⟶ U) :
    CategoryTheory.Sheaf.sectionsRestrictionSquare.{u, u, u} ⊥
        (CategoryTheory.Sheaf.presheafBaseHom.{u, u, u} (Opens.grothendieckTopology X)
          (SchemeOverRing.constantStructureMap Λ structureMap)
          (SchemeOverRing.constantBasePresheafToSheaf Λ X)) h.op =
      CommAlgCat.idSquare (sectionCotangentAlgebraMap Λ X structureMap h) :=
  rfl

/-- `openAlgebraIso` is natural in the open. -/
theorem openAlgebraIso_naturality {U V : X.Opens} (h : V ⟶ U) :
    (openAlgebra Λ X structureMap).map h.op ≫ (openAlgebraIso Λ X structureMap V).hom =
      (openAlgebraIso Λ X structureMap U).hom ≫ sectionCotangentAlgebraMap Λ X structureMap h := by
  apply (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  change (openRing Λ X structureMap).map (homOfLE (leOfHom h)).op ≫ _ = _
  rw [openRing_map]
  exact X.restrictFunctorΓ.hom.naturality h.op

/-- The comparison of `chartResolutionIso` is natural in the open: the maps of charts
`A_{n,V} ⟶ A_{n,U}` over `V ⊆ U` correspond to the maps of standard resolutions induced by the
restriction `𝒪_X(U) ⟶ 𝒪_X(V)`. -/
theorem chartResolutionIso_hom_restriction {U V : X.Opens} (h : V ⟶ U) (n : SimplexCategory) :
    Scheme.Γ.map (((standardResolutionChart Λ X structureMap).map h).app n).affine.op ≫
        (chartResolutionIso Λ X structureMap V n).hom =
      (chartResolutionIso Λ X structureMap U n).hom ≫
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
          (((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
            (sectionCotangentAlgebraMap Λ X structureMap h)).left.app (op n)) := by
  have h2 := congrArg (fun f => ((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map f).left.app
    (op n)) (openAlgebraIso_naturality Λ X structureMap h)
  rw [Functor.map_comp, Functor.map_comp] at h2
  have hnat : (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
        (((openStandardResolution Λ X structureMap).map h.op).left.app (op n)) ≫
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
          (((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
            (openAlgebraIso Λ X structureMap V).hom).left.app (op n)) =
      (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
          (((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
            (openAlgebraIso Λ X structureMap U).hom).left.app (op n)) ≫
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
          (((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
            (sectionCotangentAlgebraMap Λ X structureMap h)).left.app (op n)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ h2
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Scheme.ΓSpecIso_naturality _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (_ ≫ ·) hnat).trans (Category.assoc _ _ _).symm

/-! ### The comparison of `𝒪_X(U) ⊗_{Γ(A_{n,U})} Ω_{Γ(A_{n,U})/Λ}` with `L^{-n}_{𝒪_X(U)/Λ}` -/

/-- The chart `A_{n,U} = Spec(P_{n,U})` of the standard resolution of `𝒪_X(U)` over `Λ`. -/
abbrev resolutionChart (U : X.Opens) (n : SimplexCategory) : PolynomialChart Λ X structureMap :=
  ((standardResolutionChart Λ X structureMap).obj U).obj n

/-- The lifted ring of functions `ULift Γ(A_{n,U})` of the chart `A_{n,U}`. -/
abbrev resolutionChartRing (U : X.Opens) (n : SimplexCategory) : CommRingCat.{u + 1} :=
  (affinePresheaf.{u, u + 1} Λ X structureMap).obj (op (resolutionChart Λ X structureMap U n))

/-- The degree `n` term of the standard resolution of `𝒪_X(U)` over `Λ`. -/
abbrev resolutionTermAlgebra (U : X.Opens) (n : SimplexCategory) : CommAlgCat.{u} Λ :=
  (CommAlgCat.standardResolution.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)).left.obj
    (op n)

/-- The lifted module of differentials `Ω_{ULift Γ(A_{n,U})/ULift Λ}` of the chart `A_{n,U}`. -/
abbrev resolutionChartDifferentials (U : X.Opens) (n : SimplexCategory) :
    ModuleCat.{u + 1} (resolutionChartRing Λ X structureMap U n) :=
  CommRingCat.KaehlerDifferential
    ((basePresheafMap.{u, u + 1} Λ X structureMap).app
      (op (resolutionChart Λ X structureMap U n)))

/-- The ring map `ULift Γ(A_{n,U}) → 𝒪_X(U)` through which the cotangent term
`L^{-n}_{𝒪_X(U)/Λ}` is a module over the lifted functions of the chart: the identification of
`Γ(A_{n,U})` with the degree `n` term of the standard resolution of `𝒪_X(U)`, followed by the
augmentation. -/
def chartAugmentationHom (U : X.Opens) (n : SimplexCategory) :
    (affinePresheaf.{u, u + 1} Λ X structureMap).obj
        (op (((standardResolutionChart Λ X structureMap).obj U).obj n)) →+*
      sectionCotangentAlgebra Λ X structureMap U :=
  (CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ
      (sectionCotangentAlgebra Λ X structureMap U) (op n)).comp
    ((chartResolutionIso Λ X structureMap U n).hom.hom.comp ULift.ringEquiv.toRingHom)

/-- `chartResolutionIso` sends the image of `Λ` to the image of `Λ`. -/
theorem chartResolutionIso_hom_baseSectionsMap (U : X.Opens) (n : SimplexCategory) (r : Λ) :
    (chartResolutionIso Λ X structureMap U n).hom
        ((baseSectionsMap Λ X structureMap).app
          (op (((standardResolutionChart Λ X structureMap).obj U).obj n)) r) =
      algebraMap Λ ((CommAlgCat.standardResolution.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U)).left.obj (op n)) r := by
  rw [← ConcreteCategory.comp_apply, baseSectionsMap_comp_chartResolutionIso_hom]
  rfl

/-- The derivation `p ↦ 1 ⊗ d(p)` of the lifted functions of the chart `A_{n,U}` over `Λ` with
values in `L^{-n}_{𝒪_X(U)/Λ} = 𝒪_X(U) ⊗_{P_n} Ω_{P_n/Λ}`. -/
def chartCotangentDerivation (U : X.Opens) (n : SimplexCategory) :
    ((ModuleCat.restrictScalars (chartAugmentationHom Λ X structureMap U n)).obj
        (CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
          (op n))).Derivation
      ((basePresheafMap.{u, u + 1} Λ X structureMap).app
        (op (((standardResolutionChart Λ X structureMap).obj U).obj n))) :=
  ModuleCat.Derivation.mk
    (fun p => CommAlgCat.cotangentTermDifferential.{u, u} Λ
      (sectionCotangentAlgebra Λ X structureMap U) (op n)
        ((chartResolutionIso Λ X structureMap U n).hom p.down))
    (fun p p' => by
      change CommAlgCat.cotangentTermDifferential.{u, u} Λ _ (op n)
        ((chartResolutionIso Λ X structureMap U n).hom (p.down + p'.down)) = _
      rw [map_add, CommAlgCat.cotangentTermDifferential_add]
      rfl)
    (fun p p' => by
      change CommAlgCat.cotangentTermDifferential.{u, u} Λ _ (op n)
        ((chartResolutionIso Λ X structureMap U n).hom (p.down * p'.down)) = _
      rw [map_mul, CommAlgCat.cotangentTermDifferential_mul]
      rfl)
    (fun r => by
      change CommAlgCat.cotangentTermDifferential.{u, u} Λ _ (op n)
        ((chartResolutionIso Λ X structureMap U n).hom
          ((baseSectionsMap Λ X structureMap).app _ r.down)) = 0
      rw [chartResolutionIso_hom_baseSectionsMap, CommAlgCat.cotangentTermDifferential_algebraMap])

/-- Evaluation along the chart `U ⟶ A_{n,U}` is `chartAugmentationHom`. -/
theorem evaluation_app_down (U : X.Opens) (n : SimplexCategory)
    (p : (affinePresheaf.{u, u + 1} Λ X structureMap).obj
      (op (((standardResolutionChart Λ X structureMap).obj U).obj n))) :
    ((evaluation.{u, u + 1} Λ X structureMap).app
        (op (((standardResolutionChart Λ X structureMap).obj U).obj n)) p).down =
      chartAugmentationHom Λ X structureMap U n p := by
  change (evaluationSections Λ X structureMap).app _ p.down =
    CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ _ (op n)
      ((chartResolutionIso Λ X structureMap U n).hom p.down)
  rw [← chartResolutionIso_hom_augmentation Λ X structureMap U n]
  rfl

/-- The inverse of `chartResolutionIso`, followed by the universe lift: a ring map from the degree
`n` term of the standard resolution of `𝒪_X(U)` to the lifted functions of the chart `A_{n,U}`. -/
def resolutionToChartHom (U : X.Opens) (n : SimplexCategory) :
    resolutionTermAlgebra Λ X structureMap U n →+* resolutionChartRing Λ X structureMap U n :=
  ULift.ringEquiv.symm.toRingHom.comp (chartResolutionIso Λ X structureMap U n).inv.hom

/-- `resolutionToChartHom` is the universe lift of the inverse of `chartResolutionIso`. -/
theorem resolutionToChartHom_down (U : X.Opens) (n : SimplexCategory)
    (q : resolutionTermAlgebra Λ X structureMap U n) :
    (resolutionToChartHom Λ X structureMap U n q).down =
      (chartResolutionIso Λ X structureMap U n).inv q :=
  rfl

/-- `chartResolutionIso` carries the image of `Λ` back to the image of `Λ`. -/
theorem chartResolutionIso_inv_algebraMap (U : X.Opens) (n : SimplexCategory) (r : Λ) :
    (chartResolutionIso Λ X structureMap U n).inv
        (algebraMap Λ (resolutionTermAlgebra Λ X structureMap U n) r) =
      (baseSectionsMap Λ X structureMap).app (op (resolutionChart Λ X structureMap U n)) r := by
  rw [← chartResolutionIso_hom_baseSectionsMap]
  exact Iso.hom_inv_id_apply _ _

/-- The map of Kähler differentials `Ω_{P_n/Λ} → Ω_{ULift Γ(A_{n,U})/ULift Λ}` induced by the
inverse of `chartResolutionIso`. -/
def resolutionToChartDifferentials (U : X.Opens) (n : SimplexCategory) :
    Ω[resolutionTermAlgebra Λ X structureMap U n⁄Λ] →+
      resolutionChartDifferentials Λ X structureMap U n := by
  letI : Algebra (((Functor.const _).obj (liftRing.{u, u + 1}.obj (CommRingCat.of Λ))).obj
      (op (resolutionChart Λ X structureMap U n)))
      (resolutionChartRing Λ X structureMap U n) :=
    ((basePresheafMap.{u, u + 1} Λ X structureMap).app
      (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  letI : Algebra Λ (((Functor.const _).obj (liftRing.{u, u + 1}.obj (CommRingCat.of Λ))).obj
      (op (resolutionChart Λ X structureMap U n))) :=
    (ULift.ringEquiv.symm.toRingHom : Λ →+* ULift.{u + 1} Λ).toAlgebra
  letI : Algebra (resolutionTermAlgebra Λ X structureMap U n)
      (resolutionChartRing Λ X structureMap U n) :=
    (resolutionToChartHom Λ X structureMap U n).toAlgebra
  letI : Algebra Λ (resolutionChartRing Λ X structureMap U n) :=
    ((algebraMap (resolutionTermAlgebra Λ X structureMap U n)
      (resolutionChartRing Λ X structureMap U n)).comp (algebraMap Λ _)).toAlgebra
  haveI : IsScalarTower Λ (resolutionTermAlgebra Λ X structureMap U n)
      (resolutionChartRing Λ X structureMap U n) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Λ (((Functor.const _).obj (liftRing.{u, u + 1}.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ X structureMap U n)))
      (resolutionChartRing Λ X structureMap U n) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      congrArg ULift.up (chartResolutionIso_inv_algebraMap Λ X structureMap U n r)
  haveI : SMulCommClass (((Functor.const _).obj (liftRing.{u, u + 1}.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ X structureMap U n)))
      (resolutionTermAlgebra Λ X structureMap U n) (resolutionChartRing Λ X structureMap U n) :=
    ⟨fun a b c => by simp only [Algebra.smul_def, mul_left_comm]⟩
  exact (KaehlerDifferential.map Λ _ (resolutionTermAlgebra Λ X structureMap U n)
    (resolutionChartRing Λ X structureMap U n)).toAddMonoidHom

/-- `resolutionToChartDifferentials` sends `d q` to `d` of the corresponding function on the
chart, and is semilinear along `resolutionToChartHom`. -/
private theorem resolutionToChartDifferentials_D_and_smul (U : X.Opens) (n : SimplexCategory) :
    (∀ q : resolutionTermAlgebra Λ X structureMap U n,
      resolutionToChartDifferentials Λ X structureMap U n
          (KaehlerDifferential.D Λ (resolutionTermAlgebra Λ X structureMap U n) q) =
        CommRingCat.KaehlerDifferential.d (resolutionToChartHom Λ X structureMap U n q)) ∧
    ∀ (q : resolutionTermAlgebra Λ X structureMap U n)
      (ω : Ω[resolutionTermAlgebra Λ X structureMap U n⁄Λ]),
      resolutionToChartDifferentials Λ X structureMap U n (q • ω) =
        resolutionToChartHom Λ X structureMap U n q •
          resolutionToChartDifferentials Λ X structureMap U n ω := by
  let : Algebra (((Functor.const _).obj (liftRing.{u, u + 1}.obj (CommRingCat.of Λ))).obj
      (op (resolutionChart Λ X structureMap U n)))
      (resolutionChartRing Λ X structureMap U n) :=
    ((basePresheafMap.{u, u + 1} Λ X structureMap).app
      (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  let : Algebra Λ (((Functor.const _).obj (liftRing.{u, u + 1}.obj (CommRingCat.of Λ))).obj
      (op (resolutionChart Λ X structureMap U n))) :=
    (ULift.ringEquiv.symm.toRingHom : Λ →+* ULift.{u + 1} Λ).toAlgebra
  let : Algebra (resolutionTermAlgebra Λ X structureMap U n)
      (resolutionChartRing Λ X structureMap U n) :=
    (resolutionToChartHom Λ X structureMap U n).toAlgebra
  let : Algebra Λ (resolutionChartRing Λ X structureMap U n) :=
    ((algebraMap (resolutionTermAlgebra Λ X structureMap U n)
      (resolutionChartRing Λ X structureMap U n)).comp (algebraMap Λ _)).toAlgebra
  have : IsScalarTower Λ (resolutionTermAlgebra Λ X structureMap U n)
      (resolutionChartRing Λ X structureMap U n) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Λ (((Functor.const _).obj (liftRing.{u, u + 1}.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ X structureMap U n)))
      (resolutionChartRing Λ X structureMap U n) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      congrArg ULift.up (chartResolutionIso_inv_algebraMap Λ X structureMap U n r)
  have : SMulCommClass (((Functor.const _).obj (liftRing.{u, u + 1}.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ X structureMap U n)))
      (resolutionTermAlgebra Λ X structureMap U n) (resolutionChartRing Λ X structureMap U n) :=
    ⟨fun a b c => by simp only [Algebra.smul_def, mul_left_comm]⟩
  exact ⟨fun q => KaehlerDifferential.map_D Λ _ (resolutionTermAlgebra Λ X structureMap U n)
      (resolutionChartRing Λ X structureMap U n) q,
    fun q ω => (KaehlerDifferential.map Λ _ (resolutionTermAlgebra Λ X structureMap U n)
      (resolutionChartRing Λ X structureMap U n)).map_smul q ω⟩

/-- `resolutionToChartDifferentials` sends `d q` to `d` of the corresponding function on the
chart. -/
theorem resolutionToChartDifferentials_D (U : X.Opens) (n : SimplexCategory)
    (q : resolutionTermAlgebra Λ X structureMap U n) :
    resolutionToChartDifferentials Λ X structureMap U n
        (KaehlerDifferential.D Λ (resolutionTermAlgebra Λ X structureMap U n) q) =
      CommRingCat.KaehlerDifferential.d (resolutionToChartHom Λ X structureMap U n q) :=
  (resolutionToChartDifferentials_D_and_smul Λ X structureMap U n).1 q

/-- `resolutionToChartDifferentials` is semilinear along the inverse of `chartResolutionIso`. -/
theorem resolutionToChartDifferentials_smul (U : X.Opens) (n : SimplexCategory)
    (q : resolutionTermAlgebra Λ X structureMap U n)
    (ω : Ω[resolutionTermAlgebra Λ X structureMap U n⁄Λ]) :
    resolutionToChartDifferentials Λ X structureMap U n (q • ω) =
      resolutionToChartHom Λ X structureMap U n q •
        resolutionToChartDifferentials Λ X structureMap U n ω :=
  (resolutionToChartDifferentials_D_and_smul Λ X structureMap U n).2 q ω

/-- The lifted sections `ULift 𝒪_X(U)` of the chart `A_{n,U}` restricted along `U ⟶ X`, mapped back
to `𝒪_X(U)`. -/
def chartSectionsDown (U : X.Opens) (n : SimplexCategory) :
    (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj (op (resolutionChart Λ X structureMap U n))
      →+* sectionCotangentAlgebra Λ X structureMap U :=
  ULift.ringEquiv.toRingHom

/-- The universe lift `𝒪_X(U) → ULift 𝒪_X(U)`, onto the sections of the chart `A_{n,U}`. -/
def chartSectionsUp (U : X.Opens) (n : SimplexCategory) :
    sectionCotangentAlgebra Λ X structureMap U →+*
      (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
        (op (resolutionChart Λ X structureMap U n)) :=
  ULift.ringEquiv.symm.toRingHom

/-- `chartSectionsUp`, landing in the ring `𝒪̲_X(A_{n,U})` over which the sections of the chart site
presheaves are modules. -/
def chartScalarUp (U : X.Opens) (n : SimplexCategory) :
    sectionCotangentAlgebra Λ X structureMap U →+*
      (chartStructureRing Λ X structureMap).obj.obj
        (op (resolutionChart Λ X structureMap U n)) :=
  ULift.ringEquiv.symm.toRingHom

/-- The additive map `Ω_{Γ(A_{n,U})/Λ} → L^{-n}_{𝒪_X(U)/Λ}`, `d p ↦ 1 ⊗ d p`, induced by
`chartCotangentDerivation`. -/
def chartCotangentDesc (U : X.Opens) (n : SimplexCategory) :
    resolutionChartDifferentials Λ X structureMap U n →+
      CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n) :=
  letI := ((basePresheafMap.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  letI := Module.compHom
    ((ModuleCat.restrictScalars (chartAugmentationHom Λ X structureMap U n)).obj
      (CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n)))
    ((basePresheafMap.{u, u + 1} Λ X structureMap).app
      (op (resolutionChart Λ X structureMap U n))).hom
  haveI : IsScalarTower
      (((Functor.const _).obj (liftRing.{u, u + 1}.obj (CommRingCat.of Λ))).obj
        (op (resolutionChart Λ X structureMap U n)))
      (resolutionChartRing Λ X structureMap U n)
      ((ModuleCat.restrictScalars (chartAugmentationHom Λ X structureMap U n)).obj
        (CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
          (op n))) :=
    IsScalarTower.of_compHom _ _ _
  (Derivation.liftKaehlerDifferential
    (chartCotangentDerivation Λ X structureMap U n)).toAddMonoidHom

/-- `chartCotangentDesc` sends `d p` to `1 ⊗ d p` and is semilinear along
`chartAugmentationHom`. -/
private theorem chartCotangentDesc_d_and_smul (U : X.Opens) (n : SimplexCategory) :
    (∀ p : resolutionChartRing Λ X structureMap U n,
      chartCotangentDesc Λ X structureMap U n (CommRingCat.KaehlerDifferential.d p) =
        CommAlgCat.cotangentTermDifferential.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
          (op n) ((chartResolutionIso Λ X structureMap U n).hom p.down)) ∧
    ∀ (p : resolutionChartRing Λ X structureMap U n)
      (m : resolutionChartDifferentials Λ X structureMap U n),
      chartCotangentDesc Λ X structureMap U n (p • m) =
        chartAugmentationHom Λ X structureMap U n p •
          chartCotangentDesc Λ X structureMap U n m := by
  let := ((basePresheafMap.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  let := Module.compHom
    ((ModuleCat.restrictScalars (chartAugmentationHom Λ X structureMap U n)).obj
      (CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n)))
    ((basePresheafMap.{u, u + 1} Λ X structureMap).app
      (op (resolutionChart Λ X structureMap U n))).hom
  have : IsScalarTower
      (((Functor.const _).obj (liftRing.{u, u + 1}.obj (CommRingCat.of Λ))).obj
        (op (resolutionChart Λ X structureMap U n)))
      (resolutionChartRing Λ X structureMap U n)
      ((ModuleCat.restrictScalars (chartAugmentationHom Λ X structureMap U n)).obj
        (CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
          (op n))) :=
    IsScalarTower.of_compHom _ _ _
  exact ⟨fun p => Derivation.liftKaehlerDifferential_comp_D
      (chartCotangentDerivation Λ X structureMap U n) p,
    fun p m => (Derivation.liftKaehlerDifferential
      (chartCotangentDerivation Λ X structureMap U n)).map_smul p m⟩

/-- `chartCotangentDesc` sends `d p` to `1 ⊗ d p`. -/
theorem chartCotangentDesc_d (U : X.Opens) (n : SimplexCategory)
    (p : resolutionChartRing Λ X structureMap U n) :
    chartCotangentDesc Λ X structureMap U n (CommRingCat.KaehlerDifferential.d p) =
      CommAlgCat.cotangentTermDifferential.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
        (op n) ((chartResolutionIso Λ X structureMap U n).hom p.down) :=
  (chartCotangentDesc_d_and_smul Λ X structureMap U n).1 p

/-- `chartCotangentDesc` is semilinear along `chartAugmentationHom`. -/
theorem chartCotangentDesc_smul (U : X.Opens) (n : SimplexCategory)
    (p : resolutionChartRing Λ X structureMap U n)
    (m : resolutionChartDifferentials Λ X structureMap U n) :
    chartCotangentDesc Λ X structureMap U n (p • m) =
      chartAugmentationHom Λ X structureMap U n p • chartCotangentDesc Λ X structureMap U n m :=
  (chartCotangentDesc_d_and_smul Λ X structureMap U n).2 p m

/-- The additive map `𝒪_X(U) ⊗_{Γ(A_{n,U})} Ω_{Γ(A_{n,U})/Λ} → L^{-n}_{𝒪_X(U)/Λ}`,
`b ⊗ d p ↦ b ⊗ d p`, of the computation in the proof of Tag 08T9, on the lifted sections. -/
def chartToCotangent (U : X.Opens) (n : SimplexCategory) :
    (chartBaseChangePresheaf Λ X structureMap).obj (op (resolutionChart Λ X structureMap U n)) →+
      CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n) := by
  letI := ((evaluation.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  exact TensorProduct.liftAddHom (R := resolutionChartRing Λ X structureMap U n)
    (M := (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
      (op (resolutionChart Λ X structureMap U n)))
    (N := ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n))
    (P := CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n))
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun m => chartSectionsDown Λ X structureMap U n b •
          chartCotangentDesc Λ X structureMap U n m.down)
        (fun m m' => by
          rw [← smul_add]
          exact congrArg (chartSectionsDown Λ X structureMap U n b • ·)
            (map_add (chartCotangentDesc Λ X structureMap U n) _ _)))
      (fun b b' => by ext m; exact (congrArg (· • _) (map_add _ _ _)).trans (add_smul _ _ _)))
    (fun r b m => by
      change chartSectionsDown Λ X structureMap U n (algebraMap _ _ r * b) • _ =
        chartSectionsDown Λ X structureMap U n b •
          chartCotangentDesc Λ X structureMap U n (r • m.down)
      rw [map_mul, chartCotangentDesc_smul, mul_comm, mul_smul]
      congr 2
      exact evaluation_app_down Λ X structureMap U n r)

/-- The additive map `L^{-n}_{𝒪_X(U)/Λ} → 𝒪_X(U) ⊗_{Γ(A_{n,U})} Ω_{Γ(A_{n,U})/Λ}`,
`b ⊗ d q ↦ b ⊗ d q`, inverse to `chartToCotangent`. -/
def cotangentToChart (U : X.Opens) (n : SimplexCategory) :
    CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n) →+
      (chartBaseChangePresheaf Λ X structureMap).obj
        (op (resolutionChart Λ X structureMap U n)) := by
  letI := ((evaluation.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  exact TensorProduct.liftAddHom (R := resolutionTermAlgebra Λ X structureMap U n)
    (M := (ModuleCat.restrictScalars (CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ
      (sectionCotangentAlgebra Λ X structureMap U) (op n))).obj
        (ModuleCat.of _ (sectionCotangentAlgebra Λ X structureMap U)))
    (N := Ω[resolutionTermAlgebra Λ X structureMap U n⁄Λ])
    (P := TensorProduct (resolutionChartRing Λ X structureMap U n)
      ((zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
        (op (resolutionChart Λ X structureMap U n)))
      (ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)))
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun ω => chartSectionsUp Λ X structureMap U n b ⊗ₜ[resolutionChartRing Λ X
            structureMap U n]
          (ULift.up (resolutionToChartDifferentials Λ X structureMap U n ω) :
            ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)))
        (fun ω ω' => by rw [map_add]; exact TensorProduct.tmul_add _ _ _))
      (fun b b' => AddMonoidHom.ext fun ω =>
        (congrArg (· ⊗ₜ[resolutionChartRing Λ X structureMap U n] _) (map_add _ _ _)).trans
          (TensorProduct.add_tmul _ _ _)))
    (fun q b ω => by
      change chartSectionsUp Λ X structureMap U n
          (CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ _ (op n) q *
            (show sectionCotangentAlgebra Λ X structureMap U from b)) ⊗ₜ _ =
        chartSectionsUp Λ X structureMap U n b ⊗ₜ[resolutionChartRing Λ X structureMap U n]
          (ULift.up (resolutionToChartDifferentials Λ X structureMap U n (q • ω)) :
            ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n))
      rw [resolutionToChartDifferentials_smul]
      change _ = chartSectionsUp Λ X structureMap U n b ⊗ₜ[resolutionChartRing Λ X structureMap U n]
        (resolutionToChartHom Λ X structureMap U n q •
          (ULift.up (resolutionToChartDifferentials Λ X structureMap U n ω) :
            ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)))
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, map_mul]
      congr 2
      refine ULift.ext ((evaluation_app_down Λ X structureMap U n _).trans ?_).symm
      exact congrArg (CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ _ (op n))
        (Iso.inv_hom_id_apply (chartResolutionIso Λ X structureMap U n) q))

set_option backward.isDefEq.respectTransparency false in
/-- `cotangentToChart` is semilinear along `𝒪_X(U) → ULift 𝒪_X(U)`. -/
theorem cotangentToChart_smul (U : X.Opens) (n : SimplexCategory)
    (b : sectionCotangentAlgebra Λ X structureMap U)
    (x : CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n)) :
    cotangentToChart Λ X structureMap U n (b • x) =
      chartScalarUp Λ X structureMap U n b • cotangentToChart Λ X structureMap U n x := by
  let := ((evaluation.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  induction x using TensorProduct.inductionOn (R := resolutionTermAlgebra Λ X structureMap U n)
      (M := (ModuleCat.restrictScalars (CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ
        (sectionCotangentAlgebra Λ X structureMap U) (op n))).obj
          (ModuleCat.of _ (sectionCotangentAlgebra Λ X structureMap U)))
      (N := Ω[resolutionTermAlgebra Λ X structureMap U n⁄Λ]) with
  | add x x' hx hx' =>
    exact (congrArg _ (smul_add (A := CommAlgCat.cotangentTerm.{u, u} Λ
      (sectionCotangentAlgebra Λ X structureMap U) (op n)) b x x')).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hx').trans ((smul_add (A := (chartBaseChangePresheaf Λ X
        structureMap).obj (op (resolutionChart Λ X structureMap U n))) _ _ _).symm.trans
        (congrArg _ (map_add _ _ _).symm))))
  | tmul b' ω =>
    exact (congrArg (fun z => z ⊗ₜ[resolutionChartRing Λ X structureMap U n]
      (ULift.up (resolutionToChartDifferentials Λ X structureMap U n ω) :
        ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)))
      ((map_mul (chartSectionsUp Λ X structureMap U n) b b').trans
        (smul_eq_mul _ _).symm)).trans (TensorProduct.smul_tmul' _ _ _).symm

/-- The augmentation of the chart undoes `resolutionToChartHom`. -/
theorem chartAugmentationHom_resolutionToChartHom (U : X.Opens) (n : SimplexCategory)
    (q : resolutionTermAlgebra Λ X structureMap U n) :
    chartAugmentationHom Λ X structureMap U n (resolutionToChartHom Λ X structureMap U n q) =
      CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ
        (sectionCotangentAlgebra Λ X structureMap U) (op n) q := by
  simp only [chartAugmentationHom, resolutionToChartHom, RingHom.comp_apply]
  exact congrArg _ (Iso.inv_hom_id_apply (chartResolutionIso Λ X structureMap U n) q)

/-- `chartCotangentDesc` undoes `resolutionToChartDifferentials`: the composite
`Ω_{P_n/Λ} → Ω_{ULift Γ(A_{n,U})/ULift Λ} → L^{-n}_{𝒪_X(U)/Λ}` is `ω ↦ 1 ⊗ ω`. -/
theorem chartCotangentDesc_resolutionToChartDifferentials (U : X.Opens) (n : SimplexCategory)
    (ω : Ω[resolutionTermAlgebra Λ X structureMap U n⁄Λ]) :
    chartCotangentDesc Λ X structureMap U n
        (resolutionToChartDifferentials Λ X structureMap U n ω) =
      ((1 : sectionCotangentAlgebra Λ X structureMap U) ⊗ₜ[resolutionTermAlgebra Λ X
        structureMap U n,
        CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ _ (op n)] ω :
        CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n)) := by
  have hω : ω ∈ Submodule.span (resolutionTermAlgebra Λ X structureMap U n)
      (Set.range (KaehlerDifferential.D Λ (resolutionTermAlgebra Λ X structureMap U n))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    rw [resolutionToChartDifferentials_D, chartCotangentDesc_d, resolutionToChartHom_down,
      Iso.inv_hom_id_apply]
    rfl
  | zero =>
    rw [map_zero, map_zero]
    exact (TensorProduct.tmul_zero _ _).symm
  | add x y _ _ hx hy =>
    rw [map_add, map_add, hx, hy]
    exact (TensorProduct.tmul_add _ _ _).symm
  | smul q x _ hx =>
    rw [resolutionToChartDifferentials_smul, chartCotangentDesc_smul, hx,
      chartAugmentationHom_resolutionToChartHom]
    exact (CommAlgCat.cotangentTerm_one_tmul_smul (op n) q x).symm

set_option backward.isDefEq.respectTransparency false in
/-- `cotangentToChart` undoes `chartCotangentDesc`: the composite
`Ω_{ULift Γ(A_{n,U})/ULift Λ} → L^{-n}_{𝒪_X(U)/Λ} → ULift 𝒪_X(U) ⊗ Ω_{ULift Γ(A_{n,U})/ULift Λ}` is
`m ↦ 1 ⊗ m`. -/
theorem cotangentToChart_chartCotangentDesc (U : X.Opens) (n : SimplexCategory)
    (m : resolutionChartDifferentials Λ X structureMap U n) :
    cotangentToChart Λ X structureMap U n (chartCotangentDesc Λ X structureMap U n m) =
      letI := ((evaluation.{u, u + 1} Λ X structureMap).app
        (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
      ((1 : (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
          (op (resolutionChart Λ X structureMap U n))) ⊗ₜ[resolutionChartRing Λ X structureMap U n]
        (ULift.up m : ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)) :
        TensorProduct (resolutionChartRing Λ X structureMap U n)
          ((zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
            (op (resolutionChart Λ X structureMap U n)))
          (ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n))) := by
  let := ((evaluation.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  let := ((basePresheafMap.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  have hm : m ∈ Submodule.span (resolutionChartRing Λ X structureMap U n)
      (Set.range (KaehlerDifferential.D (((Functor.const _).obj (liftRing.{u, u + 1}.obj
        (CommRingCat.of Λ))).obj (op (resolutionChart Λ X structureMap U n)))
        (resolutionChartRing Λ X structureMap U n))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    change cotangentToChart Λ X structureMap U n
      (chartCotangentDesc Λ X structureMap U n (CommRingCat.KaehlerDifferential.d p)) = _
    rw [chartCotangentDesc_d]
    change chartSectionsUp Λ X structureMap U n 1 ⊗ₜ[resolutionChartRing Λ X structureMap U n]
      (ULift.up (resolutionToChartDifferentials Λ X structureMap U n
        (KaehlerDifferential.D Λ _ ((chartResolutionIso Λ X structureMap U n).hom p.down))) :
          ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)) = _
    have hp : resolutionToChartHom Λ X structureMap U n
        ((chartResolutionIso Λ X structureMap U n).hom p.down) = p :=
      ULift.ext (Iso.hom_inv_id_apply (chartResolutionIso Λ X structureMap U n) p.down)
    rw [resolutionToChartDifferentials_D, map_one, hp]
    rfl
  | zero =>
    rw [map_zero, map_zero]
    exact (TensorProduct.tmul_zero _ _).symm
  | add x y _ _ hx hy =>
    rw [map_add, map_add, hx, hy]
    exact (TensorProduct.tmul_add _ _ _).symm
  | smul p x _ hx =>
    refine (congrArg (cotangentToChart Λ X structureMap U n)
      (chartCotangentDesc_smul Λ X structureMap U n p x)).trans ?_
    refine (cotangentToChart_smul Λ X structureMap U n _ _).trans ?_
    rw [hx]
    have hp : chartSectionsUp Λ X structureMap U n (chartAugmentationHom Λ X structureMap U n p) =
        algebraMap _ _ p :=
      ULift.ext (evaluation_app_down Λ X structureMap U n p).symm
    change chartSectionsUp Λ X structureMap U n (chartAugmentationHom Λ X structureMap U n p) •
        ((1 : (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
          (op (resolutionChart Λ X structureMap U n))) ⊗ₜ[resolutionChartRing Λ X structureMap U n]
            (ULift.up x : ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n))) =
      (1 : (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
          (op (resolutionChart Λ X structureMap U n))) ⊗ₜ[resolutionChartRing Λ X structureMap U n]
        (p • (ULift.up x : ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)))
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- `chartToCotangent` is a left inverse of `cotangentToChart`. -/
theorem chartToCotangent_cotangentToChart (U : X.Opens) (n : SimplexCategory)
    (x : CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n)) :
    chartToCotangent Λ X structureMap U n (cotangentToChart Λ X structureMap U n x) = x := by
  induction x using TensorProduct.inductionOn (R := resolutionTermAlgebra Λ X structureMap U n)
      (M := (ModuleCat.restrictScalars (CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ
        (sectionCotangentAlgebra Λ X structureMap U) (op n))).obj
          (ModuleCat.of _ (sectionCotangentAlgebra Λ X structureMap U)))
      (N := Ω[resolutionTermAlgebra Λ X structureMap U n⁄Λ]) with
  | add x y hx hy =>
    exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))
  | tmul b ω =>
    change chartSectionsDown Λ X structureMap U n (chartSectionsUp Λ X structureMap U n b) •
      chartCotangentDesc Λ X structureMap U n
        (resolutionToChartDifferentials Λ X structureMap U n ω)
        = _
    rw [chartCotangentDesc_resolutionToChartDifferentials]
    exact (ModuleCat.ExtendScalars.smul_tmul
      (f := CommAlgCat.standardResolutionAugmentationHom.{u, u}
      Λ (sectionCotangentAlgebra Λ X structureMap U) (op n))
      (M := ModuleCat.of _ Ω[resolutionTermAlgebra Λ X structureMap U n⁄Λ]) _ 1 ω).trans
      (congrArg (fun z => (z ⊗ₜ[resolutionTermAlgebra Λ X structureMap U n,
        CommAlgCat.standardResolutionAugmentationHom.{u, u} Λ _ (op n)] ω :
          CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n)))
        (mul_one (show sectionCotangentAlgebra Λ X structureMap U from b)))

/-- `chartToCotangent` is a right inverse of `cotangentToChart`. -/
theorem cotangentToChart_chartToCotangent (U : X.Opens) (n : SimplexCategory)
    (t : (chartBaseChangePresheaf Λ X structureMap).obj
      (op (resolutionChart Λ X structureMap U n))) :
    cotangentToChart Λ X structureMap U n (chartToCotangent Λ X structureMap U n t) = t := by
  let := ((evaluation.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  induction t using TensorProduct.inductionOn (R := resolutionChartRing Λ X structureMap U n)
      (M := (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
        (op (resolutionChart Λ X structureMap U n)))
      (N := ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)) with
  | add x y hx hy =>
    exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))
  | tmul b m =>
    change cotangentToChart Λ X structureMap U n (chartSectionsDown Λ X structureMap U n b •
      chartCotangentDesc Λ X structureMap U n m.down) = _
    rw [cotangentToChart_smul, cotangentToChart_chartCotangentDesc]
    change b • ((1 : (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
        (op (resolutionChart Λ X structureMap U n))) ⊗ₜ[resolutionChartRing Λ X structureMap U n]
          m) = b ⊗ₜ[resolutionChartRing Λ X structureMap U n] m
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end AlgebraicGeometry.PolynomialChart
