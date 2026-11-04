module

public import StacksFrontier.Cotangent.StandardResolutionCharts
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartFibred
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceFibre
public import StacksFrontier.Cotangent.ResolutionPointCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionTransfer

/-!
# The fibres of the category of polynomial charts of a scheme

Let `X` be a scheme over a ring `Λ` and let `C_{X/Λ}` be its category of polynomial charts, fibred
over the opens of `X`. For an open `U` the fibre of `C_{X/Λ}` over `U` is the site `C_{𝒪_X(U)/Λ}`
of Tag 08PR, by the `Γ`–`Spec` adjunction. Through this identification the cosimplicial charts
`𝐀_{•,U} = Spec(P_{•,U})` of the standard resolution of `𝒪_X(U)` over `Λ` satisfy the condition of
Cohomology on Sites, Lemma 08Q9, by Tag 08PT. Together with the fibred category situation of
Tag 08P8 formed by `C_{X/Λ} ⥤ X_Zar`, these are the inputs of Tag 08VB.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.fibredCategorySituation`: the fibred category situation.
* `AlgebraicGeometry.PolynomialChart.specFunctor`: the functor from `C_{𝒪_X(U)/Λ}` to the fibre
  over `U`, and `AlgebraicGeometry.PolynomialChart.fibreEquivalence` the resulting equivalence.

## Main results

* `AlgebraicGeometry.PolynomialChart.standardResolutionChart_comp_whiskeringRight`:
  `U ↦ 𝐀_{•,U}` lies over the identity of `X_Zar`.
* `AlgebraicGeometry.PolynomialChart.exists_homotopyEquivalences_standardResolutionChart`: every
  `Mor(𝐀_{•,U}, W)` is homotopy equivalent to a point.

## References

* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.PolynomialChart

open AlgebraicGeometry.Space.PolynomialChart (polyIndex polyEquiv specMap_injective specPreimage
  specMap_specPreimage toSpecΓ_specMap_injective commRingCat_apply_congr commAlgCat_apply_congr
  ofAlgHom)

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
  (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-- The fibred category situation of Tag 08P8 formed by the polynomial charts of `X`: the small
Zariski ringed site `(X_Zar, 𝒪_X)` and the fibred forgetful functor `C_{X/Λ} ⥤ X_Zar`. -/
def fibredCategorySituation :
    Stacks.Sites.FibredCategory.FibredCategorySituation.{u, u, u + 1, u, u} where
  base := X.zariskiRingedSite
  C := PolynomialChart Λ X structureMap
  p := openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)
  isFibered := openFunctor_isFibered Λ X structureMap

/-- `U ↦ 𝐀_{•,U}` lies over the identity of the Zariski site: postcomposed with the forgetful
functor, every `𝐀_{•,U}` is the constant cosimplicial object at `U`, and every map
`𝐀_{•,V} ⟶ 𝐀_{•,U}` the constant one at the inclusion `V ≤ U`. -/
theorem standardResolutionChart_comp_whiskeringRight :
    (standardResolutionChart Λ X structureMap :
        (fibredCategorySituation Λ X structureMap).base.C ⥤
          CosimplicialObject (fibredCategorySituation Λ X structureMap).C) ⋙
      (Functor.whiskeringRight SimplexCategory (fibredCategorySituation Λ X structureMap).C
        (fibredCategorySituation Λ X structureMap).base.C).obj
          (fibredCategorySituation Λ X structureMap).p =
      Functor.const SimplexCategory :=
  CategoryTheory.Functor.ext (fun U => standardResolutionChart_comp_openFunctor Λ X structureMap U)
    fun _ _ _ => by
      ext
      rfl

/-! ### The chart attached to an augmented polynomial algebra -/

variable (U : X.Opens)

/-- A polynomial `Λ`-algebra is isomorphic to the polynomial algebra on its chosen variables. -/
def polyAlgIso {P : CommAlgCat.{u} Λ} (hP : CommAlgCat.IsPolynomialAlgebra Λ P) :
    P ≅ CommAlgCat.of Λ (MvPolynomial (polyIndex Λ hP) Λ) :=
  CommAlgCat.isoMk (polyEquiv Λ hP).symm

/-- The polynomial chart on `U` attached to an object of the site `C_{𝒪_X(U)/Λ}`: the spectrum of
the polynomial algebra, together with the morphism from `U` determined by the augmentation. -/
def siteChart (a : CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U))) :
    PolynomialChart Λ X structureMap :=
  ofAugmentation (polyAlgIso Λ a.unop.property) a.unop.obj.hom

/-- The morphism of polynomial charts attached to a morphism of the site `C_{𝒪_X(U)/Λ}`. -/
def siteChartHom {a b : CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U))}
    (f : a ⟶ b) : siteChart Λ X structureMap U a ⟶ siteChart Λ X structureMap U b :=
  homOfAugmentation le_rfl f.unop.hom.left (by
    rw [Over.w f.unop.hom, Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id,
      CategoryTheory.Functor.map_id, Category.comp_id])

/-- The functor from the site `C_{𝒪_X(U)/Λ}` to the category of polynomial charts of `X`. -/
def siteChartFunctor :
    CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U)) ⥤
      PolynomialChart Λ X structureMap where
  obj := siteChart Λ X structureMap U
  map := siteChartHom Λ X structureMap U
  map_id a := by
    ext
    change Spec.map _ = 𝟙 _
    rw [← Spec.map_id]
    rfl
  map_comp f g := by
    ext
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl

/-- The charts of `siteChartFunctor` lie over `U`. -/
theorem siteChartFunctor_comp_openFunctor :
    siteChartFunctor Λ X structureMap U ⋙ openFunctor =
      (Functor.const _).obj U :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => Subsingleton.elim _ _

/-- **The functor from the site `C_{𝒪_X(U)/Λ}` to the fibre of `C_{X/Λ}` over `U`.** -/
def specFunctor : CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U)) ⥤
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).Fiber U :=
  Functor.Fiber.inducedFunctor (siteChartFunctor_comp_openFunctor Λ X structureMap U)

/-- The arrow `U ⟶ Spec P` of the chart attached to an augmentation `P ⟶ 𝒪_X(U)` is the one
the augmentation induces through the `Γ`–`Spec` adjunction. -/
theorem siteChart_toAffine
    (a : CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U))) :
    (siteChart Λ X structureMap U a).toAffine = (U : Scheme.{u}).toSpecΓ ≫
      Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map a.unop.obj.hom) := rfl

/-- The structural arrow of the chart attached to an object of `C_{𝒪_X(U)/Λ}` is the spectrum of
the structure map of its algebra. -/
theorem siteChart_toBase
    (a : CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U))) :
    (siteChart Λ X structureMap U a).toBase =
      Spec.map (CommRingCat.ofHom (algebraMap Λ a.unop.obj.left)) :=
  ofAugmentation_toBase _ _

/-- A morphism of the site `C_{𝒪_X(U)/Λ}` is determined by the morphism of charts it induces. -/
instance specFunctor_faithful : (specFunctor Λ X structureMap U).Faithful where
  map_injective {a b} {f g} h := by
    have h1 : siteChartHom Λ X structureMap U f = siteChartHom Λ X structureMap U g :=
      congrArg Functor.Fiber.fiberInclusion.map h
    have h2 := specMap_injective (congrArg Hom.affine h1)
    refine Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      (CommAlgCat.hom_ext (AlgHom.ext fun x => ?_))))
    exact commRingCat_apply_congr h2 x

/-- Every morphism of the fibre over `U` comes from a morphism of the site `C_{𝒪_X(U)/Λ}`. -/
instance specFunctor_full : (specFunctor Λ X structureMap U).Full where
  map_surjective {a b} φ := by
    obtain ⟨ψ, hlift, rfl⟩ :
        ∃ (ψ : siteChart Λ X structureMap U a ⟶ siteChart Λ X structureMap U b)
          (h : (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).IsHomLift
            (𝟙 U) ψ), φ = ⟨ψ, h⟩ :=
      ⟨φ.1, φ.2, rfl⟩
    obtain ⟨g, hgspec⟩ : ∃ g : (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).obj b.unop.obj.left ⟶
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).obj a.unop.obj.left,
        Spec.map g = ψ.affine :=
      ⟨specPreimage ψ.affine, specMap_specPreimage ψ.affine⟩
    have hbc := ψ.base_comm
    rw [siteChart_toBase, siteChart_toBase] at hbc
    have hbase : CommRingCat.ofHom (algebraMap Λ b.unop.obj.left) ≫ g =
        CommRingCat.ofHom (algebraMap Λ a.unop.obj.left) := by
      refine specMap_injective ?_
      rw [Spec.map_comp, hgspec]
      exact hbc
    have hmc : (siteChart Λ X structureMap U a).toAffine ≫ ψ.affine =
        (siteChart Λ X structureMap U b).toAffine := by
      refine ψ.map_comm.trans ?_
      have h : X.homOfLE ψ.open_le = 𝟙 (U : Scheme.{u}) := Scheme.homOfLE_rfl X U
      rw [h]
      exact Category.id_comp _
    have haug : g ≫ (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map a.unop.obj.hom =
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map b.unop.obj.hom := by
      have e1 : Spec.map (g ≫ (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map a.unop.obj.hom) =
          Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map a.unop.obj.hom) ≫ ψ.affine :=
        (Spec.map_comp _ _).trans (by rw [hgspec]; rfl)
      exact toSpecΓ_specMap_injective (V := (U : Scheme.{u}))
        ((congrArg (fun t => (U : Scheme.{u}).toSpecΓ ≫ t) e1).trans
          ((Category.assoc _ _ _).symm.trans hmc))
    refine ⟨(ObjectProperty.homMk (Over.homMk (ofAlgHom Λ
      ({ __ := g.hom, commutes' := fun r => commRingCat_apply_congr hbase r } :
        (b.unop.obj.left : Type u) →ₐ[Λ] (a.unop.obj.left : Type u))) ?_)).op, ?_⟩
    · exact CommAlgCat.hom_ext (AlgHom.ext fun x => commRingCat_apply_congr haug x)
    · refine Functor.Fiber.hom_ext (Hom.ext ?_)
      change Spec.map _ = ψ.affine
      rw [← hgspec]
      rfl

/-! ### The functor is essentially surjective -/

variable {Λ X structureMap U} in
/-- A morphism of polynomial charts between charts on the same open `U` lies over the identity
of `U`. -/
theorem isHomLift_id_of_openPart {P Q : PolynomialChart Λ X structureMap} (hP : P.openPart = U)
    (hQ : Q.openPart = U) (φ : P ⟶ Q) :
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).IsHomLift (𝟙 U) φ :=
  IsHomLift.of_fac' _ _ _ hP hQ (Subsingleton.elim _ _)

variable {Λ X structureMap} in
/-- The affine space of a polynomial chart is an affine scheme. -/
instance isAffine_affineSpace (P : PolynomialChart Λ X structureMap) : IsAffine P.affineSpace :=
  IsAffine.of_isIso P.affineEquiv.hom

/-- The ring of global functions on the affine space of a polynomial chart is a `Λ`-algebra
through the structural arrow of the chart. -/
instance chartAlgebraStructure (P : PolynomialChart Λ X structureMap) :
    Algebra Λ (Γ(P.affineSpace, ⊤) : Type u) :=
  ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop).hom.toAlgebra

/-- The `Λ`-algebra of global functions on the affine space of a polynomial chart. -/
def chartAlgebra (P : PolynomialChart Λ X structureMap) : CommAlgCat.{u} Λ :=
  CommAlgCat.of Λ (Γ(P.affineSpace, ⊤) : Type u)

/-- The augmentation `Γ(A, 𝒪_A) ⟶ 𝒪_X(U)` of a polynomial chart `U ⟶ A`, given by pullback of
functions along the chart map. -/
def chartAugmentation (P : PolynomialChart Λ X structureMap) :
    chartAlgebra Λ X structureMap P ⟶ (openAlgebra Λ X structureMap).obj (op P.openPart) :=
  ofAlgHom Λ
    { __ := P.toAffine.appTop.hom
      commutes' := fun r => by
        have h : (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ (P.toAffine ≫ P.toBase).appTop =
            baseRingHom Λ X structureMap ≫ P.openPart.ι.appTop := by
          rw [show P.toAffine ≫ P.toBase = P.openPart.ι ≫ structureMap from P.comm,
            baseRingHom, Scheme.Hom.comp_appTop, Category.assoc]
        exact commRingCat_apply_congr h r }

/-- The presentation, through the affine space of a chart, of its ring of functions as a
polynomial algebra. -/
def chartAlgebraIso (P : PolynomialChart Λ X structureMap) :
    CommRingCat.of (MvPolynomial P.variableIndex Λ) ≅ Γ(P.affineSpace, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial P.variableIndex Λ))).symm ≪≫
    Scheme.Γ.mapIso P.affineEquiv.op

/-- The presentation of the ring of functions on the affine space of a chart is a map of
`Λ`-algebras. -/
theorem chartAlgebraIso_hom_comp (P : PolynomialChart Λ X structureMap) :
    CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial P.variableIndex Λ) ≫
        (chartAlgebraIso Λ X structureMap P).hom =
      CommRingCat.ofHom (algebraMap Λ (chartAlgebra Λ X structureMap P : Type u)) := by
  show CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial P.variableIndex Λ) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial P.variableIndex Λ))).inv ≫
        P.affineEquiv.hom.appTop =
    (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Hom.comp_appTop]
  rfl

/-- The ring of functions on the affine space of a polynomial chart is a polynomial
`Λ`-algebra. -/
theorem isPolynomialAlgebra_chartAlgebra (P : PolynomialChart Λ X structureMap) :
    CommAlgCat.IsPolynomialAlgebra Λ (chartAlgebra Λ X structureMap P) :=
  ⟨P.variableIndex, ⟨{ (chartAlgebraIso Λ X structureMap P).commRingCatIsoToRingEquiv with
    commutes' := fun r =>
      commRingCat_apply_congr (chartAlgebraIso_hom_comp Λ X structureMap P) r }⟩⟩

/-- The object of the site `C_{𝒪_X(U)/Λ}` attached to a polynomial chart on `U`. -/
def chartObject (P : PolynomialChart Λ X structureMap) :
    CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op P.openPart)) :=
  op ⟨Over.mk (chartAugmentation Λ X structureMap P),
    isPolynomialAlgebra_chartAlgebra Λ X structureMap P⟩

/-- The comparison from the chart attached to the augmentation of a polynomial chart `P` to `P`
itself, given by the identification of the affine space of `P` with the spectrum of its ring of
functions. -/
def chartSpecHom (P : PolynomialChart Λ X structureMap) :
    siteChart Λ X structureMap P.openPart (chartObject Λ X structureMap P) ⟶ P where
  open_le := le_rfl
  affine := P.affineSpace.isoSpec.inv
  map_comm := by
    change ((P.openPart : Scheme.{u}).toSpecΓ ≫ Spec.map P.toAffine.appTop) ≫
        P.affineSpace.isoSpec.inv = X.homOfLE (le_refl P.openPart) ≫ P.toAffine
    rw [Scheme.homOfLE_rfl, Category.id_comp, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  base_comm := by
    rw [siteChart_toBase]
    change P.affineSpace.isoSpec.inv ≫ P.toBase =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop)
    rw [Iso.inv_comp_eq, Scheme.isoSpec_hom]
    exact (AlgebraicGeometry.Space.PolynomialChart.toSpecΓ_specMap_appTop P.toBase).symm

/-- The comparison from a polynomial chart to the chart attached to its augmentation, inverse to
`chartSpecHom`. -/
def chartSpecInv (P : PolynomialChart Λ X structureMap) :
    P ⟶ siteChart Λ X structureMap P.openPart (chartObject Λ X structureMap P) where
  open_le := le_rfl
  affine := P.affineSpace.isoSpec.hom
  map_comm := by
    change P.toAffine ≫ P.affineSpace.isoSpec.hom =
      X.homOfLE (le_refl P.openPart) ≫
        (P.openPart : Scheme.{u}).toSpecΓ ≫ Spec.map P.toAffine.appTop
    rw [Scheme.homOfLE_rfl, Category.id_comp, Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality]
  base_comm := by
    rw [siteChart_toBase]
    change P.affineSpace.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop) = P.toBase
    rw [Scheme.isoSpec_hom]
    exact AlgebraicGeometry.Space.PolynomialChart.toSpecΓ_specMap_appTop P.toBase

/-- Every object of the fibre over `U` is isomorphic to the chart attached to its own
augmentation. -/
def chartSpecIso (P : PolynomialChart Λ X structureMap) :
    (specFunctor Λ X structureMap P.openPart).obj (chartObject Λ X structureMap P) ≅
      (⟨P, rfl⟩ : (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).Fiber
        P.openPart) where
  hom := ⟨chartSpecHom Λ X structureMap P,
    isHomLift_id_of_openPart (U := P.openPart)
      (P := siteChart Λ X structureMap P.openPart (chartObject Λ X structureMap P)) (Q := P)
      rfl rfl (chartSpecHom Λ X structureMap P)⟩
  inv := ⟨chartSpecInv Λ X structureMap P,
    isHomLift_id_of_openPart (U := P.openPart) (P := P)
      (Q := siteChart Λ X structureMap P.openPart (chartObject Λ X structureMap P))
      rfl rfl (chartSpecInv Λ X structureMap P)⟩
  hom_inv_id := Functor.Fiber.hom_ext (Hom.ext P.affineSpace.isoSpec.inv_hom_id)
  inv_hom_id := Functor.Fiber.hom_ext (Hom.ext P.affineSpace.isoSpec.hom_inv_id)

/-- Every object of the fibre over `U` comes from an object of the site `C_{𝒪_X(U)/Λ}`, namely
from its own ring of functions with its augmentation. -/
instance specFunctor_essSurj : (specFunctor Λ X structureMap U).EssSurj where
  mem_essImage Z := by
    obtain ⟨P, rfl⟩ := Z
    exact ⟨chartObject Λ X structureMap P, ⟨chartSpecIso Λ X structureMap P⟩⟩

/-- The functor from the site `C_{𝒪_X(U)/Λ}` to the fibre over `U` is an equivalence. -/
instance specFunctor_isEquivalence : (specFunctor Λ X structureMap U).IsEquivalence where

/-- **The fibre of `C_{X/Λ}` over an open `U` of `X` is the site `C_{𝒪_X(U)/Λ}` of Tag 08PR.** -/
def fibreEquivalence :
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).Fiber U ≌
      CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U)) :=
  (specFunctor Λ X structureMap U).asEquivalence.symm

/-! ### The cosimplicial charts of the standard resolution in the fibre -/

/-- The cosimplicial object `CommAlgCat.resolutionCosimplicialObject` of the standard resolution
of `𝒪_X(U)` over `Λ`, an object of the site `C_{𝒪_X(U)/Λ}`. -/
abbrev standardResolutionSiteObject :
    CosimplicialObject
      (CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U))) :=
  CommAlgCat.resolutionCosimplicialObject
    (CommAlgCat.standardResolution.{u, u} Λ ((openAlgebra Λ X structureMap).obj (op U))).hom
    (CommAlgCat.standardResolution_isResolution.{u, u} Λ
      ((openAlgebra Λ X structureMap).obj (op U))).isPolynomialAlgebra

/-- The morphism of charts `𝐀_{n,U} ⟶ Spec(P_{n,U})` between the two presentations of the same
affine space. -/
def standardResolutionFibreChartHom (n : SimplexCategory) :
    ((standardResolutionChart Λ X structureMap).obj U).obj n ⟶
      siteChart Λ X structureMap U ((standardResolutionSiteObject Λ X structureMap U).obj n) :=
  homOfAugmentation le_rfl (𝟙 _) (by
    rw [Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact Category.id_comp _)

/-- The inverse of `standardResolutionFibreChartHom`. -/
def standardResolutionFibreChartInv (n : SimplexCategory) :
    siteChart Λ X structureMap U ((standardResolutionSiteObject Λ X structureMap U).obj n) ⟶
      ((standardResolutionChart Λ X structureMap).obj U).obj n :=
  homOfAugmentation le_rfl (𝟙 _) (by
    rw [Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact Category.id_comp _)

/-- In the fibre over `U`, the cosimplicial charts `𝐀_{•,U}` are the image under `specFunctor` of
the cosimplicial object of the standard resolution: the two differ only in the presentations of
their affine spaces, which morphisms of charts do not see. -/
def standardResolutionFibreChartIso :
    standardResolutionFibreChart Λ X structureMap U ≅
      standardResolutionSiteObject Λ X structureMap U ⋙ specFunctor Λ X structureMap U :=
  NatIso.ofComponents
    (fun n =>
      { hom := ⟨standardResolutionFibreChartHom Λ X structureMap U n,
          isHomLift_id_of_openPart (U := U) rfl rfl
            (standardResolutionFibreChartHom Λ X structureMap U n)⟩
        inv := ⟨standardResolutionFibreChartInv Λ X structureMap U n,
          isHomLift_id_of_openPart (U := U) rfl rfl
            (standardResolutionFibreChartInv Λ X structureMap U n)⟩
        hom_inv_id := by
          apply Functor.Fiber.hom_ext
          apply Hom.ext
          change Spec.map _ ≫ Spec.map _ = 𝟙 _
          rw [← Spec.map_comp, ← Spec.map_id]
          rfl
        inv_hom_id := by
          apply Functor.Fiber.hom_ext
          apply Hom.ext
          change Spec.map _ ≫ Spec.map _ = 𝟙 _
          rw [← Spec.map_comp, ← Spec.map_id]
          rfl })
    (fun {n m} g => by
      apply Functor.Fiber.hom_ext
      apply Hom.ext
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl)

/-- **The condition of Tag 08Q9 on `𝐀_{•,U}`.** For every open `U` of `X` and every object `W`
of the fibre of `C_{X/Λ}` over `U`, the simplicial set `Mor(𝐀_{•,U}, W)` of the fibre is
homotopy equivalent to a singleton. It holds because `fibreEquivalence` carries `𝐀_{•,U}` to the
cosimplicial object of the standard resolution of `𝒪_X(U)` over `Λ` in the site
`C_{𝒪_X(U)/Λ}`, for which it is Tag 08PT. -/
theorem exists_homotopyEquivalences_standardResolutionFibreChartMor
    (W : (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).Fiber U) :
    ∃ f : (standardResolutionFibreChart Λ X structureMap U).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f := by
  let E := fibreEquivalence Λ X structureMap U
  obtain ⟨f, hf⟩ := CommAlgCat.exists_homotopyEquivalences_standardResolutionMor Λ
    ((openAlgebra Λ X structureMap).obj (op U)) (E.functor.obj W)
  have γ : standardResolutionFibreChart Λ X structureMap U ⋙ E.functor ≅
      standardResolutionSiteObject Λ X structureMap U :=
    Functor.isoWhiskerRight (standardResolutionFibreChartIso Λ X structureMap U) E.functor ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ E.counitIso ≪≫ Functor.rightUnitor _
  have α : (standardResolutionFibreChart Λ X structureMap U).op ⋙ yoneda.obj W ≅
      (standardResolutionFibreChart Λ X structureMap U ⋙ E.functor).op ⋙
        yoneda.obj (E.functor.obj W) :=
    NatIso.ofComponents (fun _ => Equiv.toIso E.fullyFaithfulFunctor.homEquiv)
      (by intro _ _ _; ext x; simp)
  exact ⟨(α ≪≫ (Functor.isoWhiskerRight (NatIso.op γ) (yoneda.obj (E.functor.obj W))).symm).hom ≫
    f, SimplicialObject.homotopyEquivalences_iso_comp _ hf⟩

/-- **The condition of Tag 08Q9 on `U ↦ 𝐀_{•,U}`**, in the spelling of the fibred category
situation: `exists_homotopyEquivalences_standardResolutionFibreChartMor` read through
`standardResolutionChart_comp_whiskeringRight`. -/
theorem exists_homotopyEquivalences_standardResolutionChart
    (U : (fibredCategorySituation Λ X structureMap).base.C)
    (W : (fibredCategorySituation Λ X structureMap).p.Fiber U) :
    ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj
          (standardResolutionChart_comp_whiskeringRight Λ X structureMap) U)).op ⋙
          yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f :=
  exists_homotopyEquivalences_standardResolutionFibreChartMor Λ X structureMap U W

end AlgebraicGeometry.PolynomialChart

end

end
