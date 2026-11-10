module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Sheafify
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.FreeSum
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Bicomplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Cellular
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Vanishing

/-!
# Derived lower shriek computed by a fibrewise point resolution

In the situation of
`StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Basic`,
for an abelian
sheaf `F` on the total category, `Lπ_!(F)` is isomorphic to the complex of sheaves on the base
whose term in degree `-n` is the sheafification of `V ↦ F(A_{n,V})`, and `L_nπ_!(F)` is the
sheafification of `V ↦ H_n(F(A_{•,V}))`. This is the computation of Stacks 08VB and 08VL for an
arbitrary fibred category over a site with fibre products.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.nonempty_derivedAbelianLowerShriekIso`:
  `Lπ_!(F)` is isomorphic to the complex of sheaves whose term in degree `-n` is the sheafification
  of `V ↦ F(A_{n,V})`.
* `FibredCategorySituation.nonempty_derivedAbelianLowerShriekHomologyIso`: `L_nπ_!(F)` is the
  sheafification of `V ↦ H_n(F(A_{•,V}))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open StacksDraft.TotalComplexQuasiIso

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  (A : s.base.C ⥤ CosimplicialObject s.C)

/-- **The complex of sheaves of a fibrewise point resolution**: the sheafification of the complex
of presheaves `V ↦ G(A_{•,V})`, its simplicial degree `n` sitting in cohomological degree `-n`. -/
abbrev pointSheafComplex (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) :
    CochainComplex (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) ℤ :=
  ((presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj ((pointMooreCochain s A).obj G)

/-- The Moore cochain complex of `G(A_{•,V})` is the total complex of the point bicomplex of the
single complex of `G` in degree `0`. -/
private def pointMooreCochainIsoTotalSingle (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) :
    (pointMooreCochain s A).obj G ≅
      (pointBicomplex s A ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)).total
        (ComplexShape.up ℤ) := by
  let := hasTotal_singleColumn ((pointMooreCochain s A).obj G) (0 : ℤ)
  let f := HomologicalComplex₂.total.map
    ((HomologicalComplex.singleMapHomologicalComplex (pointMooreCochain s A)
      (ComplexShape.up ℤ) 0).app G).inv (ComplexShape.up ℤ)
  have : IsIso f := Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  exact Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso ((pointMooreCochain s A).obj G)
    ≪≫ asIso f

/-- Sheafifying the single complex of the underlying presheaf of a sheaf `F` recovers the single
complex of `F`. -/
private def sheafifySingleIso (F : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) :
    ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC vC}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F.obj) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F :=
  (HomologicalComplex.singleMapHomologicalComplex
      (presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) (ComplexShape.up ℤ) 0).app
      F.obj ≪≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
      (asIso ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC vC}).counit.app F))

variable {A}
  (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)
  (hres : ∀ (V : s.base.C) (W : s.p.Fiber V),
    ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1},
      SimplicialObject.homotopyEquivalences (Type vC) f)

attribute [local instance] HasDerivedCategory.standard

include hres in
/-- **`Lπ_!` is computed by the complex of sheaves of a fibrewise point resolution**, given the
vanishing of the positive homology of `G(A_{•,V})` on free abelian presheaves on coproducts of
representables. -/
theorem nonempty_derivedAbelianLowerShriekIso_of_vanishing
    (hvan : ∀ G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}, IsFreeSum s G →
      ∀ n : ℕ, IsZero (((pointMooreComplex s A).obj G).homology (n + 1)))
    (F : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) :
    Nonempty (s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      DerivedCategory.Q.obj (pointSheafComplex s A F.obj)) := by
  have : s.abelianLowerShriek.Additive := s.abelianLowerShriek_additive
  have : s.abelianLowerShriek.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (F := s.abelianLowerShriek)
  obtain ⟨Q, hQle, hQ, π, hπ⟩ := exists_isFreeSum_resolution s F.obj
  let aC := presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC vC}
  let aD := presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}
  let K := (aC.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q
  have hKle : CochainComplex.IsStrictlyLE K 0 := (CochainComplex.isStrictlyLE_iff K 0).2
    fun i hi => Functor.map_isZero aC (CochainComplex.isZero_of_isStrictlyLE Q 0 i hi)
  have hπK : QuasiIso ((aC.mapHomologicalComplex (ComplexShape.up ℤ)).map π) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology π aC
  let e1 : DerivedCategory.Q.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F :=
    asIso (DerivedCategory.Q.map ((aC.mapHomologicalComplex (ComplexShape.up ℤ)).map π)) ≪≫
      DerivedCategory.Q.mapIso (sheafifySingleIso s F)
  have hcell := isIso_derivedAbelianLowerShriekComparison_app s K
    fun n => isSumOfExtensionByZeroUnitsAb_sheafify s (hQ n)
  let e2 : s.derivedAbelianLowerShriek.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        ((s.abelianLowerShriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    s.derivedAbelianLowerShriek.mapIso ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
      asIso ((Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{
        max w uD vD uC, vC, uC, vD, uD} s.topology s.base.J s.p).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  let e3 : (s.abelianLowerShriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      (aD.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((pointZero s A).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => ((pointZeroSheafifyIso s hA hres).app (Q.X n)).symm)
      (fun i j _ => ((pointZeroSheafifyIso s hA hres).inv.naturality (Q.d i j)).symm)
  have hcol := quasiIso_pointBicomplexColumnTotalMap s A Q
    fun p => quasiIso_pointMooreCochainAugmentation s A (Q.X p) (hvan _ (hQ p))
  have hunit := isIso_totalSingleRowZeroUnit
    (((pointZero s A).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
  let φ : (pointBicomplex s A Q).total (ComplexShape.up ℤ) ⟶
      ((pointZero s A).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q :=
    HomologicalComplex₂.total.map (pointBicomplexColumnMap s A Q) (ComplexShape.up ℤ) ≫
      inv (totalSingleRowZeroUnit
        (((pointZero s A).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q))
  have hφ : QuasiIso ((aD.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology φ aD
  have hrow := quasiIso_pointBicomplexTotalMap s A π
  let e5 := asIso (DerivedCategory.Q.map ((aD.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex₂.total.map ((pointBicomplexFunctor s A).map π) (ComplexShape.up ℤ))))
  exact ⟨s.derivedAbelianLowerShriek.mapIso e1.symm ≪≫ e2 ≪≫ DerivedCategory.Q.mapIso e3 ≪≫
    (asIso (DerivedCategory.Q.map ((aD.mapHomologicalComplex (ComplexShape.up ℤ)).map φ))).symm ≪≫
    e5 ≪≫ DerivedCategory.Q.mapIso
      ((aD.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (pointMooreCochainIsoTotalSingle s A F.obj)).symm⟩

include hres in
/-- **`Lπ_!` is computed by the complex of sheaves of a fibrewise point resolution**: for an
abelian sheaf `F` on the total category, `Lπ_!(F)` is isomorphic in `D(Ab(D))` to the complex of
sheaves whose term in degree `-n` is the sheafification of `V ↦ F(A_{n,V})`. -/
theorem nonempty_derivedAbelianLowerShriekIso
    (F : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) :
    Nonempty (s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      DerivedCategory.Q.obj (pointSheafComplex s A F.obj)) :=
  nonempty_derivedAbelianLowerShriekIso_of_vanishing s hA hres
    (isZero_pointMooreComplex_homology_of_isFreeSum s hA hres) F

include hres in
/-- **`L_nπ_!` is the sheafification of the homology of `V ↦ F(A_{•,V})`**: for an abelian sheaf
`F` on the total category and `n ≥ 0`, `L_nπ_!(F) = H^{-n}(Lπ_! F)` is the sheaf associated to the
presheaf `V ↦ H_n(F(A_{•,V}))`. -/
theorem nonempty_derivedAbelianLowerShriekHomologyIso
    (F : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) (n : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).obj
        (s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}).obj
        (((pointMooreComplex s A).obj F.obj).homology n)) := by
  obtain ⟨e⟩ := nonempty_derivedAbelianLowerShriekIso s hA hres F
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  exact ⟨(DerivedCategory.homologyFunctor _ (-(n : ℤ))).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ (-(n : ℤ))).app _ ≪≫
    ShortComplex.mapHomologyIso (((pointMooreCochain s A).obj F.obj).sc (-(n : ℤ)))
      (presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) ≪≫
    (presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}).mapIso
      (HomologicalComplex.extendHomologyIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) hn)⟩

end Stacks.Sites.FibredCategory.FibredCategorySituation
