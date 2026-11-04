module

public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedClasses
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact

/-!
# The derived unit `g⁻¹ ⟶ Lg^*` of Stacks 0GQ7

Let `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be a morphism of ringed topoi. The inverse image
`g⁻¹ : Mod(𝒪_𝒞) ⥤ Mod(g⁻¹𝒪_𝒞)` and the restriction of scalars
`Mod(𝒪_𝒟) ⥤ Mod(g⁻¹𝒪_𝒞)` along `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟` are exact, so they act on unbounded
derived categories. The unit `M ⟶ g^*M = 𝒪_𝒟 ⊗_{g⁻¹𝒪_𝒞} g⁻¹M` of extension and restriction of
scalars along `g^♯` derives to a natural transformation `g⁻¹K ⟶ Lg^*K` of functors
`D(𝒪_𝒞) ⥤ D(g⁻¹𝒪_𝒞)`, the derived pullback `Lg^*` of **Stacks 06YY** being read over `g⁻¹𝒪_𝒞`.

It is obtained from the universal property of `Lg^*` read over `g⁻¹𝒪_𝒞`: since `Lg^*` is
computed by K-flat resolutions (**Stacks 06YS**, **Stacks 06YY**), it stays a left derived
functor after the exact restriction of scalars, and the degreewise unit, which lives on the
homotopy category, lifts uniquely. On a complex `K` it is the degreewise unit followed by the
comparison `Lg^*K ⟶ g^*K` (`derivedUnit_app_Q`).

## Main definitions

* `Deformation.ToposThickening.LiftingMorphismDerived.invImageDerived`: the inverse image on
  derived categories.
* `.restrictDerived`: the restriction of scalars along `g^♯` on derived categories, with
  `.restrictComplex` and `.restrictDerivedFactors` its action on complexes and the factorization
  `Q ⋙ restrictDerived g ≅ restrictComplex g ⋙ Q`.
* `.pullbackUnitComplex`: the degreewise unit `g⁻¹K ⟶ g^*K` on a complex.
* `.derivedUnit`: the derived unit `g⁻¹ ⟶ Lg^*`.

## Main results

* `.isLeftDerivedFunctor_derivedPullback_comp_restrictDerived`: `Lg^*` followed by restriction
  of scalars is still a left derived functor.
* `.derivedUnit_app_Q`: the derived unit at a complex, followed by the comparison
  `Lg^*K ⟶ g^*K`, is the degreewise unit.

## References

* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.RingedToposModules (inverseImageModules extendScalarsFSharp fSharpCommRing)
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)
open Deformation.ToposThickening.InverseImageExtension (invImage baseIso
  comp_fSharpInverseImage_eq)
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

universe u v' u' w'

attribute [local instance 10000] HasDerivedCategory.standard

namespace Deformation.ToposThickening.LiftingMorphismDerived

variable {X Y : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (g : RingedToposHom Y X)

/-! ### The two exact functors on derived categories -/

/-- **The inverse image on derived categories** `g⁻¹ : D(𝒪_𝒞) ⥤ D(g⁻¹𝒪_𝒞)`, induced by the
exact inverse image of sheaves of modules. -/
abbrev invImageDerived :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
        g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategory

/-- **The restriction of scalars along `g^♯` on derived categories**
`D(𝒪_𝒟) ⥤ D(g⁻¹𝒪_𝒞)`, induced by the exact right adjoint `restrictAlong g` of
`extendRestrictAdjunction g`. -/
abbrev restrictDerived :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
        g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  (restrictAlong g).mapDerivedCategory

/-- The restriction of scalars along `g^♯` on complexes, `C(𝒪_𝒟) ⥤ C(g⁻¹𝒪_𝒞)`, its source
and target spelled as those of `Lg^*` and of the inverse image. -/
abbrev restrictComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
        g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ :=
  (restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `restrictDerived g` is induced by `restrictComplex g`:
`Q ⋙ restrictDerived g ≅ restrictComplex g ⋙ Q` (`Functor.mapDerivedCategoryFactors`). -/
def restrictDerivedFactors :
    DerivedCategory.Q ⋙ restrictDerived g ≅ restrictComplex g ⋙ DerivedCategory.Q :=
  (restrictAlong g).mapDerivedCategoryFactors

/-! ### The degreewise unit -/

/-- **The degreewise unit `g⁻¹K ⟶ g^*K`** on a complex `K` of `𝒪_𝒞`-modules, read over
`g⁻¹𝒪_𝒞`: in each degree the unit `g⁻¹Kⁱ ⟶ 𝒪_𝒟 ⊗_{g⁻¹𝒪_𝒞} g⁻¹Kⁱ` of
`extendRestrictAdjunction g`. -/
def pullbackUnitComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶
      (restrictComplex g).obj
        ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) where
  f i := (extendRestrictAdjunction g).unit.app
    ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (K.X i))
  comm' i j _ := ((extendRestrictAdjunction g).unit.naturality
    ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
      (K.d i j))).symm

/-- The degreewise unit, as a natural transformation of functors on complexes. -/
def pullbackUnitNat :
    (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        restrictComplex g where
  app K := pullbackUnitComplex g K
  naturality _ _ φ := HomologicalComplex.hom_ext _ _ fun i ↦
    (extendRestrictAdjunction g).unit.naturality
      ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map (φ.f i))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The degreewise unit is natural in the complex. -/
theorem pullbackUnitComplex_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : K ⟶ L) :
    ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ ≫ pullbackUnitComplex g L =
      pullbackUnitComplex g K ≫
        (restrictComplex g).map
          ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) :=
  (pullbackUnitNat g).naturality φ

/-! ### `Lg^*` read over `g⁻¹𝒪_𝒞` -/

/-- The derived pullback `Lg^*`, followed by restriction of scalars along `g^♯`, is a left
derived functor of degreewise pullback followed by restriction of scalars: `Lg^*` is computed by
K-flat resolutions (Stacks 06YS, 06YY), so it is absolute. -/
instance isLeftDerivedFunctor_derivedPullback_comp_restrictDerived :
    (derivedPullback g ⋙ restrictDerived g).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedPullback g) (restrictDerived g)).inv ≫
        Functor.whiskerRight (derivedPullbackComparison g) (restrictDerived g))
      (quasiIsoTarget (Y := X)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_comp_of_resolutions _ (IsKFlat (Y := X))
    (fun M ↦ hasResolutions_isKFlat (Y := X) M) (pullbackOnHomotopy g)
    (fun s hs hM hN ↦ pullbackInvertsQuasiIso_isKFlat g s hs hM hN) DerivedCategory.Qh _ _ _

/-- The degreewise pullback on the homotopy category, followed by localization, read on
complexes: it is degreewise pullback followed by `Q`. -/
def pullbackOnHomotopyQuotientIso :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ pullbackOnHomotopy g ≅
      g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (g.toModulesHom.pullbackModules.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso _) ≪≫
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (pullbackModulesIso g)
      (ComplexShape.up ℤ)) DerivedCategory.Q

/-- `derivedPullbackComparisonNat` is the counit `derivedPullbackComparison g` of `Lg^*`,
restricted to complexes and read through `pullbackOnHomotopyQuotientIso`. -/
theorem derivedPullbackComparisonNat_eq :
    derivedPullbackComparisonNat g =
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (derivedPullback g) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (derivedPullbackComparison g) ≫
        (pullbackOnHomotopyQuotientIso g).hom := by
  have h : derivedPullbackComparisonNat g =
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (derivedPullback g) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (derivedPullbackComparison g) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (g.toModulesHom.pullbackModules.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
          DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso _).hom ≫
        Functor.whiskerRight (NatIso.mapHomologicalComplex (pullbackModulesIso g)
          (ComplexShape.up ℤ)).hom DerivedCategory.Q :=
    rfl
  rw [h]
  congr 2

/-- The comparison `Lg^*K ⟶ g^*K` is the counit of `Lg^*` at `K`, read through
`pullbackOnHomotopyQuotientIso`. -/
theorem derivedPullbackComparisonComplex_eq
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    derivedPullbackComparisonComplex g K =
      (derivedPullback g).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        (derivedPullbackComparison g).app ((HomotopyCategory.quotient _ _).obj K) ≫
        (pullbackOnHomotopyQuotientIso g).hom.app K := by
  rw [derivedPullbackComparisonComplex, derivedPullbackComparisonNat_eq]
  simp

/-! ### The derived unit -/

/-- The degreewise unit, localized and read on complexes through the factorizations of the two
exact functors and of `Lg^*`'s target: the natural transformation whose lift along `Lg^*` is the
derived unit. -/
def pullbackUnitQuotientNat :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ (DerivedCategory.Qh ⋙ invImageDerived g) ⟶
      HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
        (pullbackOnHomotopy g ⋙ restrictDerived g) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).hom (invImageDerived g) ≫
    (inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors.hom ≫
    Functor.whiskerRight (pullbackUnitNat g) DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ))
      (restrictDerivedFactors g).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pullbackOnHomotopyQuotientIso g).inv (restrictDerived g) ≫
    (Functor.associator _ _ _).hom

/-- The degreewise unit on the homotopy category, localized:
`Qh ⋙ g⁻¹ ⟶ (Qh ∘ g^*) ⋙ restriction`. -/
def pullbackUnitHomotopyNat :
    DerivedCategory.Qh ⋙ invImageDerived g ⟶ pullbackOnHomotopy g ⋙ restrictDerived g :=
  CategoryTheory.Quotient.natTransLift _ (pullbackUnitQuotientNat g)

/-- `pullbackUnitHomotopyNat` on the homotopy class of a complex. -/
theorem pullbackUnitHomotopyNat_app
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (pullbackUnitHomotopyNat g).app ((HomotopyCategory.quotient _ _).obj K) =
      (pullbackUnitQuotientNat g).app K :=
  rfl

/-- **The derived unit `g⁻¹ ⟶ Lg^*`**, of functors `D(𝒪_𝒞) ⥤ D(g⁻¹𝒪_𝒞)`, the derived pullback
being read over `g⁻¹𝒪_𝒞` by restriction of scalars along `g^♯`: the lift along the left
derived functor `Lg^*` of the degreewise unit of extension and restriction of scalars. -/
def derivedUnit : invImageDerived g ⟶ derivedPullback g ⋙ restrictDerived g :=
  (derivedPullback g ⋙ restrictDerived g).leftDerivedLift
    ((Functor.associator DerivedCategory.Qh (derivedPullback g) (restrictDerived g)).inv ≫
      Functor.whiskerRight (derivedPullbackComparison g) (restrictDerived g))
    (quasiIsoTarget (Y := X)) (invImageDerived g) (pullbackUnitHomotopyNat g)

/-- The derived unit on the homotopy class of a complex, followed by the counit of `Lg^*`. -/
theorem derivedUnit_app_Qh
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedUnit g).app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) ≫
      (restrictDerived g).map
        ((derivedPullbackComparison g).app ((HomotopyCategory.quotient _ _).obj K)) =
      (pullbackUnitQuotientNat g).app K := by
  have h := Functor.leftDerived_fac_app (derivedPullback g ⋙ restrictDerived g)
    ((Functor.associator DerivedCategory.Qh (derivedPullback g) (restrictDerived g)).inv ≫
      Functor.whiskerRight (derivedPullbackComparison g) (restrictDerived g))
    (quasiIsoTarget (Y := X)) (invImageDerived g) (pullbackUnitHomotopyNat g)
    ((HomotopyCategory.quotient _ _).obj K)
  rw [pullbackUnitHomotopyNat_app] at h
  simpa [derivedUnit] using h

/-- **The derived unit on a complex** `K` of `𝒪_𝒞`-modules: followed by the comparison
`Lg^*K ⟶ g^*K`, it is the degreewise unit `g⁻¹K ⟶ g^*K` of extension and restriction of
scalars along `g^♯`, read through the factorizations `Q ⋙ g⁻¹ ≅ g⁻¹ ⋙ Q` and
`Q ⋙ restriction ≅ restriction ⋙ Q` of the two exact functors. -/
theorem derivedUnit_app_Q
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors.inv.app K ≫
      (derivedUnit g).app (DerivedCategory.Q.obj K) ≫
      (restrictDerived g).map (derivedPullbackComparisonComplex g K) ≫
      (restrictDerivedFactors g).hom.app
        ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Q.map (pullbackUnitComplex g K) := by
  have h1 : (derivedUnit g).app (DerivedCategory.Q.obj K) ≫
      (restrictDerived g).map ((derivedPullback g).map
        ((DerivedCategory.quotientCompQhIso _).inv.app K)) =
      (invImageDerived g).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        (derivedUnit g).app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) :=
    ((derivedUnit g).naturality _).symm
  rw [derivedPullbackComparisonComplex_eq]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% (derivedUnit_app_Qh g K)]
  simp only [pullbackUnitQuotientNat, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  exact Category.comp_id _

end Deformation.ToposThickening.LiftingMorphismDerived

end
