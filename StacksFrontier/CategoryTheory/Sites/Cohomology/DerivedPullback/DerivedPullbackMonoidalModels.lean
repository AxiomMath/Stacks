module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidalOnModels

/-!
# `f^*` applied termwise, on K-flat models

Let `f` be a morphism of ringed topoi presented by a morphism of sites, with `f^*` exact. This
file records two computations on complexes that identify the derived pullback `Lf^*` with `f^*`
applied termwise, `Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived`, together with its
monoidal structure:

* the identification `Lf^* ≅ f^*` of `Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived`
  at the image of a complex is the comparison of Stacks 06YY;
* the tensorator of `f^*` applied termwise to complexes is the inverse of the comparison of total
  tensor complexes `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` out of which
  Stacks 07A4 is built.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived_hom_app_Q`.
* `Stacks.Sheaves.DerivedPullback.mapHomologicalComplex_μ_pullbackTopos`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor
  monoidalCategoryMod symmetricCategoryMod CochainComplex.symmetricCategory monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod

/-- A comparison of a functor with a derived functor, read at an object isomorphic to the image
of the localization: the assembly in `derivedPullbackIsoMapDerived_hom_app_Q`, applied as a term
so that the unifier rather than the rewriter matches the spellings of the objects. -/
private lemma comp_eq_comp_comp_of_fac {D : Type*} [Category D] {A B A' B' E Z : D}
    (x : A ⟶ B) (tB : B ≅ B') (tA : A ⟶ A') (y : A' ⟶ B') (c : B ⟶ E) (fh : B' ⟶ E)
    (fac : A' ⟶ Z) (j : E ≅ Z) (hnat : x ≫ tB.hom = tA ≫ y) (hfac : tB.inv ≫ c = fh)
    (hA : y ≫ fh = fac ≫ j.inv) :
    tA ≫ fac = x ≫ c ≫ j.hom := by
  have hc : c = tB.hom ≫ fh := by rw [← hfac, Iso.hom_inv_id_assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hA, Iso.inv_hom_id, Category.comp_id]

/-- Computing a composite on a summand, applied as a term: the two spellings of the summand
inclusions involved, through `curriedTensor` and through `sheafTensor`, are definitionally but
not syntactically equal. -/
private lemma comp_comp_eq_of_summand {D : Type*} [Category D] {A B C E M : D}
    (ι : A ⟶ B) (t : B ⟶ C) (pt : C ⟶ E) (μ : A ⟶ M) (fι : M ⟶ C) (δ : M ⟶ A) (ι' : A ⟶ E)
    (h₁ : ι ≫ t = μ ≫ fι) (h₂ : fι ≫ pt = δ ≫ ι') (h₃ : μ ≫ δ = 𝟙 A) :
    ι ≫ t ≫ pt = ι' ≫ 𝟙 E := by
  rw [reassoc_of% h₁, h₂, reassoc_of% h₃, Category.comp_id]

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- `f^*` is right exact, being a left adjoint. -/
local instance preservesFiniteColimits_pullbackTopos' : PreservesFiniteColimits f.pullbackTopos :=
  PreservesColimitsOfSize.preservesFiniteColimits _

section Comparison

variable [PreservesFiniteLimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The identification of `Lf^*` with `f^*` applied termwise, at the image of a complex, is
the comparison of Stacks 06YY**: followed by the identification of `f^*` applied termwise at the
image of `K` with the image of `f^*K`, it is `Lf^*(Q K) ⟶ Q(f^* K)`. -/
theorem derivedPullbackIsoMapDerived_hom_app_Q
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullbackIsoMapDerived f).hom.app (DerivedCategory.Q.obj K) ≫
        f.pullbackTopos.mapDerivedCategoryFactors.hom.app K =
      pullbackComparisonQ f K :=
  comp_eq_comp_comp_of_fac
    ((derivedPullback f).map ((DerivedCategory.quotientCompQhIso _).inv.app K))
    ((derivedPullbackIsoMapDerived f).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))
    ((derivedPullbackIsoMapDerived f).hom.app (DerivedCategory.Q.obj K))
    ((pullbackToposMapDerived f).map ((DerivedCategory.quotientCompQhIso _).inv.app K))
    ((derivedPullbackComparison f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (f.pullbackTopos.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (f.pullbackTopos.mapDerivedCategoryFactors.hom.app K)
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
        ((f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((derivedPullbackIsoMapDerived f).hom.naturality _)
    ((derivedPullback f).leftDerived_fac_app
      ((pullbackOnHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh _)
      (HomotopyCategory.quasiIso _ _) (pullbackToposMapDerived f)
      f.pullbackTopos.mapDerivedCategoryFactorsh.hom
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (Functor.map_quotientCompQhIso_inv_comp_mapDerivedCategoryFactorsh_hom f.pullbackTopos K)

end Comparison

section Tensorator

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]

/-- **The tensorator of `f^*` applied termwise is the inverse of the comparison of total tensor
complexes of Stacks 07A4**: both act on the summand of bidegree `(p, q)` by the comparison of
Stacks 03EL, which is the tensorator of `f^*` (`pullbackToposMonoidal_δ`). -/
theorem mapHomologicalComplex_μ_pullbackTopos_comp_pullbackToposTensorTotalIso_hom
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    letI := pullbackToposMonoidal f hmos
    Functor.LaxMonoidal.μ (f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)) K L ≫
        (pullbackToposTensorTotalIso f hmos K L).hom = 𝟙 _ := by
  let := pullbackToposMonoidal f hmos
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine HomologicalComplex.mapBifunctor.hom_ext (fun p q hpq => ?_)
  have h₁ := Functor.ι_mapHomologicalComplexTensorator_hom f.pullbackTopos K L p q n hpq
  have h₂ := ι_pullbackToposTensorTotalIso_hom f hmos K L p q n hpq
  have h₃ : Functor.LaxMonoidal.μ f.pullbackTopos (K.X p) (L.X q) ≫
      pullbackToposTensorMapDeg f hmos K L p q = 𝟙 _ := by
    rw [pullbackToposTensorMapDeg_eq, ← pullbackToposMonoidal_δ f hmos (K.X p) (L.X q),
      Functor.Monoidal.μ_δ]
  rw [HomologicalComplex.id_f, HomologicalComplex.comp_f]
  exact comp_comp_eq_of_summand _ _ _ _ _ _ _ h₁ h₂ h₃

end Tensorator

end Stacks.Sheaves.DerivedPullback

end
