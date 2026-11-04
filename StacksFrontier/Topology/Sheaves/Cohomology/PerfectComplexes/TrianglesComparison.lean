module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TrianglesComponents
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOfTopCohomology

/-!
# Comparisons of the functors induced by exact functors on derived categories

For exact functors of abelian categories, the isomorphism `D(F) ≅ D(G)` induced by `F ≅ G` is the
same whether it is built by lifting along `Q` or as a map of left derived functors, and the
cohomology comparison `Hⁿ(D(F)(K)) ≅ F(Hⁿ(K))` of `F ≅ G ⋙ H` is that of `H` after that of `G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Homology

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- The two isomorphisms induced on derived categories by an isomorphism of exact functors
agree. -/
theorem mapDerivedCategoryIsoOfNatIso_eq (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso F G e =
      mapDerivedCategoryIsoOfIso F G e := by
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G.mapDerivedCategory
    (mapDerivedCategoryComparisonOfIso F G e)
  refine Iso.ext (Functor.leftDerived_ext G.mapDerivedCategory
    (mapDerivedCategoryComparisonOfIso F G e).hom
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_)
  ext K'
  obtain ⟨K, rfl⟩ : ∃ L, (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L = K' :=
    ⟨K'.as, rfl⟩
  refine Eq.trans ?_ (mapDerivedCategoryIsoOfIso_hom_app F G e _).symm
  have h1 := Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso_hom_app F G e K
  have h2 :=
    (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso F G e).hom.naturality
      ((DerivedCategory.quotientCompQhIso A).hom.app K)
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, mapDerivedCategoryComparisonOfIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.comp_obj] at h2
  rw [← Category.assoc, ← Category.assoc, ← h2, h1]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  congr 3
  simp only [← Functor.map_comp]
  congr 1
  simp only [Functor.mapHomotopyCategoryFactors, mapHomotopyCategoryIso, Quotient.lift.isLift_inv,
    NatTrans.mapHomotopyCategory_app]
  refine (congrArg (_ ≫ ·) (Category.id_comp _)).trans ?_
  refine ((HomotopyCategory.quotient B _).map_comp _ _).symm.trans ?_
  refine (congrArg (HomotopyCategory.quotient B _).map ?_).trans
    ((HomotopyCategory.quotient B _).map_id _)
  ext n
  exact e.hom_inv_id_app (K.X n)

end Stacks.Homology

namespace Stacks.MapDerivedHomologyCompat

open Stacks.ModulesOnACategory.TopCohomology

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D] [HasDerivedCategory.{w₃} D]

/-- Moving two isomorphisms across an equation. -/
theorem hom_comp_of_inv_comp {𝒞 : Type*} [Category 𝒞] {a b c d : 𝒞} (θ : a ≅ b) (t : c ≅ d)
    (x : a ⟶ c) (m : b ⟶ d) (h : θ.inv ≫ x = m ≫ t.inv) : θ.hom ≫ m = x ≫ t.hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The cohomology comparison of an exact functor `G ⋙ H ≅ F` is that of `H` after that of
`G`**, the induced functors on derived categories being identified through `e`. -/
theorem mapDerivedCategoryHomologyIso_hom_app_of_comp_iso (F : A ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (H : B ⥤ D) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : G ⋙ H ≅ F) (n : ℤ)
    (K : DerivedCategory A) :
    (DerivedCategory.homologyFunctor D n).map ((Functor.mapDerivedCategoryCompIso e).hom.app K) ≫
      (F.mapDerivedCategoryHomologyIso n).hom.app K =
    (H.mapDerivedCategoryHomologyIso n).hom.app (G.mapDerivedCategory.obj K) ≫
      H.map ((G.mapDerivedCategoryHomologyIso n).hom.app K) ≫
      e.hom.app ((DerivedCategory.homologyFunctor A n).obj K) := by
  have key : Functor.whiskerRight (Functor.mapDerivedCategoryCompIso e).hom
        (DerivedCategory.homologyFunctor D n) ≫ (F.mapDerivedCategoryHomologyIso n).hom =
      Functor.whiskerLeft G.mapDerivedCategory (H.mapDerivedCategoryHomologyIso n).hom ≫
        Functor.whiskerRight (G.mapDerivedCategoryHomologyIso n).hom H ≫
        Functor.whiskerLeft (DerivedCategory.homologyFunctor A n) e.hom := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (fun P => ?_)
    have hc := compat_Q F G H e.inv n P
    have hΘ : (Functor.mapDerivedCategoryCompIso e).inv.app (DerivedCategory.Q.obj P) =
        F.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app P) ≫
          H.mapDerivedCategoryFactors.inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app P) := by
      refine (Iso.inv_ext (f := (Functor.mapDerivedCategoryCompIso e).app
        (DerivedCategory.Q.obj P)) ?_)
      rw [Iso.app_hom, Functor.mapDerivedCategoryCompIso_hom_app_Q]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
      have h0 : (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom ≫
          NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ) = 𝟙 _ :=
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom_inv_id
      rw [← DerivedCategory.Q.map_comp_assoc, ← NatTrans.comp_app,
        Functor.mapHomologicalComplexCompIso, h0, NatTrans.id_app,
        DerivedCategory.Q.map_id (((G ⋙ H).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)]
      refine (congrArg (_ ≫ _ ≫ ·) (Category.id_comp _)).trans ?_
      rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
        CategoryTheory.Functor.map_id]
      rfl
    rw [← hΘ] at hc
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    exact hom_comp_of_inv_comp ((DerivedCategory.homologyFunctor D n).mapIso
      ((Functor.mapDerivedCategoryCompIso e).app (DerivedCategory.Q.obj P))) (e.app _) _ _ hc
      |>.trans (Category.assoc _ _ _)
  exact NatTrans.congr_app key K

end Stacks.MapDerivedHomologyCompat
