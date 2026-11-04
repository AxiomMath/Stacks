module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDirectSums

/-!
# The cohomology of `F` applied to a complex of `F`-acyclic objects

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, `𝒜` with enough injectives,
and `K` a bounded below complex of `F`-acyclic objects. By Leray's acyclicity lemma (Tag 015E)
the comparison `Q(F K) ⟶ RF(Q K)` is invertible
(`Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app`). On cohomology this gives
`Hᵐ(F K) ≅ Hᵐ(RF(K))` (`CategoryTheory.Functor.homologyIsoRightDerivedFunctorPlusOfRightAcyclic`),
natural for morphisms of such complexes
(`CategoryTheory.Functor.homologyIsoRightDerivedFunctorPlusOfRightAcyclic_hom_naturality`).

For `F = Γ(Y, -)` and `K` an acyclic resolution of a sheaf `L`, this computes `Hᵐ(Y, L)` as the
cohomology of the complex of sections, compatibly with morphisms of resolutions.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
  {B : Type*} [Category* B] [Abelian B] (F : A ⥤ B) [F.Additive]

/-- **`Hᵐ(F K) ≅ Hᵐ(RF(K))`** for a bounded below complex `K` of `F`-acyclic objects. -/
def homologyIsoRightDerivedFunctorPlusOfRightAcyclic (K : CochainComplex.Plus A)
    (hK : ∀ n, F.rightAcyclic (K.obj.X n)) (m : ℤ) :
    ((F.mapHomologicalComplex _).obj K.obj).homology m ≅
      (DerivedCategory.Plus.homologyFunctor B m).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) :=
  haveI := Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app F K hK
  ((DerivedCategory.homologyFunctorFactors B m).app ((F.mapHomologicalComplex _).obj K.obj)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor B m).mapIso
      (asIso ((F.mapCochainComplexPlusDerivedUnit).app K))

/-- The comparison `Hᵐ(F K) ≅ Hᵐ(RF(K))` is natural in the complex of acyclic objects. -/
lemma homologyIsoRightDerivedFunctorPlusOfRightAcyclic_hom_naturality
    {K L : CochainComplex.Plus A} (g : K ⟶ L) (hK : ∀ n, F.rightAcyclic (K.obj.X n))
    (hL : ∀ n, F.rightAcyclic (L.obj.X n)) (m : ℤ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map g.hom) m ≫
        (F.homologyIsoRightDerivedFunctorPlusOfRightAcyclic L hL m).hom =
      (F.homologyIsoRightDerivedFunctorPlusOfRightAcyclic K hK m).hom ≫
        (DerivedCategory.Plus.homologyFunctor B m).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g)) := by
  have h₁ : HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map g.hom) m ≫
      (DerivedCategory.homologyFunctorFactors B m).inv.app ((F.mapHomologicalComplex _).obj L.obj) =
      (DerivedCategory.homologyFunctorFactors B m).inv.app ((F.mapHomologicalComplex _).obj K.obj) ≫
        (DerivedCategory.Plus.homologyFunctor B m).map
          (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map g)) :=
    (DerivedCategory.homologyFunctorFactors B m).inv.naturality
      ((F.mapHomologicalComplex _).map g.hom)
  have h₂ := congrArg (DerivedCategory.Plus.homologyFunctor B m).map
    ((F.mapCochainComplexPlusDerivedUnit).naturality g)
  simp only [Functor.map_comp, Functor.comp_map] at h₂
  show HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map g.hom) m ≫
      (DerivedCategory.homologyFunctorFactors B m).inv.app ((F.mapHomologicalComplex _).obj L.obj) ≫
        (DerivedCategory.Plus.homologyFunctor B m).map
          ((F.mapCochainComplexPlusDerivedUnit).app L) =
    ((DerivedCategory.homologyFunctorFactors B m).inv.app ((F.mapHomologicalComplex _).obj K.obj) ≫
        (DerivedCategory.Plus.homologyFunctor B m).map
          ((F.mapCochainComplexPlusDerivedUnit).app K)) ≫
      (DerivedCategory.Plus.homologyFunctor B m).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

end CategoryTheory.Functor
