module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.HomologyOnACategory
import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a complex map to its total derived colimit

Let `C` be a small category with the chaotic topology, so that lower shriek along the morphism
to the point is the colimit over `Cᵒᵖ`. For a complex `F^•` of abelian presheaves on `C` —
equivalently, of abelian sheaves for the chaotic topology — and an object `U` of `C`, there is a
canonical map `F^•(U) ⟶ Lπ_!(F^•)` in the unbounded derived category, which is a map of `D(B)`
when `F^•` is a complex of `B̲`-modules. After the canonical identifications it is the colimit
cocone `F(U) ⟶ colim F` (`evaluationToTotalDerivedColimit_comp_counit`).

The total left derived functor of the colimit exists over any coefficient category with enough
projectives in which countable filtered colimits are exact.

## Main definitions

* `Stacks.CategoryHomology.sectionsToColimit`: the colimit cocone, as a natural transformation
  from evaluation at an object to the colimit.
* `Stacks.CategoryHomology.totalDerivedColimit`: the total left derived functor
  `Lπ_! : D(Cᵒᵖ ⥤ D) ⥤ D(D)` of the colimit, with its comparison
  `totalDerivedColimitCounit`.
* `Stacks.CategoryHomology.totalDerivedColimitAdjunction`: the derived adjunction
  `Lπ_! ⊣ π^{-1}`.
* `Stacks.CategoryHomology.evaluationToTotalDerivedColimit`: the canonical map
  `F^•(U) ⟶ Lπ_!(F^•)`.
* `Stacks.CategoryHomology.derivedAdjunctionOfEnoughProjectives`: the derived adjunction of a
  right exact left adjoint whose source has enough projectives.

## Main results

* `Stacks.CategoryHomology.diagramsEnoughProjectives`: a category of diagrams in a category
  with enough projectives has enough projectives; `moduleDiagramsEnoughProjectives` is the case
  of modules, the abelian-group-valued one being
  `Stacks.CategoryHomology.presheafEnoughProjectives`.
* `Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives` and
  `isLeftDerivedFunctor_comp_of_enoughProjectives`: a right exact functor out of an abelian
  category with enough projectives has a total left derived functor, and it is absolute.
* `Stacks.CategoryHomology.colim_hasPointwiseLeftDerivedFunctor`: the colimit over `Cᵒᵖ` has a
  total left derived functor on the unbounded derived category.
* `Stacks.CategoryHomology.totalDerivedColimit_isTriangulated`: derived lower shriek on a
  chaotic site is an exact functor of triangulated categories.
* `Stacks.CategoryHomology.evaluationToTotalDerivedColimit_comp_counit`: the canonical map
  becomes the colimit cocone after the derived comparison.

## References

* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryHomology

universe uD vD w v u

attribute [local instance] HasDerivedCategory.standard

/-! ### Enough projectives in a category of diagrams -/

section EnoughProjectives

variable (J : Type u) [SmallCategory J] (D : Type uD) [Category.{vD} D]
  [EnoughProjectives D] [∀ a b : J, HasCoproductsOfShape (a ⟶ b) D]
  [∀ a b : J, HasProductsOfShape (a ⟶ b) D] [HasCoproductsOfShape J D]

/-- A projective presentation of a diagram: the coproduct over all objects of the free diagrams
on projective covers of its values. -/
private def diagramProjectivePresentation (J : Type u) [Category.{v} J] (D : Type uD)
    [Category.{vD} D] [EnoughProjectives D] [∀ a b : J, HasCoproductsOfShape (a ⟶ b) D]
    [∀ a b : J, HasProductsOfShape (a ⟶ b) D] [HasCoproductsOfShape J D] (F : J ⥤ D) :
    ProjectivePresentation F := by
  let Q : J → D := fun X ↦ Projective.over (F.obj X)
  let Ψ : J → (J ⥤ D) := fun X ↦ (evaluationLeftAdjoint D X).obj (Q X)
  have hproj (X : J) : Projective (Ψ X) := by
    have : ((evaluation _ D).obj X).PreservesEpimorphisms :=
      ⟨@fun _ _ f hf ↦ (NatTrans.epi_iff_epi_app' D f).mp hf X⟩
    have hQ : Projective (Q X) := by dsimp [Q]; infer_instance
    exact (evaluationAdjunctionRight D X).map_projective (Q X) hQ
  have : Projective (∐ Ψ) := ⟨@fun _ _ g e _ ↦
    ⟨Sigma.desc fun X ↦ Projective.factorThru (Sigma.ι Ψ X ≫ g) e,
      Sigma.hom_ext _ _ fun X ↦ by simp [Projective.factorThru_comp]⟩⟩
  let η (X : J) : Ψ X ⟶ F :=
    ((evaluationAdjunctionRight D X).homEquiv (Q X) F).symm (Projective.π (F.obj X))
  have hf : Epi (Sigma.desc η) := by
    rw [NatTrans.epi_iff_epi_app' D (Sigma.desc η)]
    intro Y
    let q : Q Y ⟶ F.obj Y := Projective.π (F.obj Y)
    let ι₁ : (Ψ Y).obj Y ⟶ (∐ Ψ).obj Y := (Sigma.ι Ψ Y).app Y
    let ι₂ : Q Y ⟶ (Ψ Y).obj Y := (evaluationAdjunctionRight D Y).unit.app (Q Y)
    have hfac : (ι₂ ≫ ι₁) ≫ (Sigma.desc η).app Y = q := by
      calc
        (ι₂ ≫ ι₁) ≫ (Sigma.desc η).app Y = ι₂ ≫ (η Y).app Y := by simp [ι₁]
        _ = q := by
          have h := ((evaluationAdjunctionRight D Y).homEquiv (Q Y) F).apply_symm_apply
            (Projective.π (F.obj Y))
          rwa [Adjunction.homEquiv_unit] at h
    exact epi_of_epi_fac (f := ι₂ ≫ ι₁) (g := (Sigma.desc η).app Y) (h := q) hfac
  exact { p := ∐ Ψ, f := Sigma.desc η }

/-- **A category of diagrams in a category with enough projectives has enough projectives**,
provided it has the coproducts needed to form the free diagrams on the objects. -/
theorem diagramsEnoughProjectives : EnoughProjectives (J ⥤ D) :=
  ⟨fun F ↦ ⟨diagramProjectivePresentation J D F⟩⟩

end EnoughProjectives

/-! ### The same, for a category whose morphisms live in an arbitrary universe

The declarations below carry the names of their counterparts above with a prime, and drop the
smallness of the indexing category: its objects and its morphisms may live in different
universes. -/

universe vC

section EnoughProjectives

variable (J : Type u) [Category.{vC} J] (D : Type uD) [Category.{vD} D]
  [EnoughProjectives D] [∀ a b : J, HasCoproductsOfShape (a ⟶ b) D]
  [∀ a b : J, HasProductsOfShape (a ⟶ b) D] [HasCoproductsOfShape J D]

/-- **A category of diagrams in a category with enough projectives has enough projectives**,
provided it has the coproducts needed to form the free diagrams on the objects. -/
theorem diagramsEnoughProjectives' : EnoughProjectives (J ⥤ D) :=
  ⟨fun F ↦ ⟨diagramProjectivePresentation J D F⟩⟩

end EnoughProjectives

/-! ### The total left derived functor of a right exact functor -/

section Existence

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- The projective objects of an abelian category with a zero object contain zero. -/
private theorem containsZero_isProjective (A : Type*) [Category* A] [Abelian A] :
    (isProjective A).ContainsZero :=
  have hzero : IsZero (HasZeroObject.zero.choose : A) := HasZeroObject.zero.choose_spec
  have : Projective (HasZeroObject.zero.choose : A) := hzero.projective
  ⟨_, hzero, inferInstance⟩

/-- An additive functor sends bounded above acyclic complexes of projectives to acyclic
complexes. -/
private theorem acyclic_map_of_projective {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] (F : A ⥤ B) [F.Additive] (a : ℤ) (K : CochainComplex A ℤ)
    (hbound : K.IsStrictlyLE a) (hproj : ∀ n, isProjective A (K.X n))
    (hac : K.Acyclic) : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have := hbound
  have := hproj
  have : K.IsKProjective := CochainComplex.isKProjective_of_projective K a
  have hz : IsZero ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) := by
    rw [IsZero.iff_id_eq_zero]
    exact CochainComplex.IsKProjective.leftOrthogonal K (𝟙 _)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K).2 hac)
  have hz2 := (F.mapHomotopyCategory (ComplexShape.up ℤ)).map_isZero hz
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (HomotopyCategory.subcategoryAcyclic B).prop_of_isZero hz2

/-- **A right exact functor out of an abelian category with enough projectives has a total left
derived functor.** Precisely, such a functor between categories with exact countable filtered
colimits which it preserves has a total left derived functor defined at every object. -/
theorem hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F] [EnoughProjectives A]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have := containsZero_isProjective A
  apply F.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex (isProjective A)
  · intro X Y hX hY
    have := hX
    have := hY
    infer_instance
  · intro X
    exact ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩
  · exact acyclic_map_of_projective F

/-- **The total left derived functor of a right exact functor out of an abelian category with
enough projectives is absolute.** For *every* functor `G` out of `D(B)` the composite `LF ⋙ G`
is the left derived functor of `K ↦ G(F(K))`. -/
theorem isLeftDerivedFunctor_comp_of_enoughProjectives
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F] [EnoughProjectives A]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {E : Type*} [Category* E] (G : DerivedCategory B ⥤ E) :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh LF G).inv ≫ Functor.whiskerRight α G)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have := containsZero_isProjective A
  apply F.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex (isProjective A)
  · intro X Y hX hY
    have := hX
    have := hY
    infer_instance
  · intro X
    exact ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩
  · exact acyclic_map_of_projective F

/-- **The derived adjunction of a right exact left adjoint with enough projectives in the
source.** If `F ⊣ G` with `G` exact, `F` right exact and preserving countable filtered colimits,
and the source of `F` has enough projectives, then any total left derived functor of `F` is left
adjoint to the degreewise derived functor of `G`. -/
def derivedAdjunctionOfEnoughProjectives
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteColimits F] [EnoughProjectives A]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    LF ⊣ G.mapDerivedCategory :=
  have _hR : G.mapDerivedCategory.IsRightDerivedFunctor G.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ G.mapDerivedCategoryFactorsh
  have _hLR : (LF ⋙ G.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh LF G.mapDerivedCategory).inv ≫
        Functor.whiskerRight α G.mapDerivedCategory)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
    isLeftDerivedFunctor_comp_of_enoughProjectives F LF α G.mapDerivedCategory
  have _hRL : (G.mapDerivedCategory ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight G.mapDerivedCategoryFactorsh.inv LF ≫
        (Functor.associator DerivedCategory.Qh G.mapDerivedCategory LF).hom)
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      ((Functor.associator DerivedCategory.Qh G.mapDerivedCategory LF).symm ≪≫
        Functor.isoWhiskerRight G.mapDerivedCategoryFactorsh LF)
  (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) α
    G.mapDerivedCategoryFactorsh.inv

/-- The canonical map from the degreewise derived functor of an **exact** functor `E` to a total
left derived functor `LF` of a functor `F`, induced by a natural transformation `E ⟶ F`. -/
private def exactFunctorToDerivedFunctorLift
    (E F : A ⥤ B) [E.Additive] [PreservesFiniteLimits E]
    [PreservesFiniteColimits E] [F.Additive] (τ : E ⟶ F)
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    E.mapDerivedCategory ⟶ LF :=
  LF.leftDerivedLift α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    E.mapDerivedCategory
    (E.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight
        (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)) DerivedCategory.Qh)

/-- After the canonical comparisons of `E.mapDerivedCategory` and of `LF` with the degreewise
functors, `exactFunctorToDerivedFunctorLift E F τ LF α` at a complex `K` is the image of `τ`
applied degreewise to `K`. -/
private theorem exactFunctorToDerivedFunctorLift_comp
    (E F : A ⥤ B) [E.Additive] [PreservesFiniteLimits E]
    [PreservesFiniteColimits E] [F.Additive] (τ : E ⟶ F)
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : CochainComplex A ℤ) :
    (E.mapDerivedCategoryFactors.inv.app K ≫
      (exactFunctorToDerivedFunctorLift E F τ LF α).app
        (DerivedCategory.Q.obj K)) ≫
      LF.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
      α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso B).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let G := E.mapDerivedCategory
  let β : DerivedCategory.Qh ⋙ G ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
    E.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight
        (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)) DerivedCategory.Qh
  have hfac :
      (exactFunctorToDerivedFunctorLift E F τ LF α).app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) := by
    dsimp [exactFunctorToDerivedFunctorLift]
    exact Functor.leftDerived_fac_app LF α W G β
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
  have hnat :
      G.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
          (exactFunctorToDerivedFunctorLift E F τ LF α).app
            (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
        (exactFunctorToDerivedFunctorLift E F τ LF α).app (DerivedCategory.Q.obj K) ≫
          LF.map ((DerivedCategory.quotientCompQhIso A).inv.app K) := by
    simpa only [Functor.comp_obj] using
      (exactFunctorToDerivedFunctorLift E F τ LF α).naturality
        ((DerivedCategory.quotientCompQhIso A).inv.app K)
  calc
    _ = E.mapDerivedCategoryFactors.inv.app K ≫
        G.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
        (exactFunctorToDerivedFunctorLift E F τ LF α).app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
          have heq := congrArg
            (fun f ↦ E.mapDerivedCategoryFactors.inv.app K ≫ f ≫
              α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
              DerivedCategory.Qh.map
                ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
              (DerivedCategory.quotientCompQhIso B).hom.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) hnat
          simpa only [Category.assoc] using heq.symm
    _ = E.mapDerivedCategoryFactors.inv.app K ≫
        G.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
        β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
          have heq := congrArg
            (fun f ↦ E.mapDerivedCategoryFactors.inv.app K ≫
              G.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫ f ≫
              DerivedCategory.Qh.map
                ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
              (DerivedCategory.quotientCompQhIso B).hom.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) hfac
          simpa only [Category.assoc] using heq
    _ = DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := by
          have hq := (DerivedCategory.quotientCompQhIso B).hom.naturality
            ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)
          calc
            _ = (DerivedCategory.quotientCompQhIso B).inv.app
                  ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
                DerivedCategory.Qh.map
                  ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
                    ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) ≫
                (DerivedCategory.quotientCompQhIso B).hom.app
                  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
                    have hτ :
                        (E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K ≫
                          (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
                            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
                          (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K =
                        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
                          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := by
                      change (𝟙 _ ≫ (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
                        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
                          𝟙 _) = _
                      simp only [Category.id_comp, Category.comp_id]
                    simp only [β, G, NatTrans.comp_app, Functor.whiskerRight_app,
                      Functor.mapDerivedCategoryFactorsh_hom_app, Category.assoc,
                      ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
                      E.mapDerivedCategory.map_id, Category.id_comp,
                      Iso.inv_hom_id_app_assoc, hτ]
            _ = (DerivedCategory.quotientCompQhIso B).inv.app
                  ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
                (DerivedCategory.quotientCompQhIso B).hom.app
                  ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
                DerivedCategory.Q.map
                  ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) :=
                    (by simpa only [Functor.comp_map, Category.assoc] using (congrArg
                      (fun f ↦ (DerivedCategory.quotientCompQhIso B).inv.app
                        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ f) hq))
            _ = DerivedCategory.Q.map
                  ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := by simp

end Existence

/-! ### The canonical map of Stacks 08Q6 -/

section Canonical

variable (C : Type u) [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

/-- The colimit cocone, as a natural transformation from evaluation at an object of the site to
the colimit over the site. On the chaotic site this is the canonical map `F(U) ⟶ π_!F`. -/
def sectionsToColimit (U : C) :
    (evaluation Cᵒᵖ D).obj (op U) ⟶ (colim : (Cᵒᵖ ⥤ D) ⥤ D) where
  app F := colimit.ι F (op U)
  naturality _ _ η := by simp

/-- **The colimit over a small category has a total left derived functor.** -/
theorem colim_hasPointwiseLeftDerivedFunctor :
    (((colim : (Cᵒᵖ ⥤ D) ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedFunctor_of_enoughProjectives (colim : (Cᵒᵖ ⥤ D) ⥤ D)

/-- The total left derived functor `Lπ_!` of the colimit over a small category. -/
def totalDerivedColimit : DerivedCategory (Cᵒᵖ ⥤ D) ⥤ DerivedCategory D :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  ((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ))

/-- The comparison transformation exhibiting `totalDerivedColimit` as a left derived functor. -/
def totalDerivedColimitCounit :
    DerivedCategory.Qh ⋙ totalDerivedColimit C D ⟶
      (colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  ((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ))

/-- The comparison transformation does exhibit `totalDerivedColimit` as a left derived functor
of the colimit. -/
theorem totalDerivedColimit_isLeftDerivedFunctor :
    (totalDerivedColimit C D).IsLeftDerivedFunctor (totalDerivedColimitCounit C D)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) := by
  have := colim_hasPointwiseLeftDerivedFunctor C D
  dsimp [totalDerivedColimit, totalDerivedColimitCounit]
  infer_instance

/-- **The derived lower shriek of a chaotic site is left adjoint to inverse image**: the total
left derived colimit is left adjoint to the degreewise derived constant diagram. -/
def totalDerivedColimitAdjunction :
    totalDerivedColimit C D ⊣ (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory := by
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  exact derivedAdjunctionOfEnoughProjectives
    (colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ)
    (totalDerivedColimit C D) (totalDerivedColimitCounit C D)

/-- **The unit of the derived adjunction, read against the derived-functor comparison.** The unit
of `Stacks.CategoryHomology.totalDerivedColimitAdjunction` at an object coming from the homotopy
category, followed by the derived constant diagram of
`Stacks.CategoryHomology.totalDerivedColimitCounit`, is the unit of `colim ⊣ const` itself. -/
theorem totalDerivedColimitAdjunction_unit_app_comp_counit
    (X : HomotopyCategory (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) :
    (totalDerivedColimitAdjunction C D).unit.app (DerivedCategory.Qh.obj X) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((totalDerivedColimitCounit C D).app X) =
      DerivedCategory.Qh.map
          (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app X) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
          (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) := by
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  have := isLeftDerivedFunctor_comp_of_enoughProjectives (colim : (Cᵒᵖ ⥤ D) ⥤ D)
    (totalDerivedColimit C D) (totalDerivedColimitCounit C D)
    (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory
  exact Adjunction.derivedη_fac_app
    ((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
      (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ))
    (totalDerivedColimitCounit C D)
    (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv X

/-- Derived lower shriek on a chaotic site commutes with the shift. -/
instance totalDerivedColimit_commShift : (totalDerivedColimit C D).CommShift ℤ :=
  (totalDerivedColimitAdjunction C D).leftAdjointCommShift ℤ

/-- **Derived lower shriek on a chaotic site is an exact functor of triangulated categories.**
-/
instance totalDerivedColimit_isTriangulated : (totalDerivedColimit C D).IsTriangulated :=
  have : (totalDerivedColimitAdjunction C D).CommShift ℤ :=
    (totalDerivedColimitAdjunction C D).commShift_of_rightAdjoint ℤ
  (totalDerivedColimitAdjunction C D).isTriangulated_leftAdjoint

/-- **The canonical map `F^•(U) ⟶ Lπ_!(F^•)`.** For a complex `F^•` of diagrams on `Cᵒᵖ` and an
object `U` of `C`, the canonical map `F^•(U) ⟶ Lπ_!(F^•)` in the unbounded derived category,
natural in `F^•`. For `D = AddCommGrpCat` this is a map in `D(Ab)`, and for `D = ModuleCat B` it
is the same map read in `D(B)`. -/
@[stacks 08Q6 "the canonical map"]
def evaluationToTotalDerivedColimit (U : C) :
    ((evaluation Cᵒᵖ D).obj (op U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ totalDerivedColimit C D :=
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  ((evaluation Cᵒᵖ D).obj (op U)).mapDerivedCategoryFactors.inv ≫
    Functor.whiskerLeft DerivedCategory.Q
      (exactFunctorToDerivedFunctorLift ((evaluation Cᵒᵖ D).obj (op U))
        (colim : (Cᵒᵖ ⥤ D) ⥤ D) (sectionsToColimit C D U) (totalDerivedColimit C D)
        (totalDerivedColimitCounit C D))

/-- **The canonical map is the colimit cocone.** After the canonical comparisons of the total
left derived functor with the degreewise colimit, the map of `evaluationToTotalDerivedColimit` is
the colimit cocone of the complex. -/
@[stacks 08Q6 "the canonical map"]
theorem evaluationToTotalDerivedColimit_comp_counit (U : C) (K : CochainComplex (Cᵒᵖ ⥤ D) ℤ) :
    (evaluationToTotalDerivedColimit C D U).app K ≫
      (totalDerivedColimit C D).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
      (totalDerivedColimitCounit C D).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (sectionsToColimit C D U) (ComplexShape.up ℤ)).app K) :=
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  exactFunctorToDerivedFunctorLift_comp ((evaluation Cᵒᵖ D).obj (op U))
    (colim : (Cᵒᵖ ⥤ D) ⥤ D) (sectionsToColimit C D U) (totalDerivedColimit C D)
    (totalDerivedColimitCounit C D) K

end Canonical

section Canonical

variable (C : Type u) [Category.{vC} C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

/-- The colimit cocone, as a natural transformation from evaluation at an object of the site to
the colimit over the site. On the chaotic site this is the canonical map `F(U) ⟶ π_!F`. -/
def sectionsToColimit' (U : C) :
    (evaluation Cᵒᵖ D).obj (op U) ⟶ (colim : (Cᵒᵖ ⥤ D) ⥤ D) where
  app F := colimit.ι F (op U)
  naturality _ _ η := by simp

/-- **The colimit over `Cᵒᵖ` has a total left derived functor.** -/
theorem colim_hasPointwiseLeftDerivedFunctor' :
    (((colim : (Cᵒᵖ ⥤ D) ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedFunctor_of_enoughProjectives (colim : (Cᵒᵖ ⥤ D) ⥤ D)

/-- The total left derived functor `Lπ_!` of the colimit over `Cᵒᵖ`. -/
def totalDerivedColimit' : DerivedCategory (Cᵒᵖ ⥤ D) ⥤ DerivedCategory D :=
  have := colim_hasPointwiseLeftDerivedFunctor' C D
  ((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ))

/-- The comparison transformation exhibiting `totalDerivedColimit'` as a left derived functor. -/
def totalDerivedColimitCounit' :
    DerivedCategory.Qh ⋙ totalDerivedColimit' C D ⟶
      (colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  have := colim_hasPointwiseLeftDerivedFunctor' C D
  ((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ))

/-- The comparison transformation does exhibit `totalDerivedColimit'` as a left derived functor
of the colimit. -/
theorem totalDerivedColimit_isLeftDerivedFunctor' :
    (totalDerivedColimit' C D).IsLeftDerivedFunctor (totalDerivedColimitCounit' C D)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) := by
  have := colim_hasPointwiseLeftDerivedFunctor' C D
  dsimp [totalDerivedColimit', totalDerivedColimitCounit']
  infer_instance

/-- **The derived lower shriek of a chaotic site is left adjoint to inverse image**: the total
left derived colimit is left adjoint to the degreewise derived constant diagram. -/
def totalDerivedColimitAdjunction' :
    totalDerivedColimit' C D ⊣ (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory := by
  have := colim_hasPointwiseLeftDerivedFunctor' C D
  have := totalDerivedColimit_isLeftDerivedFunctor' C D
  exact derivedAdjunctionOfEnoughProjectives
    (colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ)
    (totalDerivedColimit' C D) (totalDerivedColimitCounit' C D)

/-- **The unit of the derived adjunction, read against the derived-functor comparison.** The unit
of `Stacks.CategoryHomology.totalDerivedColimitAdjunction'` at an object coming from the homotopy
category, followed by the derived constant diagram of
`Stacks.CategoryHomology.totalDerivedColimitCounit'`, is the unit of `colim ⊣ const` itself. -/
theorem totalDerivedColimitAdjunction_unit_app_comp_counit'
    (X : HomotopyCategory (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) :
    (totalDerivedColimitAdjunction' C D).unit.app (DerivedCategory.Qh.obj X) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((totalDerivedColimitCounit' C D).app X) =
      DerivedCategory.Qh.map
          (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app X) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
          (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) := by
  have := colim_hasPointwiseLeftDerivedFunctor' C D
  have := totalDerivedColimit_isLeftDerivedFunctor' C D
  have := isLeftDerivedFunctor_comp_of_enoughProjectives (colim : (Cᵒᵖ ⥤ D) ⥤ D)
    (totalDerivedColimit' C D) (totalDerivedColimitCounit' C D)
    (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory
  exact Adjunction.derivedη_fac_app
    ((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
      (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ))
    (totalDerivedColimitCounit' C D)
    (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv X

/-- Derived lower shriek on a chaotic site commutes with the shift. -/
instance totalDerivedColimit_commShift' : (totalDerivedColimit' C D).CommShift ℤ :=
  (totalDerivedColimitAdjunction' C D).leftAdjointCommShift ℤ

/-- **Derived lower shriek on a chaotic site is an exact functor of triangulated categories.**
-/
instance totalDerivedColimit_isTriangulated' : (totalDerivedColimit' C D).IsTriangulated :=
  have : (totalDerivedColimitAdjunction' C D).CommShift ℤ :=
    (totalDerivedColimitAdjunction' C D).commShift_of_rightAdjoint ℤ
  (totalDerivedColimitAdjunction' C D).isTriangulated_leftAdjoint

/-- **The canonical map `F^•(U) ⟶ Lπ_!(F^•)`.** For a complex `F^•` of diagrams on `Cᵒᵖ` and an
object `U` of `C`, the canonical map `F^•(U) ⟶ Lπ_!(F^•)` in the unbounded derived category,
natural in `F^•`. For `D = AddCommGrpCat` this is a map in `D(Ab)`, and for `D = ModuleCat B` it
is the same map read in `D(B)`. -/
@[stacks 08Q6 "the canonical map"]
def evaluationToTotalDerivedColimit' (U : C) :
    ((evaluation Cᵒᵖ D).obj (op U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ totalDerivedColimit' C D :=
  have := totalDerivedColimit_isLeftDerivedFunctor' C D
  ((evaluation Cᵒᵖ D).obj (op U)).mapDerivedCategoryFactors.inv ≫
    Functor.whiskerLeft DerivedCategory.Q
      (exactFunctorToDerivedFunctorLift ((evaluation Cᵒᵖ D).obj (op U))
        (colim : (Cᵒᵖ ⥤ D) ⥤ D) (sectionsToColimit' C D U) (totalDerivedColimit' C D)
        (totalDerivedColimitCounit' C D))

/-- **The canonical map is the colimit cocone.** After the canonical comparisons of the total
left derived functor with the degreewise colimit, the map of `evaluationToTotalDerivedColimit'`
is the colimit cocone of the complex. -/
@[stacks 08Q6 "the canonical map"]
theorem evaluationToTotalDerivedColimit_comp_counit' (U : C) (K : CochainComplex (Cᵒᵖ ⥤ D) ℤ) :
    (evaluationToTotalDerivedColimit' C D U).app K ≫
      (totalDerivedColimit' C D).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
      (totalDerivedColimitCounit' C D).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (sectionsToColimit' C D U) (ComplexShape.up ℤ)).app K) :=
  have := totalDerivedColimit_isLeftDerivedFunctor' C D
  exactFunctorToDerivedFunctorLift_comp ((evaluation Cᵒᵖ D).obj (op U))
    (colim : (Cᵒᵖ ⥤ D) ⥤ D) (sectionsToColimit' C D U) (totalDerivedColimit' C D)
    (totalDerivedColimitCounit' C D) K

end Canonical

section CanonicalComparison

variable (C : Type u) [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

/-- At a small category the size-general total left derived colimit `totalDerivedColimit'` is
`totalDerivedColimit`. -/
def totalDerivedColimitIsoTotalDerivedColimit' :
    totalDerivedColimit C D ≅ totalDerivedColimit' C D :=
  Iso.refl _

end CanonicalComparison

/-! ### The two coefficient categories of the source statement -/

/-- Colimits of shape `ℕ` of abelian groups are exact. -/
instance hasExactColimitsOfShapeNatAddCommGrpCat :
    HasExactColimitsOfShape ℕ AddCommGrpCat.{uD} :=
  have : AB5OfSize.{0, 0} AddCommGrpCat.{uD} := AB5OfSize_shrink.{0, 0, uD, uD} _
  AB5OfSize.ofShape ℕ

/-- Colimits of shape `ℕ` of modules are exact, with the universe of the modules independent of
the universe of the ring. -/
instance hasExactColimitsOfShapeNatModuleCat (B : Type w) [Ring B] :
    HasExactColimitsOfShape ℕ (ModuleCat.{max u w} B) :=
  HasExactColimitsOfShape.domain_of_functor ℕ
    (forget₂ (ModuleCat.{max u w} B) AddCommGrpCat.{max u w})

/-- **Diagrams of modules on a small category have enough projectives.** -/
instance moduleDiagramsEnoughProjectives (C : Type u) [SmallCategory C]
    (B : Type w) [Ring B] :
    EnoughProjectives (Cᵒᵖ ⥤ ModuleCat.{max u w} B) := by
  have hpr (a b : Cᵒᵖ) : HasProductsOfShape (a ⟶ b) (ModuleCat.{max u w} B) := by
    change HasLimitsOfShape (Discrete (a ⟶ b)) (ModuleCat.{max u w} B)
    have : Small.{max u w} (Discrete (a ⟶ b)) := inferInstance
    exact ModuleCat.hasLimitsOfShape
  exact diagramsEnoughProjectives Cᵒᵖ (ModuleCat.{max u w} B)

/-- **The canonical map for abelian presheaves.** The canonical map `F^•(U) ⟶ Lπ_!(F^•)` in
`D(Ab)`, for a complex `F^•` of abelian presheaves — equivalently, of abelian sheaves for the
chaotic topology — on a small category. -/
@[stacks 08Q6 "ab_map"]
def evaluationToDerivedColimitOfAbelianDiagrams (C : Type u) [SmallCategory C] (U : C) :
    ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ totalDerivedColimit C AddCommGrpCat.{max u v} :=
  evaluationToTotalDerivedColimit C AddCommGrpCat.{max u v} U

/-- **The canonical map for modules.** The canonical map `F^•(U) ⟶ Lπ_!(F^•)`, read in `D(B)`,
for a complex of modules over the constant sheaf of rings `B̲` on a small chaotic site. -/
@[stacks 08Q6 "module_map"]
def evaluationToDerivedColimitOfModuleDiagrams (C : Type u) [SmallCategory C]
    (B : Type w) [Ring B] (U : C) :
    ((evaluation Cᵒᵖ (ModuleCat.{max u w} B)).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ totalDerivedColimit C (ModuleCat.{max u w} B) :=
  evaluationToTotalDerivedColimit C (ModuleCat.{max u w} B) U

end Stacks.CategoryHomology

end
