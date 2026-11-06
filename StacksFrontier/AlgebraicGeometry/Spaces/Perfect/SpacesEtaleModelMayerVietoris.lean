module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfect
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# The Mayer–Vietoris triangle on the spaces-étale models

For an elementary distinguished square `W = U ∪ V` with intersection `P` (Stacks 08GM), part (2)
of Stacks 08GV gives on the small étale site of `W` a distinguished triangle
`j_{P!}j_P^*E ⟶ j_{U!}j_U^*E ⊕ j_{V!}j_V^*E ⟶ E ⟶`
(`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedShriekMayerVietoris`). This file
transports it to the derived categories of the spaces-étale models through the equivalences of
Stacks 03G1, with the derived extensions by zero
`AlgebraicGeometry.Space.spacesEtaleModelDerivedLowerShriek` and the derived pullbacks along the
morphisms of models
(`AlgebraicGeometry.Space.exists_mem_distTriang_spacesEtaleModelMayerVietoris`). Only the vertices
are recorded: the five lemma on directed colimits by which the proof of Stacks 09RI uses the
triangle needs a distinguished triangle with these vertices and nothing about its morphisms, since
homomorphisms out of `j_{Y!}Lj_Y^*E` are homomorphisms out of `Lj_Y^*E` by
`AlgebraicGeometry.Space.spacesEtaleModelDerivedLowerShriekAdjunction`.

## Main results

* `CategoryTheory.Pretriangulated.exists_mem_distTriang_of_iso`: a distinguished triangle with
  prescribed vertices isomorphic to those of a given one.
* `AlgebraicGeometry.Space.exists_mem_distTriang_spacesEtaleModelMayerVietoris`: the
  Mayer–Vietoris triangle on the spaces-étale models.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A distinguished triangle can be rewritten with any isomorphic objects: given isomorphisms of
three objects with the vertices of a distinguished triangle, there is a distinguished triangle
with these objects as vertices. -/
theorem exists_mem_distTriang_of_iso (T : Triangle C) (hT : T ∈ distTriang C) {X Y Z : C}
    (a : X ≅ T.obj₁) (b : Y ≅ T.obj₂) (c : Z ≅ T.obj₃) :
    ∃ (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z) (m₃ : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk m₁ m₂ m₃ ∈ distTriang C :=
  ⟨a.hom ≫ T.mor₁ ≫ b.inv, b.hom ≫ T.mor₂ ≫ c.inv,
    c.hom ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map a.inv,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ a b c (by simp) (by simp)
      (by simp [← Functor.map_comp]))⟩

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

attribute [local instance high] HasDerivedCategory.standard

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transport

variable {X W : AlgebraicSpaces B S hS} (j : X ⟶ W) (hj : IsEtale B S hS j.hom)

/-- Derived extension by zero after derived restriction, on the spaces-étale models, read on the
small étale sites through the equivalences of Stacks 03G1. -/
def spacesEtaleModelDerivedLowerShriekPullbackTransportIso
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W).O))) :
    haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W)).1
    haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W)).2.1
    haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W)).2.2
    haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W).symm).1
    haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W).symm).2.1
    haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W).symm).2.2
    haveI := etaleModulePullback_additive B S hS j hj
    haveI := preservesFiniteLimits_etaleModulePullback B S hS j hj
    haveI := preservesFiniteColimits_etaleModulePullback B S hS j hj
    (spacesEtaleModelDerivedLowerShriek B S hS j hj).obj
        ((derivedPullback (spacesEtaleModelHom B S hS j)).obj E) ≅
      (spacesEtaleModelModulesEquiv B S hS W).inverse.mapDerivedCategory.obj
        ((etaleModuleLowerShriek B S hS j hj).mapDerivedCategory.obj
          ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj
            ((spacesEtaleModelModulesEquiv B S hS W).functor.mapDerivedCategory.obj E))) :=
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W)).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W)).2.2
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W).symm).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W).symm).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W).symm).2.2
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).2.2
  haveI := etaleModulePullback_additive B S hS j hj
  haveI := preservesFiniteLimits_etaleModulePullback B S hS j hj
  haveI := preservesFiniteColimits_etaleModulePullback B S hS j hj
  (Functor.mapDerivedCategoryComp _ _).app _ ≪≫
    (spacesEtaleModelModulesEquiv B S hS W).inverse.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryComp _ _).app _ ≪≫
        (etaleModuleLowerShriek B S hS j hj).mapDerivedCategory.mapIso
          ((spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS j hj).app E))

end Transport

section MayerVietoris

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The Mayer–Vietoris triangle of Stacks 08GV, part (2), on the spaces-étale models.** For an
elementary distinguished square `W = U ∪ V` with intersection `P` and an object `E` of the derived
category of the model of `W`, there is a distinguished triangle
`j_{P!}Lj_P^*E ⟶ j_{U!}Lj_U^*E ⊞ j_{V!}Lj_V^*E ⟶ E ⟶ j_{P!}Lj_P^*E⟦1⟧`, with the derived
extensions by zero `AlgebraicGeometry.Space.spacesEtaleModelDerivedLowerShriek`. It is the triangle
`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedShriekMayerVietoris` of the small étale
sites, transported through the equivalences of Stacks 03G1. -/
theorem exists_mem_distTriang_spacesEtaleModelMayerVietoris
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W).O))) :
    ∃ (m₁ : (spacesEtaleModelDerivedLowerShriek B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj
          ((derivedPullback (spacesEtaleModelHom B S hS (edsInterHom B S hS hsq))).obj E) ⟶
        (spacesEtaleModelDerivedLowerShriek B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).obj
          ((derivedPullback (spacesEtaleModelHom B S hS (edsOpenHom B S hS hsq))).obj E) ⊞
        (spacesEtaleModelDerivedLowerShriek B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj
          ((derivedPullback (spacesEtaleModelHom B S hS (edsEtaleHom B S hS hsq))).obj E))
      (m₂ : _ ⟶ E) (m₃ : E ⟶ _), Triangle.mk m₁ m₂ m₃ ∈ distTriang _ := by
  obtain ⟨_, _, _⟩ := exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W)
  obtain ⟨_, _, _⟩ := exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS W).symm
  obtain ⟨δ, hδ⟩ := exists_mem_distTriang_edsDerivedShriekMayerVietoris B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    ((spacesEtaleModelModulesEquiv B S hS W).functor.mapDerivedCategory.obj E)
  have hT :=
    (spacesEtaleModelModulesEquiv B S hS W).inverse.mapDerivedCategory.map_distinguished _ hδ
  have : (spacesEtaleModelModulesEquiv B S hS W).inverse.mapDerivedCategory.Additive :=
    inferInstance
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (spacesEtaleModelModulesEquiv B S hS W).inverse.mapDerivedCategory
  refine exists_mem_distTriang_of_iso _ hT
    (spacesEtaleModelDerivedLowerShriekPullbackTransportIso B S hS _ _ E)
    (biprod.mapIso (spacesEtaleModelDerivedLowerShriekPullbackTransportIso B S hS _ _ E)
        (spacesEtaleModelDerivedLowerShriekPullbackTransportIso B S hS _ _ E) ≪≫ ?_)
    (((Functor.mapDerivedCategoryIdIso _).app E).symm ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (spacesEtaleModelModulesEquiv B S hS W).unitIso).app E ≪≫
      (Functor.mapDerivedCategoryComp _ _).app E)
  exact ((spacesEtaleModelModulesEquiv B S hS W).inverse.mapDerivedCategory.mapBiprod
    ((etaleModuleLowerShriek B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj
      ((etaleModulePullback B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj
        ((spacesEtaleModelModulesEquiv B S hS W).functor.mapDerivedCategory.obj E)))
    ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj
      ((etaleModulePullback B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj
        ((spacesEtaleModelModulesEquiv B S hS W).functor.mapDerivedCategory.obj E)))).symm

end MayerVietoris

end AlgebraicGeometry.Space

end
