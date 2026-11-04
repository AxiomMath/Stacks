module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedExternalTensorGenerators
public import StacksFrontier.Homology.MapHomologicalComplexSingleTensorator
public import StacksFrontier.Homology.DerivedCategory.Monoidal.DerivedTensorIsoNaturality
public import StacksFrontier.Homology.DerivedCategory.Monoidal.DerivedTensorIsoNaturalityBoth
public import StacksFrontier.Homology.KFlat.DiagramResolution
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived product formula on a product of chaotic sites

Let `C₁` and `C₂` be small categories, `R` a commutative ring, `u_i : C₁ × C₂ ⥤ C_i` the two
projections and `g_i` the induced morphisms of ringed topoi, so that `g_i^{-1}` is restriction of
diagrams of `R`-modules along `u_i`.  Write `Lπ_!` for derived lower shriek to the point on each
of the three sites, the total left derived functor of the colimit
(`Stacks.CategoryHomology.totalDerivedColimit`).  This file proves Stacks 08QB: for
`K_i ∈ D(C_i, R)` the canonical comparison

`L(π₁ × π₂)_!(g₁^{-1}K₁ ⊗^L_{R̲} g₂^{-1}K₂) ⟶ Lπ_{1,!}K₁ ⊗^L_R Lπ_{2,!}K₂`

(`Stacks.CategoryHomology.derivedExternalTensorComparison`) is an isomorphism in `D(R)`.

The proof is the one in the source.  Both sides commute with direct sums and shifts and are
exact in each variable, so by the two dévissages
`Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_of_generators_fst` and `…_snd` it
suffices to treat `K₁ = j_{U!}P` and `K₂ = j_{V!}Q`, free diagrams with projective coefficients
placed in degree zero.  There everything is underived: the restrictions `g_i^{-1}j_{U!}P` are
K-flat, so their derived tensor product is the external tensor product
`g₁^{-1}j_{U!}P ⊗ g₂^{-1}j_{V!}Q`, a projective diagram on `C₁ × C₂`, and derived lower shriek
of a projective diagram placed in degree zero is its colimit.  The comparison is a two-variable
mate (`CategoryTheory.Adjunction.externalMate`), so it is identified with the image of the
underived comparison `Stacks.CategoryHomology.colimExternalTensorComparison` -- which is
invertible -- by checking the defining property of the mate
(`CategoryTheory.Adjunction.isIso_externalMate_of_unit_comp_map`).  That check computes each of
its ingredients at those generators: the derived lower-shriek units
(`Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_Q_single`), the two derived
identifications `g_i^{-1} ∘ π_i^{-1} = π^{-1}` (`Stacks.CategoryHomology.alpha_fst_leg`), the
tensorator of the derived constant diagram
(`CategoryTheory.Functor.mu_constMapDerivedCategory_derivedTensorIso`), and finally the defining
property of the underived mate in degree zero.

The derived tensor product of diagrams on `C₁ × C₂` exists because every complex of diagrams has
a K-flat resolution, which is `Stacks.CategoryHomology.exists_kFlat_quasiIso_diagrams`.

## Main results

* `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_freeYoneda`: the comparison is
  invertible at a pair of free diagrams with projective coefficients placed in degree zero.
* `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison`: **Stacks 08QB**, the
  comparison is invertible at every pair `K₁, K₂`.
* `Stacks.CategoryHomology.derivedExternalTensorIso`: the resulting isomorphism, and
  `Stacks.CategoryHomology.isIso_derivedExternalTensorComparisonNatTrans`: the comparison is an
  isomorphism of bifunctors.

## Implementation notes

The source takes `C_i` arbitrary categories and `B` any ring.  Here `C₁`, `C₂` are small and
share the universe of the commutative ring `R` and of its modules, which is the setting in which
`Stacks.CategoryHomology.totalDerivedColimit` and the derived tensor products of
`CochainComplex.KFlatMonoidal.derivedMonoidal` are available; the identity in `D(B)` is stated
as the invertibility of the canonical comparison, which is what "with obvious notation" refers
to.

## References

* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

namespace Stacks.CategoryHomology

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CochainComplex.symmetricCategory

universe u

variable (C₁ : Type u) [SmallCategory C₁] (C₂ : Type u) [SmallCategory C₂] (R : Type u) [CommRing R]
  (hres : ∀ G : CochainComplex ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) ℤ,
      ∃ (P : CochainComplex ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) ℤ) (f : P ⟶ G),
        KFlat (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)) P ∧ QuasiIso f)

/-- The total tensor product of complexes of diagrams; instance search does not find it on its
own, the graded-object hypotheses it needs being found one at a time. -/
private abbrev complexesOfDiagramsMonoidal : MonoidalCategory
    (CochainComplex ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) ℤ) :=
  HomologicalComplex.monoidalCategory _ _


section Generators

variable (U : C₁) (V : C₂) (P Q : ModuleCat.{u} R) [Projective P] [Projective Q]

/-- The external tensor product of two generators is projective. -/
theorem projective_tensorObj_projFst_projSnd_freeYoneda : Projective
    (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj ((projFstInverseImage C₁ C₂ R).obj
    (Presheaf.freeYoneda U P))).obj ((projSndInverseImage C₁ C₂ R).obj
    (Presheaf.freeYoneda V Q))) := by
  have := projective_tensorObj P Q
  have := freeYonedaProjective ((U, V) : C₁ × C₂) (P ⊗ Q)
  exact Projective.of_iso (externalTensorFreeYonedaIso U V P Q).symm inferInstance

omit [Projective P] in
/-- The colimit of a free diagram with projective coefficients is K-flat in degree zero. -/
theorem kFlat_single_colimit_freeYoneda {C : Type u} [SmallCategory C] (W : C) [Projective P] :
    KFlat (curriedTensor (ModuleCat.{u} R)) ((HomologicalComplex.single (ModuleCat.{u} R)
        (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda W P))) := by
  have : Projective (colimit (Presheaf.freeYoneda W P)) :=
    Projective.of_iso (colimFreeYonedaIso W P).symm inferInstance
  have := flat_of_projective (colimit (Presheaf.freeYoneda W P))
  exact CochainComplex.DerivedTensor.kFlat_single_of_flat _

/-- The source of the comparison at a pair of generators, identified with the image of the
external tensor product placed in degree zero. -/
private def sourceSingleIso :
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    MonoidalCategoryStruct.tensorObj ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R)
        (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda U P))))
        ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Presheaf.freeYoneda V Q)))) ≅ DerivedCategory.Q.obj ((HomologicalComplex.single
            ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj ((projFstInverseImage C₁ C₂ R).obj
            (Presheaf.freeYoneda U P))).obj ((projSndInverseImage C₁ C₂ R).obj
            (Presheaf.freeYoneda V Q)))) :=
  letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  tensorIso (projFstDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda U P))
      (projSndDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda V Q)) ≪≫
    derivedTensorIso ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
      (kFlat_single_projFst_freeYoneda C₁ C₂ R U P)
      (kFlat_single_projSnd_freeYoneda C₁ C₂ R V Q) ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.mapBifunctorSingleIso (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))
          ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))
          ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)))

/-- The target of the comparison at a pair of generators. -/
private def targetSingleIso :
    letI := derivedMonoidal (ModuleCat.{u} R)
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    MonoidalCategoryStruct.tensorObj ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R)
        (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda U P)))) ((totalDerivedColimit C₂
        (ModuleCat.{u} R)).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda V Q)))) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (colimit (Presheaf.freeYoneda U P) ⊗ colimit (Presheaf.freeYoneda V Q))) :=
  letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  haveI := freeYonedaProjective U P
  haveI := freeYonedaProjective V Q
  tensorIso (totalDerivedColimitObjSingleIso C₁ (ModuleCat.{u} R) (Presheaf.freeYoneda U P))
      (totalDerivedColimitObjSingleIso C₂ (ModuleCat.{u} R) (Presheaf.freeYoneda V Q)) ≪≫
    derivedTensorIso (ModuleCat.{u} R)
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
        (kFlat_single_colimit_freeYoneda R P U) (kFlat_single_colimit_freeYoneda R Q V) ≪≫
      DerivedCategory.Q.mapIso
        (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R))
          (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q)))

/-- The underived comparison at the two generators, as the mate of the identities. -/
private abbrev underivedMate : colimit (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
    ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))).obj
    ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))) ⟶ colimit
    (Presheaf.freeYoneda U P) ⊗ colimit (Presheaf.freeYoneda V Q) :=
  Adjunction.externalMate colimConstAdj colimConstAdj colimConstAdj
    (projFstInverseImage C₁ C₂ R) (projSndInverseImage C₁ C₂ R) (𝟙 _) (𝟙 _)
        (Presheaf.freeYoneda U P) (Presheaf.freeYoneda V Q)

/-- The left-hand side of the transposition identity. -/
private lemma lhs_eq :
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    haveI := projective_tensorObj_projFst_projSnd_freeYoneda C₁ C₂ R U V P Q
    (sourceSingleIso C₁ C₂ R hres U V P Q).inv ≫
        (totalDerivedColimitAdjunction (C₁ × C₂) (ModuleCat.{u} R)).unit.app
            (MonoidalCategoryStruct.tensorObj ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj
            (DerivedCategory.Q.obj ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R)
            (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda U P))))
            ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj (DerivedCategory.Q.obj
                ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda V Q))))) ≫
        (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
          ((totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)).map
              (sourceSingleIso C₁ C₂ R hres U V P Q).hom ≫
            (totalDerivedColimitObjSingleIso (C₁ × C₂) (ModuleCat.{u} R)
                (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
                ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))).obj
                ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)))).hom ≫
            DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{u} R)
                (ComplexShape.up ℤ) 0).map (underivedMate C₁ C₂ R U V P Q))) ≫
        (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
            ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (colimit (Presheaf.freeYoneda U P) ⊗ colimit (Presheaf.freeYoneda V Q))) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
            (colimConstAdj.unit.app (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
            ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))).obj
            ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)))) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
              (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _) (ComplexShape.up ℤ) 0).app
            (colimit (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
                ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))).obj
                ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))))).inv ≫
          ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
                (underivedMate C₁ C₂ R U V P Q))) := by
  let := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  have := projective_tensorObj_projFst_projSnd_freeYoneda C₁ C₂ R U V P Q
  have hn := (Functor.const
      (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.naturality
      ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
      (underivedMate C₁ C₂ R U V P Q))
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [(totalDerivedColimitAdjunction (C₁ × C₂) (ModuleCat.{u} R)).unit_naturality_assoc,
      Iso.inv_hom_id_assoc,
    reassoc_of% (totalDerivedColimitAdjunction_unit_app_Q_single (C₁ × C₂) (ModuleCat.{u} R)
        (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj ((projFstInverseImage C₁ C₂ R).obj
        (Presheaf.freeYoneda U P))).obj ((projSndInverseImage C₁ C₂ R).obj
        (Presheaf.freeYoneda V Q)))),
    hn, Iso.inv_hom_id_app_assoc]

/-- The derived lower-shriek unit at a projective diagram placed in degree zero, followed by the
computation of `Lπ_!` there and the comparison of the derived constant diagram with its
degreewise action, is the image of the underived unit. -/
lemma unit_app_comp_map_totalDerivedColimitObjSingleIso_factors {C : Type u} [SmallCategory C]
    (G : Cᵒᵖ ⥤ ModuleCat.{u} R) [Projective G] :
    (totalDerivedColimitAdjunction C (ModuleCat.{u} R)).unit.app
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj G)) ≫
        (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
          (totalDerivedColimitObjSingleIso C (ModuleCat.{u} R) G).hom ≫
        (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (colimit G)) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
            (colimConstAdj.unit.app G) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
            (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _) (ComplexShape.up ℤ) 0).app
              (colimit G)).inv) := by
  rw [reassoc_of% (totalDerivedColimitAdjunction_unit_app_Q_single C (ModuleCat.{u} R) G),
    Iso.inv_hom_id_app, Functor.map_comp]
  exact congrArg (fun t => _ ≫ t) (Category.comp_id _)

/-- The first factor of the right-hand side of the transposition identity. -/
private lemma fst_leg :
    haveI := freeYonedaProjective U P
    (projFstInverseImage C₁ C₂ R).mapDerivedCategory.map
        ((totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R)).unit.app (DerivedCategory.Q.obj
        ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda U P)))) ≫
        (derivedConstCompProjFstIso C₁ C₂ R).hom.app ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj
            (DerivedCategory.Q.obj ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R)
            (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda U P)))) ≫
          (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
              (totalDerivedColimitObjSingleIso C₁ (ModuleCat.{u} R) (Presheaf.freeYoneda U P)).hom ≫
            (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
                ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (colimit (Presheaf.freeYoneda U P))) =
      (projFstDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda U P)).hom ≫
        DerivedCategory.Q.map
          (((HomologicalComplex.singleMapHomologicalComplex (projFstInverseImage C₁ C₂ R)
              (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda U P)).inv ≫
            ((projFstInverseImage C₁ C₂ R).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
                  (colimConstAdj.unit.app (Presheaf.freeYoneda U P)) ≫
                ((HomologicalComplex.singleMapHomologicalComplex
                    (Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _) (ComplexShape.up ℤ) 0).app
                  (colimit (Presheaf.freeYoneda U P))).inv)) := by
  have := freeYonedaProjective U P
  exact alpha_fst_leg C₁ C₂ R U P ((HomologicalComplex.single (ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda U P)))
    (totalDerivedColimitObjSingleIso C₁ (ModuleCat.{u} R) (Presheaf.freeYoneda U P)).hom _
    (unit_app_comp_map_totalDerivedColimitObjSingleIso_factors R (Presheaf.freeYoneda U P))

/-- The second factor of the right-hand side of the transposition identity. -/
private lemma snd_leg :
    haveI := freeYonedaProjective V Q
    (projSndInverseImage C₁ C₂ R).mapDerivedCategory.map
        ((totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R)).unit.app (DerivedCategory.Q.obj
        ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda V Q)))) ≫
        (derivedConstCompProjSndIso C₁ C₂ R).hom.app ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj
            (DerivedCategory.Q.obj ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R)
            (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda V Q)))) ≫
          (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
              (totalDerivedColimitObjSingleIso C₂ (ModuleCat.{u} R) (Presheaf.freeYoneda V Q)).hom ≫
            (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
                ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (colimit (Presheaf.freeYoneda V Q))) =
      (projSndDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda V Q)).hom ≫
        DerivedCategory.Q.map
          (((HomologicalComplex.singleMapHomologicalComplex (projSndInverseImage C₁ C₂ R)
              (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda V Q)).inv ≫
            ((projSndInverseImage C₁ C₂ R).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
                  (colimConstAdj.unit.app (Presheaf.freeYoneda V Q)) ≫
                ((HomologicalComplex.singleMapHomologicalComplex
                    (Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _) (ComplexShape.up ℤ) 0).app
                  (colimit (Presheaf.freeYoneda V Q))).inv)) := by
  have := freeYonedaProjective V Q
  exact alpha_snd_leg C₁ C₂ R V Q ((HomologicalComplex.single (ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda V Q)))
    (totalDerivedColimitObjSingleIso C₂ (ModuleCat.{u} R) (Presheaf.freeYoneda V Q)).hom _
    (unit_app_comp_map_totalDerivedColimitObjSingleIso_factors R (Presheaf.freeYoneda V Q))

/-- The first factor of the chain map the right-hand side descends to. -/
private abbrev fstChain :
    (HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P)) ⟶
        ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (ModuleCat.{u} R)
        (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda U P))) :=
  ((HomologicalComplex.singleMapHomologicalComplex (projFstInverseImage C₁ C₂ R)
      (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda U P)).inv ≫
    ((projFstInverseImage C₁ C₂ R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
          (colimConstAdj.unit.app (Presheaf.freeYoneda U P)) ≫
        ((HomologicalComplex.singleMapHomologicalComplex (Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _)
            (ComplexShape.up ℤ) 0).app
          (colimit (Presheaf.freeYoneda U P))).inv)

/-- The second factor of the chain map the right-hand side descends to. -/
private abbrev sndChain :
    (HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)) ⟶
        ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (ModuleCat.{u} R)
        (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda V Q))) :=
  ((HomologicalComplex.singleMapHomologicalComplex (projSndInverseImage C₁ C₂ R)
      (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda V Q)).inv ≫
    ((projSndInverseImage C₁ C₂ R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
          (colimConstAdj.unit.app (Presheaf.freeYoneda V Q)) ≫
        ((HomologicalComplex.singleMapHomologicalComplex (Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _)
            (ComplexShape.up ℤ) 0).app
          (colimit (Presheaf.freeYoneda V Q))).inv)

/-- The right-hand side of the transposition identity. -/
private lemma rhs_eq :
    letI := complexesOfDiagramsMonoidal C₁ C₂ R
    letI := derivedMonoidal (ModuleCat.{u} R)
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    letI := Functor.constMapDerivedCategoryMonoidal
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
    (sourceSingleIso C₁ C₂ R hres U V P Q).inv ≫
        (((projFstInverseImage C₁ C₂ R).mapDerivedCategory.map
            ((totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R)).unit.app (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Presheaf.freeYoneda U P)))) ≫
            (derivedConstCompProjFstIso C₁ C₂ R).hom.app
                ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj (DerivedCategory.Q.obj
                ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda U P))))) ⊗ₘ
          ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.map
              ((totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R)).unit.app (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda V Q)))) ≫
            (derivedConstCompProjSndIso C₁ C₂ R).hom.app
                ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj (DerivedCategory.Q.obj
                ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda V Q)))))) ≫
        Functor.LaxMonoidal.μ (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory
            ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Presheaf.freeYoneda U P)))) ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj
            (DerivedCategory.Q.obj ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R)
            (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda V Q)))) ≫
        (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
            (targetSingleIso C₁ C₂ R U V P Q).hom ≫
        (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
            ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (colimit (Presheaf.freeYoneda U P) ⊗ colimit (Presheaf.freeYoneda V Q))) =
      DerivedCategory.Q.map
        ((HomologicalComplex.mapBifunctorSingleIso (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))
            ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))
            ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))).inv ≫
          (fstChain C₁ C₂ R U P ⊗ₘ sndChain C₁ C₂ R V Q) ≫
          Functor.LaxMonoidal.μ
              ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
              (ComplexShape.up ℤ))
            ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (colimit (Presheaf.freeYoneda U P))) ((HomologicalComplex.single (ModuleCat.{u} R)
                (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda V Q))) ≫
          ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R))
              (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q))).hom) := by
  let := complexesOfDiagramsMonoidal C₁ C₂ R
  let := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  let := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := Functor.constMapDerivedCategoryMonoidal
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  have := freeYonedaProjective U P
  have := freeYonedaProjective V Q
  have hT : (targetSingleIso C₁ C₂ R U V P Q).hom =
      ((totalDerivedColimitObjSingleIso C₁ (ModuleCat.{u} R) (Presheaf.freeYoneda U P)).hom ⊗ₘ
          (totalDerivedColimitObjSingleIso C₂ (ModuleCat.{u} R) (Presheaf.freeYoneda V Q)).hom) ≫
        (derivedTensorIso (ModuleCat.{u} R)
            (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
          (kFlat_single_colimit_freeYoneda R P U) (kFlat_single_colimit_freeYoneda R Q V)).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R))
            (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q))).hom := rfl
  have hfac : (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
      (DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R))
          (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q))).hom) ≫
      (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (colimit (Presheaf.freeYoneda U P) ⊗ colimit (Presheaf.freeYoneda V Q))) =
      (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (colimit (Presheaf.freeYoneda U P)) ⊗ (HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda V Q))) ≫
        DerivedCategory.Q.map
            (((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R))
            (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q))).hom) :=
    (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.naturality
      (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R))
        (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q))).hom
  have hZ := Functor.mu_constMapDerivedCategory_derivedTensorIso (J := (C₁ × C₂)ᵒᵖ)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
    (kFlat_single_colimit_freeYoneda R P U) (kFlat_single_colimit_freeYoneda R Q V)
  rw [hT, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hfac,
    ← Functor.LaxMonoidal.μ_natural_assoc, reassoc_of% hZ]
  have hcomb :
      (((projFstInverseImage C₁ C₂ R).mapDerivedCategory.map
          ((totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R)).unit.app (DerivedCategory.Q.obj
          ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (Presheaf.freeYoneda U P)))) ≫
            (derivedConstCompProjFstIso C₁ C₂ R).hom.app
                ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj (DerivedCategory.Q.obj
                ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda U P))))) ⊗ₘ
          ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.map
              ((totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R)).unit.app (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda V Q)))) ≫
            (derivedConstCompProjSndIso C₁ C₂ R).hom.app
                ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj (DerivedCategory.Q.obj
                ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda V Q)))))) ≫
        ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
            (totalDerivedColimitObjSingleIso C₁ (ModuleCat.{u} R) (Presheaf.freeYoneda U P)).hom ⊗ₘ
          (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
              (totalDerivedColimitObjSingleIso C₂ (ModuleCat.{u} R)
              (Presheaf.freeYoneda V Q)).hom) ≫
        ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
            ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (colimit (Presheaf.freeYoneda U P))) ⊗ₘ
          (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
              ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (colimit (Presheaf.freeYoneda V Q)))) =
      ((projFstDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda U P)).hom ⊗ₘ
          (projSndDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda V Q)).hom) ≫
        (DerivedCategory.Q.map (fstChain C₁ C₂ R U P) ⊗ₘ
          DerivedCategory.Q.map (sndChain C₁ C₂ R V Q)) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [fst_leg, snd_leg]
    rfl
  have hnat := derivedTensorIso_hom_natural ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
      (fstChain C₁ C₂ R U P)
    (sndChain C₁ C₂ R V Q) (kFlat_single_projFst_freeYoneda C₁ C₂ R U P)
    (kFlat_constMapHomologicalComplex _ (kFlat_single_colimit_freeYoneda R P U))
    (kFlat_single_projSnd_freeYoneda C₁ C₂ R V Q)
    (kFlat_constMapHomologicalComplex _ (kFlat_single_colimit_freeYoneda R Q V))
  rw [reassoc_of% hcomb, reassoc_of% hnat]
  simp only [sourceSingleIso, Iso.trans_inv, tensorIso_inv, Functor.mapIso_inv, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, MonoidalCategory.id_tensorHom_id,
    Category.id_comp, Iso.inv_hom_id_assoc, Functor.map_comp]

/-- The two identifications of the degree-zero terms of `X[0]` and `Y[0]` compose to the identity
on the tensor product. -/
private lemma curriedTensor_map_singleObjXSelf_comp {A : Type*} [Category* A] [MonoidalCategory A]
    [HasZeroMorphisms A] [HasZeroObject A] (X Y : A) :
    ((curriedTensor A).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom).app
        (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Y).X 0) ≫
      ((curriedTensor A).obj X).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom = 𝟙 _ := by
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rfl

omit [Projective P] [Projective Q] in
/-- Composing with the image of an endomorphism which is the identity. -/
private lemma comp_map_eq_self {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E) {A : E}
    {B : D} (f : A ⟶ F.obj B) (g : B ⟶ B) (hg : g = 𝟙 B) : f ≫ F.map g = f := by
  subst hg
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

omit [Projective P] [Projective Q] in
/-- Precomposing with an endomorphism which is the identity. -/
private lemma eq_id_comp {D : Type*} [Category* D] {A B : D} (g : A ⟶ A) (hg : g = 𝟙 A)
    (f : A ⟶ B) : g ≫ f = f := by
  subst hg
  rw [Category.id_comp]

/-- **The chain-level transposition identity at a pair of generators**, on the summands of the
total complex. -/
private lemma chain_eq' :
    letI := complexesOfDiagramsMonoidal C₁ C₂ R
    (fstChain C₁ C₂ R U P ⊗ₘ sndChain C₁ C₂ R V Q) ≫
        Functor.LaxMonoidal.μ
            ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ))
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (colimit (Presheaf.freeYoneda U P))) ((HomologicalComplex.single (ModuleCat.{u} R)
              (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda V Q))) ≫
        ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R))
            (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q))).hom =
      (HomologicalComplex.mapBifunctorSingleIso (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))
          ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))
          ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))).hom ≫
      (HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
          (colimConstAdj.unit.app (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
          ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))).obj
          ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)))) ≫
        ((HomologicalComplex.singleMapHomologicalComplex
            (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _) (ComplexShape.up ℤ) 0).app
          (colimit (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
              ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))).obj
              ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))))).inv ≫
        ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
              (underivedMate C₁ C₂ R U V P Q)) := by
  let := complexesOfDiagramsMonoidal C₁ C₂ R
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := (HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))) (K₂ :=
      (HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)))
    (F := curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)) (c := ComplexShape.up ℤ) fun p q hpq => ?_
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · subst hp
      subst hq
      have hn : n = 0 := by
        have : (0 : ℤ) + 0 = n := hpq
        omega
      subst hn
      have hC : HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))) ((HomologicalComplex.single
          ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))) (curriedTensor
          ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))
            (ComplexShape.up ℤ) 0 0 0 hpq ≫
          (HomologicalComplex.mapBifunctorSingleIso (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))
              ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))
              ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))).hom.f 0 =
          ((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).map (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) 0 ((projFstInverseImage C₁ C₂ R).obj
                    (Presheaf.freeYoneda U P))).hom).app (((HomologicalComplex.single
                    ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                    ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))).X 0) ≫
            ((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj ((projFstInverseImage C₁ C₂ R).obj
                (Presheaf.freeYoneda U P))).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                  ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))).hom :=
        HomologicalComplex.ι_mapBifunctorSingleIso_hom
            (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)) ((projFstInverseImage C₁ C₂ R).obj
            (Presheaf.freeYoneda U P)) ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))
      have hD : HomologicalComplex.ιTensorObj ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) 0).obj (colimit (Presheaf.freeYoneda U P)))
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (colimit (Presheaf.freeYoneda V Q))) 0 0 0 hpq ≫
          (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R))
            (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q))).hom.f 0 =
          ((curriedTensor (ModuleCat.{u} R)).map (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) 0 (colimit (Presheaf.freeYoneda U P))).hom).app
                    (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                    (colimit (Presheaf.freeYoneda V Q))).X 0) ≫
            ((curriedTensor (ModuleCat.{u} R)).obj (colimit (Presheaf.freeYoneda U P))).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                  (colimit (Presheaf.freeYoneda V Q))).hom :=
        HomologicalComplex.ι_mapBifunctorSingleIso_hom (curriedTensor (ModuleCat.{u} R))
          (colimit (Presheaf.freeYoneda U P)) (colimit (Presheaf.freeYoneda V Q))
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.ι_tensorHom_f_assoc,
        Functor.ι_mu_mapHomologicalComplex_assoc, Functor.mapHomologicalComplex_map_f,
        ← Functor.map_comp, hD, HomologicalComplex.comp_f, reassoc_of% hC]
      have hmate := Adjunction.unit_comp_map_externalMate
        (colimConstAdj (J := (C₁ × C₂)ᵒᵖ) (C := ModuleCat.{u} R))
        (colimConstAdj (J := C₁ᵒᵖ) (C := ModuleCat.{u} R))
        (colimConstAdj (J := C₂ᵒᵖ) (C := ModuleCat.{u} R)) (projFstInverseImage C₁ C₂ R)
            (projSndInverseImage C₁ C₂ R) (𝟙 _) (𝟙 _) (Presheaf.freeYoneda U P)
            (Presheaf.freeYoneda V Q)
      simp only [NatTrans.id_app, Category.comp_id] at hmate
      have hL : ((fstChain C₁ C₂ R U P).f 0 ⊗ₘ (sndChain C₁ C₂ R V Q).f 0) ≫
          Functor.LaxMonoidal.μ (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _)
              (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (colimit (Presheaf.freeYoneda U P))).X 0) (((HomologicalComplex.single
              (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (colimit
              (Presheaf.freeYoneda V Q))).X 0) ≫
          (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).map
              (((curriedTensor (ModuleCat.{u} R)).map (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) 0 (colimit (Presheaf.freeYoneda U P))).hom).app
                    (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                    (colimit (Presheaf.freeYoneda V Q))).X 0) ≫
            ((curriedTensor (ModuleCat.{u} R)).obj (colimit (Presheaf.freeYoneda U P))).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                  (colimit (Presheaf.freeYoneda V Q))).hom) =
          ((projFstInverseImage C₁ C₂ R).map (colimConstAdj.unit.app (Presheaf.freeYoneda U P)) ⊗ₘ
              (projSndInverseImage C₁ C₂ R).map (colimConstAdj.unit.app
              (Presheaf.freeYoneda V Q))) ≫
            Functor.LaxMonoidal.μ (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _)
                (colim.obj (Presheaf.freeYoneda U P)) (colim.obj (Presheaf.freeYoneda V Q)) := by
        rw [← Category.assoc]
        exact comp_map_eq_self (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _) _ _
          (curriedTensor_map_singleObjXSelf_comp _ _)
      have hR : (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).map
          (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) 0 ((projFstInverseImage C₁ C₂ R).obj
                    (Presheaf.freeYoneda U P))).hom).app (((HomologicalComplex.single
                    ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                    ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))).X 0) ≫
            ((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj ((projFstInverseImage C₁ C₂ R).obj
                (Presheaf.freeYoneda U P))).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                  ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))).hom) ≫
          ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
              (colimConstAdj.unit.app (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
              ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))).obj
              ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)))) ≫
            ((HomologicalComplex.singleMapHomologicalComplex
                (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _) (ComplexShape.up ℤ) 0).app
              (colimit (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
                  ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))).obj
                  ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))))).inv ≫
            ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
                  (underivedMate C₁ C₂ R U V P Q))).f 0 =
          colimConstAdj.unit.app (((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P)) ⊗
              ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))) ≫ (Functor.const
              (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).map (underivedMate C₁ C₂ R U V P Q) :=
        (eq_id_comp _ (curriedTensor_map_singleObjXSelf_comp _ _) _).trans rfl
      exact hL.trans (hmate.symm.trans hR.symm)
    · exact (HomologicalComplex.isZero_obj_obj_single_obj_X
        (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)) ((projFstInverseImage C₁ C₂ R).obj
        (Presheaf.freeYoneda U P)) ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))
        p q (Or.inr hq)).eq_of_src _ _
  · exact (HomologicalComplex.isZero_obj_obj_single_obj_X
      (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)) ((projFstInverseImage C₁ C₂ R).obj
      (Presheaf.freeYoneda U P)) ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))
      p q (Or.inl hp)).eq_of_src _ _

/-- The underived comparison at a pair of generators is invertible, being the comparison of
`Stacks.CategoryHomology.colimExternalTensorComparison`. -/
private instance isIso_underivedMate : IsIso (underivedMate C₁ C₂ R U V P Q) :=
  isIso_colimExternalTensorComparison (Presheaf.freeYoneda U P) (Presheaf.freeYoneda V Q)

/-- **Stacks 08QB at a pair of generators**: the canonical comparison is invertible at a pair of
free diagrams with projective coefficients placed in degree zero. -/
theorem isIso_derivedExternalTensorComparison_freeYoneda :
    IsIso (derivedExternalTensorComparison C₁ C₂ R hres (DerivedCategory.Q.obj
        ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda U P))) (DerivedCategory.Q.obj ((HomologicalComplex.single
        (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda V Q)))) := by
  let := complexesOfDiagramsMonoidal C₁ C₂ R
  let := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  let := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := Functor.constMapDerivedCategoryMonoidal
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  have := projective_tensorObj_projFst_projSnd_freeYoneda C₁ C₂ R U V P Q
  let t := (totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)).map
      (sourceSingleIso C₁ C₂ R hres U V P Q).hom ≫
    (totalDerivedColimitObjSingleIso (C₁ × C₂) (ModuleCat.{u} R)
        (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj ((projFstInverseImage C₁ C₂ R).obj
        (Presheaf.freeYoneda U P))).obj ((projSndInverseImage C₁ C₂ R).obj
        (Presheaf.freeYoneda V Q)))).hom ≫
    DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
        (underivedMate C₁ C₂ R U V P Q)) ≫
    (targetSingleIso C₁ C₂ R U V P Q).inv
  have : IsIso t := by dsimp only [t]; infer_instance
  have ht : t ≫ (targetSingleIso C₁ C₂ R U V P Q).hom =
      (totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)).map
          (sourceSingleIso C₁ C₂ R hres U V P Q).hom ≫
        (totalDerivedColimitObjSingleIso (C₁ × C₂) (ModuleCat.{u} R)
            (((curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)).obj ((projFstInverseImage C₁ C₂ R).obj
            (Presheaf.freeYoneda U P))).obj ((projSndInverseImage C₁ C₂ R).obj
            (Presheaf.freeYoneda V Q)))).hom ≫
        DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{u} R)
            (ComplexShape.up ℤ) 0).map (underivedMate C₁ C₂ R U V P Q)) := by
    simp only [t, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine Adjunction.isIso_externalMate_of_unit_comp_map (totalDerivedColimitAdjunction (C₁ × C₂)
      (ModuleCat.{u} R)) (totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R))
      (totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R))
    (projFstInverseImage C₁ C₂ R).mapDerivedCategory
        (projSndInverseImage C₁ C₂ R).mapDerivedCategory
    (derivedConstCompProjFstIso C₁ C₂ R).hom (derivedConstCompProjSndIso C₁ C₂ R).hom
    (DerivedCategory.Q.obj ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R)
        (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda U P))) (DerivedCategory.Q.obj
        ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda V Q))) t ?_
  rw [← cancel_epi (sourceSingleIso C₁ C₂ R hres U V P Q).inv,
    ← cancel_mono ((Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
        (targetSingleIso C₁ C₂ R U V P Q).hom ≫
      (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (colimit (Presheaf.freeYoneda U P) ⊗ colimit (Presheaf.freeYoneda V Q))))]
  have hL := lhs_eq C₁ C₂ R hres U V P Q
  have hR := rhs_eq C₁ C₂ R hres U V P Q
  have hc := chain_eq' C₁ C₂ R U V P Q
  simp only [Category.assoc] at hL hR ⊢
  rw [← Functor.map_comp_assoc, ht, hL, hR, hc, Iso.inv_hom_id_assoc]

end Generators

section ProductFormula

/-- **Stacks 08QB.**  Let `C₁` and `C₂` be categories, `g_i` the morphisms of ringed topoi
induced by the two projections of `C₁ × C₂`, and `R` a ring.  For `K_i ∈ D(C_i, R)` the canonical
comparison

`L(π₁ × π₂)_!(g₁^{-1}K₁ ⊗^L_{R̲} g₂^{-1}K₂) ⟶ Lπ_{1,!}K₁ ⊗^L_R Lπ_{2,!}K₂`

is an isomorphism in `D(R)`. -/
@[stacks 08QB]
theorem isIso_derivedExternalTensorComparison
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R))
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    IsIso (derivedExternalTensorComparison C₁ C₂ R exists_kFlat_quasiIso_diagrams K₁ K₂) :=
  isIso_derivedExternalTensorComparison_of_generators C₁ C₂ R exists_kFlat_quasiIso_diagrams
    K₁ K₂ fun U V P Q _ _ ↦
      isIso_derivedExternalTensorComparison_freeYoneda C₁ C₂ R exists_kFlat_quasiIso_diagrams
        U V P Q

/-- The product formula of Stacks 08QB, as an isomorphism in `D(R)`:
`L(π₁ × π₂)_!(g₁^{-1}K₁ ⊗^L g₂^{-1}K₂) ≅ Lπ_{1,!}K₁ ⊗^L Lπ_{2,!}K₂`. -/
def derivedExternalTensorIso
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R))
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    letI := derivedMonoidal (ModuleCat.{u} R)
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) exists_kFlat_quasiIso_diagrams
    (totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)).obj (MonoidalCategoryStruct.tensorObj
        ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj K₁)
        ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj K₂)) ≅
      MonoidalCategoryStruct.tensorObj ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj K₁)
          ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj K₂) :=
  haveI := isIso_derivedExternalTensorComparison C₁ C₂ R K₁ K₂
  asIso (derivedExternalTensorComparison C₁ C₂ R exists_kFlat_quasiIso_diagrams K₁ K₂)

/-- The forward morphism of `derivedExternalTensorIso` is `derivedExternalTensorComparison`. -/
@[simp]
lemma derivedExternalTensorIso_hom
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R))
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    (derivedExternalTensorIso C₁ C₂ R K₁ K₂).hom =
      derivedExternalTensorComparison C₁ C₂ R exists_kFlat_quasiIso_diagrams K₁ K₂ :=
  rfl

/-- The canonical comparison of Stacks 08QB is an isomorphism of bifunctors. -/
theorem isIso_derivedExternalTensorComparisonNatTrans :
    IsIso (derivedExternalTensorComparisonNatTrans C₁ C₂ R exists_kFlat_quasiIso_diagrams) :=
  isIso_derivedExternalTensorComparisonNatTrans_of_generators C₁ C₂ R
    exists_kFlat_quasiIso_diagrams fun U V P Q _ _ ↦
      isIso_derivedExternalTensorComparison_freeYoneda C₁ C₂ R exists_kFlat_quasiIso_diagrams
        U V P Q

end ProductFormula

end Stacks.CategoryHomology

end
