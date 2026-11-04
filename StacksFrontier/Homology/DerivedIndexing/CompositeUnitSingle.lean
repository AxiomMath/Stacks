module

public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` of a composite

Let `P : 𝒜 ⥤ ℬ` and `Q : ℬ ⥤ 𝒞` be additive functors between abelian categories with enough
injectives. The canonical map `((Q ∘ P)ℱ)[0] ⟶ R(Q ∘ P)(ℱ[0])` followed by the composition
transformation `R(Q ∘ P) ⟶ RQ ∘ RP` of [Stacks, Tag 05T2] is the canonical map for `Q` at `Pℱ`
followed by `RQ` of the canonical map for `P` at `ℱ`.

## Main results

* `Stacks.DerivedIndexing.singleMapHomologicalComplex_inv_app_comp`: the comparison
  `((Q ∘ P)ℱ)[0] ⟶ (Q ∘ P)(ℱ[0])` of complexes is the comparison for `Q` at `Pℱ` followed by `Q`
  of the comparison for `P` at `ℱ`.
* `Stacks.DerivedIndexing.mapSingleFunctorCompQhIso_inv_app_comp`: the same in `D⁺`.
* `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_compTrans`: the composite of the
  canonical maps.
* `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_natTrans`: the canonical map is
  natural in the functor.

## References

* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w w'' v v' v'' u u' u''

namespace Stacks.DerivedIndexing

section Complexes

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E] (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive]

/-- **The comparison of a composite with the formation of single complexes**:
`((Q ∘ P)ℱ)[q] ⟶ (Q ∘ P)(ℱ[q])` is the comparison for `Q` at `Pℱ` followed by `Q` of the
comparison for `P` at `ℱ`. -/
public theorem singleMapHomologicalComplex_inv_app_comp (q : ℤ) (G : C) :
    (HomologicalComplex.singleMapHomologicalComplex (P ⋙ Q) (ComplexShape.up ℤ) q).inv.app G =
      (HomologicalComplex.singleMapHomologicalComplex Q (ComplexShape.up ℤ) q).inv.app (P.obj G) ≫
        (Q.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) q).inv.app G) := by
  ext i
  by_cases hi : i = q
  · subst hi
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Functor.comp_map, Category.assoc,
      ← Q.map_comp, Iso.inv_hom_id_assoc]
    rfl
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_ne (P ⋙ Q) (ComplexShape.up ℤ) hi,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_ne P (ComplexShape.up ℤ) hi,
      Q.map_zero, comp_zero]

/-- **The comparison with the formation of single complexes is natural in the functor.** -/
public theorem singleMapHomologicalComplex_inv_app_natTrans {F₁ F₂ : C ⥤ D} [F₁.Additive]
    [F₂.Additive] (τ : F₁ ⟶ F₂) (q : ℤ) (G : C) :
    (HomologicalComplex.singleMapHomologicalComplex F₁ (ComplexShape.up ℤ) q).inv.app G ≫
        (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) q).obj G) =
      (HomologicalComplex.single D (ComplexShape.up ℤ) q).map (τ.app G) ≫
        (HomologicalComplex.singleMapHomologicalComplex F₂ (ComplexShape.up ℤ) q).inv.app G := by
  ext i
  by_cases hi : i = q
  · subst hi
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc, τ.naturality]
  · simp only [HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_ne F₁ (ComplexShape.up ℤ) hi,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_ne F₂ (ComplexShape.up ℤ) hi,
      zero_comp, comp_zero]

end Complexes

section Derived

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] [HasDerivedCategory.{w} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [EnoughInjectives C]
  [EnoughInjectives D] in
/-- The class in `K⁺` of the comparison of complexes of a composite. -/
public theorem quotient_map_mapSinglePlus_comp (G : C) :
    (HomotopyCategory.Plus.quotient E).map ((mapSinglePlus (P ⋙ Q) 0).app G) =
      (HomotopyCategory.Plus.quotient E).map ((mapSinglePlus Q 0).app (P.obj G)) ≫
        Q.mapHomotopyCategoryPlus.map
          ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlus P 0).app G)) := by
  refine (HomotopyCategory.Plus.ι E).map_injective ?_
  refine Eq.trans ?_ ((HomotopyCategory.Plus.ι E).map_comp _ _).symm
  exact (congrArg (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
    (singleMapHomologicalComplex_inv_app_comp P Q 0 G)).trans (Functor.map_comp _ _ _)

/-- **The comparison `((Q ∘ P)ℱ)[0] ⟶ (Q ∘ P)(ℱ[0])` in `D⁺`** is the comparison for `Q` at `Pℱ`
followed by the class of `Q` of the comparison for `P` at `ℱ`. -/
public theorem mapSingleFunctorCompQhIso_inv_app_comp (G : C) :
    (Functor.mapSingleFunctorCompQhIso (P ⋙ Q)).inv.app G =
      (Functor.mapSingleFunctorCompQhIso Q).inv.app (P.obj G) ≫
        DerivedCategory.Plus.Qh.map (Q.mapHomotopyCategoryPlus.map
          ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlus P 0).app G))) := by
  refine (mapSingleFunctorCompQhIso_inv_app_eq (P ⋙ Q) G).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _) (mapSingleFunctorCompQhIso_inv_app_eq Q (P.obj G)).symm)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine Eq.trans ?_ (DerivedCategory.Plus.Qh.map_comp _ _)
  exact congrArg DerivedCategory.Plus.Qh.map (quotient_map_mapSinglePlus_comp P Q G)

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso in
/-- **The canonical map of a composite**: `((Q ∘ P)ℱ)[0] ⟶ R(Q ∘ P)(ℱ[0])` followed by the
composition transformation `R(Q ∘ P) ⟶ RQ ∘ RP` is the canonical map for `Q` at `Pℱ` followed by
`RQ` of the canonical map for `P` at `ℱ`. -/
public theorem rightDerivedPlusUnitSingle_comp_compTrans (G : C) :
    (rightDerivedPlusUnitSingle (P ⋙ Q)).app G ≫
        (rightDerivedPlusCompTrans P Q).app ((DerivedCategory.Plus.singleFunctor C 0).obj G) =
      (rightDerivedPlusUnitSingle Q).app (P.obj G) ≫
        Q.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle P).app G) := by
  have hm : (Functor.singleFunctorPlusIsoCompQh (A := D) 0).inv.app (P.obj G) ≫
      (Functor.mapSingleFunctorCompQhIso P).inv.app G =
        DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlus P 0).app G)) :=
    (congrArg (_ ≫ ·) (mapSingleFunctorCompQhIso_inv_app_eq P G)).trans
      (Iso.inv_hom_id_app_assoc _ _ _)
  have hnat := (rightDerivedPlusCompTrans P Q).naturality
    ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app G)
  have hfac :
      (P ⋙ Q).rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj G) ≫
      (rightDerivedPlusCompTrans P Q).app
        ((HomotopyCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.Qh).obj G) =
    Q.rightDerivedFunctorPlusUnit.app
        (P.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj G)) ≫
      Q.rightDerivedFunctorPlus.map
        (P.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj G)) :=
    (rightDerivedPlusCompTrans_fac_app P Q
      ((HomotopyCategory.Plus.singleFunctor C 0).obj G)).trans
    (rightDerivedPlusCompUnit_app P Q ((HomotopyCategory.Plus.singleFunctor C 0).obj G))
  have hu := Q.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlus P 0).app G))
  simp only [Functor.comp_map] at hnat hu
  simp only [rightDerivedPlusUnitSingle_app, Category.assoc]
  refine (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) hnat)).trans ?_
  refine (congrArg (· ≫ _) (mapSingleFunctorCompQhIso_inv_app_comp P Q G)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (_ ≫ ·) ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hfac))).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hu).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine ((congrArg (_ ≫ ·) (Q.rightDerivedFunctorPlus.map_comp _ _).symm).trans
    (Q.rightDerivedFunctorPlus.map_comp _ _).symm).trans ?_
  refine Eq.trans ?_ (Q.rightDerivedFunctorPlus.map_comp _ _)
  refine congrArg Q.rightDerivedFunctorPlus.map ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact congrArg (· ≫ _) hm.symm

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] [EnoughInjectives D] in
/-- The class in `K⁺` of the comparison with single complexes is natural in the functor. -/
public theorem quotient_map_mapSinglePlus_natTrans {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive]
    (τ : F₁ ⟶ F₂) (G : C) :
    (HomotopyCategory.Plus.quotient D).map ((mapSinglePlus F₁ 0).app G) ≫
        (Functor.mapHomotopyCategoryPlusNatTrans τ).app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj G) =
      (HomotopyCategory.Plus.singleFunctor D 0).map (τ.app G) ≫
        (HomotopyCategory.Plus.quotient D).map ((mapSinglePlus F₂ 0).app G) := by
  refine (HomotopyCategory.Plus.ι D).map_injective ?_
  refine ((HomotopyCategory.Plus.ι D).map_comp _ _).trans ?_
  refine Eq.trans ?_ ((HomotopyCategory.Plus.ι D).map_comp _ _).symm
  show (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F₁ (ComplexShape.up ℤ) 0).inv.app G) ≫
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G)) =
    (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).map (τ.app G)) ≫
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F₂ (ComplexShape.up ℤ) 0).inv.app G)
  refine ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map_comp _ _).symm.trans ?_
  refine Eq.trans ?_ ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map_comp _ _)
  exact congrArg _ (singleMapHomologicalComplex_inv_app_natTrans τ 0 G)

omit [EnoughInjectives D] in
/-- **The canonical map `(Fℱ)[0] ⟶ RF(ℱ[0])` is natural in the functor**: for `τ : F₁ ⟶ F₂` it
is carried to the canonical map of `F₂` by `τ` and by the induced `RF₁ ⟶ RF₂`. -/
public theorem rightDerivedPlusUnitSingle_comp_natTrans {F₁ F₂ : C ⥤ D} [F₁.Additive]
    [F₂.Additive] (τ : F₁ ⟶ F₂) (G : C) :
    (rightDerivedPlusUnitSingle F₁).app G ≫
        (rightDerivedFunctorPlusNatTrans τ).app ((DerivedCategory.Plus.singleFunctor C 0).obj G) =
      (DerivedCategory.Plus.singleFunctor D 0).map (τ.app G) ≫
        (rightDerivedPlusUnitSingle F₂).app G := by
  have hnat := (rightDerivedFunctorPlusNatTrans τ).naturality
    ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app G)
  have hfac := rightDerivedFunctorPlusNatTrans_app τ
    ((HomotopyCategory.Plus.singleFunctor C 0).obj G)
  have hs := (Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.naturality (τ.app G)
  have hm : (Functor.mapSingleFunctorCompQhIso F₁).inv.app G ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans τ).app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj G)) =
      (DerivedCategory.Plus.singleFunctor D 0).map (τ.app G) ≫
        (Functor.mapSingleFunctorCompQhIso F₂).inv.app G := by
    refine (congrArg (· ≫ _) (mapSingleFunctorCompQhIso_inv_app_eq F₁ G)).trans ?_
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (mapSingleFunctorCompQhIso_inv_app_eq F₂ G)).symm
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ _) hs).symm
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (_ ≫ ·) ?_
    refine (DerivedCategory.Plus.Qh.map_comp _ _).symm.trans ?_
    refine Eq.trans ?_ (DerivedCategory.Plus.Qh.map_comp _ _)
    exact congrArg DerivedCategory.Plus.Qh.map (quotient_map_mapSinglePlus_natTrans τ G)
  simp only [rightDerivedPlusUnitSingle_app, Category.assoc]
  refine (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) hnat)).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hfac).trans (Category.assoc _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hm).trans ?_
  exact Category.assoc _ _ _

end Derived

end Stacks.DerivedIndexing

end
