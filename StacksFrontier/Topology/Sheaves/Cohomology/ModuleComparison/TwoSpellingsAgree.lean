module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CompatibilityWithRestriction

/-!
# The two spellings of the canonical identification in Stacks 01F1 part (1) agree

The restriction clause of Stacks 01F1 part (1) is stated against an isomorphism which identifies
"derive module-valued sections over `U`, then forget the module structure" with "derive the
underlying abelian-group-valued sections functor". There are two ways to write that isomorphism
down:

* `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`, the instance at
  `Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso` of the general
  `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`;
* `cardRightDerivedEvaluationForgetIso`, an explicit five-fold composite through
  `CategoryTheory.HomologicalComplex.homologyFunctorIso` and
  `CategoryTheory.ShortComplex.mapHomologyIso`.

This file proves that the two are equal. They differ by morphisms which are identities but not
syntactically so: the degree-`n` homology of the cochain map induced by
`Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso`, which is `Iso.refl`, and the two
occurrences of `CategoryTheory.HomologicalComplex.homologyFunctorIso`.

## Main results

* `rightDerivedCompIso_refl_app_eq`: for additive `F` and exact additive `G`, the component at
  `M` of `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` for the identity comparison
  `F ⋙ G ≅ F ⋙ G` is the five-fold composite on the chosen injective resolution of `M`.
* `rightDerivedEvaluationForgetIso_app_eq` and `rightDerivedEvaluationForgetIso_inv_app_eq`: the
  component at a module sheaf of
  `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` is
  `cardRightDerivedEvaluationForgetIso`.
* `cardRightDerivedEvaluationForgetIso_naturality_open`: the restriction clause of Stacks 01F1
  part (1) written with the five-fold composite in place of
  `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`.

## Implementation notes

The functors `SheafOfModules.evaluation R (op U) ⋙ forget₂ _ _` and
`SheafOfModules.toSheaf R ⋙ Γ(U, -)`, and the objects
`(HomologicalComplex.homologyFunctor _ _ n).obj K` and `(K.sc n).homology`, are definitionally
but not syntactically equal, and across them `Category.assoc` is not type-correct as a rewrite.
The identities are therefore removed by the private lemma `removeInnerIdentities`, whose objects
and morphisms are all explicit, and the remaining steps are definitional unfoldings.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ModuleComparisonFaithful

/-! ### Deleting the two identity morphisms -/

section Abstract

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
  (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive] [G.PreservesHomology]

/-- Two identity morphisms `i = 𝟙 R₃` and `j = 𝟙 R₃`, and an identity `Φ.map (𝟙 Y)` under a
functor, deleted from a composite, with every object and morphism explicit. -/
private theorem removeInnerIdentities {C₁ C₂ : Type*} [Category C₁] [Category C₂] (Φ : C₁ ⥤ C₂)
    {Y : C₁} {R₁ R₃ R₄ : C₂} (a : R₁ ⟶ Φ.obj Y) (m : Φ.obj Y ⟶ R₃) (i j : R₃ ⟶ R₃)
    (z : R₃ ⟶ R₄) (hi : i = 𝟙 R₃) (hj : j = 𝟙 R₃) :
    a ≫ (m ≫ i) ≫ z = a ≫ Φ.map (𝟙 Y) ≫ m ≫ j ≫ z := by
  simp [hi, hj]

/-- **The component of `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` for the identity
comparison, written out.**  Deriving `F` on the chosen injective resolution of `M` and applying
`G`, then comparing with the degree-`n` homology of the image of that resolution under
`F ⋙ G`: the comparison is `CategoryTheory.ShortComplex.mapHomologyIso` in degree `n`, and the
remaining four factors only move between the two spellings of homology of a cochain complex. -/
theorem rightDerivedCompIso_refl_app_eq (n : ℕ) (M : A) :
    (ModuleComparison.rightDerivedCompIso F G (F ⋙ G) (Iso.refl (F ⋙ G)) n).app M =
      G.mapIso ((injectiveResolution M).isoRightDerivedObj F n) ≪≫
        G.mapIso ((HomologicalComplex.homologyFunctorIso B (ComplexShape.up ℕ) n).app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex)) ≪≫
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex).sc n).mapHomologyIso G).symm ≪≫
        ((HomologicalComplex.homologyFunctorIso D (ComplexShape.up ℕ) n).app
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution M).cocomplex))).symm ≪≫
        ((injectiveResolution M).isoRightDerivedObj (F ⋙ G) n).symm := by
  refine Iso.ext ?_
  exact removeInnerIdentities G _ _ _ _ _ (HomologicalComplex.homologyMap_id _ n) rfl

end Abstract

/-! ### The identification at the site of a topological space -/

section Space

variable {X : Type u} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (U : Opens X)

/-- **The canonical identification of Stacks 01F1 part (1), as the statement of the tag writes
it.** Derive module-valued sections over `U` on the chosen injective resolution of `M`, forget
the module structure, and compare with the degree-`n` homology of the image of that resolution
under the abelian-group-valued sections functor. The comparison is
`CategoryTheory.ShortComplex.mapHomologyIso` in degree `n`; the remaining four factors only move
between the two spellings of homology of a cochain complex. -/
noncomputable def cardRightDerivedEvaluationForgetIso (n : ℕ) (M : SheafOfModules.{u} R) :
    (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}).obj
        (((SheafOfModules.evaluation R (op U)).rightDerived n).obj M) ≅
      ((SheafOfModules.evaluation R (op U) ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}).rightDerived n).obj M :=
  let I := injectiveResolution M
  let E := SheafOfModules.evaluation R (op U)
  let G := forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  G.mapIso (I.isoRightDerivedObj E n) ≪≫
    G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ n).app K) ≪≫
    ((K.sc n).mapHomologyIso G).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso _ _ n).app
      ((G.mapHomologicalComplex _).obj K)).symm ≪≫
    (I.isoRightDerivedObj (E ⋙ G) n).symm

/-- **The two spellings of the canonical identification of Stacks 01F1 part (1) agree.** The
component at a module sheaf `M` of
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` is the five-fold composite
`cardRightDerivedEvaluationForgetIso`. -/
theorem rightDerivedEvaluationForgetIso_app_eq (n : ℕ) (M : SheafOfModules.{u} R) :
    (ModuleComparison.rightDerivedEvaluationForgetIso R U n).app M =
      cardRightDerivedEvaluationForgetIso R U n M :=
  rightDerivedCompIso_refl_app_eq (SheafOfModules.evaluation R (op U))
    (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}) n M

/-- The two spellings of the canonical identification of Stacks 01F1 part (1) agree on `inv`. -/
theorem rightDerivedEvaluationForgetIso_inv_app_eq (n : ℕ) (M : SheafOfModules.{u} R) :
    (ModuleComparison.rightDerivedEvaluationForgetIso R U n).inv.app M =
      (cardRightDerivedEvaluationForgetIso R U n M).inv :=
  congrArg Iso.inv (rightDerivedEvaluationForgetIso_app_eq R U n M)

end Space

/-! ### The restriction clause against the five-fold composite -/

section Clause

variable {X : Type u} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **Stacks 01F1, part (1), compatibility with restriction, against the five-fold composite.**
The restriction clause of Stacks 01F1 part (1) with its canonical identification written as the
explicit composite `cardRightDerivedEvaluationForgetIso` rather than as
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`. -/
theorem cardRightDerivedEvaluationForgetIso_naturality_open {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (M : SheafOfModules.{u} R) :
    (NatTrans.rightDerived
          (Functor.whiskerLeft (SheafOfModules.toSheaf R)
            (ModuleComparison.sectionsRestriction (Opens.grothendieckTopology X)
              (homOfLE h))) n).app M ≫
        (cardRightDerivedEvaluationForgetIso R U n M).inv ≫
        (ModuleComparison.canonicalSectionsForgetIso R U n).hom.app M =
      (cardRightDerivedEvaluationForgetIso R V n M).inv ≫
        (ModuleComparison.canonicalSectionsForgetIso R V n).hom.app M ≫
        (NatTrans.rightDerived
          (ModuleComparison.sectionsRestriction (Opens.grothendieckTopology X)
            (homOfLE h)) n).app ((SheafOfModules.toSheaf R).obj M) := by
  rw [← rightDerivedEvaluationForgetIso_inv_app_eq R U n M,
    ← rightDerivedEvaluationForgetIso_inv_app_eq R V n M]
  exact ModuleComparison.canonicalSectionsForgetIso_naturality_open R h n M

end Clause

end Stacks.Cohomology.ModuleComparisonFaithful

end
