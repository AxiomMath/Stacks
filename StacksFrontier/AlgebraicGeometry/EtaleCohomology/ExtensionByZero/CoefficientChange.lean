module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars

/-!
# Extension by zero along an open immersion commutes with every change of coefficients

Let `j : U ⟶ X` be an open immersion (an étale monomorphism) of schemes.  Extension by zero `j_!`
of sheaves on the small étale sites is the sheafified left Kan extension along composition with
`j`, `smallEtaleCompose j : U_étale ⥤ X_étale`.  Since this functor is fully faithful and its
essential image is closed under maps into it, each category indexing the pointwise left Kan
extension is either empty or has a terminal object.  So every functor `G` preserving initial
objects (for instance any functor between abelian categories preserving zero morphisms)
preserves these Kan extensions, and the comparison
`j_!(G ∘ F) ⟶ G ∘ j_!(F)` (`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`) is invertible
as soon as `G` commutes with sheafification.  This is used in Step 7 of the proof of
[Stacks, Tag 03UG] for the non-exact functor `Hom_{A[G]}(M^*, -)`.

## Main results

* `CategoryTheory.CostructuredArrow.preservesColimitsOfShape_of_full_of_faithful`.
* `Stacks.EtaleCohomology.preservesLeftKanExtensions_smallEtaleCompose`.
* `Stacks.EtaleCohomology.extensionByZeroCoefficientIso`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 7.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace CategoryTheory.CostructuredArrow

variable {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]

/-- **Any functor preserves the colimits indexed by `CostructuredArrow S d` when `d` lies in the
essential image of a fully faithful `S`**: that category has a terminal object. -/
theorem preservesColimitsOfShape_of_full_of_faithful (S : C ⥤ D) [S.Full] [S.Faithful]
    {c : C} {d : D} (e : S.obj c ≅ d) (G : A ⥤ B) :
    PreservesColimitsOfShape (CostructuredArrow S d) G := by
  have ht : IsTerminal (CostructuredArrow.mk (𝟙 (S.obj c))) := CostructuredArrow.mkIdTerminal
  have : PreservesColimitsOfShape (CostructuredArrow S (S.obj c)) G :=
    ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitOfDiagramTerminal ht F)
      (colimitOfDiagramTerminal ht (F ⋙ G))⟩
  exact preservesColimitsOfShape_of_equiv (CostructuredArrow.mapIso e) G

/-- **A functor preserving initial objects preserves the colimits indexed by an empty
category.** -/
theorem preservesColimitsOfShape_of_isEmpty {J : Type*} [Category* J] [IsEmpty J] (G : A ⥤ B)
    [PreservesColimitsOfShape (Discrete PEmpty.{1}) G] : PreservesColimitsOfShape J G :=
  preservesColimitsOfShape_of_equiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J) G

end CategoryTheory.CostructuredArrow


namespace Stacks.EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Every functor preserving initial objects preserves the left Kan extensions along
composition with an open immersion `j`**: the category indexing the Kan extension at `W` is
empty unless `W ⟶ X` factors through `U`, and then it has a terminal object, `smallEtaleCompose j`
being fully faithful. -/
instance preservesLeftKanExtensions_smallEtaleCompose {A B : Type*} [Category* A] [Category* B]
    (G : A ⥤ B) [PreservesColimitsOfShape (Discrete PEmpty.{1}) G]
    [∀ P : U.Etaleᵒᵖ ⥤ A, (Scheme.Etale.smallEtaleCompose j).op.HasPointwiseLeftKanExtension P] :
    G.PreservesLeftKanExtensions (Scheme.Etale.smallEtaleCompose j).op := by
  have : ∀ W : X.Etaleᵒᵖ, PreservesColimitsOfShape
      (CostructuredArrow (Scheme.Etale.smallEtaleCompose j).op W) G := by
    intro W
    rcases isEmpty_or_nonempty (CostructuredArrow (Scheme.Etale.smallEtaleCompose j).op W) with
      h | ⟨⟨Y⟩⟩
    · exact CostructuredArrow.preservesColimitsOfShape_of_isEmpty G
    · exact CostructuredArrow.preservesColimitsOfShape_of_full_of_faithful _
        (c := op (Scheme.Etale.composeDescend j Y.hom.unop))
        (Scheme.Etale.composeDescendIso j Y.hom.unop).op.symm G
  infer_instance

variable {R S : Type} [Ring R] [Ring S] (Gf : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
  [Gf.PreservesZeroMorphisms] [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose Gf]
  [X.smallEtaleTopology.PreservesSheafification Gf]

/-- **Extension by zero along an open immersion commutes with a change of coefficients** `Gf`
preserving zero morphisms and sheafification: the comparison
`j_!(Gf ∘ F) ⟶ Gf ∘ j_!(F)` is invertible. -/
def extensionByZeroCoefficientIso :
    sheafCompose U.smallEtaleTopology Gf ⋙ etaleModuleExtensionByZero.{u, 0} S j ≅
      etaleModuleExtensionByZero.{u, 0} R j ⋙ sheafCompose X.smallEtaleTopology Gf :=
  haveI : PreservesColimit (Functor.empty.{0} (ModuleCat.{u + 1} R)) Gf :=
    Functor.preservesInitialObject_of_preservesZeroMorphisms Gf
  haveI : PreservesColimitsOfShape (Discrete PEmpty.{1}) Gf :=
    preservesColimitsOfShape_pempty_of_preservesInitial (G := Gf)
  haveI : Gf.PreservesLeftKanExtensions (Scheme.Etale.smallEtaleCompose j).op := inferInstance
  asIso (coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
    X.smallEtaleTopology Gf).natTrans

end Stacks.EtaleCohomology

end
