module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Simplicial.Site

/-!
# The free abelian resolution of a simplicial space

For a simplicial topological space `X`, the whole space in every simplicial degree is an object
of its total site.  Taking the free abelian presheaves represented by these objects gives an
augmented simplicial abelian presheaf.  Its alternating face-map complex resolves the constant
presheaf of integers.

## Main definitions

* `Stacks.Topology.Simplicial.wholeSpaceFunctor`: the whole open subspace in every simplicial
  degree.
* `Stacks.Topology.Simplicial.representableSimplicialPresheaf`: the simplicial presheaf
  represented by those whole spaces.
* `Stacks.Topology.Simplicial.augmentedRepresentableSimplicialPresheaf`: its augmentation
  towards the terminal presheaf of sets.
* `Stacks.Topology.Simplicial.augmentedFreeAbelianPresheaf`: the augmented simplicial object
  whose terms are the free abelian presheaves represented by the whole spaces `X_n`.

## Main results

* `Stacks.Topology.Simplicial.freeAbelianRepresentableComplex_quasiIso_constant`: the
  augmentation of the alternating face-map complex is a quasi-isomorphism of abelian presheaves.

## Implementation notes

The terminal presheaf of sets is augmented from every simplicial presheaf.  Applying the free
abelian group functor objectwise makes its augmentation point the free abelian presheaf on a
singleton, canonically the constant presheaf `Z`. The resolution assertion is a
quasi-isomorphism in the category of abelian presheaves, rather than merely a family of
objectwise quasi-isomorphisms.

## References

* [Stacks Project, Tag 09W5](https://stacks.math.columbia.edu/tag/09W5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicTopology

universe u

namespace Stacks.Topology.Simplicial

/-- The functor which regards the whole space in each degree as an object of the total site of a
simplicial topological space. -/
def wholeSpaceFunctor (X : SimplicialObject TopCat.{u}) :
    CategoryTheory.Functor SimplexCategoryᵒᵖ (SimplicialOpen X) where
  obj n := ⟨n, ⊤⟩
  map f := { base := f, le := by simp }
  map_id _ := SimplicialOpen.Hom.ext _ _ rfl
  map_comp _ _ := SimplicialOpen.Hom.ext _ _ rfl

/-- The simplicial presheaf represented in degree `n` by the whole open subspace of `X_n`. -/
def representableSimplicialPresheaf (X : SimplicialObject TopCat.{u}) :=
  wholeSpaceFunctor X ⋙ yoneda

/-- The representable simplicial presheaf, augmented towards the terminal presheaf of sets. -/
noncomputable def augmentedRepresentableSimplicialPresheaf
    (X : SimplicialObject TopCat.{u}) :=
  SimplicialObject.augmentOfIsTerminal (representableSimplicialPresheaf X) terminalIsTerminal

/-- The augmented simplicial abelian presheaf obtained by applying the free abelian group
functor objectwise to the presheaves represented by the whole spaces `X_n`. -/
noncomputable def augmentedFreeAbelianPresheaf (X : SimplicialObject TopCat.{u}) :=
  (SimplicialObject.Augmented.whiskeringObj _ _
    ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)).obj
      (augmentedRepresentableSimplicialPresheaf X)

private abbrev evalSet {X : SimplicialObject TopCat.{u}} (V : SimplicialOpen X) :=
  (evaluation (SimplicialOpen X)ᵒᵖ Type).obj (Opposite.op V)

private abbrev evalGrp {X : SimplicialObject TopCat.{u}} (V : SimplicialOpen X) :=
  (evaluation (SimplicialOpen X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)

private def simplexHomEquiv (X : SimplicialObject TopCat.{u}) (V : SimplicialOpen X)
    (n : SimplexCategoryᵒᵖ) :
    ((representableSimplicialPresheaf X ⋙ evalSet V).obj n) ≃
      (SSet.stdSimplex.obj V.degree.unop).obj n := by
  change (V ⟶ wholeSpaceFunctor X |>.obj n) ≃ _
  exact {
    toFun := fun f => SSet.stdSimplex.objEquiv.{0}.symm f.base.unop
    invFun := fun x => ⟨(SSet.stdSimplex.objEquiv.{0} x).op, le_top⟩
    left_inv := fun f => by
      apply SimplicialOpen.Hom.ext
      change (SSet.stdSimplex.objEquiv.{0}
        (SSet.stdSimplex.objEquiv.{0}.symm f.base.unop)).op = f.base
      congr 1
    right_inv := SSet.stdSimplex.objEquiv.{0}.symm_apply_apply }

private lemma simplexHomEquiv_natural (X : SimplicialObject TopCat.{u})
    (V : SimplicialOpen X) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (g : V ⟶ (wholeSpaceFunctor X).obj i) :
    simplexHomEquiv X V j (g ≫ (wholeSpaceFunctor X).map f) =
      (SSet.stdSimplex.obj V.degree.unop).map f (simplexHomEquiv X V i g) := by
  unfold wholeSpaceFunctor at *
  dsimp only [simplexHomEquiv]
  show (SSet.stdSimplex.objEquiv.{0} (n := V.degree.unop) (m := j)).symm
      ((g ≫ (wholeSpaceFunctor X).map f).base.unop) =
    (SSet.stdSimplex.obj V.degree.unop).map f
      ((SSet.stdSimplex.objEquiv.{0} (n := V.degree.unop) (m := i)).symm g.base.unop)
  rw [SSet.stdSimplex.map_objEquiv_symm]
  rfl

private def evalRepresentableIso (X : SimplicialObject TopCat.{u}) (V : SimplicialOpen X) :
    representableSimplicialPresheaf X ⋙ evalSet V ≅ SSet.stdSimplex.obj V.degree.unop :=
  NatIso.ofComponents (fun n => Equiv.toIso (simplexHomEquiv X V n)) (by
    intro i j f
    ext g
    exact simplexHomEquiv_natural X V f g)

private noncomputable abbrev evalRepresentableAugmented (X : SimplicialObject TopCat.{u})
    (V : SimplicialOpen X) :=
  (SimplicialObject.Augmented.whiskeringObj
    ((SimplicialOpen X)ᵒᵖ ⥤ Type) Type (evalSet V)).obj
      (augmentedRepresentableSimplicialPresheaf X)

private noncomputable def evalRepresentableAugmentedIso (X : SimplicialObject TopCat.{u})
    (V : SimplicialOpen X) :
    evalRepresentableAugmented X V ≅ SSet.Augmented.stdSimplex.obj V.degree.unop := by
  have hSrc : IsTerminal (evalRepresentableAugmented X V).right := by
    change IsTerminal ((evalSet V).obj (⊤_ ((SimplicialOpen X)ᵒᵖ ⥤ Type)))
    exact terminalIsTerminal.isTerminalObj (evalSet V) _
  have hTgt : IsTerminal (SSet.Augmented.stdSimplex.obj V.degree.unop).right := by
    change IsTerminal (⊤_ Type)
    exact terminalIsTerminal
  let eR := hSrc.uniqueUpToIso hTgt
  exact Comma.isoMk (evalRepresentableIso X V) eR
    (SimplicialObject.hom_ext _ _ fun _ => hTgt.hom_ext _ _)

private noncomputable abbrev evalFreeAugmented (X : SimplicialObject TopCat.{u})
    (V : SimplicialOpen X) :=
  (SimplicialObject.Augmented.whiskeringObj
    ((SimplicialOpen X)ᵒᵖ ⥤ AddCommGrpCat) AddCommGrpCat (evalGrp V)).obj
      (augmentedFreeAbelianPresheaf X)

private noncomputable def evalFreeAugmentedIso (X : SimplicialObject TopCat.{u})
    (V : SimplicialOpen X) :
    evalFreeAugmented X V ≅
      (SimplicialObject.Augmented.whiskeringObj Type AddCommGrpCat AddCommGrpCat.free).obj
        (SSet.Augmented.stdSimplex.obj V.degree.unop) := by
  change ((SimplicialObject.Augmented.whiskeringObj Type AddCommGrpCat AddCommGrpCat.free).obj
      (evalRepresentableAugmented X V)) ≅ _
  exact (SimplicialObject.Augmented.whiskeringObj Type AddCommGrpCat AddCommGrpCat.free).mapIso
    (evalRepresentableAugmentedIso X V)

private theorem evalFreeAugmented_quasiIso (X : SimplicialObject TopCat.{u})
    (V : SimplicialOpen X) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (evalFreeAugmented X V)) := by
  let e := evalFreeAugmentedIso X V
  let Y := (SimplicialObject.Augmented.whiskeringObj Type AddCommGrpCat AddCommGrpCat.free).obj
    (SSet.Augmented.stdSimplex.obj V.degree.unop)
  let eC : (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj
        (evalFreeAugmented X V))) ≅
      (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj Y)) :=
    (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.drop.mapIso e)
  let eP : (ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj (evalFreeAugmented X V)) ≅
      (ChainComplex.single₀ AddCommGrpCat).obj (SimplicialObject.Augmented.point.obj Y) :=
    (ChainComplex.single₀ AddCommGrpCat).mapIso (SimplicialObject.Augmented.point.mapIso e)
  let eArrow : Arrow.mk (AlternatingFaceMapComplex.ε.app (evalFreeAugmented X V)) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app Y) :=
    Arrow.isoMk eC eP (by
      simpa [eC, eP, Y, SimplicialObject.Augmented.drop, SimplicialObject.Augmented.point,
        Functor.mapIso]
        using (AlternatingFaceMapComplex.ε.naturality e.hom))
  exact (quasiIso_iff_of_arrow_mk_iso _ _ eArrow).2
    (((SSet.Augmented.StandardSimplex.extraDegeneracy V.degree.unop).map
      AddCommGrpCat.free).homotopyEquiv.quasiIso_hom)

private noncomputable def evalAugmentationArrowIso (X : SimplicialObject TopCat.{u})
    (V : SimplicialOpen X) :
    Arrow.mk (((evalGrp V).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (AlternatingFaceMapComplex.ε.app (augmentedFreeAbelianPresheaf X))) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app (evalFreeAugmented X V)) := by
  let eC := (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (evalGrp V)).app (SimplicialObject.Augmented.drop.obj (augmentedFreeAbelianPresheaf X))
  let eP := (HomologicalComplex.singleMapHomologicalComplex (evalGrp V)
      (ComplexShape.down ℕ) 0).app
        (SimplicialObject.Augmented.point.obj (augmentedFreeAbelianPresheaf X))
  exact Arrow.isoMk eC eP

/-- **Stacks 09W5.** The alternating face-map complex of the free abelian presheaves represented
by `X_n`, augmented towards the constant presheaf of integers, is a resolution in abelian
presheaves. -/
@[stacks 09W5]
theorem freeAbelianRepresentableComplex_quasiIso_constant
    (X : SimplicialObject TopCat.{u}) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (augmentedFreeAbelianPresheaf X)) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro V
  -- The remaining pointwise map is the augmentation of the free abelian standard simplex.
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (evalAugmentationArrowIso X V.unop)).2 (evalFreeAugmented_quasiIso X V.unop)

end Stacks.Topology.Simplicial

end
