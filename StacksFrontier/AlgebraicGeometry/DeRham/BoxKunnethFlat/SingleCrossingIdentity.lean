module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.SingleCrossingTransport

/-!
# The naive crossing map against the box comparison at single complexes, summand by summand

For finite-order differential operator modules `𝓕` and `𝓖` placed in degrees `i` and `j`, the
naive crossing map followed by the isomorphism
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.pushforwardTotalSingleIso`, on the
summand `(i, j)`, is the transpose of the comparison of Stacks 01CD followed by the degreewise
crossing legs, transported into `𝓕 ⊠ 𝓖`.

## Main results

* `ι_naiveCrossing_pushforwardTotalSingleIso`: on the summand `(i, j)`, the naive crossing map
  followed by `pushforwardTotalSingleIso` is the transported comparison composed with the crossing
  legs.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.DeRhamDirectImage
open scoped CategoryTheory.Prod

universe u

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

/-- The chase behind `ι_naiveCrossing_pushforwardTotalSingleIso`, every object and morphism a
variable. -/
private theorem chase_f {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {A B D : HomologicalComplex C (ComplexShape.up ℤ)} (N : A ⟶ B) (T : B ⟶ D) (n : ℤ)
    {x y z : C} (ι : x ⟶ A.X n) (H : x ⟶ y) (ιW : y ⟶ B.X n) (E : y ⟶ z) (Bx : z ⟶ D.X n)
    (h1 : ι ≫ N.f n = H ≫ ιW) (h2 : ιW ≫ T.f n = E ≫ Bx) :
    ι ≫ (N ≫ T).f n = H ≫ E ≫ Bx := by
  rw [HomologicalComplex.comp_f, reassoc_of% h1, h2]


section LegFactors

variable {W X' S' : Scheme.{u}} (p : W ⟶ X') (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g)
  (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace)
      ℤ)

/-- The degreewise crossing leg for `g` presented as the factorization `p ∘ c` is, in every degree,
the crossing leg of the box comparison. -/
theorem naiveCrossingLeg_ofFactors_f (n : ℤ) :
    (Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase c) (toInverseImageBase g)
        p.toLRSHom.toShHom (relativeInverseImageProjectionOfFactors p c g hg)
        (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors p c g hg) K).f n =
      crossingLegOfFactors p c g hg (K.X n) :=
  (Stacks.Cohomology.KunnethNaive.naiveCrossingLeg_f _ _ _ _ _ K n).trans rfl

end LegFactors

section SingleBox

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (F : FiniteOrderDifferentialOperatorCategory a)
  (G : FiniteOrderDifferentialOperatorCategory b) (i j : ℤ)

/-- **The naive crossing map followed by `θ`, on the summand `(i, j)`.** -/
theorem ι_naiveCrossing_pushforwardTotalSingleIso :
    HomologicalComplex.ιMapBifunctor ((pullbackComplex
        (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
        F.module))) ((pullbackComplex (relativeInverseImageProjectionOfFactors (pullback.snd a b) b
        (pullback.fst a b ≫ a) pullback.condition.symm)).obj
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
        G.module))) (Stacks.SheafOfModules.Tensor.sheafTensor
        (inverseImageBase (pullback.fst a b ≫ a)).sheaf) (ComplexShape.up ℤ) i j (i + j) rfl ≫
        ((Stacks.Cohomology.KunnethNaive.naiveCrossing (toInverseImageBase a) (toInverseImageBase b)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
            (pullback.snd a b).toLRSHom.toShHom (Stacks.Cohomology.BoxKunneth.fstProjection a b)
            (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm) (toInverseImageBase_comp_relativeInverseImageProjection
            (pullback.fst a b) a) (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)
            ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)) ≫
            (pushforwardTotalSingleIso a b F G i j).hom).f (i + j) =
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase (pullback.fst a b ≫ a))).homEquiv _ _
        ((comparisonAppIso (toInverseImageBase (pullback.fst a b ≫ a))
            (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
            i).obj F.module))).X i) (((pullbackComplex (relativeInverseImageProjectionOfFactors
            (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)).obj
            ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
            (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ)
            j).obj G.module))).X j)).hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            (pullback a b).toRingedSpace.sheaf).map
            ((Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase a)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
            (Stacks.Cohomology.BoxKunneth.fstProjection a b)
            (toInverseImageBase_comp_relativeInverseImageProjection (pullback.fst a b) a)
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)).f i)).app _
            ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).obj
            _).map ((Stacks.Cohomology.KunnethNaive.naiveCrossingLeg (toInverseImageBase b)
            (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.snd a b).toLRSHom.toShHom
            (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm)
            (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
            (pullback.fst a b ≫ a) pullback.condition.symm)
            ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)).f j)) ≫
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl := by
  have hLB := Stacks.Cohomology.KunnethNaive.ι_naiveCrossing_f (toInverseImageBase a)
      (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
      (Stacks.Cohomology.BoxKunneth.fstProjection a b)
      (toInverseImageBase_comp_relativeInverseImageProjection (pullback.fst a b) a)
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)
    (toInverseImageBase b) (pullback.snd a b).toLRSHom.toShHom
        (relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
        pullback.condition.symm) (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors
        (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm)
        ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module) i j (i + j) rfl
  have hθ := pushforward_ι_pushforwardTotalSingleIso_hom_f a b F G i j
  exact chase_f _ _ (i + j) _ _ _ _ _ hLB hθ


/-- **Steps (4)–(5) at single complexes, from the degreewise pullbacks of the direct images**:
`Tot(p'^*ψ ⊗ q'^*ψ)` followed by the comparison of step (5). -/
def singleBoxComparison : (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor
    (inverseImageBase (pullback.fst a b ≫ a)).sheaf)).obj
    (((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
    ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex (toInverseImageBase a)).obj
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module))),
    ((pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).obj
    ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex (toInverseImageBase b)).obj
    ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)))) ⟶
    HomologicalComplex.mapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
    (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) :=
  HomologicalComplex.mapBifunctorMap ((pullbackComplex
      (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map (pushforwardSingleIso a F i).hom)
      ((pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
      (pushforwardSingleIso b G j).hom) (Stacks.SheafOfModules.Tensor.sheafTensor
      (inverseImageBase (pullback.fst a b ≫ a)).sheaf) (ComplexShape.up ℤ) ≫
    Stacks.Cohomology.BoxKunneth.boxTotalComplexComparison a b
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)

/-- On the summand `(i, j)`, the map of steps (4)–(5) is `ψ` in degrees `i` and `j` followed by
the degreewise comparison `p^{-1}𝓕 ⊗ q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖`. -/
theorem ι_singleBoxComparison :
    HomologicalComplex.ιMapBifunctor ((pullbackComplex
        (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
        F.module))) ((pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).obj
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
        G.module))) (Stacks.SheafOfModules.Tensor.sheafTensor
        (inverseImageBase (pullback.fst a b ≫ a)).sheaf) (ComplexShape.up ℤ) i j (i + j) rfl ≫
        (singleBoxComparison a b F G i j).f (i + j) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
          (pullback.fst a b ≫ a)).sheaf).map ((StacksDraft.KFlat.modulePullback
          (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map
          ((pushforwardSingleIso a F i).hom.f i))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
            (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
            (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
          ((pushforwardSingleIso b G j).hom.f j)) ≫
        relativeBoxComparison a b (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)
            (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) ≫
            HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ)
            i).obj F) ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
            (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
            (i + j) rfl := by
  have h1 : HomologicalComplex.ιMapBifunctor ((pullbackComplex
      (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
      ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
      (toInverseImageBase a)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
      F.module))) ((pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).obj
      ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
      (toInverseImageBase b)).obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj
      G.module))) (Stacks.SheafOfModules.Tensor.sheafTensor
      (inverseImageBase (pullback.fst a b ≫ a)).sheaf) (ComplexShape.up ℤ) i j (i + j) rfl ≫
      (HomologicalComplex.mapBifunctorMap ((pullbackComplex
      (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map (pushforwardSingleIso a F i).hom)
      ((pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
      (pushforwardSingleIso b G j).hom) (Stacks.SheafOfModules.Tensor.sheafTensor
      (inverseImageBase (pullback.fst a b ≫ a)).sheaf) (ComplexShape.up ℤ)).f (i + j) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
          (pullback.fst a b ≫ a)).sheaf).map ((StacksDraft.KFlat.modulePullback
          (Stacks.Cohomology.BoxKunneth.fstProjection a b)).map
          ((pushforwardSingleIso a F i).hom.f i))).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
            (pullback.fst a b ≫ a)).sheaf).obj _).map ((StacksDraft.KFlat.modulePullback
            (Stacks.Cohomology.BoxKunneth.sndProjection a b)).map
          ((pushforwardSingleIso b G j).hom.f j)) ≫ HomologicalComplex.ιMapBifunctor
              ((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
              (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)))
              ((pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).obj
              (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)))
              (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase
              (pullback.fst a b ≫ a)).sheaf) (ComplexShape.up ℤ) i j (i + j) rfl :=
    HomologicalComplex.ι_mapBifunctorMap _ _ _ _ _ _ _ _
  have h2 : HomologicalComplex.ιMapBifunctor ((pullbackComplex
      (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
      (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)))
      ((pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).obj
      (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)))
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase (pullback.fst a b ≫ a)).sheaf)
      (ComplexShape.up ℤ) i j (i + j) rfl ≫ (Stacks.Cohomology.BoxKunneth.boxTotalComplexComparison
      a b ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)).f (i + j) = relativeBoxComparison
      a b (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)
      (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) ≫
      HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
      (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j (i + j)
      rfl :=
    Stacks.Cohomology.BoxKunneth.ι_boxTotalComplexComparison a b
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G) i j (i + j) rfl
  exact (chase_f _ _ (i + j) _ _ _ _ _ (h1.trans (Category.assoc _ _ _).symm) h2).trans
    (Category.assoc _ _ _)

/-- The degreewise crossing leg of `p` in degree `i` is the crossing leg of the box comparison. -/
theorem naiveCrossingLeg_fst_f : (Stacks.Cohomology.KunnethNaive.naiveCrossingLeg
    (toInverseImageBase a) (toInverseImageBase (pullback.fst a b ≫ a))
    (pullback.fst a b).toLRSHom.toShHom (Stacks.Cohomology.BoxKunneth.fstProjection a b)
    (toInverseImageBase_comp_relativeInverseImageProjection (pullback.fst a b) a)
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)).f i =
    (crossingLegOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
    (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i)) :=
  (Stacks.Cohomology.KunnethNaive.naiveCrossingLeg_f _ _ _ _ _ _ i).trans rfl


end SingleBox

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
