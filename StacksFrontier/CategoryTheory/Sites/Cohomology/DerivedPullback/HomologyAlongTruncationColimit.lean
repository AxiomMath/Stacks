module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSizeTruncation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.Homology.HomologyColimit

/-!
# The cohomology of a derived pullback is a colimit over the truncations

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi and `K` a complex of
`𝒪'`-modules.  The K-flat resolution of Stacks 06YS presents `K` as a sequential colimit of
bounded above complexes of flat modules `Dₙ`, the `n`-th resolving the truncation `τ_{≤ n} K`;
the colimit is K-flat with flat terms, so `Lf^* K` is its degreewise pullback, which commutes
with the colimit, and so does cohomology.  Hence `Hʲ(Lf^* K)` is a sequential colimit of the
`Hʲ(Lf^* τ_{≤ n} K)`, and any property of `𝒪`-modules stable under sequential colimits and
isomorphisms passes from the truncations to `K`.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.prop_homology_derivedPullback_of_truncLE`: the
  passage from the truncations to `K`.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

noncomputable section

universe v u w v' u' w'

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  (f : RingedToposHom X Y)

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

/-- A quasi-isomorphism `g : C ⟶ L` with `C` K-flat identifies `Lf^* L` with the degreewise
pullback of `C`. -/
private def derivedPullbackIsoOfQuasiIso
    {C L : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ℤ}
    (g : C ⟶ L) [QuasiIso g]
    [IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))] :
    (derivedPullback f).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj
        (((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  (derivedPullback f).mapIso ((asIso (DerivedCategory.Q.map g)).symm ≪≫
        ((DerivedCategory.quotientCompQhIso _).app C).symm) ≪≫
    asIso ((derivedPullbackComparison f).app _) ≪≫
    DerivedCategory.Qh.mapIso
      (((f.toModulesHom.pullbackModules).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app C) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- **The cohomology of `Lf^* K` is determined by the truncations of `K`.**  If a property `P`
of `𝒪`-modules, closed under isomorphisms and under sequential colimits, holds for the
cohomology sheaves of every `Lf^* τ_{≤ n} K`, it holds for those of `Lf^* K`. -/
theorem prop_homology_derivedPullback_of_truncLE
    (P : ObjectProperty
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))))
    [P.IsClosedUnderIsomorphisms]
    (hP : ∀ F : ℕ ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)),
      (∀ n, P (F.obj n)) → P (colimit F))
    (K : CochainComplex
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ℤ)
    (hK : ∀ (n : ℕ) (j : ℤ), P ((DerivedCategory.homologyFunctor _ j).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj (K.truncLE (n : ℤ))))))
    (j : ℤ) :
    P ((DerivedCategory.homologyFunctor _ j).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj K))) := by
  obtain ⟨D, α, hLE, hDflat, hqis, -, htr⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize_truncLE Y.O K
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize Y.O
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize X.O
  have := Stacks.SheafOfModules.KFlatResolution.hasExactColimitsOfShape_nat_ofSize X.O
  let pb := (f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)
  have hPk : IsKFlat (Y := Y) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (colimit D)) :=
    ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
      Y.O D hLE hDflat,
      Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize Y.O D hDflat⟩
  have := isIso_derivedPullbackComparison_app_isKFlat f _ hPk
  have : QuasiIso α := hqis
  have : PreservesColimitsOfSize.{0, 0} (f.toModulesHom.pullbackModules) :=
    (RingedToposHom.pullbackAdjPushforwardModules f).leftAdjoint_preservesColimits
  have := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
    (f.toModulesHom.pullbackModules)
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) (J := ℕ)
    (ComplexShape.up ℤ) j
  -- `Lf^* K` is the degreewise pullback of the colimit
  let e₁ := derivedPullbackIsoOfQuasiIso f α
  -- degreewise pullback and cohomology commute with the colimit
  let e₂ : (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).obj (pb.obj (colimit D)) ≅
      colimit (D ⋙ pb ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j) :=
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).mapIso
        (preservesColimitIso pb D) ≪≫
      preservesColimitIso (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j) _ ≪≫
      HasColimit.isoOfNatIso (Functor.associator _ _ _)
  refine P.prop_of_iso (((DerivedCategory.homologyFunctor _ j).mapIso e₁ ≪≫
      (DerivedCategory.homologyFunctorFactors _ j).app _ ≪≫ e₂).symm) (hP _ fun n => ?_)
  obtain ⟨b, hb⟩ := hLE n
  obtain ⟨q, hq⟩ := htr n
  have := isIso_derivedPullbackComparison_app_isKFlat f
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (D.obj n))
    ⟨(Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O _).1
      (Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Y.O _ ⟨b, hb⟩ (hDflat n)),
      hDflat n⟩
  have : QuasiIso q := hq
  let e₃ := derivedPullbackIsoOfQuasiIso f q
  exact P.prop_of_iso ((DerivedCategory.homologyFunctor _ j).mapIso e₃ ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app _) (hK n j)

end Stacks.Cohomology.DerivedPullbackOfToposHom

end

end
