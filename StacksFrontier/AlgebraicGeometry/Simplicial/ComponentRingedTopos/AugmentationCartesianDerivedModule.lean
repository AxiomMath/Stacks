module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationCartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentTensorComplex
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensorPullback
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesianDerived
import StacksCore.Tactic.StacksAttribute

/-!
# Pullbacks along an augmentation are cartesian

Let `S` be a simplicial-site situation (Stacks 09WE), in either of its two cases, and `a` an
augmentation of `S` towards a site `(D, K)` (Stacks 0D6Z), with total augmentation
`a : Sh(C_total) ⟶ Sh(D)` of Stacks 0D70. Let `A` be a ringed augmentation of Stacks 0D9D: sheaves
of rings `O` on the total site and `O_D` on `(D, K)` with `a^♯ : O_D ⟶ a_*O`. Stacks 0D7H says
that every pullback along `a` is cartesian:

1. `a⁻¹𝒢` for a sheaf of sets or of abelian groups `𝒢` on `(D, K)`;
2. `a⁻¹E` for an object `E` of `D(D)`;
3. `a^*F` for a sheaf of `O_D`-modules `F`;
4. `La^*E` for an object `E` of `D(O_D)`.

This file proves part (4) and assembles the four parts.

## Main results

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation`
  `.isCartesianDerivedModule_derivedPullbackModules`: the derived pullback `La^*E` of an object
  of `D(O_D)` is cartesian.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.isCartesian_pullbacks`: all four
  pullbacks along `a` are cartesian.

## The argument for part (4)

The source deduces every part from the identities `a_m ∘ f_φ = a_n`. On derived categories we go
through K-flat resolutions instead. Every object of `D(O_D)` is isomorphic to a K-flat complex
`P` with flat terms (Stacks 06YS). Then `La^*P` is computed by degreewise pullback `a^*P`
(Stacks 06YY), and `a^*P` is again K-flat with flat terms (Stacks 0G7E). Its restriction
`g_m^*a^*P` to degree `m` is K-flat with flat terms too, so `Lf_φ^*` of it is computed
degreewise. The derived transition at `a^*P` is therefore the image in the derived category of
the degreewise transition `f_φ^*(a^*P^i)_m ⟶ (a^*P^i)_n`, and part (3) makes that transition
invertible in every degree.

## Implementation notes

The ringed augmentation of part (3) and part (4) is universally quantified in
`Augmentation.isCartesian_pullbacks`. This follows the source, where `O`, `O_D` and `a^♯` are
introduced only after parts (1) and (2).

## References

* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

/-- **A cartesian sheaf of modules has invertible transitions between its literal restrictions.**
If the transitions `f_φ^*(g_m^*M) ⟶ g_n^*M` of `M` are invertible, so are the transitions
`f_φ^*(M|_{C_m}) ⟶ M|_{C_n}` of its restrictions, from which the derived transitions are
built: the two differ by the identifications `g_n^* ≅ (-)|_{C_n}` of Stacks 0D72. -/
theorem isIso_componentModulesTransition_app_of_isModuleFiberTransitionIso
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
    (M : (S.totalRingedTopos O).Modules) (hM : S.IsModuleFiberTransitionIso O M)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((S.componentModulesTransition O φ).app M) := by
  change IsIso ((S.componentModuleTransition O φ).app M)
  rw [componentModuleTransition_app_eq_moduleFiberTransition]
  have h := hM φ
  exact ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapIso
      ((componentPullbackModulesRestrictionIso S O m).app M).symm ≪≫
    asIso ((S.moduleFiberTransition O φ).app M) ≪≫
      (componentPullbackModulesRestrictionIso S O n).app M).isIso_hom

namespace RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

attribute [local instance] hasWeakSheafifyComponent hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- **The derived transitions are invertible at the degreewise pullback of a K-flat complex.**
Let `P` be a K-flat complex of `O_D`-modules with flat terms. Then the derived transition
`Lf_φ^*(a^*P)_m ⟶ (a^*P)_n` is invertible. The restriction of `a^*P` to degree `m` is K-flat with
flat terms (Stacks 0G7E at `a` and at `g_m`), so `Lf_φ^*` of it is computed degreewise
(Stacks 06YY). What is left is the degreewise transition of `a^*P`, and each of its terms is
the pullback of a sheaf of modules, so Stacks 0D7H (3) makes it invertible. -/
theorem isIso_derivedComponentModuleTransition_app_pullback
    (P : HomotopyCategory A.augmentationRingedTopos.Modules (ComplexShape.up ℤ))
    (hP : A.augmentationKFlat P) {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((S.derivedComponentModuleTransition A.O φ).app
      (DerivedCategory.Qh.obj
        (((A.totalRingedHom.toModulesHom.pullbackModules).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj P))) := by
  have hX := A.augmentationKFlat_pullback P hP
  set X := ((A.totalRingedHom.toModulesHom.pullbackModules).mapHomotopyCategory
    (ComplexShape.up ℤ)).obj P
  have h1 := S.isIso_derivedTransitionComparison_app A.O φ
    (((S.componentModulesRestriction A.O m).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)
    ⟨S.kFlat_componentModulesRestrictionComplex A.O m _ hX.1 hX.2,
      S.isFlat_componentModulesRestrictionComplex_X A.O m _ hX.2⟩
  have h2 : IsIso ((mapHomotopyCategoryTransition (ComplexShape.up ℤ)
      (S.componentModulesRestriction A.O m)
      (S.transitionRingedToposHom A.O φ).toModulesHom.pullbackModules
      (S.componentModulesRestriction A.O n) (S.componentModulesTransition A.O φ)).app X) := by
    rw [mapHomotopyCategoryTransition_app]
    have hi : ∀ i, IsIso (((NatTrans.mapHomologicalComplex
        (S.componentModulesTransition A.O φ) (ComplexShape.up ℤ)).app X.as).f i) := fun i ↦
      S.isIso_componentModulesTransition_app_of_isModuleFiberTransitionIso A.O _
        (A.isCartesianModule_pullbackModules (P.as.X i)) φ
    have := @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ hi
    exact Functor.map_isIso _ _
  delta derivedComponentModuleTransition derivedComponentModuleRestriction
  rw [liftedTransition_app_q]
  infer_instance

/-- Let `E` be an object of `D(O_D)`. Then the derived pullback `La^*E` along the ringed
augmentation of Stacks 0D9D is a cartesian object of `D(O)`: every derived transition
`Lf_φ^*(La^*E)_m ⟶ (La^*E)_n` is an isomorphism. -/
@[stacks 0D7H "part (4)"]
theorem isCartesianDerivedModule_derivedPullbackModules
    (E : DerivedCategory A.augmentationRingedTopos.Modules) :
    S.IsCartesianDerivedModule A.O (A.derivedPullbackModules.obj E) := by
  intro m n φ
  have := Localization.essSurj (DerivedCategory.Qh (C := A.augmentationRingedTopos.Modules))
    (HomotopyCategory.quasiIso A.augmentationRingedTopos.Modules (ComplexShape.up ℤ))
  obtain ⟨P, hP, s, hs⟩ := A.hasResolutions_augmentationKFlat (DerivedCategory.Qh.objPreimage E)
  have hsi : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh _ s hs
  have hc := A.isIso_derivedPullbackModulesComparison_app P hP
  let e : A.derivedPullbackModules.obj E ≅
      DerivedCategory.Qh.obj
        (((A.totalRingedHom.toModulesHom.pullbackModules).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj P) :=
    (A.derivedPullbackModules.mapIso
        (asIso (DerivedCategory.Qh.map s) ≪≫ DerivedCategory.Qh.objObjPreimageIso E)).symm ≪≫
      asIso (A.derivedPullbackModulesComparison.app P)
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  exact A.isIso_derivedComponentModuleTransition_app_pullback P hP φ

end RingedAugmentation

namespace Augmentation

/-- Let `a` be an augmentation of a simplicial-site situation towards a site `(D, K)`. Then every
pullback along `a` is cartesian:

1. `a⁻¹𝒢`, for a sheaf of sets `𝒢` on `(D, K)` and for a sheaf of abelian groups `𝒢`;
2. `a⁻¹E`, for an object `E` of `D(D)`;
3. `a^*F`, for a ringed augmentation `A` of Stacks 0D9D and a sheaf of `O_D`-modules `F`;
4. `La^*E`, for a ringed augmentation `A` and an object `E` of `D(O_D)`. -/
@[stacks 0D7H]
theorem isCartesian_pullbacks (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) (a : Augmentation S D K) :
    ((∀ G : Sheaf K (Type u),
        IsCartesianSheaf S ((totalMorphismOfTopoi S D K a).inverseImage.obj G)) ∧
      ∀ G : Sheaf K Ab.{u}, IsCartesianAbSheaf S ((totalInverseImageAb S D K a).obj G)) ∧
    (∀ E : DerivedCategory (Sheaf K AddCommGrpCat.{u}),
      S.IsCartesianDerived ((derivedTotalInverseImage S D K a).obj E)) ∧
    (∀ (A : RingedAugmentation S D K a)
      (F : SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.augmentationRingedTopos.J)
          A.augmentationRingedTopos.O))),
      S.IsModuleFiberTransitionIso A.O (A.totalRingedHom.toModulesHom.pullbackModules.obj F)) ∧
    ∀ (A : RingedAugmentation S D K a) (E : DerivedCategory A.augmentationRingedTopos.Modules),
      S.IsCartesianDerivedModule A.O (A.derivedPullbackModules.obj E) :=
  ⟨⟨isCartesianSheaf_totalMorphismOfTopoi_inverseImage S D K a,
      isCartesianAbSheaf_totalInverseImageAb S D K a⟩,
    isCartesianDerived_derivedTotalInverseImage S D K a,
    fun A ↦ A.isCartesianModule_pullbackModules,
    fun A ↦ A.isCartesianDerivedModule_derivedPullbackModules⟩

end Augmentation

end CategoryTheory.SimplicialSiteSituation

end
