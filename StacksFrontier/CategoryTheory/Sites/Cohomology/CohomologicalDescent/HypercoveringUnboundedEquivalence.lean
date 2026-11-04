module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackOfIsIsoFSharp
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringTotalOlssonLaszlo
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalenceOfAdjunction

/-!
# Unbounded cohomological descent for a local family of weak Serre subcategories

Let `(C, O_C)` be a ringed site and `A_U ⊂ Mod(O_U)` weak Serre subcategories satisfying
conditions 0DC2, 0DC3 and 0DC4 (a `LocalSerreFamily`), and let `A ⊂ Mod(O_C)` be the modules
whose restriction to every `C/U` lies in `A_U`. Let `C` have equalizers and fibre products and
let `K` be a hypercovering, with total ringed site `((C/K)_total, O)` of Remark 0D9W and
augmentation `a`. Let `A_total ⊂ Mod(O)` be the cartesian `O`-modules `F` whose restrictions
`F_n` lie in `A_{K_n} = ∏_i A_{U_{n,i}}`. Stacks 0DC7 asserts that `A_total` is a weak Serre
subcategory and that

`La^* : D_A(O_C) ⟶ D_{A_total}(O)`

is an equivalence of categories with quasi-inverse `Ra_*`.

## The argument

It is the source's: Stacks 0D7V for `a`. Its assumptions are
1. `a` is flat — here `a^*` is exact because `O = a⁻¹O_C`, so `La^*` is degreewise;
2. `a^*` induces an equivalence `A ⟶ A_total` (`totalLocalSerre_pullbackModules` and
   `exists_pullbackModules_iso_of_totalLocalSerre`, the covering argument of the source);
3. `F ⟶ Ra_*a^*F` is invertible for `F` in `A`, which is Stacks 0DA0 in all of `D(O_C)`;
4. and 5. the two Olsson--Laszlo situations (`totalOlssonLaszloSituation` and
   `baseOlssonLaszloSituation`).

The argument of 0D7V is run through `Stacks.Cohomology.CohomologicalDescent`
`.equivalenceOfAdjunctionUnbounded`, which needs of `Ra_*` only that it is a triangulated right
adjoint preserving boundedness below: the library's own Stacks 0D7V is stated for a morphism of
ringed topoi presented by a continuous functor of sites, which `a` is not. Its two further inputs
— that `Ra_*` of an object of `A_total` placed in degree zero is an object of `A` placed in
degree zero, and that the counit is invertible on `D⁺_{A_total}(O)` — are the bounded below
case: an object of `A_total` is `a^*N` with `N` in `A`, and `Ra_*La^*N = N`.

## Main results

* `AlgebraicGeometry.RingedToposHom.derivedPullbackCompHomologyIsoOfIsIsoFSharp`: for a morphism
  of ringed topoi with invertible structure map, `H^q(Lf^*-) = f^*H^q(-)`.
* `Stacks.CategoryTheory.Hypercovering.exists_derivedPullbackEquivalence_localSerreFamily`:
  **Stacks 0DC7**.

## Implementation notes

The derived categories are those of the `HasDerivedCategory.standard` model, in which the
derived pullback and pushforward along `a` and Stacks 0DA0 are constructed in this library.

## References

* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 0DA2](https://stacks.math.columbia.edu/tag/0DA2)
* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite Stacks.Cohomology.DerivedPushforward Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

attribute [local instance] pullbackModules_preservesFiniteLimits_of_isIso_fSharp
  pullbackModules_preservesFiniteColimits_of_adjunction

/-- **`H^q(Lf^*-) = f^*H^q(-)`, naturally**, for a morphism of ringed topoi with invertible
structure map. -/
def derivedPullbackCompHomologyIsoOfIsIsoFSharp (q : ℤ) :
    (leftDerivedPullbackOfIsIsoFSharp f).functor ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ≅
      DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q ⋙
        f.toModulesHom.pullbackModules :=
  Functor.isoWhiskerRight (derivedPullbackNatIsoOfIsIsoFSharp f) _ ≪≫
    StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      f.toModulesHom.pullbackModules q

end AlgebraicGeometry.RingedToposHom

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})
  (T : LocalSerreFamily.{u} (pretopologyRingedSite J OC))

/-- The class `A ⊂ Mod(O_C)` of the modules whose restriction to every `C/U` lies in `A_U`. -/
abbrev baseLocalSerre :
    ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) :=
  LocalSerreFamily.globalProperty (pretopologyRingedSite J OC) T

/-- `Ra_*` of an object of `A_total` placed in degree zero is an object of `A` placed in degree
zero: the object is `a^*N` with `N` in `A`, and `Ra_*La^*N = N` (Stacks 0DA0). -/
def derivedPushforwardSingleIsoOfTotalLocalSerre
    (M : SheafOfModules.{u}
      ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O))
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC))
    (e : (hypercoveringRingedAugmentation J H OC).totalRingedHom.toModulesHom.pullbackModules.obj N
      ≅ M) :
    (derivedPushforward (X := (hypercoveringSituation J H).totalRingedTopos
        (hypercoveringRingedAugmentation J H OC).O)
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
        (hypercoveringRingedAugmentation J H OC).totalRingedHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          ((hypercoveringSituation J H).totalRingSheaf
            (hypercoveringRingedAugmentation J H OC).O)) 0).obj M) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) 0).obj N :=
  (derivedPushforward (X := (hypercoveringSituation J H).totalRingedTopos
      (hypercoveringRingedAugmentation J H OC).O)
      (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso e.symm ≪≫
        (RingedToposHom.derivedPullbackSingleFunctorObjIso
          (hypercoveringRingedAugmentation J H OC).totalRingedHom N).symm) ≪≫
    (@asIso _ _ _ _ ((RingedToposHom.derivedAdjunctionOfIsIsoFSharp
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).unit.app _)
      (isIso_derivedPullbackPushforwardUnit_app_of_hypercoveringOfTerminal J H OC
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) 0).obj N))).symm

/-- **Stacks 0DC7.** Let `(C, O_C)` be a ringed site with equalizers and fibre products, and let
`A_U ⊂ Mod(O_U)` be weak Serre subcategories satisfying conditions 0DC2, 0DC3 and 0DC4 (the
fields of `T : LocalSerreFamily`), with `A ⊂ Mod(O_C)` the modules whose restriction to every
`C/U` lies in `A_U`. Let `K` be a hypercovering of `C`, let
`a : ((C/K)_total, O) ⟶ (C, O_C)` be the ringed augmentation of Remark 0D9W, with `O = a⁻¹O_C`,
and let `A_total ⊂ Mod(O)` be the cartesian `O`-modules `F` whose restriction `F_n` lies in
`A_{K_n} = ∏_i A_{U_{n,i}}` for every `n`. Then `A_total` is a weak Serre subcategory of
`Mod(O)`, and `La^*` defines an equivalence

`D_A(O_C) ⟶ D_{A_total}(O)`

with quasi-inverse `Ra_*`: there is an equivalence of the full subcategories of the unbounded
derived categories on the objects with cohomology in `A`, respectively `A_total`, whose functor
is the restriction of the derived pullback `La^*` and whose inverse is the restriction of the
derived direct image `Ra_*`. -/
@[stacks 0DC7]
theorem exists_derivedPullbackEquivalence_localSerreFamily :
    (totalLocalSerre J H OC T).IsWeakSerreClass ∧
      ∃ e : (DerivedCategoryB.derivedCategoryB (baseLocalSerre J OC T)).FullSubcategory ≌
          (DerivedCategoryB.derivedCategoryB (totalLocalSerre J H OC T)).FullSubcategory,
        e.functor ⋙ (DerivedCategoryB.derivedCategoryB (totalLocalSerre J H OC T)).ι =
            (DerivedCategoryB.derivedCategoryB (baseLocalSerre J OC T)).ι ⋙
              (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
                (hypercoveringRingedAugmentation J H OC).totalRingedHom).functor ∧
          e.inverse ⋙ (DerivedCategoryB.derivedCategoryB (baseLocalSerre J OC T)).ι =
            (DerivedCategoryB.derivedCategoryB (totalLocalSerre J H OC T)).ι ⋙
              derivedPushforward (X := (hypercoveringSituation J H).totalRingedTopos
                (hypercoveringRingedAugmentation J H OC).O)
                (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
                (hypercoveringRingedAugmentation J H OC).totalRingedHom := by
  have := LocalSerreFamily.isWeakSerreClass_globalProperty (pretopologyRingedSite J OC) T
  have := isWeakSerreClass_totalLocalSerre J H OC T
  have hsurj : ∀ M, totalLocalSerre J H OC T M →
      (hypercoveringRingedAugmentation J H
        OC).totalRingedHom.toModulesHom.pullbackModules.essImage M := fun M hM ↦ by
    obtain ⟨N, -, ⟨e⟩⟩ := exists_pullbackModules_iso_of_totalLocalSerre J H OC T M hM
    exact ⟨N, ⟨e⟩⟩
  have hex : ∀ M, totalLocalSerre J H OC T M → ∃ N, baseLocalSerre J OC T N ∧ Nonempty
      ((derivedPushforward (X := (hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          ((hypercoveringSituation J H).totalRingSheaf
            (hypercoveringRingedAugmentation J H OC).O)) 0).obj M) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) 0).obj N) := fun M hM ↦ by
    obtain ⟨N, hN, ⟨e⟩⟩ := exists_pullbackModules_iso_of_totalLocalSerre J H OC T M hM
    exact ⟨N, hN, ⟨derivedPushforwardSingleIsoOfTotalLocalSerre J H OC M N e⟩⟩
  refine ⟨inferInstance,
    equivalenceOfAdjunctionUnbounded (totalOlssonLaszloSituation J H OC T)
      (baseOlssonLaszloSituation J OC T)
      (RingedToposHom.derivedAdjunctionOfIsIsoFSharp
        (hypercoveringRingedAugmentation J H OC).totalRingedHom)
      (hRC := RingedToposHom.commShift_derivedPushforward
        (hypercoveringRingedAugmentation J H OC).totalRingedHom)
      (hRT := RingedToposHom.isTriangulated_derivedPushforward
        (hypercoveringRingedAugmentation J H OC).totalRingedHom)
      (hypercoveringRingedAugmentation J H OC).totalRingedHom.toModulesHom.pullbackModules
      (RingedToposHom.derivedPullbackCompHomologyIsoOfIsIsoFSharp
        (hypercoveringRingedAugmentation J H OC).totalRingedHom)
      (RingedToposHom.isGE_derivedPushforward_obj
        (hypercoveringRingedAugmentation J H OC).totalRingedHom)
      (totalLocalSerre_pullbackModules J H OC T) (fun M hM ↦ by
        obtain ⟨N, -, ⟨e⟩⟩ := hex M hM
        exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0)
      (fun M hM p ↦ by
        obtain ⟨N, hN, ⟨e⟩⟩ := hex M hM
        let eH := (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) (p : ℤ)).mapIso e
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · exact ObjectProperty.prop_of_iso _
            (eH ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) 0).app N).symm hN
        · exact ObjectProperty.prop_of_isZero _ ((DerivedCategory.isZero_of_isLE
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) 0).obj N) 0 (p : ℤ)
            (by omega)).of_iso eH))
      (fun K _ ↦ isIso_derivedPullbackPushforwardUnit_app_of_hypercoveringOfTerminal J H OC K)
      (fun E hE ↦ RingedToposHom.isIso_derivedCounit_app_of_property
        (hypercoveringRingedAugmentation J H OC).totalRingedHom (totalLocalSerre J H OC T)
        (isIso_derivedPullbackPushforwardUnit_app_of_hypercoveringOfTerminal J H OC) hsurj E hE),
    rfl, rfl⟩

end Stacks.CategoryTheory.Hypercovering

end
