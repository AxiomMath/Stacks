module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfASquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DerivedCanonicalMapAndTriangle
public import StacksFrontier.CategoryTheory.Sites.Modules.CoarserTopology

/-!
# A sheaf whose direct image lies in the essential image of `Rε_*` is `ε_*`-acyclic

Let `C` carry two Grothendieck topologies `J' ≤ J`, let `R` be a sheaf of rings for `J`, and let
`ε : (C_J, R) ⟶ (C_{J'}, R)` be the comparison of the two topologies, with direct image `ε_*` on
sheaves of modules and inverse image `ε^*`, the `J`-sheafification. Stacks, Cohomology on Sites,
Section 0EWK, records that `ε^* ∘ Rε_* = id` on `D(R_J)`. This file proves that objectwise for
an arbitrary right derived functor `Rε_*` of `ε_*` and an arbitrary model of the two derived
categories, and reads off the consequence used in the proof of Stacks 0EWU: if a sheaf of
modules `M` for `J` has `ε_* M`, placed in degree zero, in the essential image of `Rε_*`, then
`Rε_*(M[0]) ≅ (ε_* M)[0]`, so that the higher direct images `R^n ε_* M` vanish for `n > 0`.

## Main results

* `Stacks.Sites.CoarserTopology.qObjModulePushforwardIso`: the direct image of a K-injective
  complex represents the derived direct image of the object it represents.
* `Stacks.Sites.CoarserTopology.nonempty_modulePullback_mapDerivedCategory_obj_iso`:
  `ε^* Rε_* K ≅ K` for every object `K` of `D(R_J)`.
* `Stacks.Sites.CoarserTopology.nonempty_iso_singleFunctor_of_essImage`: if `(ε_* M)[0]` is in
  the essential image of `Rε_*`, then `Rε_*(M[0]) ≅ (ε_* M)[0]`.
* `Stacks.Sites.CoarserTopology.isZero_rightDerived_modulePushforward_of_essImage`: under the
  same hypothesis, `R^n ε_* M = 0` for every `n > 0`.

## Implementation notes

`ε^* ∘ Rε_* = id` is proved on a K-injective representative `I` of `K`: `Rε_* K` is represented
by `ε_* I`, which is K-injective as well, and `ε^*` is exact, so `ε^* Rε_* K` is represented by
`ε^* ε_* I`, which is `I` because the counit of `ε^* ⊣ ε_*` is invertible, `ε_*` being fully
faithful. The isomorphism is constructed objectwise; no naturality is recorded.

The derived categories are arbitrary models, `[HasDerivedCategory _]`; nothing here forces the
standard one.

## References

* [Stacks Project, Section 0EWK](https://stacks.math.columbia.edu/tag/0EWK)
* [Stacks Project, Tag 0EWU](https://stacks.math.columbia.edu/tag/0EWU)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w r

namespace Stacks.Sites.CoarserTopology

variable {C : Type u} [Category.{w} C] {J J' : GrothendieckTopology C} (h : J' ≤ J)
  (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

variable [HasDerivedCategory (SheafOfModules.{v} R)]
  [HasDerivedCategory (SheafOfModules.{v} (ringSheafOfLe h R))]
  (Rε : DerivedCategory (SheafOfModules.{v} R) ⥤
    DerivedCategory (SheafOfModules.{v} (ringSheafOfLe h R)))
  (η : (modulePushforward.{u, v, w, r} h R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
  [Rε.IsRightDerivedFunctor η
    (HomotopyCategory.quasiIso (SheafOfModules.{v} R) (ComplexShape.up ℤ))]

/-- **The direct image of a K-injective complex computes `Rε_*`.** For a K-injective complex `I`
of sheaves of modules for `J`, the complex `ε_* I` represents `Rε_*` of the object represented by
`I`: the unit of a right derived functor is invertible at a K-injective complex (Stacks 070K). -/
def qObjModulePushforwardIso (I : CochainComplex (SheafOfModules.{v} R) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj
        (((modulePushforward.{u, v, w, r} h R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      Rε.obj (DerivedCategory.Q.obj I) :=
  have _hη : IsIso (η.app ((HomotopyCategory.quotient (SheafOfModules.{v} R)
      (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.MayerVietoris.isIso_unit_app_of_isKInjective _
      (Stacks.MayerVietoris.CanonicalMapOfComplexes.exists_kInjectiveResolution.{u, v} (R := R))
      DerivedCategory.Qh Rε η I
  (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{v} (ringSheafOfLe h R))).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso
      (((modulePushforward.{u, v, w, r} h R).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app I).symm ≪≫
    asIso (η.app _) ≪≫
    Rε.mapIso ((DerivedCategory.quotientCompQhIso (SheafOfModules.{v} R)).app I)

/-- `ε^* ε_*` is the identity on complexes, the counit of `ε^* ⊣ ε_*` being invertible. -/
def modulePullbackMapModulePushforwardIso (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    ((modulePullback.{u, v, w, r} h R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePushforward.{u, v, w, r} h R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅ I :=
  (Functor.mapHomologicalComplexCompIso
      (asIso (modulePullbackAdjPushforward.{u, v, w, r} h R).counit)
      (ComplexShape.up ℤ)).app I ≪≫
    (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app I

include η in
/-- **`ε^* Rε_* K ≅ K`** for every object `K` of the derived category of sheaves of modules for
`J`, which is the objectwise form of `ε^* ∘ Rε_* = id` (Stacks, Section 0EWK, (6)). -/
theorem nonempty_modulePullback_mapDerivedCategory_obj_iso
    (K : DerivedCategory (SheafOfModules.{v} R)) :
    Nonempty ((modulePullback.{u, v, w, r} h R).mapDerivedCategory.obj (Rε.obj K) ≅ K) := by
  obtain ⟨I, f, hI, hf⟩ :=
    Stacks.MayerVietoris.CanonicalMapOfComplexes.exists_kInjectiveResolution.{u, v}
      (R := R) (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map f) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hf
  let eK : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
  exact ⟨(modulePullback.{u, v, w, r} h R).mapDerivedCategory.mapIso
      (Rε.mapIso eK.symm ≪≫ (qObjModulePushforwardIso h R Rε η I).symm) ≪≫
    (modulePullback.{u, v, w, r} h R).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (modulePullbackMapModulePushforwardIso h R I) ≪≫ eK⟩

include η in
/-- **If `(ε_* M)[0]` is in the essential image of `Rε_*`, then `Rε_*(M[0]) ≅ (ε_* M)[0]`.**
Writing `(ε_* M)[0] ≅ Rε_* K`, applying `ε^*` gives `K ≅ ε^* Rε_* K ≅ (ε^* ε_* M)[0] ≅ M[0]`. -/
theorem nonempty_iso_singleFunctor_of_essImage (M : SheafOfModules.{v} R)
    (hM : Rε.essImage ((DerivedCategory.singleFunctor _ 0).obj
      ((modulePushforward.{u, v, w, r} h R).obj M))) :
    Nonempty (Rε.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward.{u, v, w, r} h R).obj M)) := by
  obtain ⟨K, ⟨e⟩⟩ := hM
  obtain ⟨c⟩ := nonempty_modulePullback_mapDerivedCategory_obj_iso h R Rε η K
  let d : (modulePullback.{u, v, w, r} h R).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj ((modulePushforward.{u, v, w, r} h R).obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj M :=
    ((modulePullback.{u, v, w, r} h R).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (asIso ((modulePullbackAdjPushforward.{u, v, w, r} h R).counit.app M))
  let eK : K ≅ (DerivedCategory.singleFunctor _ 0).obj M :=
    c.symm ≪≫ (modulePullback.{u, v, w, r} h R).mapDerivedCategory.mapIso e ≪≫ d
  exact ⟨Rε.mapIso eK.symm ≪≫ e⟩

include η in
/-- **A sheaf of modules whose direct image lies in the essential image of `Rε_*` is
`ε_*`-acyclic.** If `(ε_* M)[0]` is in the essential image of `Rε_*`, then `R^n ε_* M = 0` for
every `n > 0`: `R^n ε_* M` is `H^n(Rε_*(M[0]))`, and `Rε_*(M[0]) ≅ (ε_* M)[0]`. -/
theorem isZero_rightDerived_modulePushforward_of_essImage
    [EnoughInjectives (SheafOfModules.{v} R)] (M : SheafOfModules.{v} R)
    (hM : Rε.essImage ((DerivedCategory.singleFunctor _ 0).obj
      ((modulePushforward.{u, v, w, r} h R).obj M)))
    (n : ℕ) (hn : 0 < n) :
    IsZero (((modulePushforward.{u, v, w, r} h R).rightDerived n).obj M) := by
  obtain ⟨e⟩ := nonempty_iso_singleFunctor_of_essImage h R Rε η M hM
  refine IsZero.of_iso ?_ ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (modulePushforward.{u, v, w, r} h R) Rε η
    (Stacks.MayerVietoris.CanonicalMapOfComplexes.exists_kInjectiveResolution.{u, v} (R := R))
      n).app M).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso e)
  exact DerivedCategory.isZero_of_isLE _ 0 _ (by omega)

end Stacks.Sites.CoarserTopology
