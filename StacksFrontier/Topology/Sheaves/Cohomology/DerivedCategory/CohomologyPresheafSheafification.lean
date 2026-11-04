module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExistsKInjectiveResolution
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.Sheafify.Module
import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification of the cohomology presheaf

Let `(X, O_X)` be a ringed space and `K` an object of the unbounded derived category
`D(O_X)`. The sheafification of the presheaf `U ↦ H^q(U, K)` is the `q`-th cohomology sheaf
of `K`.

## Main definitions

* `Stacks.Cohomology.CohomologyPresheaf.derivedSectionsPresheaf`: derived sections on all
  opens at once, as a derived presheaf.
* `Stacks.Cohomology.CohomologyPresheaf.cohomologyPresheaf`: the presheaf `U ↦ H^q(U, K)`.

## Main results

* `Stacks.Cohomology.CohomologyPresheaf.cohomologyPresheafEvaluationIso`: the value of the
  presheaf on an open is derived cohomology over that open.
* `Stacks.Cohomology.CohomologyPresheaf.sheafificationCohomologyPresheafIso`: the sheafification
  of that presheaf is the cohomology sheaf of `K`, naturally in `K`.

## References

* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Homology (mapHomotopyCategoryIso exactHomologyIso homotopyHomologyIso)
open Stacks.Cohomology (sheafificationHomologyIso)
open Stacks.Cohomology.OpenSubspace (hasRightDerivedFunctor_of_moduleKInjectives)

universe wX wP wG u

namespace Stacks.Cohomology.CohomologyPresheaf

private def totalDerivedHomologyPostcompIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {C : Type*} [Category C] [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    (F : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory B)
    (E : B ⥤ C) (q : ℤ) :
    (F.totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) ⋙
        DerivedCategory.homologyFunctor B q ⋙ E) ≅
        (F ⋙ DerivedCategory.homologyFunctor B q ⋙ E).totalRightDerived
          DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) := by
  let A := SheafOfModules.{u} O
  let c := ComplexShape.up ℤ
  let W := HomotopyCategory.quasiIso A c
  let Hq := DerivedCategory.homologyFunctor B q
  let S : HomotopyCategory A c ⥤ C := F ⋙ Hq ⋙ E
  let R := F.totalRightDerived DerivedCategory.Qh W
  let T : DerivedCategory A ⥤ C := R ⋙ Hq ⋙ E
  let R0 := S.totalRightDerived DerivedCategory.Qh W
  let α0 := S.totalRightDerivedUnit DerivedCategory.Qh W
  let αF := F.totalRightDerivedUnit DerivedCategory.Qh W
  let β : S ⟶ DerivedCategory.Qh ⋙ T :=
    (Functor.associator F Hq E).hom ≫
      Functor.whiskerRight αF (Hq ⋙ E) ≫
      (Functor.associator DerivedCategory.Qh R (Hq ⋙ E)).hom
  have hpt :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      S (moduleExistsKInjectiveResolution A)
  have hptF :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      F (moduleExistsKInjectiveResolution A)
  let t := R0.rightDerivedDesc α0 W T β
  have ht (Y : DerivedCategory A) : IsIso (t.app Y) := by
    let K := DerivedCategory.Qh.objPreimage Y
    obtain ⟨K₀, hK₀⟩ := HomotopyCategory.quotient_obj_surjective K
    let I := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj K₀
    let f := (Stacks.Injectives.kInjectiveResolutionInclusion A).app K₀
    have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A c).map f)) :=
      Localization.inverts DerivedCategory.Qh W _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 (inferInstanceAs (QuasiIso f)))
    have eK : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj K₀) ≅ Y := by
      rw [hK₀]
      exact DerivedCategory.Qh.objObjPreimageIso Y
    let eY : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj I) ≅ Y :=
      (asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A c).map f))).symm ≪≫ eK
    have : IsIso (α0.app ((HomotopyCategory.quotient A c).obj I)) :=
      hpt.2 DerivedCategory.Qh R0 α0 I inferInstance
    have : IsIso (αF.app ((HomotopyCategory.quotient A c).obj I)) :=
      hptF.2 DerivedCategory.Qh R αF I inferInstance
    have hβ : IsIso (β.app ((HomotopyCategory.quotient A c).obj I)) := by
      have hmap : IsIso ((Hq ⋙ E).map (αF.app ((HomotopyCategory.quotient A c).obj I))) := by
        apply Functor.map_isIso
      dsimp [β]
      let : IsIso (𝟙 (E.obj (Hq.obj (F.obj ((HomotopyCategory.quotient A c).obj I))))) :=
        Iso.isIso_hom (Iso.refl _)
      let : IsIso (𝟙 (E.obj (Hq.obj
          (R.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj I)))))) :=
        Iso.isIso_hom (Iso.refl _)
      exact (isIso_comp_left_iff _ _).2 ((isIso_comp_right_iff _ _).2 hmap)
    have : IsIso (α0.app ((HomotopyCategory.quotient A c).obj I) ≫
        t.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj I))) := by
      rw [R0.rightDerived_fac_app α0 W T β]
      exact hβ
    have := (isIso_comp_left_iff _ _).mp this
    have hcomp : IsIso
        (t.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj I)) ≫
          T.map eY.hom) := by infer_instance
    rw [← t.naturality eY.hom] at hcomp
    exact (isIso_comp_left_iff _ _).mp hcomp
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact (asIso t).symm

/-- The homotopy-category functor whose right derived functor simultaneously computes
sections on every open subset. -/
public abbrev homotopySectionsPresheaf {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)] :
    HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (PresheafOfModules.{u} O.obj) :=
  (SheafOfModules.forget O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Derived sections on all open subsets, assembled with their restriction maps. -/
public abbrev derivedSectionsPresheaf {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)] :
    DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (PresheafOfModules.{u} O.obj) :=
  (homotopySectionsPresheaf O).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))

/-- The presheaf `U ↦ H^q(U, K)`, including its natural restriction maps. -/
public abbrev cohomologyPresheaf {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (K : DerivedCategory (SheafOfModules.{u} O)) (q : ℤ) :
    PresheafOfModules.{u} O.obj :=
  (DerivedCategory.homologyFunctor _ q).obj ((derivedSectionsPresheaf O).obj K)

private noncomputable def sourceCohomologyIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    [HasDerivedCategory.{wG} AddCommGrpCat.{u}] (q : ℤ) :
    homotopySectionsPresheaf O ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) q ⋙
        PresheafOfModules.evaluation O.obj (Opposite.op U) ⋙
          forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op U))) AddCommGrpCat.{u} ≅
      Stacks.Cohomology.OpenSubspace.homotopySectionsOnOpen O U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} q := by
  let c := ComplexShape.up ℤ
  let F := SheafOfModules.forget O
  let E := PresheafOfModules.evaluation O.obj (Opposite.op U) ⋙
    forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op U))) AddCommGrpCat.{u}
  let FE := SheafOfModules.evaluation O (Opposite.op U) ⋙
    forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op U))) AddCommGrpCat.{u}
  let Fmap := F.mapHomotopyCategory c
  let Emap := E.mapHomotopyCategory c
  let HqP := DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) q
  let HqG := DerivedCategory.homologyFunctor AddCommGrpCat.{u} q
  let hP := HomotopyCategory.homologyFunctor (PresheafOfModules.{u} O.obj) c q
  let hG := HomotopyCategory.homologyFunctor AddCommGrpCat.{u} c q
  haveI : E.Additive := inferInstance
  haveI : PreservesFiniteLimits E := by infer_instance
  haveI : PreservesFiniteColimits E := by infer_instance
  let eL : ((Fmap ⋙ DerivedCategory.Qh) ⋙ HqP) ⋙ E ≅
      Fmap ⋙ ((DerivedCategory.Qh ⋙ HqP) ⋙ E) :=
    Functor.isoWhiskerRight (Functor.associator Fmap DerivedCategory.Qh HqP) E ≪≫
      Functor.associator Fmap (DerivedCategory.Qh ⋙ HqP) E
  let eFactor : (DerivedCategory.Qh ⋙ HqP) ⋙ E ≅ hP ⋙ E :=
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh
      (PresheafOfModules.{u} O.obj) q) E
  let eH : Fmap ⋙ (hP ⋙ E) ≅ Fmap ⋙ (Emap ⋙ hG) :=
    Functor.isoWhiskerLeft Fmap (homotopyHomologyIso E q)
  let eComp : Fmap ⋙ (Emap ⋙ hG) ≅ FE.mapHomotopyCategory c ⋙ hG :=
    (Functor.associator Fmap Emap hG).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E)) c) hG ≪≫
      Functor.isoWhiskerRight
        (mapHomotopyCategoryIso
          (Functor.associator F (PresheafOfModules.evaluation O.obj (Opposite.op U))
            (forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op U))) AddCommGrpCat.{u})) c) hG
  let eHF : FE.mapHomotopyCategory c ⋙ hG ≅
      ((FE.mapHomotopyCategory c ⋙ DerivedCategory.Qh) ⋙ HqG) :=
    Functor.isoWhiskerLeft (FE.mapHomotopyCategory c)
      (DerivedCategory.homologyFunctorFactorsh AddCommGrpCat.{u} q).symm ≪≫
      (Functor.associator (FE.mapHomotopyCategory c) DerivedCategory.Qh HqG).symm
  have hmain : ((Fmap ⋙ DerivedCategory.Qh) ⋙ HqP) ⋙ E ≅
      ((FE.mapHomotopyCategory c ⋙ DerivedCategory.Qh) ⋙ HqG) :=
    eL ≪≫ Functor.isoWhiskerLeft Fmap eFactor ≪≫ eH ≪≫ eComp ≪≫ eHF
  have hmain' : (Fmap ⋙ DerivedCategory.Qh) ⋙ (HqP ⋙ E) ≅
      ((FE.mapHomotopyCategory c ⋙ DerivedCategory.Qh) ⋙ HqG) :=
    (Functor.associator (Fmap ⋙ DerivedCategory.Qh) HqP E).symm ≪≫ hmain
  simpa [homotopySectionsPresheaf, Stacks.Cohomology.OpenSubspace.homotopySectionsOnOpen,
    Stacks.Cohomology.OpenSubspace.sectionsOnOpen, FE, F, E, Fmap, HqP, HqG, hP, hG, c] using hmain'

/-- The value on `U` of the cohomology presheaf is `H^q(U, K)`. -/
@[stacks 0BKJ "values on opens", no_expose]
public def cohomologyPresheafEvaluationIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    [HasDerivedCategory.{wG} AddCommGrpCat.{u}]
    (q : ℤ) :
    derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) q ⋙
          PresheafOfModules.evaluation O.obj (Opposite.op U) ⋙
          forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op U))) AddCommGrpCat.{u} ≅
      Stacks.Cohomology.OpenSubspace.derivedSectionsOnOpen O U ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} q := by
  let A := SheafOfModules.{u} O
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let F₁ := homotopySectionsPresheaf O
  let E₁ := PresheafOfModules.evaluation O.obj (Opposite.op U) ⋙
    forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op U))) AddCommGrpCat.{u}
  let H₁ := DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) q
  let S₁ := F₁ ⋙ H₁ ⋙ E₁
  let F₂ := Stacks.Cohomology.OpenSubspace.homotopySectionsOnOpen O U
  let E₂ := 𝟭 AddCommGrpCat.{u}
  let H₂ := DerivedCategory.homologyFunctor AddCommGrpCat.{u} q
  let S₂ := F₂ ⋙ H₂ ⋙ E₂
  let : S₁.HasRightDerivedFunctor W := hasRightDerivedFunctor_of_moduleKInjectives O S₁
  let : S₂.HasRightDerivedFunctor W := hasRightDerivedFunctor_of_moduleKInjectives O S₂
  let e₁ := totalDerivedHomologyPostcompIso O F₁ E₁ q
  let e₂ := totalDerivedHomologyPostcompIso O F₂ E₂ q
  let R₁ := S₁.totalRightDerived DerivedCategory.Qh W
  let α₁ := S₁.totalRightDerivedUnit DerivedCategory.Qh W
  let R₂ := S₂.totalRightDerived DerivedCategory.Qh W
  let α₂ := S₂.totalRightDerivedUnit DerivedCategory.Qh W
  let Sopen := F₂ ⋙ H₂
  let : Sopen.HasRightDerivedFunctor W := hasRightDerivedFunctor_of_moduleKInjectives O Sopen
  let Ropen := Sopen.totalRightDerived DerivedCategory.Qh W
  let αopen := Sopen.totalRightDerivedUnit DerivedCategory.Qh W
  let eSource : S₁ ≅ S₂ :=
    sourceCohomologyIso O U q ≪≫ (Functor.rightUnitor (F₂ ⋙ H₂)).symm
  let e₁₂ := Functor.rightDerivedNatIso R₁ R₂ α₁ α₂ W eSource
  let eSourceOpen : S₂ ≅ Sopen := Functor.rightUnitor Sopen
  let e₂open := Functor.rightDerivedNatIso R₂ Ropen α₂ αopen W eSourceOpen
  exact e₁ ≪≫ e₁₂ ≪≫ e₂open ≪≫ e₂.symm

/-- Sheafifying the presheaf `U ↦ H^q(U, K)` gives the `q`-th cohomology sheaf of `K`, naturally
in the derived object `K`. -/
@[stacks 0BKJ "associated sheaf", no_expose]
public def sheafificationCohomologyPresheafIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (q : ℤ) :
    derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) q ⋙
          PresheafOfModules.sheafification (𝟙 O.obj) ≅
        DerivedCategory.homologyFunctor (SheafOfModules.{u} O) q := by
  let A := SheafOfModules.{u} O
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let F := homotopySectionsPresheaf O
  let a := PresheafOfModules.sheafification (𝟙 O.obj)
  let HqP := DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) q
  let S := F ⋙ HqP ⋙ a
  let hA := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) q
  let HqA := DerivedCategory.homologyFunctor A q
  let αA := (DerivedCategory.homologyFunctorFactorsh A q).inv
  let : S.HasRightDerivedFunctor W := hasRightDerivedFunctor_of_moduleKInjectives O S
  let : hA.HasRightDerivedFunctor W := hasRightDerivedFunctor_of_moduleKInjectives O hA
  let : HqA.IsRightDerivedFunctor αA W := by
    simpa [W] using (Functor.isRightDerivedFunctor_iff_of_inverts HqA αA
      (HomotopyCategory.homologyFunctor_inverts_quasiIso A (ComplexShape.up ℤ) q)).2
      (by infer_instance)
  let e₁ := totalDerivedHomologyPostcompIso O F a q
  let R₁ := S.totalRightDerived DerivedCategory.Qh W
  let α₁ := S.totalRightDerivedUnit DerivedCategory.Qh W
  let RA := hA.totalRightDerived DerivedCategory.Qh W
  let αhA := hA.totalRightDerivedUnit DerivedCategory.Qh W
  let eSource := sheafificationHomologyIso O q
  let e₂ := Functor.rightDerivedNatIso R₁ RA α₁ αhA W eSource
  let e₃ := Functor.rightDerivedNatIso RA HqA αhA αA W (Iso.refl hA)
  exact e₁ ≪≫ e₂ ≪≫ e₃

end Stacks.Cohomology.CohomologyPresheaf
