module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification of the cohomology presheaf on a ringed site

Let `(C, O)` be a ringed site and `K` an object of the unbounded derived category `D(O)`. The
sheafification of the presheaf `U ↦ H^q(U, K)` is the `q`-th cohomology sheaf `H^q(K)` of `K`,
naturally in `K`. The presheaf is the right derived functor of the forgetful functor from
sheaves of modules to presheaves of modules, followed by `H^q`; its value at an object `U` is
derived cohomology over `U`, and also cohomology on the localized site `C/U` (Tag 0D6F).

## Main definitions

* `Stacks.Cohomology.SiteCohomologyPresheaf.homotopySectionsPresheaf`: the functor whose right
  derived functor assembles derived sections over all objects of the site.
* `Stacks.Cohomology.SiteCohomologyPresheaf.derivedSectionsPresheaf`: that right derived functor.
* `Stacks.Cohomology.SiteCohomologyPresheaf.cohomologyPresheaf`: the presheaf `U ↦ H^q(U, K)`.
* `Stacks.Cohomology.SiteCohomologyPresheaf.homotopySheafificationHomologyIso`: the underived
  comparison between sheafified homology of the underlying presheaves and homology.

## Main results

* `Stacks.Cohomology.SiteCohomologyPresheaf.cohomologyPresheafEvaluationIso` (Tag 0BKV, values
  on objects): the value of the presheaf on `U` is derived cohomology over `U`.
* `Stacks.Cohomology.SiteCohomologyPresheaf.cohomologyPresheafSliceIso` (Tag 0BKV, cohomology on
  the slice site): the same value, read on `C/U`.
* `Stacks.Cohomology.SiteCohomologyPresheaf.sheafificationCohomologyPresheafIso` (Tag 0BKV,
  associated sheaf): the sheafification of that presheaf is the cohomology sheaf of `K`,
  naturally in `K`.
* `Stacks.Cohomology.SiteCohomologyPresheaf.sheafificationCohomologyPresheafIso_comp` (Tag 0BKV,
  canonical comparison): that isomorphism is the one induced by
  `homotopySheafificationHomologyIso`.

## References

* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Homology (mapHomotopyCategoryIso homotopyHomologyIso)

namespace Stacks.Cohomology.SiteCohomologyPresheaf

universe u v w uB vB uH vH wG wD g

attribute [local instance] HasDerivedCategory.standard

section Postcomposition

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [HasDerivedCategory.{wD} A] {B : Type uB} [Category.{vB} B] {H : Type uH} [Category.{vH} H]

/-- The canonical comparison exhibiting `RF ⋙ G` as a candidate right derived functor of
`F ⋙ G`: it is the unit of `RF` whiskered with `G`. -/
def totalRightDerivedCompUnit (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ B)
    [F.HasRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : B ⥤ H) :
    F ⋙ G ⟶ DerivedCategory.Qh ⋙ (F.totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⋙ G) :=
  Functor.whiskerRight (F.totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) G ≫
    (Functor.associator DerivedCategory.Qh _ G).hom

omit [IsGrothendieckAbelian.{wG} A] in
/-- The comparison `totalRightDerivedCompUnit` is `G` applied to the unit of `RF`. -/
@[simp]
theorem totalRightDerivedCompUnit_app (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ B)
    [F.HasRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : B ⥤ H) (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (totalRightDerivedCompUnit F G).app K =
      G.map ((F.totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).app K) := by
  simp [totalRightDerivedCompUnit]

/-- Over a Grothendieck abelian category, postcomposing a total right derived functor with any
functor again gives a right derived functor. -/
theorem isRightDerivedFunctor_totalRightDerived_comp
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ B)
    [F.HasRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : B ⥤ H) :
    (F.totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⋙ G).IsRightDerivedFunctor
      (totalRightDerivedCompUnit F G) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I hI => ?_)
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective F
    (F.totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (F.totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) I
  rw [totalRightDerivedCompUnit_app]
  infer_instance

/-- Postcomposing a total right derived functor with any functor gives a right derived functor
of the composite, with comparison the unit of `RF` whiskered on the right by `G`. -/
instance isRightDerivedFunctor_totalRightDerived_whiskerRight
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ B)
    [F.HasRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : B ⥤ H) :
    (F.totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight (F.totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) G)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I hI => ?_)
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective F
    (F.totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (F.totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) I
  exact Functor.map_isIso G _

end Postcomposition


section RingedSite

/-- The functor underlying derived sections over all objects of a ringed site. -/
abbrev homotopySectionsPresheaf (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ) ⥤
      DerivedCategory (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
  letI : (SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  (SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
    (.up ℤ) ⋙
    DerivedCategory.Qh

/-- Derived sections, with all restriction maps, as a derived presheaf. -/
abbrev derivedSectionsPresheaf (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(homotopySectionsPresheaf X).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ))] :
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
  (homotopySectionsPresheaf X).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ))

/-- The presheaf `U ↦ H^q(U, K)`, including its restriction maps. -/
abbrev cohomologyPresheaf (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(homotopySectionsPresheaf X).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (q : ℤ) :
    PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
  (DerivedCategory.homologyFunctor _ q).obj ((derivedSectionsPresheaf X).obj K)

/-- Sheafification of presheaves of modules along the identity is additive. -/
instance additive_sheafification {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [HasSheafify J AddCommGrpCat.{g}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{g}] :
    (PresheafOfModules.sheafification (𝟙 R.obj) :
      PresheafOfModules.{g} R.obj ⥤ SheafOfModules.{g} R).Additive := by
  have hbig := (PresheafOfModules.sheafificationAdjunction
    (𝟙 R.obj)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (PresheafOfModules.sheafification (𝟙 R.obj) :
      PresheafOfModules.{g} R.obj ⥤ SheafOfModules.{g} R) :=
    ⟨fun _ _ _ => hbig.preservesColimitsOfShape⟩
  have : (PresheafOfModules.sheafification (𝟙 R.obj) :
      PresheafOfModules.{g} R.obj ⥤ SheafOfModules.{g} R).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have : PreservesBinaryBiproducts (PresheafOfModules.sheafification (𝟙 R.obj) :
      PresheafOfModules.{g} R.obj ⥤ SheafOfModules.{g} R) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Sheafification of presheaves of modules along the identity preserves finite colimits. -/
instance preservesFiniteColimits_sheafification {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [HasSheafify J AddCommGrpCat.{g}] [J.WEqualsLocallyBijective AddCommGrpCat.{g}] :
    PreservesFiniteColimits (PresheafOfModules.sheafification (𝟙 R.obj) :
      PresheafOfModules.{g} R.obj ⥤ SheafOfModules.{g} R) :=
  ⟨fun _ _ _ => (PresheafOfModules.sheafificationAdjunction
    (𝟙 R.obj)).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩

/-- The underived comparison: sheafifying the homology of the underlying complex of
presheaves recovers the homology sheaf of the complex. -/
def homotopySheafificationHomologyIso (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (q : ℤ) :
    (homotopySectionsPresheaf X ⋙
      DerivedCategory.homologyFunctor (PresheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q) ⋙
        PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ≅
      HomotopyCategory.homologyFunctor (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ) q := by
  let A := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let P := PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
  let c := ComplexShape.up ℤ
  let F : A ⥤ P := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let a : P ⥤ A :=
    PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  letI : F.Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  letI := additive_sheafification (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let HqP := DerivedCategory.homologyFunctor P q
  let hP := HomotopyCategory.homologyFunctor P c q
  let hA := HomotopyCategory.homologyFunctor A c q
  let Fmap := F.mapHomotopyCategory c
  let amap := a.mapHomotopyCategory c
  let eL : ((Fmap ⋙ DerivedCategory.Qh) ⋙ HqP) ⋙ a ≅
      Fmap ⋙ ((DerivedCategory.Qh ⋙ HqP) ⋙ a) :=
    Functor.isoWhiskerRight (Functor.associator Fmap DerivedCategory.Qh HqP) a ≪≫
      Functor.associator Fmap (DerivedCategory.Qh ⋙ HqP) a
  let eFactor : (DerivedCategory.Qh ⋙ HqP) ⋙ a ≅ hP ⋙ a :=
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh P q) a
  let eH : Fmap ⋙ (hP ⋙ a) ≅ Fmap ⋙ (amap ⋙ hA) :=
    Functor.isoWhiskerLeft Fmap (by simpa [amap, hP, hA, c] using homotopyHomologyIso a q)
  let eComp : Fmap ⋙ (amap ⋙ hA) ≅ (F ⋙ a).mapHomotopyCategory c ⋙ hA :=
    (Functor.associator Fmap amap hA).symm ≪≫
      (by
        simpa [Fmap, amap] using
          Functor.isoWhiskerRight
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ a)) c) hA)
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  have hCounit : IsIso adj.counit := by
    change IsIso (PresheafOfModules.sheafificationAdjunction.{w}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit
    infer_instance
  let eF : F ⋙ a ≅ 𝟭 A := @asIso _ _ _ _ adj.counit hCounit
  let eHF : (F ⋙ a).mapHomotopyCategory c ⋙ hA ≅ hA := by
    let eId : (F ⋙ a).mapHomotopyCategory c ≅ (𝟭 A).mapHomotopyCategory c :=
      mapHomotopyCategoryIso eF c
    let idIso : (𝟭 A).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory A c) := by
      refine NatIso.ofComponents (fun K => Iso.refl K) ?_
      intro K L f
      obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      obtain ⟨L₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
      obtain ⟨f₀, rfl⟩ := (HomotopyCategory.quotient A c).map_surjective f
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    exact Functor.isoWhiskerRight eId hA ≪≫
      Functor.isoWhiskerRight idIso hA ≪≫ Functor.leftUnitor hA
  have hmain : ((Fmap ⋙ DerivedCategory.Qh) ⋙ HqP) ⋙ a ≅ hA :=
    eL ≪≫ Functor.isoWhiskerLeft Fmap eFactor ≪≫ eH ≪≫ eComp ≪≫ eHF
  simpa [homotopySectionsPresheaf, Fmap, HqP, hP, hA, F, A, P, c] using hmain

end RingedSite


section AssociatedSheaf

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The homology functor on the derived category is a right derived functor of the homology
functor on the homotopy category, with unit the inverse of the canonical factorization. -/
theorem isRightDerivedFunctor_homologyFunctor (q : ℤ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).IsRightDerivedFunctor
      (DerivedCategory.homologyFunctorFactorsh (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).inv
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ)) := by
  refine (Functor.isRightDerivedFunctor_iff_of_inverts _ _
    (HomotopyCategory.homologyFunctor_inverts_quasiIso (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) q)).2 ?_
  infer_instance

variable [IsGrothendieckAbelian.{g} (SheafOfModules.{w}
  (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- Sheafifying the presheaf `U ↦ H^q(U, K)` gives the `q`-th cohomology sheaf of `K`,
naturally in the derived object `K`. -/
@[stacks 0BKV "associated sheaf"]
def sheafificationCohomologyPresheafIso (q : ℤ) :
    derivedSectionsPresheaf X ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
          PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ≅
        DerivedCategory.homologyFunctor (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q :=
  have := isRightDerivedFunctor_homologyFunctor X q
  have := isRightDerivedFunctor_totalRightDerived_comp (homotopySectionsPresheaf X)
    (DerivedCategory.homologyFunctor (PresheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
      PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
  Functor.rightDerivedNatIso _ _
    (totalRightDerivedCompUnit (homotopySectionsPresheaf X)
      (DerivedCategory.homologyFunctor (PresheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
        PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)))
    (DerivedCategory.homologyFunctorFactorsh (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).inv
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ))
    (homotopySheafificationHomologyIso X q)

/-- Characterization of the associated-sheaf isomorphism: on a complex, it agrees with the
canonical exact-sheafification comparison after the unit of the total right derived
presheaf-sections functor. -/
@[stacks 0BKV "canonical comparison"]
theorem sheafificationCohomologyPresheafIso_comp (q : ℤ)
    (I : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ)) :
    (DerivedCategory.homologyFunctor (PresheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
        PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
        (((homotopySectionsPresheaf X).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))).app I) ≫
      (sheafificationCohomologyPresheafIso X q).hom.app (DerivedCategory.Qh.obj I) =
        (homotopySheafificationHomologyIso X q).hom.app I ≫
          (DerivedCategory.homologyFunctorFactorsh
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).inv.app I := by
  have := isRightDerivedFunctor_homologyFunctor X q
  have := isRightDerivedFunctor_totalRightDerived_comp (homotopySectionsPresheaf X)
    (DerivedCategory.homologyFunctor (PresheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
      PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
  rw [← totalRightDerivedCompUnit_app (homotopySectionsPresheaf X)
    (DerivedCategory.homologyFunctor (PresheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
      PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) I]
  exact Functor.rightDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (homotopySheafificationHomologyIso X q).hom I

end AssociatedSheaf


section Evaluation

open Stacks.Cohomology.Localization

/-- Sections of a presheaf of modules over an object of the site, as abelian groups. -/
public abbrev presheafSections (X : RingedSite.{u, u, u}) (U : X.C) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⥤ AddCommGrpCat.{u} :=
  PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (Opposite.op U) ⋙
    forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj
      (Opposite.op U))) AddCommGrpCat.{u}

/-- Restriction of sections of a presheaf of modules over objects of the site, viewed as
abelian groups. -/
public def presheafSectionsRestriction (X : RingedSite.{u, u, u}) {U V : X.C} (g : U ⟶ V) :
    presheafSections X V ⟶ presheafSections X U where
  app M := M.presheaf.map g.op
  naturality _ _ h :=
    (((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map h).naturality g.op).symm

/-- Restriction of sections of a sheaf of modules, viewed as abelian groups. Its component at
a sheaf `F` is `F.val.presheaf.map g.op`. -/
public def sectionsRestriction (X : RingedSite.{u, u, u}) {U V : X.C} (g : U ⟶ V) :
    sectionsOverObject X V ⟶ sectionsOverObject X U :=
  Functor.whiskerLeft (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (presheafSectionsRestriction X g)

/-- The established restriction map on hypercohomology over objects of the site, obtained by
deriving restriction of sections. -/
public def hypercohomologyRestriction (X : RingedSite.{u, u, u}) {U V : X.C} (g : U ⟶ V)
    (q : ℤ) :
    derivedSectionsOverObject X V ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} q ⟶
      derivedSectionsOverObject X U ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} q :=
  Functor.whiskerRight
    ((derivedSectionsOverObject X V).rightDerivedNatTrans
      (derivedSectionsOverObject X U)
      ((homotopySectionsOverObject X V).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
      ((homotopySectionsOverObject X U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))
      (Functor.whiskerRight
        ((sectionsRestriction X g).mapHomotopyCategory (ComplexShape.up ℤ))
        DerivedCategory.Qh))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q)

/-- Evaluation of the hypercohomology presheaf at `U` is the established cohomology functor
`H^q(U, -)`. -/
@[stacks 0BKV "values on objects"]
public def cohomologyPresheafEvaluationIso (X : RingedSite.{u, u, u}) (U : X.C) (q : ℤ) :
    derivedSectionsPresheaf X ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
        PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
          (Opposite.op U) ⋙
        forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj
          (Opposite.op U))) AddCommGrpCat.{u} ≅
      derivedSectionsOverObject X U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} q :=
  let : (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  Functor.rightDerivedNatIso _ _
    (Functor.whiskerRight ((homotopySectionsPresheaf X).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))
      (DerivedCategory.homologyFunctor (PresheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
        presheafSections X U))
    (Functor.whiskerRight ((homotopySectionsOverObject X U).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (Stacks.Homology.derivedSourceIso (SheafOfModules.forget.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (presheafSections X U) q)

/-- The evaluation identifications commute with the restriction maps. -/
@[stacks 0BKV "restriction maps"]
public theorem cohomologyPresheafEvaluationIso_naturality (X : RingedSite.{u, u, u})
    {U V : X.C} (g : U ⟶ V)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (q : ℤ) :
    (cohomologyPresheaf X K q).presheaf.map g.op ≫
        (cohomologyPresheafEvaluationIso X U q).hom.app K =
      (cohomologyPresheafEvaluationIso X V q).hom.app K ≫
        (hypercohomologyRestriction X g q).app K := by
  let : (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have key : Functor.whiskerLeft (derivedSectionsPresheaf X ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q)
        (presheafSectionsRestriction X g) ≫ (cohomologyPresheafEvaluationIso X U q).hom =
      (cohomologyPresheafEvaluationIso X V q).hom ≫ hypercohomologyRestriction X g q := by
    refine Functor.rightDerived_ext (L := DerivedCategory.Qh)
      (RF := (derivedSectionsPresheaf X ⋙
          (DerivedCategory.homologyFunctor (PresheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
            presheafSections X V)))
      (α := Functor.whiskerRight ((homotopySectionsPresheaf X).totalRightDerivedUnit
        DerivedCategory.Qh (HomotopyCategory.quasiIso (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
        (DerivedCategory.homologyFunctor _ q ⋙ presheafSections X V))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) _ _ _ ?_
    refine NatTrans.ext (funext fun I => ?_)
    refine Stacks.Homology.comp_eq_of_squares
      ((presheafSectionsRestriction X g).naturality _)
      (Functor.rightDerivedNatTrans_app
        (derivedSectionsPresheaf X ⋙ (DerivedCategory.homologyFunctor _ q ⋙
          presheafSections X U)) _ _ _
        (HomotopyCategory.quasiIso (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
        (Stacks.Homology.derivedSourceIso (SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (presheafSections X U) q).hom I)
      (Functor.rightDerivedNatTrans_app
        (derivedSectionsPresheaf X ⋙ (DerivedCategory.homologyFunctor _ q ⋙
          presheafSections X V)) _ _ _
        (HomotopyCategory.quasiIso (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
        (Stacks.Homology.derivedSourceIso (SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (presheafSections X V) q).hom I)
      ?_
      (congr_app (Stacks.Homology.derivedSourceIso_hom_naturality
        (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q
          (presheafSectionsRestriction X g)) I)
    exact ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map_comp _ _).symm.trans
      ((congrArg _ (Functor.rightDerivedNatTrans_app _ _ _ _
        (HomotopyCategory.quasiIso (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
        (Functor.whiskerRight
          ((sectionsRestriction X g).mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh) I)).trans (Functor.map_comp _ _ _))
  exact congr_app key K

/-- The same evaluation, expressed using cohomology on the localized site `C/U`; its second
factor is the comparison of Tag 0D6F. -/
@[stacks 0BKV "cohomology on the slice site"]
public def cohomologyPresheafSliceIso (X : RingedSite.{u, u, u}) (U : X.C) (q : ℤ) :
    derivedSectionsPresheaf X ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q ⋙
        PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
          (Opposite.op U) ⋙
        forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj
          (Opposite.op U))) AddCommGrpCat.{u} ≅
      derivedRestriction X U ⋙ derivedSectionsOnSlice X U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} q :=
  cohomologyPresheafEvaluationIso X U q ≪≫ cohomologyOverObjectIsoRestriction X U q

end Evaluation


end Stacks.Cohomology.SiteCohomologyPresheaf

end
