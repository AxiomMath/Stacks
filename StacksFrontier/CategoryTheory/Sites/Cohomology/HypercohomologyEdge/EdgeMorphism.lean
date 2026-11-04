module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksCore.Tactic.StacksAttribute

/-! # The hypercohomology edge morphism on a ringed site

Let `(C, O)` be a ringed site, `U` an object of `C` and `K` an object of the unbounded derived
category of `O`-modules. There is a canonical comparison

`H^q(U, K) ⟶ Γ(U, H^q(K))`

from degree-`q` hypercohomology over `U` to the sections over `U` of the degree-`q` cohomology
sheaf of `K`. This file constructs it, naturally in `K`.

The construction is forced by Tag 0BKV. Derived sections are taken simultaneously over every
object of the site, as the unbounded right derived functor of the forgetful functor from sheaves
of `O`-modules to presheaves of `O`-modules; its degree-`q` cohomology is then the presheaf
`U ↦ H^q(U, K)`, and `sectionsEvaluationIso` identifies its value at `U` with the hypercohomology
module `H^q(U, K)`. Sheafifying that presheaf gives the cohomology sheaf `H^q(K)`, which is
`sheafificationCohomologyPresheafIso`. The edge morphism is therefore nothing but the unit of
sheafification, read on sections over `U`: a presheaf map `H^q(-, K) ⟶ H^q(K)` into a sheaf.
Naturality in `K` is retained throughout, since every step is an isomorphism or a unit of
functors on `D(O)`.

Both comparisons are instances of one observation, which Tag 0BKV supplies as
`Stacks.Cohomology.SiteCohomologyPresheaf.isRightDerivedFunctor_totalRightDerived_comp`:
postcomposing a total right derived functor with *any* functor again gives a total right derived
functor. Each comparison is then `CategoryTheory.Functor.rightDerivedNatIso` applied to an
underived comparison of the two homotopy-category functors, which is what makes it canonical
rather than merely existent.

## Main definitions

* `Stacks.Cohomology.HypercohomologyEdge.homotopySections`, `derivedSections`: unbounded derived
  sections over an object of the site, with values in modules over the ring of sections there.
* `Stacks.Cohomology.HypercohomologyEdge.homotopySectionsPresheaf`, `derivedSectionsPresheaf`:
  derived sections over all objects at once, with values in presheaves of modules.
* `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge`: the edge morphism.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso`: the value at `U` of the derived
  sections presheaf is derived sections over `U`.
* `Stacks.Cohomology.HypercohomologyEdge.sheafificationCohomologyPresheafIso`: sheafifying the
  degree-`q` cohomology presheaf gives the degree-`q` cohomology sheaf.
* `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge_app_eq`: the edge morphism is the
  unit of sheafification, read on sections over `U`.

## Implementation notes

The site objects, site morphisms, structure rings and modules carry independent universes, as in
`Stacks.Cohomology.moduleCohomology`, so the comparisons of Tag 0BKV -- which are stated for a
`AlgebraicGeometry.RingedSite` with the ring and module universes equal -- are rebuilt here at
independent universes from their general ingredients. `IsGrothendieckAbelian` for the sheaves of
modules is carried as a hypothesis with its own universe: it is what supplies the K-injective
resolutions, and at independent universes it is not automatic, because a separator of presheaves
of modules is a coproduct indexed by the objects of the site. It also supplies every
`CategoryTheory.Functor.HasRightDerivedFunctor` instance in sight, through
`Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck`.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.SiteCohomologyPresheaf
open Stacks.Homology (mapHomotopyCategoryIso homotopyHomologyIso)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]

omit [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] in
/-- Evaluation of sheaves of `O`-modules at an object of the site is additive. -/
lemma evaluation_additive (U : C) :
    (SheafOfModules.evaluation O (.op U) :
      SheafOfModules.{wModule} O ⥤ ModuleCat.{wModule} (O.obj.obj (.op U))).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

attribute [local instance] evaluation_additive

/-- The homotopy-category functor whose right derived functor is derived sections over `U`. -/
abbrev homotopySections (U : C) :
    HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{wModule} (O.obj.obj (.op U))) :=
  (SheafOfModules.evaluation O (.op U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The homotopy-category functor whose right derived functor is derived sections over every
object of the site at once. -/
abbrev homotopySectionsPresheaf :
    HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (PresheafOfModules.{wModule} O.obj) :=
  (SheafOfModules.forget O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The underived comparison behind `sectionsEvaluationIso`: degreewise sections over every
object of the site, read at `U`, are degreewise sections over `U`. -/
def homotopySectionsEvaluationIso (U : C) (q : ℤ) :
    homotopySectionsPresheaf O ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
        PresheafOfModules.evaluation O.obj (.op U) ≅
      homotopySections O U ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q := by
  let c := ComplexShape.up ℤ
  let F := SheafOfModules.forget O
  let E := PresheafOfModules.evaluation O.obj (.op U)
  let Fmap := F.mapHomotopyCategory c
  let Emap := E.mapHomotopyCategory c
  let HqP := DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q
  let HqM := DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q
  let hP := HomotopyCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) c q
  let hM := HomotopyCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) c q
  let eL : ((Fmap ⋙ DerivedCategory.Qh) ⋙ HqP) ⋙ E ≅
      Fmap ⋙ ((DerivedCategory.Qh ⋙ HqP) ⋙ E) :=
    Functor.isoWhiskerRight (Functor.associator Fmap DerivedCategory.Qh HqP) E ≪≫
      Functor.associator Fmap (DerivedCategory.Qh ⋙ HqP) E
  let eFactor : (DerivedCategory.Qh ⋙ HqP) ⋙ E ≅ hP ⋙ E :=
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh
      (PresheafOfModules.{wModule} O.obj) q) E
  let eH : Fmap ⋙ (hP ⋙ E) ≅ Fmap ⋙ (Emap ⋙ hM) :=
    Functor.isoWhiskerLeft Fmap (homotopyHomologyIso E q)
  let eComp : Fmap ⋙ (Emap ⋙ hM) ≅ (F ⋙ E).mapHomotopyCategory c ⋙ hM :=
    (Functor.associator Fmap Emap hM).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E)) c) hM
  let eHF : (F ⋙ E).mapHomotopyCategory c ⋙ hM ≅
      ((F ⋙ E).mapHomotopyCategory c ⋙ DerivedCategory.Qh) ⋙ HqM :=
    Functor.isoWhiskerLeft ((F ⋙ E).mapHomotopyCategory c)
      (DerivedCategory.homologyFunctorFactorsh
        (ModuleCat.{wModule} (O.obj.obj (.op U))) q).symm ≪≫
      (Functor.associator ((F ⋙ E).mapHomotopyCategory c) DerivedCategory.Qh HqM).symm
  exact (Functor.associator (Fmap ⋙ DerivedCategory.Qh) HqP E).symm ≪≫ eL ≪≫
    Functor.isoWhiskerLeft Fmap eFactor ≪≫ eH ≪≫ eComp ≪≫ eHF

/-- Sheafification of presheaves of `O`-modules along the identity preserves finite colimits. -/
private theorem sheafification_preservesFiniteColimits_aux :
    PreservesFiniteColimits (PresheafOfModules.sheafification (𝟙 O.obj) :
      PresheafOfModules.{wModule} O.obj ⥤ SheafOfModules.{wModule} O) :=
  ⟨fun _ _ _ => (PresheafOfModules.sheafificationAdjunction
    (𝟙 O.obj)).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩

/-- Sheafification of presheaves of `O`-modules along the identity is additive, at independent
ring and module universes. -/
lemma sheafification_additive :
    (PresheafOfModules.sheafification (𝟙 O.obj) :
      PresheafOfModules.{wModule} O.obj ⥤ SheafOfModules.{wModule} O).Additive := by
  let a : PresheafOfModules.{wModule} O.obj ⥤ SheafOfModules.{wModule} O :=
    PresheafOfModules.sheafification (𝟙 O.obj)
  have : PreservesFiniteColimits a := sheafification_preservesFiniteColimits_aux O
  have : a.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have : PreservesBinaryBiproducts a := preservesBinaryBiproducts_of_preservesBinaryCoproducts a
  exact Functor.additive_of_preservesBinaryBiproducts a

/-- Sheafification of presheaves of `O`-modules along the identity preserves finite colimits, at
independent ring and module universes. -/
lemma sheafification_preservesFiniteColimits :
    PreservesFiniteColimits (PresheafOfModules.sheafification (𝟙 O.obj) :
      PresheafOfModules.{wModule} O.obj ⥤ SheafOfModules.{wModule} O) :=
  sheafification_preservesFiniteColimits_aux O

attribute [local instance] sheafification_additive sheafification_preservesFiniteColimits

/-- The underived comparison behind `sheafificationCohomologyPresheafIso`: sheafifying the
degree-`q` homology of the underlying complex of presheaves recovers the degree-`q` homology
sheaf. It is built from exactness of sheafification and invertibility of its counit on
sheaves. -/
def homotopySheafificationHomologyIso (q : ℤ) :
    (homotopySectionsPresheaf O ⋙
      DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q) ⋙
        PresheafOfModules.sheafification (𝟙 O.obj) ≅
      HomotopyCategory.homologyFunctor (SheafOfModules.{wModule} O) (ComplexShape.up ℤ) q := by
  let A := SheafOfModules.{wModule} O
  let P := PresheafOfModules.{wModule} O.obj
  let c := ComplexShape.up ℤ
  let F := SheafOfModules.forget O
  let a : P ⥤ A := PresheafOfModules.sheafification (𝟙 O.obj)
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
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  have hCounit : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  let eF : F ⋙ a ≅ 𝟭 A := @asIso _ _ _ _ adj.counit hCounit
  let eHF : (F ⋙ a).mapHomotopyCategory c ⋙ hA ≅ hA := by
    let idIso : (𝟭 A).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory A c) := by
      refine NatIso.ofComponents Iso.refl fun {K L} f => ?_
      obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      obtain ⟨L₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
      obtain ⟨f₀, rfl⟩ := (HomotopyCategory.quotient A c).map_surjective f
      rw [Functor.mapHomotopyCategory_map,
        show ((𝟭 A).mapHomologicalComplex c).map f₀ = f₀ by ext; rfl]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    exact Functor.isoWhiskerRight (mapHomotopyCategoryIso eF c) hA ≪≫
      Functor.isoWhiskerRight idIso hA ≪≫ Functor.leftUnitor hA
  exact eL ≪≫ Functor.isoWhiskerLeft Fmap eFactor ≪≫ eH ≪≫ eComp ≪≫ eHF

variable [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

/-- Unbounded derived sections over an object of a ringed site. -/
abbrev derivedSections (U : C) :
    DerivedCategory (SheafOfModules.{wModule} O) ⥤
      DerivedCategory (ModuleCat.{wModule} (O.obj.obj (.op U))) :=
  (homotopySections O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))

/-- Unbounded derived sections over all objects of a ringed site at once: the right derived
functor of the forgetful functor to presheaves of modules. Its degree-`q` cohomology is the
presheaf `U ↦ H^q(U, K)`, with all its restriction maps. -/
abbrev derivedSectionsPresheaf :
    DerivedCategory (SheafOfModules.{wModule} O) ⥤
      DerivedCategory (PresheafOfModules.{wModule} O.obj) :=
  (homotopySectionsPresheaf O).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))

omit [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)] in
/-- The homology functor on the derived category is a right derived functor of the homology
functor on the homotopy category, with unit the inverse of the canonical factorization. -/
lemma isRightDerivedFunctor_homologyFunctor (q : ℤ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).IsRightDerivedFunctor
      (DerivedCategory.homologyFunctorFactorsh (SheafOfModules.{wModule} O) q).inv
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) :=
  (Functor.isRightDerivedFunctor_iff_of_inverts _ _
    (HomotopyCategory.homologyFunctor_inverts_quasiIso (SheafOfModules.{wModule} O)
      (ComplexShape.up ℤ) q)).2 inferInstance

/-- Evaluating the degree-`q` cohomology presheaf of `K` at `U` gives the hypercohomology module
`H^q(U, K)`, naturally in `K`. -/
def sectionsEvaluationIso (U : C) (q : ℤ) :
    derivedSectionsPresheaf O ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
        PresheafOfModules.evaluation O.obj (.op U) ≅
      derivedSections O U ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q :=
  have := isRightDerivedFunctor_totalRightDerived_comp (homotopySectionsPresheaf O)
    (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
      PresheafOfModules.evaluation O.obj (.op U))
  have := isRightDerivedFunctor_totalRightDerived_comp (homotopySections O U)
    (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q)
  Functor.rightDerivedNatIso _ _
    (totalRightDerivedCompUnit (homotopySectionsPresheaf O) _)
    (totalRightDerivedCompUnit (homotopySections O U) _)
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))
    (homotopySectionsEvaluationIso O U q)

/-- Sheafifying the degree-`q` cohomology presheaf of `K` gives the degree-`q` cohomology sheaf of
`K`, naturally in `K`. -/
def sheafificationCohomologyPresheafIso (q : ℤ) :
    derivedSectionsPresheaf O ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
        PresheafOfModules.sheafification (𝟙 O.obj) ≅
      DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q :=
  have := isRightDerivedFunctor_homologyFunctor O q
  have := isRightDerivedFunctor_totalRightDerived_comp (homotopySectionsPresheaf O)
    (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
      PresheafOfModules.sheafification (𝟙 O.obj))
  Functor.rightDerivedNatIso _ _
    (totalRightDerivedCompUnit (homotopySectionsPresheaf O) _)
    (DerivedCategory.homologyFunctorFactorsh (SheafOfModules.{wModule} O) q).inv
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))
    (homotopySheafificationHomologyIso O q)

/-- The unit of sheafification on the degree-`q` cohomology presheaf of `K`, read on sections
over `U`. This is the sole substantive factor of `hypercohomologyEdge`. -/
def cohomologyPresheafUnit (U : C) (q : ℤ) :
    derivedSectionsPresheaf O ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
        PresheafOfModules.evaluation O.obj (.op U) ⟶
      (derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
          PresheafOfModules.sheafification (𝟙 O.obj)) ⋙
        SheafOfModules.evaluation O (.op U) :=
  Functor.whiskerLeft (derivedSectionsPresheaf O ⋙
      DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
    (Functor.whiskerRight (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit
      (PresheafOfModules.evaluation O.obj (.op U)))

/-- The unit factor of the edge morphism, at a derived object, is the sheafification unit on the
degree-`q` cohomology presheaf taken on sections over `U`. -/
lemma cohomologyPresheafUnit_app (U : C) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (cohomologyPresheafUnit O U q).app K =
      (PresheafOfModules.evaluation O.obj (.op U)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit.app
          ((DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj
            ((derivedSectionsPresheaf O).obj K))) :=
  rfl

/-- The natural hypercohomology edge morphism `H^q(U, K) ⟶ Γ(U, H^q(K))`.

It is the unit of sheafification on the degree-`q` cohomology presheaf of `K`, read on sections
over `U`: `sectionsEvaluationIso` identifies the source with hypercohomology and
`sheafificationCohomologyPresheafIso` identifies the target with sections of the cohomology
sheaf. -/
def hypercohomologyEdge (U : C) (q : ℤ) :
    derivedSections O U ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q ⟶
      DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q ⋙
        SheafOfModules.evaluation O (.op U) :=
  (sectionsEvaluationIso O U q).inv ≫ cohomologyPresheafUnit O U q ≫
    Functor.whiskerRight (sheafificationCohomologyPresheafIso O q).hom
      (SheafOfModules.evaluation O (.op U))

/-- The three-factor description of the edge morphism at a derived object. -/
lemma hypercohomologyEdge_app (U : C) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (hypercohomologyEdge O U q).app K =
      (sectionsEvaluationIso O U q).inv.app K ≫ (cohomologyPresheafUnit O U q).app K ≫
        (SheafOfModules.evaluation O (.op U)).map
          ((sheafificationCohomologyPresheafIso O q).hom.app K) :=
  rfl

/-- The edge morphism at `K` is invertible exactly when the unit of sheafification is invertible
on the sections over `U` of the degree-`q` cohomology presheaf of `K`. The other two factors of
`hypercohomologyEdge` are isomorphisms, so this is the whole content of Tag 0BKZ. -/
lemma isIso_hypercohomologyEdge_app_iff (U : C) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    IsIso ((hypercohomologyEdge O U q).app K) ↔
      IsIso ((cohomologyPresheafUnit O U q).app K) := by
  rw [hypercohomologyEdge_app, isIso_comp_left_iff, isIso_comp_right_iff]

end Stacks.Cohomology.HypercohomologyEdge

end
