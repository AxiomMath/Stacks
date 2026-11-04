module

public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparison
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedSystem
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectNaturality
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulSectionsNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySectionsRestriction

/-!
# Further results on `KoszulCohomologyComparison`

Results about the objects of `StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparison`
that need imports beyond those of that module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace
open Stacks.SheafOfModules (StructureSheafModules ringedSite derivedRestrict
  sliceToSubspaceFunctor derivedRestrictToSubspaceIso derivedSheafHomSectionsEquiv)

universe u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

/-- **Taking preimages under a fully faithful functor is compatible with postcomposition.**  The
preimage of `w ≫ F g` is the preimage of `w` followed by `g`. -/
public lemma preimage_comp_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Full]
    [F.Faithful] {X Y Z : C} (w : F.obj X ⟶ F.obj Y) (g : Y ⟶ Z) :
    F.preimage (w ≫ F.map g) = F.preimage w ≫ g := by
  apply F.map_injective
  rw [F.map_preimage, F.map_comp, F.map_preimage]

/-- **The four-step chain of `Koszul.DerivedSystem.sectionsEquiv` is natural in the coefficient
object.**  Stated for abstract data, so that the concrete naturality statement needs only the
naturality of the Stacks 08DK identification: `ri` compares two models of restriction to `U`,
`S` compares the two models of `𝒪_U`-modules, `sd` is `H⁰(U, -)`, `T` is
`H⁰(U, RSheafHom(𝒪_X, -))` with `θ` the identification of `RSheafHom(𝒪_X, -)` with the identity
read on it, and `dk` with its inverse `dkinv` is Stacks 08DK out of `X = 𝒪_X`.

The identification is passed as a pair of mutually inverse families of plain functions rather
than as a family of additive equivalences, and the identity functor is eliminated in favour of
the family `θ`: every instance and every functor the elaborator would otherwise have to compare
across the two spellings of the structure sheaf costs elaboration budget, and the concrete
instance of this lemma has none to spare. -/
private lemma chain_naturality {C : Type*} [Category C] {Dsl : Type*} [Category Dsl]
    {Dsp : Type*} [Category Dsp] (V : C ⥤ Dsl) (Rst : C ⥤ Dsp) (S : Dsl ⥤ Dsp) [S.Full]
    [S.Faithful] (ri : V ⋙ S ≅ Rst) (sd T : C ⥤ AddCommGrpCat.{u})
    (θ : ∀ M : C, T.obj M ⟶ sd.obj M)
    (θn : ∀ (M M' : C) (g : M ⟶ M'), T.map g ≫ θ M' = θ M ≫ sd.map g) (X : C)
    (dk : ∀ M : C, ↥(T.obj M) → (V.obj X ⟶ V.obj M))
    (dkinv : ∀ M : C, (V.obj X ⟶ V.obj M) → ↥(T.obj M))
    (hleft : ∀ (M : C) (x : ↥(T.obj M)), dkinv M (dk M x) = x)
    (hright : ∀ (M : C) (y : V.obj X ⟶ V.obj M), dk M (dkinv M y) = y)
    (dkn : ∀ (M M' : C) (g : M ⟶ M') (ξ : ↥(T.obj M)),
      dk M' ((T.map g) ξ) = dk M ξ ≫ V.map g)
    {E E' : C} (g : E ⟶ E') (v : Rst.obj X ⟶ Rst.obj E) :
    (θ E') (dkinv E' (S.preimage
          ((ri.app X).hom ≫ (v ≫ Rst.map g) ≫ (ri.app E').inv))) =
      (sd.map g) ((θ E) (dkinv E (S.preimage ((ri.app X).hom ≫ v ≫ (ri.app E).inv)))) := by
  have hinv : Rst.map g ≫ (ri.app E').inv = (ri.app E).inv ≫ S.map (V.map g) :=
    ri.inv.naturality g
  have h1 : (ri.app X).hom ≫ (v ≫ Rst.map g) ≫ (ri.app E').inv =
      ((ri.app X).hom ≫ v ≫ (ri.app E).inv) ≫ S.map (V.map g) := by
    simp only [Category.assoc]
    rw [hinv]
  have hinj : ∀ (M : C) (a b : ↥(T.obj M)), dk M a = dk M b → a = b := by
    intro M a b hab
    rw [← hleft M a, ← hleft M b, hab]
  have h3 : dkinv E' (S.preimage ((ri.app X).hom ≫ v ≫ (ri.app E).inv) ≫ V.map g) =
      (T.map g) (dkinv E (S.preimage ((ri.app X).hom ≫ v ≫ (ri.app E).inv))) := by
    refine hinj E' _ _ ?_
    rw [hright, dkn, hright]
  have h4 : ∀ ξ : ↥(T.obj E), (θ E') ((T.map g) ξ) = (sd.map g) ((θ E) ξ) := fun ξ => by
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (θn E E' g) ξ
  rw [h1, preimage_comp_map, h3]
  exact h4 _

section Sections

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

attribute [local instance] hasMapBifunctorSheafTensor

attribute [local instance] preservesFiniteLimitsOver

attribute [local instance] preservesFiniteColimitsOver

attribute [local instance] Stacks.SheafOfModules.preservesFiniteLimitsOverRingedSite

attribute [local instance] Stacks.SheafOfModules.preservesFiniteColimitsOverRingedSite

/-- The four steps of `Koszul.DerivedSystem.sectionsEquiv`, spelled out: transport along the
components of `Stacks.SheafOfModules.derivedRestrictToSubspaceIso`, take the preimage under the
comparison of the two models of `𝒪_U`-modules, invert Stacks 08DK, and identify
`RSheafHom(𝒪_X, E)` with `E`. -/
public lemma sectionsEquiv_apply (E : DerivedCategory (StructureSheafModules Rc))
    (v : (derivedRestriction (structureSheaf Rc) U).obj
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) ⟶
        (derivedRestriction (structureSheaf Rc) U).obj E) :
    sectionsEquiv Rc U E v =
      ((sectionsDegreeZero Rc U).map
          ((RingedSite.derivedStructureSheafHomNatIso (ringedSite Rc)).app E).hom)
        ((derivedSheafHomSectionsEquiv Rc U
              (RingedSite.derivedStructureSheaf (ringedSite Rc)) E).symm
          ((sliceToSubspaceFunctor Rc U).mapDerivedCategory.preimage
            (((derivedRestrictToSubspaceIso Rc U).app
                  (RingedSite.derivedStructureSheaf (ringedSite Rc))).hom ≫ v ≫
              ((derivedRestrictToSubspaceIso Rc U).app E).inv))) :=
  rfl

/-- The identification of `RSheafHom(𝒪_X, -)` with the identity is natural in `E`, read on
degree-zero hypercohomology over `U`. -/
private lemma structureSheafHomNatIso_sections_naturality
    {M M' : DerivedCategory (StructureSheafModules Rc)} (w : M ⟶ M') :
    ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
          (op (RingedSite.derivedStructureSheaf (ringedSite Rc))) ⋙
        sectionsDegreeZero Rc U).map w ≫
      (sectionsDegreeZero Rc U).map
        ((RingedSite.derivedStructureSheafHomNatIso (ringedSite Rc)).app M').hom =
    (sectionsDegreeZero Rc U).map
        ((RingedSite.derivedStructureSheafHomNatIso (ringedSite Rc)).app M).hom ≫
      (sectionsDegreeZero Rc U).map w := by
  have h : ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
        (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).map w ≫
      ((RingedSite.derivedStructureSheafHomNatIso (ringedSite Rc)).app M').hom =
      ((RingedSite.derivedStructureSheafHomNatIso (ringedSite Rc)).app M).hom ≫ w :=
    (RingedSite.derivedStructureSheafHomNatIso (ringedSite Rc)).hom.naturality w
  exact ((sectionsDegreeZero Rc U).map_comp _ _).symm.trans
    ((congrArg (sectionsDegreeZero Rc U).map h).trans ((sectionsDegreeZero Rc U).map_comp _ _))

/-- Stacks 08DK out of the structure sheaf is natural in the coefficient object: the
specialisation of `Stacks.SheafOfModules.derivedSheafHomSectionsEquiv_naturality` to the
identity in the contravariant variable. -/
private lemma derivedSheafHomSectionsEquivFromUnit_naturality
    {M M' : DerivedCategory (StructureSheafModules Rc)} (w : M ⟶ M')
    (ξ : ↥((sectionsDegreeZero Rc U).obj
      (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
        (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M))) :
    derivedSheafHomSectionsEquiv Rc U
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) M'
      (((sectionsDegreeZero Rc U).map
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
          (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).map w)) ξ) =
      derivedSheafHomSectionsEquiv Rc U
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) M ξ ≫
        (derivedRestrict Rc U).map w :=
  RingedSite.derivedSheafHomSectionsEquiv_naturality_target (ringedSite Rc) U w ξ

end Sections

variable {A : CommRingCat.{u}} {r : ℕ}

end Koszul.DerivedSystem

end
