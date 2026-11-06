module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.Interface

/-!
# The *moreover* clause of Stacks 01EN: the functorial quasi-isomorphism

Besides the δ-functor comparison, Stacks 01EN asserts a *functorial* quasi-isomorphism
`Č•(𝒰, F) ⟶ RȞ⁰(𝒰, F)` in the bounded below derived category, and specifies it: for any
injective resolution `F ⟶ J•`, it is the composite of the two augmentations

* `α : Ȟ⁰(𝒰, J•) ⟶ Tot(Č•(𝒰, J•))`, the inclusion of degree-zero Čech cohomology into the
  degree-zero Čech cochains of each `J^q`, and
* `β : Č•(𝒰, F) ⟶ Tot(Č•(𝒰, J•))`, the Čech complex of the augmentation `F ⟶ J^0`,

into the total complex of the Čech bicomplex of `J•`, read in the derived category as
`Q(β) ≫ Q(α)⁻¹` followed by the identification of `Ȟ⁰(𝒰, J•)` with the total right derived
functor at `F`.

This file states that clause and constructs every object it names; the clause itself — the
natural isomorphism, the quasi-isomorphy of `α` and of `β`, and the characterizing equation —
is proved in `StacksDraft.Ch20.Sec13.Tag01ENMoreover`, so nothing is tagged here.

## Main definitions

* `cechComplexIntFunctor`, `cechComplexPlusFunctor`: the Čech complex of Stacks 01EJ extended
  by zero to integer degrees, and the same as a bounded below complex.
* `rightDerivedCechFunctor`: the total right derived functor `RȞ⁰(𝒰, -)` on `D⁺`.
* `cechZeroInclusion`: the inclusion of degree-zero Čech cohomology into degree-zero Čech
  cochains, the component of the augmentation `α`.
* `cechBicomplex`: the Čech bicomplex of a complex of presheaves of modules, whose `(q, p)`
  term is the Čech `p`-cochains of `J^q`.
* `injectiveResolutionIso`, `injectiveResolutionToRightDerived`: the identification of a
  presheaf with its injective resolution in `D⁺`, and the resulting map from the Čech `Ȟ⁰` of
  the resolution to the total right derived functor.
* `CechResolutionComparison`: the two prescribed augmentations, their quasi-isomorphy, and the
  equation characterizing the comparison at a given resolution.
* `CechComplexIsoRightDerived`: the *moreover* clause of Stacks 01EN, as a type.

## Where the clause is proved

`CechComplexIsoRightDerived` is inhabited in `StacksDraft.Ch20.Sec13.Tag01ENMoreover`, by
`cechComplexIsoRightDerived`, which carries the tag. That file builds the two augmentations
with their prescribed component formulas, proves each a quasi-isomorphism by [Stacks, Tag 0133]
applied in one of the two directions of the bicomplex, shows
`injectiveResolutionToRightDerived` to be an isomorphism by identifying it with the inverse of
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedComparison`, and assembles the
natural isomorphism at a resolution chosen for each presheaf.

No homotopy bookkeeping is involved in the lifting of a morphism of presheaves to the chosen
resolutions: `CategoryTheory.InjectiveResolution.desc_commutes` is an equality of morphisms of
complexes, not a homotopy, and `CategoryTheory.InjectiveResolution.desc_commutes_zero` gives
its degree-zero component directly.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01EL](https://stacks.math.columbia.edu/tag/01EL)
* [Stacks Project, Tag 01EM](https://stacks.math.columbia.edu/tag/01EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechExactFunctor (presheafCechComplexFunctor)
open Stacks.Cohomology.CechComparison

universe u

namespace Stacks.Cohomology.CechTotalComparison

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, u} (TopCat.of X))

/-- The Čech complex of Stacks 01EJ extended by zero to integer degrees. -/
def cechComplexIntFunctor :
    Modules.{u} O ⥤ CochainComplex (SectionModules.{u} O 𝒰) ℤ :=
  presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le ⋙
    embeddingUpNat.extendFunctor _

/-- The integer-indexed Čech complex functor `cechComplexIntFunctor` is additive. -/
instance cechComplexIntFunctor_additive : (cechComplexIntFunctor.{u} O 𝒰).Additive := by
  dsimp only [cechComplexIntFunctor]
  infer_instance

/-- The Čech complex as a bounded-below integer-indexed complex. -/
def cechComplexPlusFunctor :
    Modules.{u} O ⥤ CochainComplex.Plus (SectionModules.{u} O 𝒰) :=
  ObjectProperty.lift _ (cechComplexIntFunctor.{u} O 𝒰) (fun F ↦ ⟨0, by
    change CochainComplex.IsStrictlyGE
      (((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).obj F).extend
        embeddingUpNat) 0
    infer_instance⟩)

/-- The actual total right-derived functor `RȞ⁰(𝒰, -)` on the bounded-below derived
category. -/
def rightDerivedCechFunctor :
    DerivedCategory.Plus (Modules.{u} O) ⥤ DerivedCategory.Plus (SectionModules.{u} O 𝒰) :=
  (cechCohomologyZeroFunctor.{u} O 𝒰).rightDerivedFunctorPlus

/-- Degree-zero Čech cohomology embeds into the degree-zero Čech cochains. -/
def cechZeroInclusion (F : Modules.{u} O) :
    (cechCohomologyZeroFunctor.{u} O 𝒰).obj F ⟶ ((cechComplexIntFunctor.{u} O 𝒰).obj F).X 0 :=
  (CochainComplex.isoHomologyπ₀
    ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).obj F)).inv ≫
    HomologicalComplex.iCycles _ 0 ≫
    (HomologicalComplex.extendXIso _ embeddingUpNat (i := 0) rfl).inv

/-- The double complex with `(q, p)` term equal to Čech `p`-cochains of `J^q`. -/
def cechBicomplex (J : CochainComplex (Modules.{u} O) ℤ) :
    HomologicalComplex₂ (SectionModules.{u} O 𝒰) (up ℤ) (up ℤ) :=
  ((cechComplexIntFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj J

/-- An injective resolution identifies a presheaf in degree zero with its resolution. -/
def injectiveResolutionIso (F : Modules.{u} O) (J : InjectiveResolution F) :
    (DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj F ≅
      DerivedCategory.Plus.Q.obj ⟨J.cochainComplex, 0, inferInstance⟩ :=
  ObjectProperty.isoMk _ (@asIso _ _ _ _ (DerivedCategory.Q.map J.ι')
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ J.ι').2 inferInstance))

/-- The canonical identification of degree-zero Čech cohomology applied to an
injective resolution with the total right-derived functor. -/
def injectiveResolutionToRightDerived (F : Modules.{u} O) (J : InjectiveResolution F) :
    DerivedCategory.Q.obj
      (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
        J.cochainComplex) ⟶
      ((rightDerivedCechFunctor.{u} O 𝒰).obj
        ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj F)).obj :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
  ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.quotient (Modules.{u} O)).obj
      ⟨J.cochainComplex, 0, inferInstance⟩)).hom ≫
  ((rightDerivedCechFunctor.{u} O 𝒰).map
    (ObjectProperty.homMk ((DerivedCategory.quotientCompQhIso _).hom.app
      J.cochainComplex))).hom ≫
  ((rightDerivedCechFunctor.{u} O 𝒰).mapIso
    (injectiveResolutionIso.{u} O F J)).inv.hom

/-- The two prescribed quasi-isomorphisms into the total Čech complex of an
injective resolution, and the equation specifying their quotient in the derived category. -/
structure CechResolutionComparison
    (e : cechComplexPlusFunctor.{u} O 𝒰 ⋙ DerivedCategory.Plus.Q ≅
      DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0 ⋙
        rightDerivedCechFunctor.{u} O 𝒰)
    (F : Modules.{u} O) (J : InjectiveResolution F) where
  /-- The augmentation of the total complex by the degree-zero Čech cohomology of the
  resolution. -/
  α : ((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
      J.cochainComplex ⟶ (cechBicomplex.{u} O 𝒰 J.cochainComplex).total (up ℤ)
  /-- The augmentation of the total complex by the Čech complex of `F` itself. -/
  β : (cechComplexIntFunctor.{u} O 𝒰).obj F ⟶
      (cechBicomplex.{u} O 𝒰 J.cochainComplex).total (up ℤ)
  /-- `α` is the inclusion of degree-zero Čech cohomology into the degree-zero Čech cochains,
  landing in the `(q, 0)` corner. -/
  α_f (q : ℤ) : α.f q = cechZeroInclusion.{u} O 𝒰 (J.cochainComplex.X q) ≫
    (cechBicomplex.{u} O 𝒰 J.cochainComplex).ιTotal (up ℤ) q 0 q (by simp)
  /-- `β` is the Čech complex of the augmentation `F ⟶ J^0`, landing in the `(0, p)` corner. -/
  β_f (p : ℤ) : β.f p =
    ((cechComplexIntFunctor.{u} O 𝒰).map
      ((HomologicalComplex.singleObjXSelf (up ℤ) 0 F).inv ≫ J.ι'.f 0)).f p ≫
    (cechBicomplex.{u} O 𝒰 J.cochainComplex).ιTotal (up ℤ) 0 p p (by simp)
  /-- `α` is a quasi-isomorphism. -/
  [quasiIso_α : QuasiIso α]
  /-- `β` is a quasi-isomorphism. -/
  [quasiIso_β : QuasiIso β]
  /-- The comparison at `F` is `Q(β) ≫ Q(α)⁻¹` followed by the identification of the Čech `Ȟ⁰`
  of the resolution with the total right derived functor. -/
  comparison : (e.hom.app F).hom = DerivedCategory.Q.map β ≫
    inv (DerivedCategory.Q.map α) ≫ injectiveResolutionToRightDerived.{u} O 𝒰 F J

/-- **Stacks Project, Tag 01EN, moreover assertion**, as a type. A natural isomorphism from the
Čech complex functor to the total right-derived functor of degree-zero Čech cohomology which,
at every injective resolution, is the map prescribed by the two augmentations into the total
Čech complex. Inhabiting this type is the content of the clause; see the module docstring for
what inhabiting it needs. -/
def CechComplexIsoRightDerived : Type _ :=
  { e : cechComplexPlusFunctor.{u} O 𝒰 ⋙ DerivedCategory.Plus.Q ≅
      DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0 ⋙
        rightDerivedCechFunctor.{u} O 𝒰 //
    ∀ (F : Modules.{u} O) (J : InjectiveResolution F),
      Nonempty (CechResolutionComparison.{u} O 𝒰 e F J) }

end Stacks.Cohomology.CechTotalComparison

end
