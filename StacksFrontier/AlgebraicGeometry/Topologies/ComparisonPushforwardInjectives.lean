module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfLe
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Reading a sheaf of modules for a coarser topology preserves injectives

Let `K ≤ J` be Grothendieck topologies on a category `C` and `R` a sheaf of rings for `J`.
Reading a `J`-sheaf of `R`-modules as a `K`-sheaf,
`Stacks.SheafOfModules.comparisonPushforward`, is the direct image of the morphism of ringed
sites `(C, J) ⟶ (C, K)` given by the identity functor. Its left adjoint is `J`-sheafification
of the underlying presheaf of modules, which is exact. Hence the direct image preserves
injective objects and finite limits, which is what makes it usable as the inner functor of a
composite of derived functors.

## Main results

* `Stacks.SheafOfModules.comparisonPullbackIso`: the left adjoint is the `J`-sheafification of
  the underlying presheaf of modules.
* `Stacks.SheafOfModules.preservesFiniteLimits_comparisonPullback`: the left adjoint is left
  exact.
* `Stacks.SheafOfModules.preservesInjectiveObjects_comparisonPushforward`: the direct image
  preserves injective objects.
* `Stacks.SheafOfModules.preservesFiniteLimits_comparisonPushforward`: the direct image is left
  exact.
* `Stacks.SheafOfModules.comparisonPushforwardCompPullbackIso` and
  `Stacks.SheafOfModules.preservesHomology_comparisonPullback`: sheafification for the finer
  topology is exact and undoes the direct image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : K ≤ J)
  (R : Sheaf J RingCat.{w})

/-- Global sections do not see the topology: the global sections of a `J`-sheaf of modules are
those of the same module read as a `K`-sheaf. -/
def globalSectionsIsoComparisonPushforward :
    Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u, v, w, m} R ≅
      comparisonPushforward.{u, v, w, m} h R ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u, v, w, m} (ringOfLe h R) :=
  Iso.refl _

/-- Sections over an object do not see the topology. -/
def evaluationIsoComparisonPushforward (X : Cᵒᵖ) :
    _root_.SheafOfModules.evaluation.{m} R X ≅
      comparisonPushforward.{u, v, w, m} h R ⋙
        _root_.SheafOfModules.evaluation.{m} (ringOfLe h R) X :=
  Iso.refl _

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The left adjoint of reading a `J`-sheaf of modules as a `K`-sheaf is the `J`-sheafification
of the underlying presheaf of modules. -/
def comparisonPullbackIso :
    comparisonPullback.{u, v, w, m} h R ≅
      _root_.SheafOfModules.forget.{m} (ringOfLe h R) ⋙
        PresheafOfModules.sheafification.{m} (𝟙 R.obj) := by
  letI := isContinuous_id_of_le h
  letI : (PresheafOfModules.pushforward.{m}
      (F := Functor.id C) (𝟙 R.obj)).IsRightAdjoint := inferInstance
  exact _root_.SheafOfModules.pullbackIso.{m} (F := Functor.id C)
      (⟨𝟙 R.obj⟩ : ringOfLe h R ⟶
        ((Functor.id C).sheafPushforwardContinuous RingCat.{w} K J).obj R) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (PresheafOfModules.pullbackId.{m} R.obj) _ ≪≫
        Functor.leftUnitor _)

/-- `J`-sheafification of a `K`-sheaf of modules is left exact. -/
theorem preservesFiniteLimits_comparisonPullback :
    PreservesFiniteLimits (comparisonPullback.{u, v, w, m} h R) :=
  preservesFiniteLimits_of_natIso (comparisonPullbackIso h R).symm

/-- **Reading a sheaf of modules for a coarser topology preserves injective objects.** Its left
adjoint, sheafification for the finer topology, preserves monomorphisms. -/
theorem preservesInjectiveObjects_comparisonPushforward :
    (comparisonPushforward.{u, v, w, m} h R).PreservesInjectiveObjects :=
  have := preservesFiniteLimits_comparisonPullback h R
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (comparisonAdjunction.{u, v, w, m} h R)

/-- Reading a sheaf of modules for a coarser topology is left exact, being a right adjoint. -/
theorem preservesFiniteLimits_comparisonPushforward :
    PreservesFiniteLimits (comparisonPushforward.{u, v, w, m} h R) :=
  have := (comparisonAdjunction.{u, v, w, m} h R).isRightAdjoint
  inferInstance

/-- Sheafification for the finer topology undoes reading a sheaf of modules for the coarser one:
the counit of `Stacks.SheafOfModules.comparisonAdjunction` is an isomorphism. -/
def comparisonPushforwardCompPullbackIso :
    comparisonPushforward.{u, v, w, m} h R ⋙ comparisonPullback.{u, v, w, m} h R ≅ 𝟭 _ :=
  NatIso.ofComponents (comparisonPullbackObjIso.{u, v, w, m} h R)
    (fun g => (comparisonAdjunction.{u, v, w, m} h R).counit.naturality g)

attribute [local instance] preservesZeroMorphisms_comparisonPullback in
/-- Sheafification for the finer topology is exact. -/
theorem preservesHomology_comparisonPullback :
    (comparisonPullback.{u, v, w, m} h R).PreservesHomology :=
  have := preservesFiniteLimits_comparisonPullback h R
  have : PreservesFiniteColimits (comparisonPullback.{u, v, w, m} h R) :=
    (comparisonAdjunction.{u, v, w, m} h R).leftAdjoint_preservesColimits.{0, 0}
      |>.preservesFiniteColimits
  Functor.preservesHomologyOfExact _

end Stacks.SheafOfModules
