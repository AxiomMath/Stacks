module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.AbelianSheafStalk

/-!
# Discrete `G`-modules as abelian groups and as `ℤ`-modules

For a topological group `G`, a discrete `G`-module is encoded in two ways: as an abelian group
with a continuous `G`-action, and as a `ℤ`-module with a continuous `G`-action. Both are full
subcategories of actions of `G`, cut out by continuity and by discreteness of the underlying
topological space, and the forgetful functor from `ℤ`-modules to abelian groups is an
equivalence which matches the two conditions. Hence the two encodings are equivalent.

## Main definitions

* `CategoryTheory.Equivalence.mapDiscreteContAction` — an equivalence of the ambient concrete
  categories over `TopCat` which respects continuity and discreteness induces an equivalence of
  the categories of discrete continuous `G`-actions.
* `CategoryTheory.continuousGModuleEquivContinuousGAddCommGrp` — discrete continuous
  `G`-modules are the same as discrete `G`-modules in the abelian-group encoding.

## Main results

* `Action.isContinuous_of_iso` — continuity of an action depends only on its isomorphism class.
* `ContAction.isDiscrete_isClosedUnderIsomorphisms` — so does discreteness of the underlying
  topological space.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

attribute [local instance] discreteForget₂AddCommGrpCat

/-- `ℤ`-modules are given the discrete topology when forming continuous actions. -/
local instance discreteForget₂ModuleCatInt : HasForget₂ (ModuleCat.{w} ℤ) TopCat.{w} where
  forget₂ := forget (ModuleCat.{w} ℤ) ⋙ TopCat.discrete
  forget_comp := rfl

namespace CategoryTheory

/-- For an equivalence `E`, the action obtained from `X` by transporting along `E.inverse` and
back along `E.functor` is isomorphic to `X`, by the counit of `E`. -/
def Equivalence.mapActionCounitIso {V W : Type*} [Category* V] [Category* W]
    (G : Type*) [Monoid G] (E : V ≌ W) (X : Action W G) :
    (E.functor.mapAction G).obj ((E.inverse.mapAction G).obj X) ≅ X :=
  Action.mkIso (E.counitIso.app X.V) (fun g ↦ E.counitIso.hom.naturality (X.ρ g))

end CategoryTheory

section Transport

variable {V W : Type*} [Category* V] {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] [HasForget₂ V TopCat]
    [Category* W] {FW : W → W → Type*} {CW : W → Type*} [∀ X Y, FunLike (FW X Y) (CW X) (CW Y)]
    [ConcreteCategory W FW] [HasForget₂ W TopCat]
    {G : Type*} [Monoid G] [TopologicalSpace G]

/-- Continuity of an action depends only on its isomorphism class. -/
lemma Action.isContinuous_of_iso {A B : Action V G} (e : A ≅ B) (h : B.IsContinuous) :
    A.IsContinuous := by
  refine (TopCat.homeoOfIso ((forget₂ (Action V G) TopCat).mapIso e)).isInducing.continuousSMul
    (f := id) continuous_id ?_
  intro c x
  show ((forget₂ V TopCat).map (A.ρ c) ≫ (forget₂ V TopCat).map e.hom.hom) x =
    ((forget₂ V TopCat).map e.hom.hom ≫ (forget₂ V TopCat).map (B.ρ c)) x
  rw [← Functor.map_comp, ← Functor.map_comp, e.hom.comm c]

/-- Of two isomorphic continuous actions, one has a discrete underlying space exactly when the
other does. -/
instance ContAction.isDiscrete_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (ContAction.IsDiscrete (V := V) (G := G)) where
  of_iso e h :=
    (TopCat.homeoOfIso ((forget₂ (ContAction V G) TopCat).mapIso e)).discreteTopology_iff.mp h

namespace CategoryTheory

/-- An equivalence of the ambient categories which preserves continuity of actions in both
directions and matches the discreteness conditions induces an equivalence of the categories of
discrete continuous `G`-actions. -/
def Equivalence.mapDiscreteContAction (G : Type*) [Monoid G] [TopologicalSpace G] (E : V ≌ W)
    (H₁ : ∀ X : ContAction V G, ((E.functor.mapAction G).obj X.obj).IsContinuous)
    (H₂ : ∀ X : ContAction W G, ((E.inverse.mapAction G).obj X.obj).IsContinuous)
    (h : ObjectProperty.inverseImage (ContAction.IsDiscrete (V := W) (G := G))
      (E.mapContAction G H₁ H₂).functor = ContAction.IsDiscrete (V := V) (G := G)) :
    DiscreteContAction V G ≌ DiscreteContAction W G :=
  (E.mapContAction G H₁ H₂).congrFullSubcategory h

end CategoryTheory

end Transport

/-- An action of `G` on a `ℤ`-module is continuous exactly when the corresponding action on the
underlying abelian group is. -/
lemma Action.isContinuous_mapAction_forget₂Int_iff {G : Type u} [Monoid G] [TopologicalSpace G]
    (Y : Action (ModuleCat.{w} ℤ) G) :
    (((forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).mapAction G).obj Y).IsContinuous ↔
      Y.IsContinuous :=
  Iff.rfl

namespace CategoryTheory

/-- Forgetting the `ℤ`-module structure is an equivalence from discrete continuous `G`-modules
to abelian groups with a continuous `G`-action. -/
def continuousGModuleEquivContinuousGAddCommGrp (G : Type u) [Group G] [TopologicalSpace G] :
    ContinuousGModule.{u, w} G ≌ ContinuousGAddCommGrp.{u, w} G :=
  Equivalence.mapDiscreteContAction G
    (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence (fun X ↦ X.property)
    (fun X ↦ (Action.isContinuous_mapAction_forget₂Int_iff _).mp (Action.isContinuous_of_iso
      (Equivalence.mapActionCounitIso G
        (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence X.obj) X.property))
    (by ext X; exact iff_of_true ⟨rfl⟩ ⟨rfl⟩)

end CategoryTheory

end
