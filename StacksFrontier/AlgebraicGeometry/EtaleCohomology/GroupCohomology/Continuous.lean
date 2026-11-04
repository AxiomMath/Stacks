module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RepresentationTheory.Invariants
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.Injectives.Module.ContinuousGroupModules

/-!
# Continuous group cohomology

For a topological group `G`, continuous group cohomology of a discrete continuous `G`-module is
the right derived functor of taking `G`-invariants. For a discrete group this is group
cohomology; for Galois groups it is called Galois cohomology.

## Main definitions

* `ContinuousGModule` is the category of discrete abelian groups with continuous `G`-action.
* `continuousGModuleInvariants` is the functor `M ↦ Mᴳ`.
* `continuousGroupCohomologyFunctor` is its higher right derived functor.
* `continuousGroupCohomology` is the continuous group cohomology group of a module.

## Implementation notes

Discrete abelian groups are expressed as discrete continuous `ℤ`-modules, using
`Stacks.Injectives.ContinuousModule`. Invariants are computed by forgetting continuity, passing to
`ℤ`-linear representations and applying `Rep.invariantsFunctor`, and the derived functors are
`CategoryTheory.Functor.rightDerivedPlus`. Mathlib's cochain-based `continuousCohomology` allows
nondiscrete topological coefficients, whereas the present construction right derives invariants on
discrete continuous modules.

## References

* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits ZeroObject

universe u v

/-- The forgetful functor from abelian groups to topological spaces, giving each group the discrete
topology. -/
local instance : HasForget₂ (ModuleCat.{v} ℤ) TopCat.{v} :=
  { forget₂ := forget (ModuleCat.{v} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The underlying space of a `G`-action on an abelian group is discrete. -/
instance action_discreteTopology (X : Action (ModuleCat.{v} ℤ) G) :
    DiscreteTopology ((forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj X) := ⟨rfl⟩

/-- The underlying space of a `G`-action on an abelian group is nonempty. -/
instance action_nonempty (X : Action (ModuleCat.{v} ℤ) G) :
    Nonempty ((forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj X) := ⟨(0 : X.V)⟩

/-- Continuous `G`-actions on abelian groups are closed under subobjects. -/
instance continuous_closedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects
      (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G)) where
  prop_of_mono {X Y} f _ hY := by
    have continuous_of_comp_injective_discrete
        {X Y : Type v} {Z : Type u} [Nonempty X] [TopologicalSpace X]
        [TopologicalSpace Y] [DiscreteTopology Y] [TopologicalSpace Z]
        (f : X → Y) (hf : Function.Injective f) {g : Z → X}
        (h : Continuous (f ∘ g)) : Continuous g := by
      obtain ⟨s, hs⟩ := hf.hasLeftInverse
      convert (continuous_of_discreteTopology : Continuous s).comp h using 1
      ext z
      exact (hs _).symm
    have : Mono f.hom := inferInstanceAs (Mono ((Action.forget _ G).map f))
    have hf := (ModuleCat.mono_iff_injective f.hom).mp inferInstance
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro x
    apply continuous_of_comp_injective_discrete
      (Y := (forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj Y)
      (fun y : (forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj X => f.hom y) hf
    have h := (continuous_prod_of_discrete_right.mp (Action.isContinuous_def Y |>.mp hY))
      (f.hom x)
    exact h.congr fun g => (ConcreteCategory.congr_hom (f.comm g) x).symm

/-- Continuous `G`-actions on abelian groups are closed under quotients. -/
instance continuous_closedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G)) where
  prop_of_epi {X Y} f _ hX := by
    have : Epi f.hom := inferInstanceAs (Epi ((Action.forget _ G).map f))
    have hf := (ModuleCat.epi_iff_surjective f.hom).mp inferInstance
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    have h := (continuous_prod_of_discrete_right.mp (Action.isContinuous_def X |>.mp hX)) x
    have h' := (continuous_of_discreteTopology : Continuous
      (Y := (forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj Y)
      (fun x : (forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj X =>
        (f.hom x : (forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj Y))).comp h
    exact h'.congr fun g => ConcreteCategory.congr_hom (f.comm g) x

/-- Continuous `G`-actions on abelian groups are closed under finite products. -/
instance continuous_closedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G)) where
  isClosedUnderLimitsOfShape J _ := ⟨by
    have continuous_of_comp_injective_discrete
        {X Y : Type v} {Z : Type u} [Nonempty X] [TopologicalSpace X]
        [TopologicalSpace Y] [DiscreteTopology Y] [TopologicalSpace Z]
        (f : X → Y) (hf : Function.Injective f) {g : Z → X}
        (h : Continuous (f ∘ g)) : Continuous g := by
      obtain ⟨s, hs⟩ := hf.hasLeftInverse
      convert (continuous_of_discreteTopology : Continuous s).comp h using 1
      ext z
      exact (hs _).symm
    rintro X ⟨p⟩
    let F := Action.forget (ModuleCat.{v} ℤ) G
    have hi := Concrete.to_product_injective_of_isLimit _
      (isLimitOfPreserves F p.isLimit)
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro x
    let D (j : Discrete J) := (forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj (p.diag.obj j)
    apply continuous_of_comp_injective_discrete
      (Y := ∀ j, D j)
      (fun y : (forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj X =>
        (fun j => (p.π.app j).hom y : ∀ j, D j)) hi
    apply continuous_pi
    intro j
    have h := (continuous_prod_of_discrete_right.mp
      (Action.isContinuous_def (p.diag.obj j) |>.mp (p.prop_diag_obj j)))
      ((p.π.app j).hom x)
    exact h.congr fun g => (ConcreteCategory.congr_hom ((p.π.app j).comm g) x).symm⟩

/-- The zero `G`-action on an abelian group is continuous. -/
instance continuous_containsZero :
    ObjectProperty.ContainsZero
      (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G)) where
  exists_zero := by
    let Z := (0 : Action (ModuleCat.{v} ℤ) G)
    refine ⟨Z, isZero_zero _, ?_⟩
    have hZ := (Action.forget (ModuleCat.{v} ℤ) G).map_isZero (isZero_zero _)
    have : Subsingleton Z.V := ModuleCat.isZero_iff_subsingleton.mp hZ
    exact ⟨(continuous_const
      (Y := (forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj Z)
      (y := (0 : Z.V))).congr fun _ => Subsingleton.elim (0 : Z.V) _⟩

/-- Discrete continuous `G`-actions are closed under subobjects. -/
instance discrete_closedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects
      (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G)) where
  prop_of_mono _ _ _ := ⟨rfl⟩

/-- Discrete continuous `G`-actions are closed under quotients. -/
instance discrete_closedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G)) where
  prop_of_epi _ _ _ := ⟨rfl⟩

/-- Discrete continuous `G`-actions are closed under finite products. -/
instance discrete_closedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G)) where
  isClosedUnderLimitsOfShape _ _ := ⟨fun _ _ => ⟨rfl⟩⟩

/-- The zero continuous `G`-action is discrete. -/
instance discrete_containsZero :
    ObjectProperty.ContainsZero
      (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G)) where
  exists_zero := ⟨0, isZero_zero _, ⟨rfl⟩⟩

/-- Discrete abelian groups with continuous `G`-action. -/
abbrev ContinuousGModule := Stacks.Injectives.ContinuousModule.{0, u, v} ℤ G

/-- Discrete continuous `G`-modules form an abelian category. -/
instance continuousGModuleAbelian : Abelian (ContinuousGModule.{u, v} G) :=
  inferInstanceAs (Abelian (ObjectProperty.FullSubcategory
    (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G))))

/-- The category of discrete continuous `G`-modules has enough injectives. -/
instance continuousGModuleEnoughInjectives [IsTopologicalGroup G] :
    EnoughInjectives (ContinuousGModule.{u, max u v} G) :=
  enoughInjectives_of_hasFunctorialInjectiveEmbeddings _
    (Stacks.Injectives.continuousModule_hasFunctorialInjectiveEmbeddings ℤ G)

/-- The functor taking a discrete continuous `G`-module to its invariant subgroup. -/
abbrev continuousGModuleInvariants : ContinuousGModule.{u, v} G ⥤ AddCommGrpCat.{v} :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
    Rep.ActionToRep ℤ G ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}

/-- The invariants functor is additive. -/
instance continuousGModuleInvariants_additive : (continuousGModuleInvariants G).Additive where
  map_add := by
    intros
    ext
    rfl

attribute [local instance] HasDerivedCategory.standard

/-- The `i`-th continuous group cohomology functor, namely the `i`-th right
derived functor of taking invariants. -/
@[stacks 04JR "the cohomology functors"]
abbrev continuousGroupCohomologyFunctor [IsTopologicalGroup G]
    (i : ℕ) : ContinuousGModule.{u, max u v} G ⥤ AddCommGrpCat.{max u v} :=
  (continuousGModuleInvariants.{u, max u v} G).rightDerivedPlus i

/-- The continuous group cohomology group `Hⁱ(G, M)`. For discrete groups this
is group cohomology, and for Galois groups it is Galois cohomology. When
`G = Gal(Kˢᵉᵖ/K)`, it is also denoted `Hⁱ(K, M)`. -/
@[stacks 04JR "the cohomology groups"]
abbrev continuousGroupCohomology [IsTopologicalGroup G]
    (i : ℕ) (M : ContinuousGModule.{u, max u v} G) : AddCommGrpCat.{max u v} :=
  (continuousGroupCohomologyFunctor G i).obj M

