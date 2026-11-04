module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RepresentationTheory.Invariants
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.Injectives.Module.ContinuousGroupModules
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology

/-!
# Continuous group cohomology with coefficients in a commutative ring

Let `G` be a topological group and `R` a commutative ring. A continuous discrete `R`-`G`-module
is an `R`-module with a continuous action of `G`, the module carrying the discrete topology;
these form the abelian category `Stacks.Injectives.ContinuousModule R G`. Taking `G`-invariants
is a left exact functor to `R`-modules, and its higher right derived functors are continuous
group cohomology with `R`-module coefficients.

This refines the `R = ℤ` case
`Stacks.GroupCohomology.continuousGroupCohomologyFunctor`: forgetting the `R`-module structure
turns the functors defined here into the ones defined there, which is [Stacks, Tag 0DVD].

## Main definitions

* `Stacks.ContinuousCohomology.continuousModuleInvariants` — the left exact functor `M ↦ Mᴳ`
  with values in `R`-modules.
* `Stacks.ContinuousCohomology.cohomologyFunctor` — its `i`-th right derived functor,
  `Hⁱ(G, -)` with `R`-module coefficients.

## Implementation notes

The category of continuous discrete `R`-`G`-modules is abelian for all three universes
independent: it is a full subcategory of `Action (ModuleCat R) G` containing zero and closed
under subobjects, quotients and finite products. The closure instances are proved here in the
generality in which `Stacks.Injectives.ContinuousModule` is stated. Enough injectives is
available once the coefficient universe contains the group universe, which is the bound of
[Stacks, Tag 04JF].

Invariants are obtained by forgetting continuity and discreteness, passing to `R`-linear
representations and applying Mathlib's `Rep.invariantsFunctor`, which already carries its
`Additive` and `Linear R` instances; the `R`-linearity is what makes the comparison of
[Stacks, Tag 0DVE] an isomorphism of `R`-modules rather than of abelian groups.

`cohomologyFunctor` takes the derived category of the source as a free
`[HasDerivedCategory.{d} …]` argument instead of pinning
`CategoryTheory.HasDerivedCategory.standard` with a file-level `attribute [local instance]`. At
the standard model the morphisms of the derived category live a universe above its objects, which
makes statements about coproducts in it false rather than merely unavailable (see the
implementation notes of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`); leaving the
model free means every statement proved here holds in particular at the standard model and at
any locally small one.

## References

* [Stacks Project, Tag 04JF](https://stacks.math.columbia.edu/tag/04JF)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
* [Stacks Project, Tag 0DVD](https://stacks.math.columbia.edu/tag/0DVD)
-/

@[expose] public noncomputable section

open CategoryTheory Limits ZeroObject

universe d u v w

namespace Stacks.ContinuousCohomology

open scoped Stacks.DiscreteModuleTopology

section Abelian

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The underlying topological space of an action on an `R`-module is nonempty: it contains
`0`. -/
instance actionNonempty (X : Action (ModuleCat.{w} R) G) :
    Nonempty ((forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X) := ⟨(0 : X.V)⟩

/-- A map into a discrete space whose composition with an injection is continuous is itself
continuous: an injection into a discrete space has a continuous left inverse. -/
lemma continuous_of_comp_injective_discrete {X Y : Type w} {Z : Type v}
    [Nonempty X] [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology Y]
    [TopologicalSpace Z] (f : X → Y) (hf : Function.Injective f) {g : Z → X}
    (h : Continuous (f ∘ g)) : Continuous g := by
  obtain ⟨s, hs⟩ := hf.hasLeftInverse
  convert (continuous_of_discreteTopology : Continuous s).comp h using 1
  ext z
  exact (hs _).symm

/-- Continuous actions on `R`-modules are closed under subobjects. -/
instance continuousClosedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects
      (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) where
  prop_of_mono {X Y} f _ hY := by
    have : Mono f.hom := inferInstanceAs (Mono ((Action.forget _ G).map f))
    have hf := (ModuleCat.mono_iff_injective f.hom).mp inferInstance
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro x
    apply continuous_of_comp_injective_discrete
      (Y := (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj Y)
      (fun y : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X => f.hom y) hf
    have h := (continuous_prod_of_discrete_right.mp
      (Action.isContinuous_def Y |>.mp hY)) (f.hom x)
    exact h.congr fun g => (ConcreteCategory.congr_hom (f.comm g) x).symm

/-- Continuous actions on `R`-modules are closed under quotients. -/
instance continuousClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) where
  prop_of_epi {X Y} f _ hX := by
    have : Epi f.hom := inferInstanceAs (Epi ((Action.forget _ G).map f))
    have hf := (ModuleCat.epi_iff_surjective f.hom).mp inferInstance
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    have h := (continuous_prod_of_discrete_right.mp
      (Action.isContinuous_def X |>.mp hX)) x
    have h' := (continuous_of_discreteTopology : Continuous
      (Y := (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj Y)
      (fun x : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X =>
        (f.hom x : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj Y))).comp h
    exact h'.congr fun g => ConcreteCategory.congr_hom (f.comm g) x

/-- Continuous actions on `R`-modules are closed under finite products. -/
instance continuousClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) where
  isClosedUnderLimitsOfShape J _ := ⟨by
    rintro X ⟨p⟩
    have hi := Concrete.to_product_injective_of_isLimit _
      (isLimitOfPreserves (Action.forget (ModuleCat.{w} R) G) p.isLimit)
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro x
    apply continuous_of_comp_injective_discrete
      (Y := ∀ j, (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj (p.diag.obj j))
      (fun y : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X =>
        (fun j => (p.π.app j).hom y :
          ∀ j, (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj (p.diag.obj j))) hi
    apply continuous_pi
    intro j
    have h := (continuous_prod_of_discrete_right.mp
      (Action.isContinuous_def (p.diag.obj j) |>.mp (p.prop_diag_obj j)))
      ((p.π.app j).hom x)
    exact h.congr fun g => (ConcreteCategory.congr_hom ((p.π.app j).comm g) x).symm⟩

/-- The zero action on an `R`-module is continuous. -/
instance continuousContainsZero :
    ObjectProperty.ContainsZero
      (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) where
  exists_zero := by
    refine ⟨(0 : Action (ModuleCat.{w} R) G), isZero_zero _, ?_⟩
    have hZ := (Action.forget (ModuleCat.{w} R) G).map_isZero
      (isZero_zero (Action (ModuleCat.{w} R) G))
    have hsub : Subsingleton (0 : Action (ModuleCat.{w} R) G).V :=
      ModuleCat.isZero_iff_subsingleton.mp hZ
    refine ⟨(continuous_const
      (Y := (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj
        (0 : Action (ModuleCat.{w} R) G))
      (y := (0 : (0 : Action (ModuleCat.{w} R) G).V))).congr fun _ => ?_⟩
    exact hsub.elim _ _

/-- Continuous actions on `R`-modules form an abelian category: they are a full subcategory of
`Action (ModuleCat R) G` containing zero and closed under kernels, cokernels and finite
products. -/
instance contActionAbelian : Abelian (ContAction (ModuleCat.{w} R) G) :=
  inferInstanceAs (Abelian (ObjectProperty.FullSubcategory
    (Action.IsContinuous (V := ModuleCat.{w} R) (G := G))))

/-- Discrete continuous actions on `R`-modules are closed under subobjects. -/
instance discreteClosedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) where
  prop_of_mono _ _ _ := ⟨rfl⟩

/-- Discrete continuous actions on `R`-modules are closed under quotients. -/
instance discreteClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) where
  prop_of_epi _ _ _ := ⟨rfl⟩

/-- Discrete continuous actions on `R`-modules are closed under finite products. -/
instance discreteClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) where
  isClosedUnderLimitsOfShape _ _ := ⟨fun _ _ => ⟨rfl⟩⟩

/-- The zero continuous action on an `R`-module is discrete. -/
instance discreteContainsZero :
    ObjectProperty.ContainsZero
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) where
  exists_zero := ⟨0, isZero_zero _, ⟨rfl⟩⟩

/-- The abelian structure on continuous discrete `R`-`G`-modules, viewed as the full subcategory
of `ContAction (ModuleCat R) G` of discrete objects. -/
@[instance_reducible]
def fullSubcategoryAbelian :
    Abelian (ObjectProperty.FullSubcategory
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G))) := inferInstance

/-- Continuous discrete `R`-`G`-modules form an abelian category, with the ring, group and
coefficient universes independent. -/
instance abelian : Abelian (Stacks.Injectives.ContinuousModule.{u, v, w} R G) :=
  fullSubcategoryAbelian.{u, v, w} R G

/-- For a topological group `G`, the category of continuous discrete `R`-`G`-modules has enough
injectives when the coefficient universe contains both the ring and the group universe. -/
instance enoughInjectives [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :=
  enoughInjectives_of_hasFunctorialInjectiveEmbeddings _
    (Stacks.Injectives.continuousModule_hasFunctorialInjectiveEmbeddings.{u, v, w} R G)

end Abelian

section Invariants

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The category of continuous discrete `R`-`G`-modules is `R`-linear. -/
instance continuousModuleLinear :
    Linear R (Stacks.Injectives.ContinuousModule.{u, v, w} R G) := by
  change Linear R (ObjectProperty.FullSubcategory
    (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)))
  infer_instance

/-- The functor taking a continuous discrete `R`-`G`-module to its `R`-module of
`G`-invariants. -/
abbrev continuousModuleInvariants :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
    Rep.ActionToRep R G ⋙ Rep.invariantsFunctor R G

/-- The `G`-invariants functor on continuous discrete `R`-`G`-modules is additive. -/
instance continuousModuleInvariants_additive :
    (continuousModuleInvariants.{u, v, w} R G).Additive where
  map_add := by
    intros
    ext x : 2
    simp only [ModuleCat.hom_add, LinearMap.add_apply]
    apply Subtype.ext
    rfl

/-- The `i`-th continuous group cohomology functor with `R`-module coefficients: the `i`-th right
derived functor of taking `G`-invariants. -/
abbrev cohomologyFunctor [IsTopologicalGroup G]
    [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)]
    [HasDerivedCategory.{d} (ModuleCat.{max u v w} R)] (i : ℕ) :
    Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G ⥤ ModuleCat.{max u v w} R :=
  (continuousModuleInvariants.{u, v, max u v w} R G).rightDerivedPlus i

end Invariants

end Stacks.ContinuousCohomology
