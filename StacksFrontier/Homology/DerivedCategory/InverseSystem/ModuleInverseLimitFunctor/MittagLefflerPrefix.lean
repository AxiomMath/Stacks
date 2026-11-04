module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.Tactic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.ShortComplex.InverseLimit
public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DoubleResolution


/-!
# Derived inverse limits of modules over an inverse system of rings

For an inverse system of rings `A : ℕᵒᵖ ⥤ RingCat`, the inverse-limit functor from compatible
systems of `A`-modules to modules over `lim A` admits a right derived functor on the unbounded
derived categories. Its higher derived functors vanish above degree one, the value on a module
system is represented by the two-term product complex with differential `1 - shift`,
Mittag--Leffler systems are right acyclic, every complex has a quasi-isomorphic complex of
right-acyclic terms, and a termwise right-acyclic complex computes the derived limit termwise.

## Main definitions

* `ModuleInverseLimit.moduleDiagram`: the terms of a compatible module system, restricted along
  the limit projections to modules over the inverse-limit ring.
* `ModuleInverseLimit.moduleDiagramFunctor`: the previous construction, functorially.
* `ModuleInverseLimit.inverseLimit`: the canonical inverse-limit module functor.
* `ModuleInverseLimit.inverseLimitToProduct`, `ModuleInverseLimit.productMap`: the canonical map
  from the inverse limit into the product of the terms, and the induced map of products.

## Main results

* `ModuleInverseLimit.inverseLimit_hasRightDerivedFunctor_and_computations`: existence and the
  computations of the derived inverse-limit functor for modules over an inverse system of rings.

## Implementation notes

The category of compatible module systems is `PresheafOfModules A`. Restriction along the limit
projections makes every term a module over the limit ring. The inverse-limit functor and the
products in the two-term representative are limits and products in that fixed module category;
thus their scalar actions are the pointwise actions induced by the projections of the limit ring.

Existence on `K⁺` is the adapted-class criterion of Stacks 05T8 applied to the Mittag--Leffler
systems, which are cofinal by the prefix construction below; the passage to unbounded complexes
is the bounded-cohomological-dimension criterion of Stacks 07K7, whose hypothesis is supplied by
the vanishing in degree two.

## References

* [Stacks Project, Tag 091D](https://stacks.math.columbia.edu/tag/091D)
-/

/-!
# Module diagrams, the inverse-limit functor and prefix systems

The module diagram of a compatible module system over the inverse-limit ring, the inverse-limit
functor, the map into the product of the terms, and the Mittag--Leffler prefix system into
which every module system embeds. Part of `ModuleInverseLimitFunctor`.
-/

section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace ModuleInverseLimit

attribute [local instance] HasDerivedCategory.standard

universe u v

/-- The diagram of modules over the limit ring underlying a compatible system of modules. Its
`n`-th term is obtained by restricting scalars along `lim A ⟶ Aₙ`. -/
public noncomputable def moduleDiagram (A : ℕᵒᵖ ⥤ RingCat.{u})
    (M : PresheafOfModules.{v} A) : ℕᵒᵖ ⥤ ModuleCat.{v} (limit A : RingCat.{u}) where
  obj n := (ModuleCat.restrictScalars.{v} (limit.π A n).hom).obj (M.obj n)
  map {i j} f :=
    (ModuleCat.restrictScalars.{v} (limit.π A i).hom).map (M.map f) ≫
      (ModuleCat.restrictScalarsComp' (limit.π A i).hom (A.map f).hom
        (limit.π A j).hom (congrArg RingCat.Hom.hom (limit.w A f)).symm).inv.app _
  map_id X := by
    ext x
    change M.map (𝟙 X) x = x
    simp
    rfl
  map_comp f g := by
    ext x
    change M.map (f ≫ g) x = M.map g (M.map f x)
    simp
    rfl

/-- The `n`-th term of `moduleDiagram A M` is `M.obj n` with scalars restricted along the
projection `lim A ⟶ Aₙ`. -/
@[simp]
public lemma moduleDiagram_obj (A : ℕᵒᵖ ⥤ RingCat.{u})
    (M : PresheafOfModules.{v} A) (n : ℕᵒᵖ) :
    (moduleDiagram A M).obj n =
      (ModuleCat.restrictScalars.{v} (limit.π A n).hom).obj (M.obj n) := rfl

/-- The natural transformation between limit-ring module diagrams induced by a morphism of
compatible module systems. -/
public noncomputable def moduleDiagramMap (A : ℕᵒᵖ ⥤ RingCat.{u})
    {M N : PresheafOfModules.{v} A} (f : M ⟶ N) : moduleDiagram A M ⟶ moduleDiagram A N where
  app n := (ModuleCat.restrictScalars.{v} (limit.π A n).hom).map (f.app n)
  naturality i j g := by
    ext x
    change f.app j (M.map g x) = N.map g (f.app i x)
    exact PresheafOfModules.naturality_apply f g x

/-- The `n`-th component of `moduleDiagramMap A f` is `f.app n` with scalars restricted along
the projection `lim A ⟶ Aₙ`. -/
@[simp]
public lemma moduleDiagramMap_app (A : ℕᵒᵖ ⥤ RingCat.{u})
    {M N : PresheafOfModules.{v} A} (f : M ⟶ N) (n : ℕᵒᵖ) :
    (moduleDiagramMap A f).app n =
      (ModuleCat.restrictScalars.{v} (limit.π A n).hom).map (f.app n) := rfl

/-- Restricting every term to the limit ring, functorially in a compatible module system. -/
public noncomputable def moduleDiagramFunctor (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} A ⥤ (ℕᵒᵖ ⥤ ModuleCat.{v} (limit A : RingCat.{u})) where
  obj M := moduleDiagram A M
  map f := moduleDiagramMap A f
  map_id M := by
    ext n x
    change (𝟙 M : M ⟶ M).app n x = x
    rfl
  map_comp f g := by
    ext n x
    change (f ≫ g).app n x = g.app n (f.app n x)
    rfl

/-- The canonical inverse-limit functor from compatible module systems to modules over the
inverse-limit ring. -/
public noncomputable def inverseLimit (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} A ⥤ ModuleCat.{v} (limit A : RingCat.{u}) :=
  moduleDiagramFunctor A ⋙ lim

/-- The canonical map from the inverse limit into the product of the terms. -/
public noncomputable def inverseLimitToProduct (A : ℕᵒᵖ ⥤ RingCat.{u})
    (M : PresheafOfModules.{v} A) :
    (inverseLimit A).obj M ⟶
      ∏ᶜ fun n : ℕ ↦ (moduleDiagram A M).obj (Opposite.op n) :=
  Pi.lift fun n ↦ limit.π (moduleDiagram A M) (Opposite.op n)

/-- The map on products induced by a morphism of compatible module systems. -/
public noncomputable def productMap (A : ℕᵒᵖ ⥤ RingCat.{u})
    {M N : PresheafOfModules.{v} A} (f : M ⟶ N) :
    (∏ᶜ fun n : ℕ ↦ (moduleDiagram A M).obj (Opposite.op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ (moduleDiagram A N).obj (Opposite.op n) :=
  Pi.lift fun n ↦
    Pi.π (fun n : ℕ ↦ (moduleDiagram A M).obj (Opposite.op n)) n ≫
      (moduleDiagramMap A f).app (Opposite.op n)

/-- The map `(inverseLimit A).map f` commutes with the limit projections onto the `n`-th terms,
whose components are given by `moduleDiagramMap A f`. -/
@[simp, reassoc]
public lemma inverseLimit_map_π (A : ℕᵒᵖ ⥤ RingCat.{u})
    {M N : PresheafOfModules.{v} A} (f : M ⟶ N) (n : ℕᵒᵖ) :
    (inverseLimit A).map f ≫ limit.π (moduleDiagram A N) n =
      limit.π (moduleDiagram A M) n ≫ (moduleDiagramMap A f).app n := by
  apply limMap_π

end ModuleInverseLimit
end

end

section

@[expose] public noncomputable section

open CategoryTheory Opposite

universe ringLevel moduleLevel

namespace ModuleInverseLimit

set_option backward.isDefEq.respectTransparency false

private instance prefixComponentModule
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕ) (index : Fin (stage + 1)) :
    Module (rings.obj (op stage)) (system.obj (op index.val)) :=
  Module.compHom _ (rings.map (homOfLE (Nat.le_of_lt_succ index.isLt)).op).hom

private abbrev prefixObj
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕ) : ModuleCat.{moduleLevel} (rings.obj (op stage)) :=
  ModuleCat.of _ ((index : Fin (stage + 1)) → system.obj (op index.val))

private def prefixMap
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    {source target : ℕᵒᵖ} (transition : source ⟶ target) :
    prefixObj rings system source.unop ⟶
      (ModuleCat.restrictScalars (rings.map transition).hom).obj
        (prefixObj rings system target.unop) := by
  letI : Module (rings.obj source) (prefixObj rings system source.unop) :=
    (prefixObj rings system source.unop).isModule
  letI : Module (rings.obj target) (prefixObj rings system target.unop) :=
    (prefixObj rings system target.unop).isModule
  letI : Module (rings.obj source) (prefixObj rings system target.unop) :=
    Module.compHom _ (rings.map transition).hom
  exact ModuleCat.ofHom
    { toFun := fun values index => values ⟨index.val, by
        have order := leOfHom transition.unop
        omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro scalar values
        funext index
        change (rings.map (homOfLE (by
          have order := leOfHom transition.unop
          omega : index.val ≤ source.unop)).op) scalar •
            (values ⟨index.val, by have order := leOfHom transition.unop; omega⟩) =
            (rings.map (homOfLE (Nat.le_of_lt_succ index.isLt)).op)
              ((rings.map transition) scalar) •
                (values ⟨index.val, by have order := leOfHom transition.unop; omega⟩)
        have factor : (homOfLE (by
            have order := leOfHom transition.unop
            omega : index.val ≤ source.unop)).op =
            transition ≫ (homOfLE (Nat.le_of_lt_succ index.isLt)).op := Subsingleton.elim _ _
        rw [factor, rings.map_comp]
        rfl }

private def prefixSystem
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    PresheafOfModules.{moduleLevel} rings where
  obj stage := prefixObj rings system stage.unop
  map transition := prefixMap rings system transition
  map_id stage := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext index
    rfl
  map_comp first second := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext index
    rfl

private def prefixUnitMap
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    system ⟶ prefixSystem rings system where
  app stage := by
    letI : Module (rings.obj stage) (prefixObj rings system stage.unop) :=
      (prefixObj rings system stage.unop).isModule
    exact ModuleCat.ofHom
      { toFun := fun value index =>
          system.map (homOfLE (Nat.le_of_lt_succ index.isLt)).op value
        map_add' := by
          intro left right
          funext index
          exact map_add _ left right
        map_smul' := by
          intro scalar value
          funext index
          exact system.map_smul _ scalar value }
  naturality transition := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro value
    funext index
    change system.map (homOfLE (Nat.le_of_lt_succ index.isLt)).op
        (system.map transition value) =
      system.map (homOfLE (by
        have order := leOfHom transition.unop
        omega)).op value
    rw [← system.map_comp_apply]
    exact system.congr_map_apply (Subsingleton.elim _ _) value

private theorem prefixUnitMap_mono
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    Mono (prefixUnitMap rings system) := by
  apply PresheafOfModules.mono_of_injective
  intro stage left right equal
  have last := congrFun equal ⟨stage.unop, Nat.lt_succ_self _⟩
  change system.map (homOfLE (le_refl stage.unop)).op left =
    system.map (homOfLE (le_refl stage.unop)).op right at last
  have identity : (homOfLE (le_refl stage.unop)).op = 𝟙 stage := Subsingleton.elim _ _
  rw [identity, system.map_id] at last
  exact last

private theorem prefixSystem_map_surjective
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    {source target : ℕᵒᵖ} (transition : source ⟶ target) :
    Function.Surjective ((prefixSystem rings system).presheaf.map transition) := by
  intro values
  refine ⟨fun index => if bound : index.val < target.unop + 1 then
    values ⟨index.val, bound⟩ else 0, ?_⟩
  funext index
  show (if bound : index.val < target.unop + 1 then values ⟨index.val, bound⟩ else 0) = values
    index
  simp [index.isLt]

private theorem prefixSystem_isMittagLeffler
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    ((prefixSystem rings system).presheaf ⋙ forget Ab).IsMittagLeffler := by
  apply Functor.isMittagLeffler_of_surjective
  exact fun _ _ transition => prefixSystem_map_surjective rings system transition

private theorem surjectiveImage_map_surjective
    {rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}}
    {sourceSystem targetSystem : PresheafOfModules.{moduleLevel} rings}
    (quotient : sourceSystem ⟶ targetSystem) [Epi quotient]
    {source target : ℕᵒᵖ} (transition : source ⟶ target)
    (surjective : Function.Surjective (sourceSystem.presheaf.map transition)) :
    Function.Surjective (targetSystem.presheaf.map transition) := by
  intro value
  obtain ⟨representative, represented⟩ := PresheafOfModules.surjective_of_epi quotient target value
  obtain ⟨lift, lifted⟩ := surjective representative
  refine ⟨quotient.app source lift, ?_⟩
  show targetSystem.map transition (quotient.app source lift) = value
  rw [← PresheafOfModules.naturality_apply quotient transition lift]
  exact (congrArg (quotient.app target) lifted).trans represented

private theorem prefixCokernel_isMittagLeffler
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    ((CategoryTheory.Limits.cokernel (prefixUnitMap rings system)).presheaf ⋙
      forget Ab).IsMittagLeffler := by
  apply Functor.isMittagLeffler_of_surjective
  exact fun _ _ transition => surjectiveImage_map_surjective
    (CategoryTheory.Limits.cokernel.π (prefixUnitMap rings system)) transition
    (prefixSystem_map_surjective rings system transition)


end ModuleInverseLimit

end

end
