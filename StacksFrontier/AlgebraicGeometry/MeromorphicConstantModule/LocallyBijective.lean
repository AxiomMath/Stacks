module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Sheafifying a morphism which is bijective on a basis

A morphism of presheaves on a topological space which is bijective on the sections over every
member of a basis of the topology is locally bijective, hence inverted by sheafification. For
presheaves of modules this gives a criterion for the sheafification of a morphism of presheaves
of modules to be an isomorphism of sheaves of modules.

This is the module-level counterpart of
`Stacks.AlgebraicGeometry.GenericPointProduct.isIso_sheafifyLift_of_isIso_basis`, which compares a
presheaf with a *sheaf*. Here the two sides are both presheaves and neither has computable
sections after sheafification, so the comparison has to be made before sheafifying.

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallyInjective_of_bijective_basis` and
  `isLocallySurjective_of_bijective_basis`: bijectivity on a basis implies local bijectivity.
* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.isIso_sheafification_map_of_bijective_basis`:
  the sheafification of such a morphism of presheaves of modules is an isomorphism.

## Implementation notes

The covering sieves of `Opens.grothendieckTopology` are the sieves whose members cover the open
set pointwise, by `Opens.mem_grothendieckTopology`, so membership of the image sieve or the
equalizer sieve is checked by producing, for each point, a basis element containing it. That is
exactly what `Opens.isBasis_iff_nbhd` supplies.

The passage from local bijectivity to an isomorphism of sheaves of modules goes through
`CategoryTheory.GrothendieckTopology.W`: the underlying morphism of presheaves of abelian groups
is inverted by `presheafToSheaf`, the functor `PresheafOfModules.sheafification` followed by
`SheafOfModules.toSheaf` *is* `PresheafOfModules.toPresheaf` followed by `presheafToSheaf` (the
isomorphism `PresheafOfModules.sheafificationCompToSheaf` is `Iso.refl`), and
`SheafOfModules.toSheaf` reflects isomorphisms.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe w' v v' u u'

namespace Stacks.AlgebraicGeometry.MeromorphicConstantModule

section Basis

variable {Y : TopCat.{u}} {ι : Type*} {B : ι → Opens Y}
variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{w'} A FA]
variable {P Q : TopCat.Presheaf A Y} (f : P ⟶ Q)

/-- A morphism of presheaves which is injective on the sections over every member of a basis of
the topology is locally injective. -/
theorem isLocallyInjective_of_injective_basis (hB : Opens.IsBasis (Set.range B))
    (hf : ∀ i, Function.Injective (ConcreteCategory.hom (f.app (op (B i))))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) f where
  equalizerSieve_mem {U} s t h := by
    intro x hx
    obtain ⟨V, ⟨i, rfl⟩, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
    refine ⟨B i, homOfLE hVU, ?_, hxV⟩
    refine hf i ?_
    rw [NatTrans.naturality_apply f (homOfLE hVU).op s,
      NatTrans.naturality_apply f (homOfLE hVU).op t, h]

/-- A morphism of presheaves which is surjective on the sections over every member of a basis of
the topology is locally surjective. -/
theorem isLocallySurjective_of_surjective_basis (hB : Opens.IsBasis (Set.range B))
    (hf : ∀ i, Function.Surjective (ConcreteCategory.hom (f.app (op (B i))))) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) f where
  imageSieve_mem {U} s := by
    intro x hx
    obtain ⟨V, ⟨i, rfl⟩, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
    obtain ⟨t, ht⟩ := hf i (Q.map (homOfLE hVU).op s)
    exact ⟨B i, homOfLE hVU, ⟨t, ht⟩, hxV⟩

end Basis

section Modules

variable {Y : TopCat.{u}}
  {R₀ : (Opens Y)ᵒᵖ ⥤ RingCat.{u}} {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
  (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) α]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) α]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{v}]

/-- A morphism of presheaves of modules whose underlying morphism of presheaves of abelian groups
is locally bijective has an isomorphism for its sheafification. -/
theorem isIso_sheafification_map
    {M N : PresheafOfModules.{v} R₀} (ψ : M ⟶ N)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf R₀).map ψ)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf R₀).map ψ)] :
    IsIso ((PresheafOfModules.sheafification.{v} α).map ψ) := by
  have hW : IsIso ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v}).map
      ((PresheafOfModules.toPresheaf R₀).map ψ)) :=
    ((Opens.grothendieckTopology Y).W_iff ((PresheafOfModules.toPresheaf R₀).map ψ)).mp
      ((Opens.grothendieckTopology Y).W_of_isLocallyBijective
        ((PresheafOfModules.toPresheaf R₀).map ψ))
  have h : IsIso ((SheafOfModules.toSheaf.{v} R).map
      ((PresheafOfModules.sheafification.{v} α).map ψ)) := hW
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)

/-- A morphism of presheaves of modules on a topological space which is bijective on the sections
over every member of a basis of the topology has an isomorphism for its sheafification. -/
theorem isIso_sheafification_map_of_bijective_basis {ι : Type*} {B : ι → Opens Y}
    (hB : Opens.IsBasis (Set.range B))
    {M N : PresheafOfModules.{v} R₀} (ψ : M ⟶ N)
    (hψ : ∀ i, Function.Bijective (ψ.app (op (B i))).hom) :
    IsIso ((PresheafOfModules.sheafification.{v} α).map ψ) := by
  have := isLocallyInjective_of_injective_basis
    ((PresheafOfModules.toPresheaf R₀).map ψ) hB (fun i ↦ (hψ i).1)
  have := isLocallySurjective_of_surjective_basis
    ((PresheafOfModules.toPresheaf R₀).map ψ) hB (fun i ↦ (hψ i).2)
  exact isIso_sheafification_map α ψ

end Modules

end Stacks.AlgebraicGeometry.MeromorphicConstantModule

end
