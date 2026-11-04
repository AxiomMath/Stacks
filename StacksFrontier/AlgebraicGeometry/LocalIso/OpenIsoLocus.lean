module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplayRestrict
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# The open locus where a morphism of modules is an isomorphism

Let `X` be a scheme and let `α : F ⟶ G` be a morphism of `𝒪_X`-modules with `F` of finite type
and `G` coherent.  This file studies the set

`L(α) = {x ∈ X | α is an isomorphism on the stalk at x}`,

proves that it is **open**, and proves that `α` restricts to an isomorphism over any open
contained in it — so that `L(α)` is the largest open over which `α` becomes invertible.

## Main definitions

* `Stacks.AlgebraicGeometry.IsoLocus.stalkIsoLocus`: the set `L(α)` above.

## Main results

* `Stacks.AlgebraicGeometry.IsoLocus.isOpen_stalkIsoLocus`: **`L(α)` is open.**  For `x ∈ L(α)`,
  [Stacks, Tag 01Y3] part (4) produces an open `U ∋ x` over which `α` is invertible, and the
  stalks of a restriction are the stalks of the original module
  (`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), so all of `U` lies in `L(α)`.
* `Stacks.AlgebraicGeometry.IsoLocus.isIso_restrictFunctor_map_of_subset`: **`α` restricts to an
  isomorphism over any open contained in `L(α)`.**  Invertibility of a morphism of sheaves of
  modules over a space is detected on stalks
  (`ExtensionByZeroModules.isIso_of_stalk_isIso`), and the same identification of stalks
  transports the hypothesis to the open subscheme.
* `Stacks.AlgebraicGeometry.IsoLocus.exists_isIso_restrictFunctor_map_of_subset_stalkIsoLocus`:
  **a morphism which is a stalkwise isomorphism at every point of a subset `Z` restricts to an
  isomorphism over an open neighbourhood of `Z`.**  No hypothesis on `Z` is needed; in
  particular `Z` may be the underlying set of a closed subscheme.

## Implementation notes

`AlgebraicGeometry.exists_isIso_over_of_stalk_isIso` asks for coherence of the **target** of the
morphism and finite type of its **source**, and states its stalk hypothesis with
`CategoryTheory.Functor.map` of `PresheafOfModules.toPresheaf` applied to the `val` of the
morphism; that spelling is definitionally the `AlgebraicGeometry.Scheme.Modules.Hom.mapPresheaf`
one used here.

## References

* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.IsoLocus

variable {X : Scheme.{u}}

/-- **The locus where a morphism of modules is an isomorphism on stalks.** -/
def stalkIsoLocus {F G : X.Modules} (α : F ⟶ G) : Set X :=
  {x | IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map (Scheme.Modules.Hom.mapPresheaf α))}

/-- A point `x` lies in `stalkIsoLocus α` if and only if `α` induces an isomorphism on the stalks
at `x`. -/
theorem mem_stalkIsoLocus_iff {F G : X.Modules} (α : F ⟶ G) (x : X) :
    x ∈ stalkIsoLocus α ↔
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map (Scheme.Modules.Hom.mapPresheaf α)) :=
  Iff.rfl

/-- **Every point of an open over which `α` restricts to an isomorphism lies in the locus.** -/
theorem subset_stalkIsoLocus_of_isIso_restrictFunctor_map {F G : X.Modules} (α : F ⟶ G)
    (U : X.Opens) (h : IsIso ((Scheme.Modules.restrictFunctor U.ι).map α)) :
    (U : Set X) ⊆ stalkIsoLocus α := by
  intro y hy
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictStalkNatIso U.ι (⟨y, hy⟩ : U)) α).mp
      (by dsimp only [Functor.comp_map]; have := h; infer_instance)

/-- **The locus where a morphism of modules is an isomorphism on stalks is open**, provided the
source is of finite type and the target is coherent.

This is [Stacks, Tag 01Y3] part (4) made into an open set: that tag gives, at each point of the
locus, an open neighbourhood over which the morphism is invertible, and invertibility over an
open forces the locus to contain the whole of it. -/
theorem isOpen_stalkIsoLocus {F G : X.Modules} [F.IsFiniteType]
    [_root_.SheafOfModules.IsCoherent G] (α : F ⟶ G) : IsOpen (stalkIsoLocus α) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, hiso⟩ := AlgebraicGeometry.exists_isIso_over_of_stalk_isIso α x hx
  exact ⟨(U : Set X), subset_stalkIsoLocus_of_isIso_restrictFunctor_map α U
    (IdealPowerColimit.isIso_restrictFunctor_map_of_isIso_over U α hiso), U.isOpen, hxU⟩

/-- **A morphism of modules restricts to an isomorphism over any open contained in its stalkwise
isomorphism locus.**  No finiteness hypothesis is needed: invertibility of a morphism of sheaves
of modules over a space is detected stalkwise. -/
theorem isIso_restrictFunctor_map_of_subset {F G : X.Modules} (α : F ⟶ G) (U : X.Opens)
    (hU : (U : Set X) ⊆ stalkIsoLocus α) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso _ _ fun y => ?_
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictStalkNatIso U.ι y) α).mpr (hU y.2)

/-- **A morphism which is a stalkwise isomorphism at every point of a subset restricts to an
isomorphism over an open neighbourhood of that subset.**

For a morphism from a module of finite type to a coherent module, this is the local-to-global
form of [Stacks, Tag 01Y3] part (4): the open neighbourhood can be taken to be the whole
stalkwise isomorphism locus, which is open. -/
theorem exists_isIso_restrictFunctor_map_of_subset_stalkIsoLocus {F G : X.Modules}
    [F.IsFiniteType] [_root_.SheafOfModules.IsCoherent G] (α : F ⟶ G) (Z : Set X)
    (hZ : Z ⊆ stalkIsoLocus α) :
    ∃ U : X.Opens, Z ⊆ (U : Set X) ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) :=
  ⟨⟨stalkIsoLocus α, isOpen_stalkIsoLocus α⟩, hZ,
    isIso_restrictFunctor_map_of_subset α _ subset_rfl⟩

end Stacks.AlgebraicGeometry.IsoLocus

end
