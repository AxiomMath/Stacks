module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleBaseChange

/-!
# The lisse-étale site of a scheme: subcanonicality and the empty object

Two properties of the lisse-étale site of the algebraic stack of a scheme `U` over `S`, both of
them consumed by the counterexample of **Stacks 07BG**.

The first is that the site is *subcanonical*: representable presheaves on it are sheaves. The
second concerns a smooth object whose underlying scheme is empty — the empty scheme is smooth
over anything, so such an object exists as soon as the empty scheme belongs to the big site. It
is initial in the site, and the *empty* family covers it.

Together these two say that the empty family covers an object exactly when that object is empty:
one direction is `AlgebraicGeometry.Stack.LisseEtale.bot_mem_topology_of_isEmpty`, and the other
is `CategoryTheory.GrothendieckTopology.bot_notMem_of_isEmpty_hom` applied with the
subcanonicality below. That equivalence is what turns the collapse of an equaliser into a
contradiction in 07BG.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.homOfIsEmpty`: the unique morphism out of an empty smooth
  object.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.subcanonical_topology`: the lisse-étale site of a scheme is
  subcanonical.
* `AlgebraicGeometry.Stack.LisseEtale.hom_ext_of_isEmpty`: at most one morphism leaves an empty
  smooth object.
* `AlgebraicGeometry.Stack.LisseEtale.bot_mem_topology_of_isEmpty`: the empty family covers an
  empty smooth object.

## Implementation notes

Subcanonicality is transported from the ambient étale site along the inclusion of the smooth
objects by `CategoryTheory.GrothendieckTopology.subcanonical_of_full_of_faithful`: the inclusion
is fully faithful and, by `AlgebraicGeometry.Stack.LisseEtale.isContinuous_inclusion_topology'`,
continuous. The ambient site is subcanonical because it is a double localization of the big étale
topology (`AlgebraicGeometry.Stack.LisseEtale.associatedTopology_schemeStack`), which is coarser
than the chosen fppf topology and so subcanonical by
`AlgebraicGeometry.BigFppfSite.subcanonical_topology`.

An empty smooth object is initial because a morphism of the site is determined by the morphism of
schemes underneath it — the inclusion of the big site into all schemes is faithful, and the two
slice forgetful functors are — and the empty scheme is initial among schemes.

The empty family is a *chosen* étale covering family of the big site in the sense of
**Stacks 03FF**: its index type is empty, so the cardinality bound of the chosen system is
satisfied, and the empty family of an empty scheme is jointly surjective with every member
satisfying any property whatever.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07BG](https://stacks.math.columbia.edu/tag/07BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The lisse-étale site of a scheme is subcanonical.** -/
theorem subcanonical_topology (U : BigFppfOver B S hS) :
    (topology.{u, w} B S hS (schemeStack.{u, w} B S hS U)).Subcanonical := by
  have h1 : (etaleTopology B).Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le (etaleTopology_le_topology B)
  have h2 : ((etaleTopology B).over (B.obj hS)).Subcanonical :=
    GrothendieckTopology.subcanonical_over (etaleTopology B) (B.obj hS)
  have hA : (associatedTopology B S hS
      (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B)).Subcanonical := by
    rw [associatedTopology_schemeStack.{u, w} B S hS U]
    exact GrothendieckTopology.subcanonical_over
      ((etaleTopology B).over (B.obj hS)) U
  have hc := isContinuous_inclusion_topology'.{u, w} B S hS (schemeStack.{u, w} B S hS U)
  exact GrothendieckTopology.subcanonical_of_full_of_faithful
    (inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    (topology.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))

variable {U : BigFppfOver B S hS}

/-- An empty smooth object of the lisse-étale site of a scheme admits at most one morphism to
any object. -/
theorem hom_ext_of_isEmpty
    {V W : LisseEtale.{u, w} B S hS (schemeStack.{u, w} B S hS U)}
    [IsEmpty (B.inclusion.obj
      ((toSchemes.{u, w} B S hS (schemeStack.{u, w} B S hS U)).obj V))]
    (f g : V ⟶ W) : f = g := by
  have : IsEmpty (B.inclusion.obj V.obj.left.left) := ‹IsEmpty _›
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  exact isInitialOfIsEmpty.hom_ext _ _

/-- An empty smooth object of the lisse-étale site of a scheme admits a morphism to any object:
its underlying scheme is initial. -/
noncomputable def homOfIsEmpty
    (V W : LisseEtale.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    [IsEmpty (B.inclusion.obj
      ((toSchemes.{u, w} B S hS (schemeStack.{u, w} B S hS U)).obj V))] : V ⟶ W := by
  have : IsEmpty (B.inclusion.obj V.obj.left.left) := ‹IsEmpty _›
  let k := B.inclusion.preimage (X := V.obj.left.left) (Y := W.obj.left.left)
    (isInitialOfIsEmpty.to _)
  have hk : k ≫ W.obj.left.hom = V.obj.left.hom :=
    B.inclusion.map_injective (isInitialOfIsEmpty.hom_ext _ _)
  exact ObjectProperty.homMk (Over.homMk (Over.homMk k hk)
    (Over.OverMorphism.ext (B.inclusion.map_injective (isInitialOfIsEmpty.hom_ext _ _))))

/-- **The empty family covers an empty smooth object of the lisse-étale site of a scheme.** It is
a chosen étale covering family of the big site, since the empty family of an empty scheme is
jointly surjective and every one of its (nonexistent) members is étale. -/
theorem bot_mem_topology_of_isEmpty
    (V : LisseEtale.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    [IsEmpty (B.inclusion.obj
      ((toSchemes.{u, w} B S hS (schemeStack.{u, w} B S hS U)).obj V))] :
    (⊥ : Sieve V) ∈ topology.{u, w} B S hS (schemeStack.{u, w} B S hS U) V := by
  set E := PreZeroHypercover.empty.{u + 1} V
  set G := toSchemes.{u, w} B S hS (schemeStack.{u, w} B S hS U)
  have hb : ((E.map G).map B.inclusion).presieve₀ = (⊥ : Presieve _) := by
    refine le_antisymm ?_ bot_le
    rintro Y g ⟨i⟩
    exact i.elim
  have hE : IsCovering.{u, w} B S hS (schemeStack.{u, w} B S hS U) ⟨V, E⟩ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (E.map G).presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion _
      rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map, hb]
      exact Scheme.bot_mem_precoverage _ _
    · simp [E]
    · change ((E.map G).map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage _
      rw [hb]
      exact Scheme.bot_mem_precoverage _ _
  simpa [E] using (precoverage.{u, w} B S hS
    (schemeStack.{u, w} B S hS U)).generate_mem_toGrothendieck
      (R := E.presieve₀) ⟨E, rfl, hE⟩

end AlgebraicGeometry.Stack.LisseEtale

end
