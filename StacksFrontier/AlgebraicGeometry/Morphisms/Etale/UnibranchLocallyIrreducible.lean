module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Properties.UnibranchEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.IrreducibleEtaleNeighborhood
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Schemes étale over an irreducible geometrically unibranch scheme are locally irreducible

Let `X` be an irreducible scheme which is geometrically unibranch, and let `W ⟶ X` be étale.
Every point of `W` has an irreducible open neighbourhood, and consequently a connected scheme
étale over `X` is irreducible.

The local statement combines two finiteness facts with the criterion of Stacks Tag 0CB4. An
affine open `W₀` of `W` lying over an affine open of `X` has only finitely many irreducible
components: their generic points lie over the generic point of `X`, because an étale morphism is
generalizing and a generic point of a component has no proper generalization, and the fibre of
`W₀` over that point is finite, the morphism being quasi-compact and locally quasi-finite. On the
other hand `W₀` is an étale neighbourhood of the image of `w`, so by Tag 0CB4 exactly one of its
irreducible components passes through `w`. Deleting the finitely many others leaves an open
neighbourhood of `w` inside one irreducible set.

The global statement is topological: in a quasi-sober space in which every point has an
irreducible open neighbourhood, every irreducible component is open, so a connected such space
is irreducible. Connectedness alone does not suffice for reducible bases: a nodal curve has
connected étale covers which are reducible.

## Main results

* `Topology.exists_isOpen_subset_of_existsUnique_mem_irreducibleComponents` — in a space with
  finitely many irreducible components, a point on exactly one of them has an open neighbourhood
  inside it.
* `Topology.irreducibleSpace_of_connectedSpace_of_forall_exists_isIrreducible` — a connected
  quasi-sober space in which every point has an irreducible open neighbourhood is irreducible.
* `AlgebraicGeometry.exists_isOpen_isIrreducible_of_etale_of_isGeometricallyUnibranch` — the
  local statement.
* `AlgebraicGeometry.irreducibleSpace_of_etale_of_isGeometricallyUnibranch` — the global
  statement.

## References

* [Stacks Project, Tag 0CB4](https://stacks.math.columbia.edu/tag/0CB4)
* [Stacks Project, Tag 0BQ2](https://stacks.math.columbia.edu/tag/0BQ2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace Topology

/-- **A point lying on exactly one of finitely many irreducible components has an open
neighbourhood inside that component**: the complement of the union of the other components. -/
public theorem exists_isOpen_subset_of_existsUnique_mem_irreducibleComponents {α : Type*}
    [TopologicalSpace α] (hfin : (irreducibleComponents α).Finite) {x : α}
    (hx : ∃! Z : irreducibleComponents α, x ∈ (Z : Set α)) :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsPreirreducible U := by
  obtain ⟨Z, hxZ, huniq⟩ := hx
  let others : Set (Set α) := irreducibleComponents α \ {(Z : Set α)}
  have hU : IsOpen (⋃₀ others)ᶜ := by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  refine ⟨(⋃₀ others)ᶜ, hU, ?_, Z.2.1.2.open_subset hU fun y hy ↦ ?_⟩
  · rintro ⟨W, ⟨hW, hWZ⟩, hxW⟩
    exact hWZ (congrArg Subtype.val (huniq ⟨W, hW⟩ hxW))
  · by_contra hyZ
    exact hy ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
      fun h ↦ hyZ (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩

/-- An irreducible set whose closure contains the generic point of an irreducible component lies
in that component, by maximality of the component. -/
private theorem subset_of_mem_closure_of_isGenericPoint {α : Type*} [TopologicalSpace α]
    {Z S : Set α} (hZ : Z ∈ irreducibleComponents α) {ξ : α} (hξ : IsGenericPoint ξ Z)
    (hS : IsIrreducible S) (hξS : ξ ∈ closure S) : S ⊆ Z :=
  subset_closure.trans (hZ.2 hS.closure (by
    rw [← hξ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξS) isClosed_closure))

/-- **A connected quasi-sober space in which every point has an irreducible open neighbourhood is
irreducible.** Such a neighbourhood of a point `z` contains the generic point of every irreducible
component through `z`, so its closure, which is irreducible, contains that component and therefore
equals it; hence every irreducible component is open, and a connected space has only one. -/
public theorem irreducibleSpace_of_connectedSpace_of_forall_exists_isIrreducible {α : Type*}
    [TopologicalSpace α] [QuasiSober α] [ConnectedSpace α]
    (h : ∀ z : α, ∃ U : Set α, IsOpen U ∧ z ∈ U ∧ IsPreirreducible U) : IrreducibleSpace α := by
  obtain ⟨w⟩ := (inferInstance : Nonempty α)
  have hZc : IsClosed (irreducibleComponent w) := isClosed_irreducibleComponent
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := w)) hZc
  have hZo : IsOpen (irreducibleComponent w) := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hUo, hzU, hUirr⟩ := h z
    exact ⟨U, subset_of_mem_closure_of_isGenericPoint
      (irreducibleComponent_mem_irreducibleComponents w) hξ ⟨⟨z, hzU⟩, hUirr⟩
      (subset_closure ((hξ.specializes hz).mem_open hUo hzU)), hUo, hzU⟩
  have huniv : irreducibleComponent w = Set.univ :=
    (isClopen_iff.mp ⟨hZc, hZo⟩).resolve_left (Set.nonempty_iff_ne_empty.mp
      ⟨w, mem_irreducibleComponent⟩)
  refine (irreducibleSpace_def α).2 ?_
  rw [Set.top_eq_univ, ← huniv]
  exact isIrreducible_irreducibleComponent

end Topology

namespace AlgebraicGeometry

/-- **A generic point of an irreducible component of a scheme étale over an irreducible scheme
lies over the generic point.** An étale morphism is generalizing, so the generic point of the base
lifts to a generalization of the point, which is the point itself by maximality. -/
@[ega "IV 18.10.6" "(i), (ii)"]
public theorem map_eq_genericPoint_of_mem_irreducibleComponents {W X : Scheme.{u}} (f : W ⟶ X)
    [Flat f] [IrreducibleSpace X] {Z : Set W} (hZ : Z ∈ irreducibleComponents W) {ξ : W}
    (hξ : IsGenericPoint ξ Z) : f.base ξ = genericPoint X := by
  obtain ⟨ξ', hξ'ξ, hfξ'⟩ := Flat.generalizingMap f (genericPoint_specializes (f.base ξ))
  have hξ'Z : ξ' ∈ Z := Topology.subset_of_mem_closure_of_isGenericPoint hZ hξ
    isIrreducible_singleton hξ'ξ.mem_closure rfl
  have : ξ' = ξ := (hξ'ξ.antisymm (hξ.specializes hξ'Z)).eq
  rw [← this, hfξ']

/-- **A quasi-compact scheme étale over an irreducible scheme has finitely many irreducible
components**: their generic points lie over the generic point of the base, and the fibre over it
of a quasi-compact locally quasi-finite morphism is finite. -/
@[sga "7 VIII 5.2" "special case"]
public theorem finite_irreducibleComponents_of_etale_of_quasiCompact {W X : Scheme.{u}}
    (f : W ⟶ X) [Etale f] [QuasiCompact f] [IrreducibleSpace X] :
    (irreducibleComponents W).Finite := by
  have : LocallyQuasiFinite f := (locallyQuasiFinite_of_etale f).2
  have hfin := f.finite_preimage_singleton (genericPoint X)
  have hgen : ∀ Z ∈ irreducibleComponents W, ∃ ξ : W, IsGenericPoint ξ Z := fun Z hZ ↦
    QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  rcases isEmpty_or_nonempty W with hW | hW
  · refine Set.finite_empty.subset fun Z hZ ↦ ?_
    obtain ⟨z, -⟩ := hZ.1.nonempty
    exact isEmptyElim z
  choose! g hg using hgen
  refine Set.Finite.of_finite_image (f := g) (hfin.subset ?_) ?_
  · rintro _ ⟨Z, hZ, rfl⟩
    exact map_eq_genericPoint_of_mem_irreducibleComponents f hZ (hg Z hZ)
  · intro Z₁ hZ₁ Z₂ hZ₂ h
    rw [← (hg Z₁ hZ₁).def, ← (hg Z₂ hZ₂).def, h]

/-- **A scheme étale over an irreducible, geometrically unibranch scheme is locally
irreducible**: every point has an irreducible open neighbourhood. -/
@[sga "3 X 5.14.0" "partial"]
public theorem exists_isOpen_isPreirreducible_of_etale_of_isGeometricallyUnibranch
    {W X : Scheme.{u}} (f : W ⟶ X) [Etale f] [IrreducibleSpace X]
    (hX : IsGeometricallyUnibranch X) (w : W) :
    ∃ U : Set W, IsOpen U ∧ w ∈ U ∧ IsPreirreducible U := by
  obtain ⟨X₀, hX₀, hwX₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := f.base w) (U := ⊤) (by simp)
  obtain ⟨W₀, hW₀, hwW₀, hW₀le⟩ :=
    exists_isAffineOpen_mem_and_subset (X := W) (x := w) (U := f ⁻¹ᵁ X₀) hwX₀
  have : IsAffine W₀ := hW₀
  have : IsAffine X₀ := hX₀
  have : IrreducibleSpace X₀ := Subtype.irreducibleSpace
    ⟨⟨f.base w, hwX₀⟩, (IrreducibleSpace.isIrreducible_univ X).2.open_subset X₀.2
      (Set.subset_univ _)⟩
  have : Etale (f.resLE X₀ W₀ hW₀le) :=
    MorphismProperty.of_postcomp @Etale (W' := @Etale) (f.resLE X₀ W₀ hW₀le) X₀.ι
      (inferInstanceAs (Etale X₀.ι))
      ((Scheme.Hom.resLE_comp_ι f hW₀le).symm ▸ inferInstanceAs (Etale (W₀.ι ≫ f)))
  let N : EtaleNeighborhood X (f.base w) :=
    { scheme := W₀
      point := ⟨w, hwW₀⟩
      toBase := W₀.ι ≫ f
      map_point := rfl }
  have huniq := (isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent X
    (f.base w)).1 (hX _) N
  obtain ⟨U₀, hU₀o, hwU₀, hU₀irr⟩ :=
    Topology.exists_isOpen_subset_of_existsUnique_mem_irreducibleComponents
      (finite_irreducibleComponents_of_etale_of_quasiCompact (f.resLE X₀ W₀ hW₀le)) huniq
  exact ⟨Subtype.val '' U₀, W₀.2.isOpenEmbedding_subtypeVal.isOpenMap _ hU₀o, ⟨_, hwU₀, rfl⟩,
    hU₀irr.image _ continuous_subtype_val.continuousOn⟩

/-- **A connected scheme étale over an irreducible, geometrically unibranch scheme is
irreducible.** -/
@[sga "3 X 5.14.0" "partial", sga "7 XVIII 6.1.5" "more general"]
public theorem irreducibleSpace_of_etale_of_isGeometricallyUnibranch {W X : Scheme.{u}}
    (f : W ⟶ X) [Etale f] [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
    [ConnectedSpace W] : IrreducibleSpace W :=
  Topology.irreducibleSpace_of_connectedSpace_of_forall_exists_isIrreducible
    (exists_isOpen_isPreirreducible_of_etale_of_isGeometricallyUnibranch f hX)

end AlgebraicGeometry
