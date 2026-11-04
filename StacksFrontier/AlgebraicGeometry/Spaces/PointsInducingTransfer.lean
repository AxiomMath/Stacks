module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Transferring the inducing property along a cartesian square of presheaves

Let
```
W ⟶ P
↓    ↓
Z ⟶ X
```
be a cartesian square of presheaves on the big fppf site of `S`, with `W ⟶ P` inducing on the
point spaces of Tag 03BU, `W ⟶ Z` surjective on points, and `P ⟶ X` open on points. Then
`Z ⟶ X` is inducing. This is the step by which a statement about the point topology of a
morphism of algebraic spaces is reduced to the same statement for a base change of it along an
étale chart, and it is used twice in the proof of Tag 0AC8: once to pass from the target to an
étale chart of it, and once to pass from the source to an étale atlas of the source.

The argument is the one in the proof of Tag 0ABJ, which is carried out for an immersion in
`StacksFrontier/AlgebraicGeometry/Spaces/ImmersionPointEmbedding.lean`; here it is isolated from
the hypotheses of that tag.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isInducing_pointsMap_of_exists_points` and
  `AlgebraicGeometry.Space.isInducing_pointsMap_of_isPullback`: the transfer statement, for a
  commuting square with the point-lifting property and for a cartesian square.
* `AlgebraicGeometry.Space.mono_toScheme_map`: a monomorphism of the big fppf site of `S` has
  a monomorphic underlying morphism of schemes.
* `AlgebraicGeometry.Space.exists_isOpen_inter_eq_singleton`: a nonempty finite subset of a
  T0 space has a point isolated in it by an open set of the ambient space.

## Implementation notes

The point topology of Tag 03BX, `AlgebraicGeometry.Space.pointTopology`, is installed as a
local instance, as elsewhere in this directory.

The three hypotheses of the transfer enter in three different places. An open set of `|Z|`
pulls back to an open set of `|W|`, which is the preimage along `|W| → |P|` of an open set `O`
of `|P|` because that map is inducing; the image of `O` in `|X|` is open because `|P| → |X|` is
open; one inclusion of the identification of its preimage with the original open set is Tag
03H4 for the square (`AlgebraicGeometry.Space.exists_points_of_isPullback`), and the other is
surjectivity of `|W| → |Z|`.

`AlgebraicGeometry.Space.mono_toScheme_map` is not an instance of faithfulness, which gives
only the converse implication: it holds because
`AlgebraicGeometry.BigFppfOver.toScheme` preserves pullbacks, and being a monomorphism is the
statement that the square on the identities is cartesian
(`CategoryTheory.IsKernelPair.id_of_mono`).

`AlgebraicGeometry.Space.exists_isOpen_inter_eq_singleton` is the shrinking step of the proof
of Tag 0AC8, which the source performs with the words "after shrinking `V` we may assume `v` is
the only one". No point of a finite set need be isolated in the ambient space, and no point of
the set need be isolated in it either unless the chosen point is allowed to vary: what is true,
and what the statement says, is that *some* point of the set is, namely one which is maximal
for the specialization order. Finiteness is needed, and the T0 axiom, which for a scheme is
`AlgebraicGeometry.Scheme.instT0Space`.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Isolating a point of a finite subset of a T0 space -/

/-- **The shrinking step.** A nonempty finite subset `F` of a T0 topological space contains a
point `v` which an open set of the ambient space separates from the rest of `F`.

The point cannot be prescribed: in the spectrum of a discrete valuation ring the fibre of the
identity over the closed point is a single point which no open set separates from the generic
point. A point maximal for the specialization order works, and one exists because `F` is
finite; the open set is then the complement of the closures of the other points of `F`. -/
theorem exists_isOpen_inter_eq_singleton {α : Type*} [TopologicalSpace α] [T0Space α]
    {F : Set α} (hfin : Set.Finite F) (hne : F.Nonempty) :
    ∃ v ∈ F, ∃ O : Set α, IsOpen O ∧ v ∈ O ∧ O ∩ F = {v} := by
  obtain ⟨v, hvF, hmax⟩ := Set.Finite.exists_maximalFor (fun x : α => closure {x}) F hfin hne
  have hkey : ∀ v' ∈ F, v ∈ closure {v'} → v' = v := by
    intro v' hv' hmem
    have h1 : closure {v} ⊆ closure {v'} :=
      closure_minimal (by simpa using hmem) isClosed_closure
    have h2 : closure {v'} ⊆ closure {v} := hmax hv' h1
    exact ((specializes_iff_closure_subset.mpr h2).antisymm
      (specializes_iff_closure_subset.mpr h1)).eq.symm
  have hvC : v ∉ ⋃ v' ∈ F \ {v}, closure {v'} := by
    intro hmem
    obtain ⟨v', hv', hmemc⟩ := Set.mem_iUnion₂.mp hmem
    exact hv'.2 (hkey v' hv'.1 hmemc)
  refine ⟨v, hvF, (⋃ v' ∈ F \ {v}, closure {v'})ᶜ, ?_, hvC, ?_⟩
  · exact ((hfin.sdiff).isClosed_biUnion fun _ _ ↦ isClosed_closure).isOpen_compl
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hvC, hvF⟩, fun x hx ↦ ?_⟩
    by_contra hne'
    exact hx.1 (Set.mem_iUnion₂.mpr ⟨x, ⟨hx.2, hne'⟩, subset_closure rfl⟩)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Monomorphisms of the site on underlying schemes -/

/-- A monomorphism of the big fppf site of `S` has monomorphic underlying morphism of schemes.

Faithfulness of `AlgebraicGeometry.BigFppfOver.toScheme` gives the converse implication only.
This direction holds because that functor preserves pullbacks, and a morphism is a
monomorphism exactly when the square on its identities is cartesian. -/
theorem mono_toScheme_map {a b : BigFppfOver B S hS} (f : a ⟶ b) [Mono f] :
    Mono ((BigFppfOver.toScheme B S hS).map f) := by
  have hk : IsPullback (𝟙 a) (𝟙 a) f f := IsKernelPair.id_of_mono f
  exact IsKernelPair.mono_of_isIso_fst ((BigFppfOver.toScheme B S hS).map_isPullback hk)

/-! ### The transfer -/

attribute [local instance] pointTopology

/-- **Transfer of the inducing property along a commuting square with the lifting property.**
Let
```
W ⟶ P
↓    ↓
Z ⟶ X
```
commute, with `|P| → |X|` open, `|W| → |P|` inducing, `|W| → |Z|` surjective, and every pair
of points of `|Z|` and `|P|` with the same image in `|X|` in the image of a single point of
`|W|`. Then `|Z| → |X|` is inducing.

The lifting hypothesis is weaker than the square being cartesian, which is what
`AlgebraicGeometry.Space.isInducing_pointsMap_of_isPullback` assumes: it is also satisfied by a
square which factors through a cartesian one by a morphism surjective on points, and that is
how the square of the proof of Tag 0AC8 arises — its top left corner is the spectrum of the
residue field of the fibre of a chart rather than that fibre itself. -/
theorem isInducing_pointsMap_of_exists_points
    {W P Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {α : W ⟶ Z} {β : W ⟶ P} {π : Z ⟶ X} {ρ : P ⟶ X} (hcomm : α ≫ π = β ≫ ρ)
    (hρ : IsOpenMap (pointsMap B S hS P ρ))
    (hβ : Topology.IsInducing (pointsMap B S hS W β))
    (hα : Function.Surjective (pointsMap B S hS W α))
    (hlift : ∀ (z : points B S hS Z) (o : points B S hS P),
      pointsMap B S hS Z π z = pointsMap B S hS P ρ o →
      ∃ w : points B S hS W, pointsMap B S hS W α w = z ∧
        pointsMap B S hS W β w = o) :
    Topology.IsInducing (pointsMap B S hS Z π) := by
  have key : ∀ T : Set (points B S hS Z), IsOpen T →
      ∃ V : Set (points B S hS X), IsOpen V ∧ pointsMap B S hS Z π ⁻¹' V = T := by
    intro T hT
    obtain ⟨O, hO, hOeq⟩ := hβ.isOpen_iff.mp
      (hT.preimage (continuous_pointsMap B S hS α))
    have hiff : ∀ w, pointsMap B S hS W β w ∈ O ↔ pointsMap B S hS W α w ∈ T :=
      fun w ↦ Set.ext_iff.mp hOeq w
    refine ⟨pointsMap B S hS P ρ '' O, hρ O hO, ?_⟩
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨o, hoO, hoz⟩
      obtain ⟨w, hwα, hwβ⟩ := hlift z o hoz.symm
      rwa [← hwα, ← hiff, hwβ]
    · intro z hz
      obtain ⟨w, hwα⟩ := hα z
      refine ⟨_, (hiff w).mpr (by rwa [hwα]), ?_⟩
      rw [← hwα, ← pointsMap_apply_comm B S hS hcomm w]
  exact (Topology.isInducing_iff _).mpr (le_antisymm
    (continuous_iff_le_induced.mp (continuous_pointsMap B S hS π))
    (TopologicalSpace.le_def.mpr fun T hT ↦ isOpen_induced_iff.mpr (key T hT)))

/-- **Transfer of the inducing property along a cartesian square.** Let `W = Z ×_X P` be a
cartesian square of presheaves on the big fppf site of `S`. If `|W| → |P|` is inducing,
`|W| → |Z|` is surjective and `|P| → |X|` is open, then `|Z| → |X|` is inducing.

This is the argument of Tag 0ABJ, isolated from the hypotheses of that tag; the point topology
is the one of Tag 03BX. The lifting hypothesis of
`AlgebraicGeometry.Space.isInducing_pointsMap_of_exists_points` is Tag 03H4 for the square. -/
theorem isInducing_pointsMap_of_isPullback
    {W P Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {α : W ⟶ Z} {β : W ⟶ P} {π : Z ⟶ X} {ρ : P ⟶ X} (hsq : IsPullback α β π ρ)
    (hρ : IsOpenMap (pointsMap B S hS P ρ))
    (hβ : Topology.IsInducing (pointsMap B S hS W β))
    (hα : Function.Surjective (pointsMap B S hS W α)) :
    Topology.IsInducing (pointsMap B S hS Z π) :=
  isInducing_pointsMap_of_exists_points B S hS hsq.w hρ hβ hα
    fun z o hzo ↦ exists_points_of_isPullback B S hS hsq z o hzo

end AlgebraicGeometry.Space

end
