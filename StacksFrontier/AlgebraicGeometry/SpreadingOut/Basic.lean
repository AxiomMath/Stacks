module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Spreading out a trivialization along a finite morphism, for Stacks 0C0T

Stacks Tag 0C0T says: for `f : X ⟶ Y` finite, `V ⊆ Y` open with `f ∣_ V` an isomorphism and
`Vᶜ` discrete, every invertible `𝒪_X`-module is the pullback of an invertible `𝒪_Y`-module.

The elementary route to that assertion is: for each `t ∈ Vᶜ`, trivialise the module on `f⁻¹(U_t)`
for some open `U_t ∋ t`, shrink `U_t` so that `U_t ∩ Vᶜ = {t}`, and glue over `{V} ∪ {U_t}`. This
file supplies the **spreading-out** step of that route, together with the assembled covering it
produces.

## Main results

All names below live in the namespace `Stacks.AlgebraicGeometry.Tag0C0TSpreadingOut`.

* `exists_opens_mem_preimage_le`: for a morphism of schemes whose underlying map is closed, an
  open containing the fibre over `t` contains the preimage of an open neighbourhood of `t`. This
  is the spreading-out step in purely topological form, and it is where finiteness of `f` is
  spent.
* `exists_opens_trivialization_preimage`: the same statement carrying a sectionwise trivialization
  along with it.
* `exists_opens_trivialization_preimage_of_fiber_subset_singleton`: for `f` finite and `L`
  invertible, if the fibre over `t` has at most one point then `L` is sectionwise trivial on
  `f⁻¹(U)` for some open `U ∋ t`. No hypothesis on `V` is used.
* `exists_opens_inter_compl_eq_singleton`: the discreteness hypothesis of Tag 0C0T, in the form
  the route uses.
* `exists_opens_cover_trivialization_of_fiber_subset_singleton`: the two steps combined — a family
  of opens of `Y`, indexed by `Vᶜ`, which together with `V` covers `Y`, each meeting `Vᶜ` in
  exactly its own point, and each with `L` sectionwise trivial on its preimage. This is the
  complete input to the gluing step, so with it the only thing between this file and Tag 0C0T is
  that gluing and the removal of the one-point-fibre hypothesis.

## The local input

The source's proof trivialises `L` near a point of `Vᶜ` through the triviality of the Picard group
of a semilocal ring (`Subsingleton (CommRing.Pic R)` for `[Finite (MaximalSpectrum R)]` in
Mathlib). The ring in question presents `X ×_Y Spec 𝒪_{Y,t}`, and passing from a trivialization
there to one over `f⁻¹(U_t)` is a spreading-out across a limit. This file treats the case where
the limit does not appear: when the fibre over `t` has at most one point, `L` is already trivial
near that point, and closedness of `f` carries the trivialization down to a neighbourhood of `t`.

## Implementation notes

**Nothing crosses an open immersion.** The currency throughout is
`Stacks.SheafDescent.Trivialization`, which is a family of isomorphisms **on sections** over the
objects lying over an open, so restricting one is `Stacks.SheafDescent.Trivialization.comp` — a
reindexing, with no module sheaf moved anywhere. There is consequently no `eqToHom` and no
compiler option in this file. Producing a trivialization through a point is
`Stacks.SectionProduct.exists_trivialization_at`, and the result that consumes a covering family
of them is `Stacks.SheafDescent.isInvertible_of_trivialization`, so the shape below is already
the one the gluing step wants.

**Invertibility is an explicit argument.** `Stacks.SheafOfModules.IsInvertible X.presheaf hX L` is
the predicate Tag 0C0T's statement uses, with `hX` a *proof* that the composite of `X.presheaf`
with `forget₂ CommRingCat RingCat` is a sheaf; instance search does not see through
`AlgebraicGeometry.Scheme.ringCatSheaf` to find it. So invertibility is passed as an ordinary
hypothesis and the sheaf proof as an implicit argument, which is checked by unification at default
transparency rather than by instance synthesis, and the bridge to
`Stacks.Ample.IsInvertibleModule` is applied by hand through
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`.

**The topological step.** `IsClosedMap.comap_nhds_le` (pinned Mathlib,
`Mathlib/Topology/Maps/Basic.lean`) says `comap f (𝓝 t) ≤ 𝓝ˢ (f ⁻¹' {t})` for a closed map, which is
exactly "an open containing the fibre contains the preimage of a neighbourhood"; the neighbourhood
is replaced by its interior to make it an `Opens`. Closedness of a finite morphism is
`AlgebraicGeometry.Scheme.Hom.isClosedMap`.

## References

* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Filter
open scoped Topology

universe u

namespace Stacks.AlgebraicGeometry.Tag0C0TSpreadingOut

/-! ### The Picard group of a semilocal ring -/

/-! ### Spreading out along a closed map -/

/-- **An open containing a fibre of a closed map contains the preimage of a neighbourhood of the
point.** For `f : X ⟶ Y` with closed underlying map, `t : Y` and `W` an open of `X` containing
`f⁻¹(t)`, there is an open `U ∋ t` of `Y` with `f ⁻¹ᵁ U ≤ W`.

This is `IsClosedMap.comap_nhds_le` — the characterisation of a closed map as
`comap f (𝓝 t) ≤ 𝓝ˢ (f ⁻¹' {t})` — with the resulting neighbourhood of `t` replaced by its
interior so as to be an open of `Y`. It is the step of Tag 0C0T's route in which finiteness of
`f` is spent, and nothing about modules enters it. -/
theorem exists_opens_mem_preimage_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedMap f.base) (t : Y) (W : X.Opens)
    (hW : f.base ⁻¹' {t} ⊆ (W : Set X)) :
    ∃ U : Y.Opens, t ∈ U ∧ f ⁻¹ᵁ U ≤ W := by
  obtain ⟨S, hS, hSW⟩ := hf.comap_nhds_le (W.isOpen.mem_nhdsSet.mpr hW)
  refine ⟨⟨interior S, isOpen_interior⟩, mem_interior_iff_mem_nhds.mpr hS, fun x hx ↦ ?_⟩
  have hxS : f.base x ∈ interior S := hx
  exact hSW (Set.mem_preimage.mpr (interior_subset hxS))

/-- **A sectionwise trivialization on an open containing a fibre of a closed map descends to the
preimage of a neighbourhood of the point.** The open `U` is the one produced by
`Stacks.AlgebraicGeometry.Tag0C0TSpreadingOut.exists_opens_mem_preimage_le`, and the
trivialization is carried to `f ⁻¹ᵁ U` by `Stacks.SheafDescent.Trivialization.comp` along the
inclusion `f ⁻¹ᵁ U ⟶ W`: a trivialization is a family of isomorphisms on sections indexed by the
objects lying over `W`, so its restriction is a reindexing and no sheaf is moved. -/
theorem exists_opens_trivialization_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedMap f.base) (L : X.Modules) (t : Y) (W : X.Opens)
    (hW : f.base ⁻¹' {t} ⊆ (W : Set X))
    (tw : Stacks.SheafDescent.Trivialization X.presheaf L.val W) :
    ∃ U : Y.Opens, t ∈ U ∧
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf L.val (f ⁻¹ᵁ U)) := by
  obtain ⟨U, htU, hUW⟩ := exists_opens_mem_preimage_le f hf t W hW
  exact ⟨U, htU, ⟨tw.comp (homOfLE hUW)⟩⟩

/-- **Tag 0C0T's local input, for a fibre with at most one point.** If `f : X ⟶ Y` is finite, `L`
is an invertible `𝒪_X`-module, and the fibre of `f` over `t` is contained in a single point, then
`L` is sectionwise trivial on `f ⁻¹ᵁ U` for some open `U ∋ t`.

No hypothesis on an open `V ⊆ Y`, and no discreteness, is used. The point is that for a
one-point fibre the semilocal Picard group of Tag 0C0T's proof is not needed: clause 2 of Tag 0B8M
already trivialises `L` near the single point, in the form
`Stacks.SectionProduct.exists_trivialization_at`, and closedness of a finite morphism —
`AlgebraicGeometry.Scheme.Hom.isClosedMap` — carries that trivialization down to a neighbourhood
of `t`. The invertibility hypothesis is the predicate Tag 0C0T is stated with, bridged to the
class `Stacks.Ample.IsInvertibleModule` by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. -/
theorem exists_opens_trivialization_preimage_of_fiber_subset_singleton {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (L : X.Modules)
    {hX : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf)}
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf hX L)
    (t : Y) (x : X) (hfib : f.base ⁻¹' {t} ⊆ {x}) :
    ∃ U : Y.Opens, t ∈ U ∧
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf L.val (f ⁻¹ᵁ U)) := by
  have : Stacks.Ample.IsInvertibleModule X L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf hX L).mp hL
  obtain ⟨W, hxW, ⟨tw⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L x
  exact exists_opens_trivialization_preimage f (Scheme.Hom.isClosedMap f) L t W
    (hfib.trans (Set.singleton_subset_iff.mpr hxW)) tw

/-! ### The discreteness hypothesis -/

/-- **Tag 0C0T's discreteness hypothesis, in the form its route uses.** If the complement of an
open `V` of a scheme carries the discrete topology, then every point `t ∉ V` has an open
neighbourhood meeting that complement only in `t`.

This is Mathlib's `isOpen_inter_eq_singleton_of_mem_discrete`, whose hypothesis `IsDiscrete`
is `isDiscrete_iff_discreteTopology` applied to the hypothesis as Tag 0C0T states it. Membership
`t ∈ U` is not asserted separately because it follows from the displayed equality. -/
theorem exists_opens_inter_compl_eq_singleton {Y : Scheme.{u}} (V : Y.Opens)
    [DiscreteTopology ((V : Set Y)ᶜ : Set Y)] {t : Y} (ht : t ∉ V) :
    ∃ U : Y.Opens, (U : Set Y) ∩ (V : Set Y)ᶜ = {t} := by
  obtain ⟨U, hU, hUV⟩ := isOpen_inter_eq_singleton_of_mem_discrete
    (s := ((V : Set Y)ᶜ)) (isDiscrete_iff_discreteTopology.mpr ‹_›) ht
  exact ⟨⟨U, hU⟩, hUV⟩

/-! ### The covering the gluing step consumes -/

/-- **The complete input to Tag 0C0T's gluing step, when every fibre over `Vᶜ` has at most one
point.** For `f : X ⟶ Y` finite, `V` an open of `Y` with discrete complement, and `L` an
invertible `𝒪_X`-module whose fibres over `Vᶜ` are contained in single points, there is a family
`U` of opens of `Y` indexed by `Vᶜ` such that

* `t ∈ U t` for every `t ∈ Vᶜ`;
* `U t` meets `Vᶜ` in exactly `t`, so the members of the family overlap only inside `V`;
* `V` together with the `U t` covers `Y`;
* `L` is sectionwise trivial on `f ⁻¹ᵁ (U t)` for every `t`.

Each `U t` is the intersection of the neighbourhood supplied by
`Stacks.AlgebraicGeometry.Tag0C0TSpreadingOut.exists_opens_inter_compl_eq_singleton` with the one
supplied by `exists_opens_trivialization_preimage_of_fiber_subset_singleton` in this same
namespace; the trivialization survives the intersection because a trivialization restricts along
any inclusion of opens.

**What remains between this and Tag 0C0T.** Over `V` the module asked for already exists, as
`Stacks.AlgebraicGeometry.InvertibleFiniteDescent.exists_isInvertible_pullback_iso_restrict`, and
over `U t` it is the structure sheaf, by the trivialization above. What is not done is the gluing
of those pieces
into a single invertible `𝒪_Y`-module together with an isomorphism `f^* M ≅ L`: that asks for the
comparison isomorphisms of a `Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData` over the
overlaps, with their naturality and cocycle conditions, and none of those is constructed here.
The other missing piece is the one-point-fibre hypothesis itself, which is what the semilocal
Picard group of the source's proof removes; see the module docstring. -/
theorem exists_opens_cover_trivialization_of_fiber_subset_singleton {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (V : Y.Opens) [DiscreteTopology ((V : Set Y)ᶜ : Set Y)]
    (L : X.Modules)
    {hX : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf)}
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf hX L)
    (hfib : ∀ t : Y, t ∉ V → ∃ x : X, f.base ⁻¹' {t} ⊆ {x}) :
    ∃ U : ((V : Set Y)ᶜ : Set Y) → Y.Opens,
      (∀ t, (t : Y) ∈ U t) ∧
      (∀ t, (U t : Set Y) ∩ (V : Set Y)ᶜ = {(t : Y)}) ∧
      V ⊔ ⨆ t, U t = ⊤ ∧
      ∀ t, Nonempty (Stacks.SheafDescent.Trivialization X.presheaf L.val (f ⁻¹ᵁ U t)) := by
  have key : ∀ t : ((V : Set Y)ᶜ : Set Y), ∃ U : Y.Opens,
      (U : Set Y) ∩ (V : Set Y)ᶜ = {(t : Y)} ∧ (t : Y) ∈ U ∧
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf L.val (f ⁻¹ᵁ U)) := by
    intro t
    obtain ⟨x, hx⟩ := hfib t t.2
    obtain ⟨U₁, hU₁⟩ := exists_opens_inter_compl_eq_singleton V t.2
    obtain ⟨U₂, htU₂, ⟨tw⟩⟩ :=
      exists_opens_trivialization_preimage_of_fiber_subset_singleton f L hL (t : Y) x hx
    have htU₁ : (t : Y) ∈ U₁ := (hU₁.ge rfl).1
    refine ⟨U₁ ⊓ U₂, ?_, ⟨htU₁, htU₂⟩, ⟨tw.comp (homOfLE ?_)⟩⟩
    · refine subset_antisymm (fun y hy ↦ hU₁.le ⟨hy.1.1, hy.2⟩) ?_
      rintro y rfl
      exact ⟨⟨htU₁, htU₂⟩, t.2⟩
    · exact f.preimage_mono inf_le_right
  choose U hUinter hUmem hUtriv using key
  refine ⟨U, hUmem, hUinter, ?_, hUtriv⟩
  refine top_le_iff.mp fun y _ ↦ ?_
  by_cases hy : y ∈ V
  · exact Or.inl hy
  · exact Or.inr (Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hUmem ⟨y, hy⟩⟩)

end Stacks.AlgebraicGeometry.Tag0C0TSpreadingOut

end
